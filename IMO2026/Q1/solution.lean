import Mathlib
open Multiset
open Nat

set_option backward.isDefEq.respectTransparency false

-- ============================================================
-- Definitions (mirroring `IMO2026/Q1/problem.lean`; this file is
-- self-contained so the verifier, which ignores imports, can check it).
-- ============================================================

abbrev Board : Type := Multiset ℕ

def IsInitial (B : Board) : Prop :=
  Multiset.card B = 2026 ∧ ∀ a ∈ B, 1 < a

def Move (B B' : Board) : Prop :=
  ∃ (m n : ℕ) (s : Board), 1 < m ∧ 1 < n ∧
    B = m ::ₘ n ::ₘ s ∧
    B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s

def IsTerminal (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) ≤ 1

def HasUniqueLarge (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) = 1

def Reachable (B B' : Board) : Prop := Relation.ReflTransGen Move B B'

noncomputable def gExp (p : ℕ) (B : Board) : ℕ :=
  (B.map (fun a => padicValNat p a)).gcd

noncomputable def Mval (B : Board) : ℕ :=
  ∏ p ∈ B.prod.primeFactors, p ^ gExp p B

-- ============================================================
-- Count and product of entries > 1
-- ============================================================

def count_gt_one (B : Board) : ℕ := Multiset.card (B.filter (fun a => 1 < a))

def prod_gt_one (B : Board) : ℕ := (B.filter (fun a => 1 < a)).prod

lemma count_gt_one_cons (a : ℕ) (s : Board) :
    count_gt_one (a ::ₘ s) = count_gt_one s + (if 1 < a then 1 else 0) := by
  unfold count_gt_one
  rw [Multiset.filter_cons]
  by_cases h : 1 < a
  · rw [if_pos h, Multiset.card_add, Multiset.card_singleton, if_pos h, add_comm]
  · rw [if_neg h, if_neg h, Multiset.card_add, Multiset.card_zero, Nat.zero_add, Nat.add_zero]

lemma prod_gt_one_cons (a : ℕ) (s : Board) :
    prod_gt_one (a ::ₘ s) = (if 1 < a then a else 1) * prod_gt_one s := by
  unfold prod_gt_one
  rw [Multiset.filter_cons]
  by_cases h : 1 < a
  · rw [if_pos h, Multiset.prod_add, Multiset.prod_singleton, if_pos h]
  · rw [if_neg h, if_neg h, zero_add, one_mul]

-- Every entry of a filtered-by-(1 < ·) multiset is ≥ 2, hence ≥ 1, so the
-- product is ≥ 1.
lemma prod_le_prod_of_all_le {t : Board} (h : ∀ x ∈ t, 1 ≤ x) : 1 ≤ t.prod := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons]
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self a t)
    have ht : 1 ≤ t.prod := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    calc (1 : ℕ) = 1 * 1 := by simp
      _ ≤ a * t.prod := Nat.mul_le_mul ha ht

lemma prod_gt_one_pos (s : Board) : 0 < prod_gt_one s :=
  prod_le_prod_of_all_le (fun x hx => le_of_lt (Multiset.mem_filter.mp hx).2)

lemma prod_eq_one_of_forall_eq_one {s : Board} (h : ∀ a ∈ s, a = 1) : s.prod = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a = 1 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ a' ∈ s, a' = 1 := fun a' ha' => h a' (Multiset.mem_cons_of_mem ha')
    simp [ha, ih hs]

lemma prod_ne_zero_of_forall_pos {B : Board} (h : ∀ a ∈ B, 1 ≤ a) : B.prod ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro h0
  have := h 0 h0
  omega

-- ============================================================
-- Entries of reachable boards are ≥ 1
-- ============================================================

lemma entry_pos {B₀ B' : Board} (hB₀ : IsInitial B₀) (hreach : Reachable B₀ B') :
    ∀ a ∈ B', 1 ≤ a := by
  induction hreach with
  | refl => exact fun a ha => le_of_lt (hB₀.2 a ha)
  | tail hprev hmove ih =>
    intro a ha
    rcases hmove with ⟨m, n, s, hm, hn, hbb, hbc⟩
    rw [hbc] at ha
    rcases Multiset.mem_cons.mp ha with (rfl | ha1)
    · have h0 : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
      omega
    · rcases Multiset.mem_cons.mp ha1 with (rfl | ha2)
      · have hgcd_dvd : Nat.gcd m n ∣ Nat.lcm m n :=
          Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
        have hlcm_pos : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
        have h0 : 0 < Nat.lcm m n / Nat.gcd m n :=
          Nat.div_pos (Nat.le_of_dvd hlcm_pos hgcd_dvd) (Nat.gcd_pos_of_pos_left n (by omega))
        omega
      · have ha_prev : a ∈ (m ::ₘ n ::ₘ s) :=
          Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem ha2)
        rw [← hbb] at ha_prev
        exact ih a ha_prev

-- ============================================================
-- Basic move invariants
-- ============================================================

lemma card_invariant {B B' : Board} (h : Move B B') : Multiset.card B = Multiset.card B' := by
  rcases h with ⟨m, n, s, hm, hn, hB, hB'⟩
  rw [hB, hB']
  simp

lemma prod_dvd_of_move {B B' : Board} (h : Move B B') : B'.prod ∣ B.prod := by
  rcases h with ⟨m, n, s, _, _, hB, hB'⟩
  have h_dvd_lcm : Nat.gcd m n ∣ Nat.lcm m n :=
    Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  refine ⟨Nat.gcd m n, ?_⟩
  rw [hB, Multiset.prod_cons, Multiset.prod_cons, ← Nat.mul_assoc, ← Nat.gcd_mul_lcm m n, hB',
      Multiset.prod_cons, Multiset.prod_cons]
  conv_lhs => rw [show Nat.lcm m n = Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n)
                     from (Nat.mul_div_cancel' h_dvd_lcm).symm]
  ring

lemma count_gt_one_noninc {B B' : Board} (h : Move B B') : count_gt_one B' ≤ count_gt_one B := by
  rcases h with ⟨m, n, s, hm, hn, hB, hB'⟩
  rw [hB, hB']
  simp [count_gt_one_cons, hm, hn]
  split_ifs <;> omega

-- The lexicographic measure (prod of entries > 1, count of entries > 1)
-- strictly decreases with every move.
lemma measure_decreases {B B' : Board} (h : Move B B') :
    Prod.Lex (· < ·) (· < ·) (prod_gt_one B', count_gt_one B') (prod_gt_one B, count_gt_one B) := by
  rcases h with ⟨m, n, s, hm, hn, hB, hB'⟩
  by_cases hg : Nat.gcd m n = 1
  · -- gcd = 1: product unchanged, count decreases
    have hlcm : Nat.lcm m n = m * n := by
      rw [← Nat.gcd_mul_lcm m n, hg, one_mul]
    have hlg : Nat.lcm m n / Nat.gcd m n = m * n := by
      rw [hlcm, hg, Nat.div_one]
    have hmul : 1 < m * n := by nlinarith [hm, hn]
    have hprod_eq : prod_gt_one B' = prod_gt_one B := by
      rw [hB, hB', hlg, hg]
      simp [prod_gt_one_cons, hm, hn, hmul, mul_comm, mul_left_comm, mul_assoc]
    have hcount_lt : count_gt_one B' < count_gt_one B := by
      rw [hB, hB', hlg, hg]
      simp [count_gt_one_cons, hm, hn, hmul]
    rw [hprod_eq]
    exact Prod.Lex.right (prod_gt_one B) hcount_lt
  · -- gcd > 1: product decreases
    have hg' : 1 < Nat.gcd m n := by
      have h0 : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
      omega
    have hgcd_dvd : Nat.gcd m n ∣ Nat.lcm m n :=
      Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
    have hlcm_pos : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
    have hps_pos : 0 < prod_gt_one s := prod_gt_one_pos s
    have hprod_lt : prod_gt_one B' < prod_gt_one B := by
      have hBprod : prod_gt_one B = m * n * prod_gt_one s := by
        rw [hB]
        simp [prod_gt_one_cons, hm, hn, mul_assoc]
      have hle1 : prod_gt_one B' ≤ Nat.lcm m n * prod_gt_one s := by
        rw [hB', prod_gt_one_cons, prod_gt_one_cons]
        have h1 : (if 1 < Nat.gcd m n then Nat.gcd m n else 1) ≤ Nat.gcd m n := by
          split_ifs <;> omega
        have h2 : (if 1 < Nat.lcm m n / Nat.gcd m n then Nat.lcm m n / Nat.gcd m n else 1) ≤
              Nat.lcm m n / Nat.gcd m n := by
          split_ifs
          · exact le_refl _
          · have hpos : 0 < Nat.lcm m n / Nat.gcd m n :=
              Nat.div_pos (Nat.le_of_dvd hlcm_pos hgcd_dvd) (by omega)
            omega
        calc (if 1 < Nat.gcd m n then Nat.gcd m n else 1) *
              ((if 1 < Nat.lcm m n / Nat.gcd m n then Nat.lcm m n / Nat.gcd m n else 1) * prod_gt_one s)
            ≤ Nat.gcd m n * ((Nat.lcm m n / Nat.gcd m n) * prod_gt_one s) :=
              Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (le_refl _))
          _ = Nat.lcm m n * prod_gt_one s := by
              rw [← mul_assoc, Nat.mul_div_cancel' hgcd_dvd]
      have hlt : Nat.lcm m n * prod_gt_one s < m * n * prod_gt_one s := by
        have hlcm_lt : Nat.lcm m n < m * n := by
          have hgl : Nat.gcd m n * Nat.lcm m n = m * n := Nat.gcd_mul_lcm m n
          nlinarith
        exact Nat.mul_lt_mul_of_pos_right hlcm_lt hps_pos
      rw [hBprod]
      exact lt_of_le_of_lt hle1 hlt
    exact Prod.Lex.left (count_gt_one B') (count_gt_one B) hprod_lt

-- ============================================================
-- Statement (a), part 1 — termination
-- ============================================================

theorem statement_a_termination (B₀ : Board) (hB₀ : IsInitial B₀) :
    ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1)) := by
  rintro ⟨f, hf0, hf⟩
  let r : ℕ × ℕ → ℕ × ℕ → Prop := Prod.Lex (· < ·) (· < ·)
  have hwf_lt : WellFounded (· < · : ℕ → ℕ → Prop) := (inferInstance : WellFoundedLT ℕ).wf
  have hwf : WellFounded r := WellFounded.prod_lex hwf_lt hwf_lt
  let g : ℕ → ℕ × ℕ := fun k => (prod_gt_one (f k), count_gt_one (f k))
  have hchain : ∀ k, r (g (k + 1)) (g k) := fun k => measure_decreases (hf k)
  have hne : (Set.range g).Nonempty := ⟨g 0, 0, rfl⟩
  obtain ⟨n, hn⟩ := hwf.min_mem (Set.range g) hne
  have hnotlt : ¬ r (g (n + 1)) (hwf.min (Set.range g) hne) :=
    hwf.not_lt_min (Set.range g) ⟨n + 1, rfl⟩
  rw [← hn] at hnotlt
  exact hnotlt (hchain n)

-- ============================================================
-- gcd and padicValNat lemmas
-- ============================================================

lemma gcd_eq_gcd_min_sub (a b : ℕ) : Nat.gcd a b = Nat.gcd (min a b) (max a b - min a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact (Nat.gcd_sub_self_right h).symm
  · rw [min_eq_right h, max_eq_left h, Nat.gcd_comm a b]
    exact (Nat.gcd_sub_self_right h).symm

lemma padicValNat_gcd_eq (p : ℕ) (hp : p.Prime) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) := by
  rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp,
      Nat.factorization_gcd hm hn, Finsupp.inf_apply]

lemma padicValNat_lcm_eq (p : ℕ) (hp : p.Prime) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.lcm m n) = max (padicValNat p m) (padicValNat p n) := by
  rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp,
      Nat.factorization_lcm hm hn, Finsupp.sup_apply]

lemma padicValNat_lcm_div_gcd_eq (p : ℕ) (hp : p.Prime) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.lcm m n / Nat.gcd m n) =
      max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hgcd_dvd : Nat.gcd m n ∣ Nat.lcm m n :=
    Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  rw [padicValNat.div_of_dvd hgcd_dvd, padicValNat_lcm_eq p hp hm hn, padicValNat_gcd_eq p hp hm hn]

lemma gcd_padicValNat_move (p : ℕ) (hp : p.Prime) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.gcd (padicValNat p m) (padicValNat p n) =
      Nat.gcd (padicValNat p (Nat.gcd m n)) (padicValNat p (Nat.lcm m n / Nat.gcd m n)) := by
  rw [padicValNat_gcd_eq p hp hm hn, padicValNat_lcm_div_gcd_eq p hp hm hn]
  exact gcd_eq_gcd_min_sub _ _

-- ============================================================
-- gExp and Mval invariance
-- ============================================================

lemma gExp_invariant {B B' : Board} (h : Move B B') (p : ℕ) (hp : p.Prime) :
    gExp p B = gExp p B' := by
  rcases h with ⟨m, n, s, _, _, hB, hB'⟩
  subst hB hB'
  unfold gExp
  have h1 : ((m ::ₘ n ::ₘ s).map (fun a => padicValNat p a)).gcd =
      Nat.gcd (padicValNat p m)
        (Nat.gcd (padicValNat p n) ((s.map (fun a => padicValNat p a)).gcd)) := by
    rw [Multiset.map_cons, Multiset.gcd_cons, Multiset.map_cons, Multiset.gcd_cons]
    rfl
  have h2 : ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).map (fun a => padicValNat p a)).gcd
      = Nat.gcd (padicValNat p (Nat.gcd m n))
          (Nat.gcd (padicValNat p (Nat.lcm m n / Nat.gcd m n)) ((s.map (fun a => padicValNat p a)).gcd)) := by
    rw [Multiset.map_cons, Multiset.gcd_cons, Multiset.map_cons, Multiset.gcd_cons]
    rfl
  have heq : Nat.gcd (padicValNat p m) (padicValNat p n) =
      Nat.gcd (padicValNat p (Nat.gcd m n)) (padicValNat p (Nat.lcm m n / Nat.gcd m n)) :=
    gcd_padicValNat_move p hp (by omega) (by omega)
  rw [h1, h2, ← Nat.gcd_assoc, ← Nat.gcd_assoc, heq]

lemma gExp_eq_zero_of_not_dvd_prod (p : ℕ) (hp : p.Prime) (B : Board)
    (h : ¬ p ∣ B.prod) : gExp p B = 0 := by
  unfold gExp
  apply (Multiset.gcd_eq_zero_iff _).mpr
  intro x hx
  rcases Multiset.mem_map.mp hx with ⟨a, ha, rfl⟩
  apply padicValNat.eq_zero_of_not_dvd
  intro hp_dvd_a
  exact h (Nat.dvd_trans hp_dvd_a (Multiset.dvd_prod ha))

lemma Mval_invariant {B B' : Board} (h : Move B B') (hBne : B.prod ≠ 0) : Mval B = Mval B' := by
  have hB'ne : B'.prod ≠ 0 := by
    rcases prod_dvd_of_move h with ⟨k, hk⟩
    intro h0
    apply hBne
    rw [hk, h0, Nat.zero_mul]
  unfold Mval
  set S := (B.prod).primeFactors ∪ (B'.prod).primeFactors with hS
  have h_left : (∏ p ∈ (B.prod).primeFactors, p ^ gExp p B) = (∏ p ∈ S, p ^ gExp p B) := by
    apply Finset.prod_subset (Finset.subset_union_left)
    intro p hpS hpn
    have hpB' : p ∈ (B'.prod).primeFactors := by
      rcases Finset.mem_union.mp hpS with hmem | hmem
      · exact absurd hmem hpn
      · exact hmem
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hpB').1
    have hndvd : ¬ p ∣ B.prod := by
      intro hdvd
      exact hpn (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hBne⟩)
    rw [gExp_eq_zero_of_not_dvd_prod p hpp B hndvd, pow_zero]
  have h_right : (∏ p ∈ (B'.prod).primeFactors, p ^ gExp p B') = (∏ p ∈ S, p ^ gExp p B') := by
    apply Finset.prod_subset (Finset.subset_union_right)
    intro p hpS hpn
    have hpB : p ∈ (B.prod).primeFactors := by
      rcases Finset.mem_union.mp hpS with hmem | hmem
      · exact hmem
      · exact absurd hmem hpn
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hpB).1
    have hndvd : ¬ p ∣ B'.prod := by
      intro hdvd
      exact hpn (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hB'ne⟩)
    rw [gExp_eq_zero_of_not_dvd_prod p hpp B' hndvd, pow_zero]
  calc (∏ p ∈ (B.prod).primeFactors, p ^ gExp p B)
      = ∏ p ∈ S, p ^ gExp p B := h_left
    _ = ∏ p ∈ S, p ^ gExp p B' := by
        apply Finset.prod_congr rfl
        intro p hpS
        have hpp : p.Prime := by
          rcases Finset.mem_union.mp hpS with hmem | hmem
          · exact (Nat.mem_primeFactors.mp hmem).1
          · exact (Nat.mem_primeFactors.mp hmem).1
        rw [gExp_invariant h p hpp]
    _ = ∏ p ∈ (B'.prod).primeFactors, p ^ gExp p B' := h_right.symm

lemma Mval_eq_of_reachable {B₀ B' : Board} (hB₀ : IsInitial B₀) (hreach : Reachable B₀ B') :
    Mval B' = Mval B₀ := by
  induction hreach with
  | refl => rfl
  | tail hprev hmove ih =>
    have hbne := prod_ne_zero_of_forall_pos (entry_pos hB₀ hprev)
    have h1 := Mval_invariant hmove hbne
    rw [← h1]
    exact ih

-- ============================================================
-- Statement (a), part 2 — unique large entry
-- ============================================================

theorem Mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
  obtain ⟨hcard, hall⟩ := hB₀
  have hne : B₀ ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hcard
    exact absurd hcard (by decide : ¬ 0 = 2026)
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  have ha1 : 1 < a := hall a ha
  have hane : a ≠ 0 := by omega
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (show a ≠ 1 by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  have hpB : p ∣ B₀.prod := Nat.dvd_trans hpa (Multiset.dvd_prod ha)
  have hB0ne : B₀.prod ≠ 0 := prod_ne_zero_of_forall_pos (fun x hx => le_of_lt (hall x hx))
  have hpPF : p ∈ B₀.prod.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpB, hB0ne⟩
  have hg1 : 1 ≤ gExp p B₀ := by
    unfold gExp
    have hmem : padicValNat p a ∈ B₀.map (padicValNat p) := Multiset.mem_map.mpr ⟨a, ha, rfl⟩
    have hpos : 0 < padicValNat p a := by
      rcases (padicValNat_dvd_iff 1 a).mp (by simpa using hpa) with hzero | hle
      · exact absurd hzero hane
      · exact hle
    have hgne : (B₀.map (padicValNat p)).gcd ≠ 0 := by
      intro hg
      have h_dvd : (B₀.map (padicValNat p)).gcd ∣ padicValNat p a :=
        Multiset.gcd_dvd hmem
      rw [hg, Nat.zero_dvd] at h_dvd
      exact absurd h_dvd (Nat.ne_of_gt hpos)
    exact Nat.pos_of_ne_zero hgne
  have hgt : 1 < p ^ gExp p B₀ := by
    calc (1 : ℕ) < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ gExp p B₀ := Nat.pow_le_pow_right hp.pos hg1
  have hdvd : p ^ gExp p B₀ ∣ Mval B₀ := by
    unfold Mval
    exact Finset.dvd_prod_of_mem (fun p => p ^ gExp p B₀) hpPF
  have hM1 : 1 ≤ Mval B₀ := by
    unfold Mval
    apply Finset.one_le_prod
    intro p' hp'
    exact Nat.one_le_pow (gExp p' B₀) p' ((Nat.mem_primeFactors.mp hp').1.pos)
  have hle : p ^ gExp p B₀ ≤ Mval B₀ := Nat.le_of_dvd (by omega) hdvd
  omega

theorem statement_a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
  show Multiset.card (B'.filter (fun a => 1 < a)) = 1
  have hle : Multiset.card (B'.filter (fun a => 1 < a)) ≤ 1 := hterm
  suffices h : 0 < Multiset.card (B'.filter (fun a => 1 < a)) by omega
  by_contra h0
  have hcard0 : Multiset.card (B'.filter (fun a => 1 < a)) = 0 := Nat.eq_zero_of_not_pos h0
  have hall_one : ∀ a ∈ B', a = 1 := by
    intro a ha
    have h1 : 1 ≤ a := entry_pos hB₀ hreach a ha
    by_contra hne1
    have hgt : 1 < a := by omega
    have hmem : a ∈ B'.filter (fun a => 1 < a) := Multiset.mem_filter.mpr ⟨ha, hgt⟩
    have hempty : B'.filter (fun a => 1 < a) = 0 := Multiset.card_eq_zero.mp hcard0
    rw [hempty] at hmem
    simpa using hmem
  have hMval1 : Mval B' = 1 := by
    unfold Mval
    rw [prod_eq_one_of_forall_eq_one hall_one, Nat.primeFactors_one, Finset.prod_empty]
  have hMv : Mval B' = Mval B₀ := Mval_eq_of_reachable hB₀ hreach
  have hgt : 1 < Mval B₀ := Mval_gt_one B₀ hB₀
  omega

-- ============================================================
-- Value of M
-- ============================================================

lemma gExp_eq_of_filter_singleton {B' : Board} {M : ℕ}
    (hfilter : B'.filter (fun a => 1 < a) = {M}) (p : ℕ) :
    gExp p B' = padicValNat p M := by
  unfold gExp
  apply Nat.dvd_antisymm
  · apply Multiset.gcd_dvd
    have hMB' : M ∈ B' := by
      have hmem : M ∈ B'.filter (fun a => 1 < a) := by rw [hfilter]; simp
      exact Multiset.mem_of_mem_filter hmem
    exact Multiset.mem_map.mpr ⟨M, hMB', rfl⟩
  · rw [Multiset.dvd_gcd]
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨a, ha, rfl⟩
    by_cases hgt : 1 < a
    · have haf : a ∈ B'.filter (fun a => 1 < a) := Multiset.mem_filter.mpr ⟨ha, hgt⟩
      rw [hfilter] at haf
      have haeq : a = M := by simpa using haf
      rw [haeq]
    · have ha01 : a = 0 ∨ a = 1 := by omega
      rcases ha01 with rfl | rfl
      · simp
      · simp

lemma prod_eq_of_filter_singleton {B' : Board} {M : ℕ}
    (hfilter : B'.filter (fun a => 1 < a) = {M}) (hpos : ∀ a ∈ B', 1 ≤ a) :
    B'.prod = M := by
  have hsplit : B' = B'.filter (fun a => 1 < a) + B'.filter (fun a => ¬ 1 < a) :=
    (Multiset.filter_add_not _ _).symm
  have hones : ∀ a ∈ B'.filter (fun a => ¬ 1 < a), a = 1 := by
    intro a ha
    have hmem : a ∈ B' := Multiset.mem_of_mem_filter ha
    have hnle : ¬ 1 < a := (Multiset.mem_filter.mp ha).2
    have h1 := hpos a hmem
    omega
  rw [hsplit, hfilter, Multiset.prod_add, prod_eq_one_of_forall_eq_one hones]
  simp

theorem terminal_value_eq_Mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ := by
  have huniq : HasUniqueLarge B' := statement_a_unique_large B₀ hB₀ B' hreach hterm
  have hfilter : B'.filter (fun a => 1 < a) = {M} := by
    obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp huniq
    have hMx : M ∈ B'.filter (fun a => 1 < a) := Multiset.mem_filter.mpr ⟨hMem, hM⟩
    rw [hx] at hMx
    have hMeq : M = x := by simpa using hMx
    rw [hMeq, hx]
  have hMvalB' : Mval B' = M := by
    unfold Mval
    have hprod : B'.prod = M := prod_eq_of_filter_singleton hfilter (entry_pos hB₀ hreach)
    rw [hprod]
    have hM0 : M ≠ 0 := by omega
    calc
      (∏ p ∈ M.primeFactors, p ^ gExp p B') = (∏ p ∈ M.primeFactors, p ^ padicValNat p M) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [gExp_eq_of_filter_singleton hfilter p]
      _ = (M.factorization.prod fun p k => p ^ k) := by
        rw [Finsupp.prod, Nat.support_factorization]
        refine Finset.prod_congr rfl fun p hp => ?_
        rw [Nat.factorization_def M (Nat.prime_of_mem_primeFactors hp)]
      _ = M := Nat.prod_factorization_pow_eq_self hM0
  rw [← hMvalB']
  exact Mval_eq_of_reachable hB₀ hreach

-- ============================================================
-- Statement (b) — invariance
-- ============================================================

lemma exists_large_of_card_eq_one {B : Board}
    (h : Multiset.card (B.filter (fun a => 1 < a)) = 1) :
    ∃ M, M ∈ B ∧ 1 < M := by
  obtain ⟨M, hM⟩ := Multiset.card_eq_one.mp h
  have hmem : M ∈ B.filter (fun a => 1 < a) := by rw [hM]; simp
  exact ⟨M, Multiset.mem_of_mem_filter hmem, (Multiset.mem_filter.mp hmem).2⟩

theorem statement_b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
  intro M
  constructor
  · intro ⟨hM, hMem⟩
    have hMv : M = Mval B₀ := terminal_value_eq_Mval B₀ hB₀ B₁ h₁ t₁ M hM hMem
    obtain ⟨M₂, hMem₂, hM₂⟩ :=
      exists_large_of_card_eq_one (statement_a_unique_large B₀ hB₀ B₂ h₂ t₂)
    have hM₂v : M₂ = Mval B₀ := terminal_value_eq_Mval B₀ hB₀ B₂ h₂ t₂ M₂ hM₂ hMem₂
    rw [hMv, ← hM₂v]
    exact ⟨hM₂, hMem₂⟩
  · intro ⟨hM, hMem⟩
    have hMv : M = Mval B₀ := terminal_value_eq_Mval B₀ hB₀ B₂ h₂ t₂ M hM hMem
    obtain ⟨M₁, hMem₁, hM₁⟩ :=
      exists_large_of_card_eq_one (statement_a_unique_large B₀ hB₀ B₁ h₁ t₁)
    have hM₁v : M₁ = Mval B₀ := terminal_value_eq_Mval B₀ hB₀ B₁ h₁ t₁ M₁ hM₁ hMem₁
    rw [hMv, ← hM₁v]
    exact ⟨hM₁, hMem₁⟩
