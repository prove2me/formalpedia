-- Prove2me | solution 1 for APrioriTSP.Sampling.proposition_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:36:54.99604+00:00
-- url     : https://prove2.me/submissions/1286e700-3a60-4f2c-b01f-ada4dccee65c

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

open APrioriTSP.Sampling Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace APTSPProp10

variable {V : Type} [Fintype V] [DecidableEq V]

/-- probability of a pattern: all of `S` active, none of `U` active. -/
theorem pattern (q : V → ℝ) (S U : Finset V) (hSU : Disjoint S U) :
    ∑ A : Finset V, subsetProb q A * (if S ⊆ A ∧ Disjoint U A then 1 else 0) =
      (∏ v ∈ S, q v) * ∏ v ∈ U, (1 - q v) := by
  set f : V → ℝ := fun v => if v ∈ U then 0 else q v with hf
  set g : V → ℝ := fun v => if v ∈ S then 0 else 1 - q v with hg
  have key : ∀ A : Finset V, subsetProb q A * (if S ⊆ A ∧ Disjoint U A then 1 else 0) =
      (∏ v ∈ A, f v) * ∏ v ∈ univ \ A, g v := by
    intro A
    unfold subsetProb
    by_cases hc : S ⊆ A ∧ Disjoint U A
    · rw [if_pos hc, mul_one]
      congr 1
      · apply Finset.prod_congr rfl; intro v hv
        simp only [hf]; rw [if_neg]; intro hvU
        exact Finset.disjoint_left.1 hc.2 hvU hv
      · apply Finset.prod_congr rfl; intro v hv
        simp only [hg]; rw [if_neg]; intro hvS
        simp at hv; exact hv (hc.1 hvS)
    · rw [if_neg hc, mul_zero]
      rw [not_and_or] at hc
      rcases hc with h1 | h1
      · rw [Finset.not_subset] at h1
        obtain ⟨s, hsS, hsA⟩ := h1
        have : ∏ v ∈ univ \ A, g v = 0 := by
          apply Finset.prod_eq_zero (i := s) (by simp [hsA])
          simp [hg, hsS]
        rw [this, mul_zero]
      · rw [Finset.not_disjoint_iff] at h1
        obtain ⟨u, huU, huA⟩ := h1
        have : ∏ v ∈ A, f v = 0 := by
          apply Finset.prod_eq_zero huA
          simp [hf, huU]
        rw [this, zero_mul]
  rw [Finset.sum_congr rfl (fun A _ => key A)]
  have h2 := (Finset.prod_add f g (univ : Finset V)).symm
  rw [Finset.powerset_univ] at h2
  rw [h2]
  have h3 : ∀ v, f v + g v = (if v ∈ S then q v else 1) * (if v ∈ U then 1 - q v else 1) := by
    intro v
    simp only [hf, hg]
    by_cases hS : v ∈ S
    · have hU : v ∉ U := Finset.disjoint_left.1 hSU hS
      simp [hS, hU]
    · by_cases hU : v ∈ U
      · simp [hS, hU]
      · simp [hS, hU]
  rw [Finset.prod_congr rfl (fun v _ => h3 v), Finset.prod_mul_distrib,
    Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter, Finset.univ_inter]

/-- path cost of a list -/
def pathCost (c : V → V → ℝ) : List V → ℝ
  | [] => 0
  | [_] => 0
  | x :: y :: l => c x y + pathCost c (y :: l)

/-- cost of the edge from `u` to the head of `F` -/
def headCost (c : V → V → ℝ) (u : V) : List V → ℝ
  | [] => 0
  | h :: _ => c u h

theorem pathCost_cons (c : V → V → ℝ) (u : V) (F : List V) :
    pathCost c (u :: F) = headCost c u F + pathCost c F := by
  cases F with
  | nil => simp [pathCost, headCost]
  | cons h t => simp [pathCost, headCost]

theorem zip_sum_eq_pathCost (c : V → V → ℝ) (y : V) :
    ∀ (F : List V) (x : V), (((x :: F).zip (F ++ [y])).map (fun e => c e.1 e.2)).sum =
      pathCost c (x :: F ++ [y]) := by
  intro F
  induction F with
  | nil => intro x; simp [pathCost]
  | cons z F ih =>
    intro x
    have := ih z
    simp only [List.cons_append, List.zip_cons_cons, List.map_cons, List.sum_cons] at this ⊢
    rw [this]
    simp [pathCost]

theorem cycleCost_cons (c : V → V → ℝ) (x : V) (F : List V) :
    cycleCost c (x :: F) = pathCost c (x :: F ++ [x]) := by
  unfold cycleCost
  rw [List.rotate_cons_succ, List.rotate_zero]
  exact zip_sum_eq_pathCost c x F x

theorem headCost_filter (c : V → V → ℝ) (d u : V) (A : Finset V) :
    ∀ e : List V, ∑ b ∈ range e.length,
      (if e.getD b d ∈ A ∧ ∀ s, s < b → e.getD s d ∉ A then c u (e.getD b d) else 0) =
        headCost c u (e.filter (· ∈ A)) := by
  intro e
  induction e with
  | nil => simp [headCost]
  | cons z e ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    by_cases hz : z ∈ A
    · have h0 : ∀ b ∈ range e.length, (if (z :: e).getD (b + 1) d ∈ A ∧
          ∀ s, s < b + 1 → (z :: e).getD s d ∉ A then c u ((z :: e).getD (b + 1) d) else 0) = 0 := by
        intro b _
        rw [if_neg]
        intro ⟨_, h2⟩
        exact h2 0 (by omega) (by simpa using hz)
      rw [Finset.sum_eq_zero h0]
      simp [hz, headCost, List.filter_cons]
    · have h0 : ∀ b ∈ range e.length, (if (z :: e).getD (b + 1) d ∈ A ∧
          ∀ s, s < b + 1 → (z :: e).getD s d ∉ A then c u ((z :: e).getD (b + 1) d) else 0) =
          (if e.getD b d ∈ A ∧ ∀ s, s < b → e.getD s d ∉ A then c u (e.getD b d) else 0) := by
        intro b _
        simp only [List.getD_cons_succ]
        congr 1
        apply propext
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun s hs => by have := h2 (s + 1) (by omega); simpa using this⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun s hs => ?_⟩
          rcases s with _ | s
          · simpa using hz
          · simpa using h2 s (by omega)
      rw [Finset.sum_congr rfl h0, ih]
      simp [hz, List.filter_cons]

/-- the path cost of the active sublist is the sum over consecutive active pairs. -/
theorem pathCost_filter (c : V → V → ℝ) (d : V) (A : Finset V) :
    ∀ e : List V, pathCost c (e.filter (· ∈ A)) =
      ∑ a ∈ range e.length, ∑ b ∈ range e.length,
        (if a < b ∧ e.getD a d ∈ A ∧ e.getD b d ∈ A ∧ ∀ s ∈ Finset.Ioo a (b), e.getD s d ∉ A
          then c (e.getD a d) (e.getD b d) else 0) := by
  intro e
  induction e with
  | nil => simp [pathCost]
  | cons u e ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp_rw [Finset.sum_range_succ' (fun b => (if _ < b ∧ _ then _ else _))]
    -- terms with a + 1, b + 1
    have hab : ∀ a b, (if a + 1 < b + 1 ∧ (u :: e).getD (a + 1) d ∈ A ∧
        (u :: e).getD (b + 1) d ∈ A ∧ ∀ s ∈ Finset.Ioo (a + 1) (b + 1), (u :: e).getD s d ∉ A
        then c ((u :: e).getD (a + 1) d) ((u :: e).getD (b + 1) d) else 0) =
        (if a < b ∧ e.getD a d ∈ A ∧ e.getD b d ∈ A ∧ ∀ s ∈ Finset.Ioo a (b), e.getD s d ∉ A
          then c (e.getD a d) (e.getD b d) else 0) := by
      intro a b
      simp only [List.getD_cons_succ]
      congr 1
      apply propext
      constructor
      · rintro ⟨h0, h1, h2, h3⟩
        refine ⟨by omega, h1, h2, fun s hs => ?_⟩
        obtain ⟨hs1, hs2⟩ := Finset.mem_Ioo.1 hs
        have := h3 (s + 1) (Finset.mem_Ioo.2 ⟨by omega, by omega⟩); simpa using this
      · rintro ⟨h0, h1, h2, h3⟩
        refine ⟨by omega, h1, h2, fun s hs => ?_⟩
        obtain ⟨hs1, hs2⟩ := Finset.mem_Ioo.1 hs
        rcases s with _ | s
        · omega
        · simpa using h3 s (Finset.mem_Ioo.2 ⟨by omega, by omega⟩)
    have ha0 : ∀ a, (if a + 1 < 0 ∧ (u :: e).getD (a + 1) d ∈ A ∧
        (u :: e).getD 0 d ∈ A ∧ ∀ s ∈ Finset.Ioo (a + 1) 0, (u :: e).getD s d ∉ A
        then c ((u :: e).getD (a + 1) d) ((u :: e).getD 0 d) else 0) = 0 := by
      intro a; rw [if_neg]; omega
    have h00 : (if 0 < 0 ∧ (u :: e).getD 0 d ∈ A ∧
        (u :: e).getD 0 d ∈ A ∧ ∀ s ∈ Finset.Ioo 0 (0), (u :: e).getD s d ∉ A
        then c ((u :: e).getD 0 d) ((u :: e).getD 0 d) else 0) = 0 := by
      rw [if_neg]; omega
    have h0b : ∀ b, (if 0 < b + 1 ∧ (u :: e).getD 0 d ∈ A ∧
        (u :: e).getD (b + 1) d ∈ A ∧ ∀ s ∈ Finset.Ioo 0 (b + 1), (u :: e).getD s d ∉ A
        then c ((u :: e).getD 0 d) ((u :: e).getD (b + 1) d) else 0) =
        if u ∈ A then (if e.getD b d ∈ A ∧ ∀ s, s < b → e.getD s d ∉ A then c u (e.getD b d)
          else 0) else 0 := by
      intro b
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      by_cases hu : u ∈ A
      · rw [if_pos hu]
        congr 1
        apply propext
        constructor
        · rintro ⟨_, _, h2, h3⟩
          exact ⟨h2, fun s hs => by simpa using h3 (s + 1) (Finset.mem_Ioo.2 ⟨by omega, by omega⟩)⟩
        · rintro ⟨h2, h3⟩
          refine ⟨by omega, hu, h2, fun s hs => ?_⟩
          obtain ⟨hs1, hs2⟩ := Finset.mem_Ioo.1 hs
          rcases s with _ | s
          · omega
          · simpa using h3 s (by omega)
      · rw [if_neg hu, if_neg]
        rintro ⟨_, h1, _⟩; exact hu h1
    simp only [hab, ha0, h00, h0b, Finset.sum_const_zero, add_zero]
    rw [← ih]
    by_cases hu : u ∈ A
    · simp only [hu, if_true]
      rw [headCost_filter c d u A e, List.filter_cons, if_pos (by simpa using hu),
        pathCost_cons]
      ring
    · simp only [hu, if_false, Finset.sum_const_zero, add_zero]
      rw [List.filter_cons, if_neg (by simpa using hu)]

theorem geom_tail (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (m : ℕ) :
    ∑' i : ℕ, (if m ≤ i then (1 - p) ^ i * p ^ 2 else 0) = p * (1 - p) ^ m := by
  have hr0 : 0 ≤ 1 - p := by linarith
  have hr1 : 1 - p < 1 := by linarith
  have hgs : Summable (fun i : ℕ => (1 - p) ^ i * p ^ 2) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_right _
  have hs : Summable (fun i : ℕ => if m ≤ i then (1 - p) ^ i * p ^ 2 else 0) := by
    apply Summable.of_nonneg_of_le _ _ hgs
    · intro i; split_ifs <;> positivity
    · intro i; split_ifs
      · exact le_rfl
      · positivity
  rw [← hs.sum_add_tsum_nat_add m]
  have h1 : ∑ i ∈ range m, (if m ≤ i then (1 - p) ^ i * p ^ 2 else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i hi; simp at hi; rw [if_neg (by omega)]
  have h2 : ∀ i : ℕ, (if m ≤ i + m then (1 - p) ^ (i + m) * p ^ 2 else 0) =
      ((1 - p) ^ m * p ^ 2) * (1 - p) ^ i := by
    intro i; rw [if_pos (by omega)]; ring
  rw [h1, zero_add, tsum_congr h2, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1,
    sub_sub_cancel]
  field_simp

theorem tourVertex_eq (d : V) (T : List V) (hd : T.head? = some d) (j : ℤ) :
    tourVertex d T j = T.getD j.toNat d := by
  unfold tourVertex
  split_ifs with h
  · rfl
  · rw [Int.toNat_of_nonpos (by omega)]
    cases T with
    | nil => simp at hd
    | cons x R => simp at hd; simp [hd]

theorem hopC_eq (c : V → V → ℝ) (p : ℝ) (d : V) (T : List V) (hd : T.head? = some d) (k : ℕ) :
    hopC c p d T k = p ^ 2 * (∑ a ∈ range T.length, c (T.getD a d) (T.getD (a + k) d) +
      ∑ t ∈ range k, c (T.getD 0 d) (T.getD t d)) := by
  unfold hopC
  congr 1
  simp_rw [tourVertex_eq d T hd]
  have hb : ∑ m ∈ range (k + T.length),
      c (T.getD (m - k) d) (T.getD m d) =
      ∑ j ∈ Finset.Icc (-(k : ℤ)) ((T.length : ℤ) - 1),
        c (T.getD j.toNat d) (T.getD (j + k).toNat d) := by
    apply Finset.sum_nbij' (fun m : ℕ => (m : ℤ) - k) (fun j : ℤ => (j + k).toNat)
    · intro m hm; simp at hm ⊢; omega
    · intro j hj; simp at hj ⊢; omega
    · intro m _; simp
    · intro j hj; simp at hj ⊢; omega
    · intro m _
      congr 2
      · omega
      · omega
  rw [← hb, Finset.sum_range_add, add_comm]
  congr 1
  · apply Finset.sum_congr rfl; intro a _
    congr 2
    · omega
    · omega
  · apply Finset.sum_congr rfl; intro t ht
    simp at ht
    congr 2
    omega

theorem kappaX (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (n a b : ℕ) :
    ∑' i : ℕ, (1 - p) ^ i * p ^ 2 * (if a < n ∧ b = min (a + (i + 1)) n then 1 else 0) =
      if a < b ∧ b < n then p ^ 2 * (1 - p) ^ (b - a - 1)
      else if a < n ∧ b = n then p * (1 - p) ^ (n - a - 1) else 0 := by
  by_cases h1 : a < b ∧ b < n
  · rw [if_pos h1]
    have : ∀ i : ℕ, (1 - p) ^ i * p ^ 2 * (if a < n ∧ b = min (a + (i + 1)) n then 1 else 0) =
        if i = b - a - 1 then (1 - p) ^ i * p ^ 2 else 0 := by
      intro i
      by_cases hi : i = b - a - 1
      · rw [if_pos hi, if_pos (by omega), mul_one]
      · rw [if_neg hi, if_neg (by omega), mul_zero]
    rw [tsum_congr this, tsum_ite_eq]; ring
  · rw [if_neg h1]
    by_cases h2 : a < n ∧ b = n
    · rw [if_pos h2, ← geom_tail p hp0 hp1 (n - a - 1)]
      apply tsum_congr; intro i
      by_cases hi : n - a - 1 ≤ i
      · rw [if_pos hi, if_pos (by omega), mul_one]
      · rw [if_neg hi, if_neg (by omega), mul_zero]
    · rw [if_neg h2]
      have : ∀ i : ℕ, (1 - p) ^ i * p ^ 2 * (if a < n ∧ b = min (a + (i + 1)) n then 1 else 0) =
          0 := by
        intro i; rw [if_neg (by omega), mul_zero]
      rw [tsum_congr this, tsum_zero]

theorem kappaY (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (n a b : ℕ) :
    ∑' i : ℕ, (1 - p) ^ i * p ^ 2 * (if a = 0 ∧ b < n ∧ b ≤ i then 1 else 0) =
      if a = 0 ∧ b < n then p * (1 - p) ^ b else 0 := by
  by_cases h1 : a = 0 ∧ b < n
  · rw [if_pos h1, ← geom_tail p hp0 hp1 b]
    apply tsum_congr; intro i
    by_cases hi : b ≤ i
    · rw [if_pos hi, if_pos (by omega), mul_one]
    · rw [if_neg hi, if_neg (by omega), mul_zero]
  · rw [if_neg h1]
    have : ∀ i : ℕ, (1 - p) ^ i * p ^ 2 * (if a = 0 ∧ b < n ∧ b ≤ i then 1 else 0) = 0 := by
      intro i; rw [if_neg (by omega), mul_zero]
    rw [tsum_congr this, tsum_zero]

end APTSPProp10

open APTSPProp10 in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (pf : V → ℝ) (d : V) (p : ℝ) (hp : 0 < p)
    (hnorm : IsNormalized c pf d p) (T : List V) (hT : IsTour T) (hd : T.head? = some d) :
    aPrioriCost c pf T = ∑' i : ℕ, (1 - p) ^ i * hopC c p d T (i + 1) := by
  obtain ⟨hI, hnp⟩ := hnorm
  obtain ⟨hnd, hall⟩ := hT
  have hcdd : c d d = 0 := hI.c_self d
  have hpd : pf d = 1 := hI.p_depot
  obtain ⟨R, rfl⟩ : ∃ R, T = d :: R := by
    cases T with
    | nil => simp at hd
    | cons x R => simp at hd; exact ⟨R, by rw [hd]⟩
  simp_rw [hopC_eq c p d (d :: R) hd]
  set n := (d :: R).length with hn
  set w : ℕ → V := fun a => (d :: R).getD a d with hw
  have hw0 : w 0 = d := by simp [hw]
  have hwn : ∀ m, n ≤ m → w m = d := fun m hm => List.getD_eq_default _ _ hm
  have hwinj : ∀ s t, s < n → t < n → w s = w t → s = t := by
    intro s t hs ht heq
    simp only [hw] at heq
    rw [List.getD_eq_getElem _ _ hs, List.getD_eq_getElem _ _ ht] at heq
    exact (List.Nodup.getElem_inj_iff hnd).1 heq
  have hwne : ∀ s, 1 ≤ s → s < n → w s ≠ d := by
    intro s h1 h2 heq
    have := hwinj s 0 h2 (by simp [hn]) (by rw [heq, hw0])
    omega
  have hpw : ∀ s, 1 ≤ s → s < n → pf (w s) = p := fun s h1 h2 => hnp _ (hwne s h1 h2)
  have hn1 : 1 ≤ n := by simp [hn]
  -- degenerate case: only the depot
  by_cases hn2 : n = 1
  · have hR : R = [] := by simpa [hn] using hn2
    subst hR
    have hc0 : ∀ u v, c u v = 0 := by
      intro u v
      have hu := hall u; have hv := hall v
      simp at hu hv; rw [hu, hv, hcdd]
    simp [aPrioriCost, cycleCost, hc0]
  have hp1 : p ≤ 1 := by
    have := hI.p_le_one (w 1); rwa [hpw 1 le_rfl (by omega)] at this
  -- getD of the extended list
  have hge : ∀ a, (d :: R ++ [d]).getD a d = w a := by
    intro a
    by_cases ha : a < n
    · rw [List.getD_append _ _ _ _ ha]
    · rw [hwn a (by omega), List.getD_append_right _ _ _ _ (by omega)]
      rcases (a - (d :: R).length) with _ | m
      · simp
      · simp
  -- LHS as a sum over pairs
  set cond : Finset V → ℕ → ℕ → Prop := fun A a b =>
    d ∈ A ∧ (a < b ∧ w a ∈ A ∧ w b ∈ A ∧ ∀ s ∈ Finset.Ioo a b, w s ∉ A) with hcond
  have hL1 : ∀ A : Finset V, subsetProb pf A * cycleCost c ((d :: R).filter (· ∈ A)) =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
        c (w a) (w b) * (subsetProb pf A * (if cond A a b then 1 else 0)) := by
    intro A
    by_cases hdA : d ∈ A
    · have e1 : (d :: R).filter (· ∈ A) = d :: R.filter (· ∈ A) := by
        rw [List.filter_cons, if_pos (by simpa using hdA)]
      have e2 : d :: R.filter (· ∈ A) ++ [d] = (d :: R ++ [d]).filter (· ∈ A) := by
        rw [List.filter_append, List.filter_cons, if_pos (by simpa using hdA)]
        simp [hdA]
      rw [e1, cycleCost_cons, e2, pathCost_filter c d A (d :: R ++ [d])]
      have hlen : (d :: R ++ [d]).length = n + 1 := by simp [hn]
      rw [hlen, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _
      simp only [hge, hcond]
      by_cases hc : a < b ∧ w a ∈ A ∧ w b ∈ A ∧ ∀ s ∈ Finset.Ioo a b, w s ∉ A
      · rw [if_pos hc, if_pos ⟨hdA, hc⟩]; ring
      · rw [if_neg hc, if_neg (fun h => hc h.2)]; ring
    · have hP : subsetProb pf A = 0 := by
        unfold subsetProb
        have : ∏ v ∈ univ \ A, (1 - pf v) = 0 :=
          Finset.prod_eq_zero (i := d) (by simp [hdA]) (by rw [hpd]; ring)
        rw [this, mul_zero]
      rw [hP, zero_mul]
      symm
      apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro b _
      ring
  set ρ : ℕ → ℝ := fun s => if s = 0 ∨ s = n then 1 else p with hρ
  set coefL : ℕ → ℕ → ℝ := fun a b => if a < b then ρ a * ρ b * (1 - p) ^ (b - a - 1) else 0
    with hcoefL
  have hL3 : ∀ a ∈ range (n + 1), ∀ b ∈ range (n + 1),
      ∑ A : Finset V, subsetProb pf A * (if cond A a b then 1 else 0) = coefL a b := by
    intro a ha b hb
    simp only [Finset.mem_range] at ha hb
    by_cases hab : a < b
    · set S : Finset V := insert d (insert (w a) {w b}) with hS
      set U : Finset V := (Finset.Ioo a b).image w with hU
      have hmid : ∀ s ∈ Finset.Ioo a b, 1 ≤ s ∧ s < n := by
        intro s hs; simp at hs; omega
      have hdisj : Disjoint S U := by
        rw [Finset.disjoint_left]
        intro v hvS hvU
        simp only [hU, Finset.mem_image] at hvU
        obtain ⟨s, hs, rfl⟩ := hvU
        obtain ⟨hs1, hs2⟩ := hmid s hs
        have hs' := Finset.mem_Ioo.1 hs
        simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hvS
        rcases hvS with h | h | h
        · exact hwne s hs1 hs2 h
        · by_cases ha0 : a = 0
          · rw [ha0, hw0] at h; exact hwne s hs1 hs2 h
          · have := hwinj s a hs2 (by omega) h; omega
        · by_cases hbn : b = n
          · rw [hbn, hwn n le_rfl] at h; exact hwne s hs1 hs2 h
          · have := hwinj s b hs2 (by omega) h; omega
      have hiff : ∀ A : Finset V, (if cond A a b then (1 : ℝ) else 0) =
          if S ⊆ A ∧ Disjoint U A then 1 else 0 := by
        intro A
        congr 1
        apply propext
        simp only [hcond, hS, hU, Finset.insert_subset_iff, Finset.singleton_subset_iff,
          Finset.disjoint_left, Finset.mem_image]
        constructor
        · rintro ⟨h1, _, h2, h3, h4⟩
          refine ⟨⟨h1, h2, h3⟩, ?_⟩
          rintro v ⟨s, hs, rfl⟩; exact h4 s hs
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          exact ⟨h1, hab, h2, h3, fun s hs => h4 ⟨s, hs, rfl⟩⟩
      simp_rw [hiff]
      rw [pattern pf S U hdisj]
      have hprodU : ∏ v ∈ U, (1 - pf v) = (1 - p) ^ (b - a - 1) := by
        rw [hU, Finset.prod_image]
        · rw [Finset.prod_congr rfl (fun s hs => by
            rw [hpw s (hmid s hs).1 (hmid s hs).2])]
          rw [Finset.prod_const, Nat.card_Ioo]
        · intro s hs t ht hst
          exact hwinj s t (hmid s hs).2 (hmid t ht).2 hst
      have hprodS : ∏ v ∈ S, pf v = ρ a * ρ b := by
        simp only [hρ]
        by_cases ha0 : a = 0
        · subst ha0
          rw [hS, hw0]
          by_cases hbn : b = n
          · subst hbn
            rw [hwn _ le_rfl]
            simp [hpd]
          · have hb1 : 1 ≤ b := by omega
            have hwb : w b ≠ d := hwne b hb1 (by omega)
            rw [Finset.insert_eq_of_mem (by simp), Finset.prod_insert (by simp; exact hwb.symm),
              Finset.prod_singleton, hpd, hpw b hb1 (by omega)]
            rw [if_pos (Or.inl rfl), if_neg (by omega)]; try ring
        · have ha1 : 1 ≤ a := by omega
          have hwa : w a ≠ d := hwne a ha1 (by omega)
          by_cases hbn : b = n
          · subst hbn
            rw [hS, hwn _ le_rfl]
            rw [Finset.pair_comm, Finset.insert_eq_of_mem (by simp),
              Finset.prod_insert (by simp; exact hwa.symm), Finset.prod_singleton, hpd,
              hpw a ha1 (by omega)]
            rw [if_neg (by omega), if_pos (Or.inr rfl)]; try ring
          · have hb1 : 1 ≤ b := by omega
            have hwb : w b ≠ d := hwne b hb1 (by omega)
            have hab' : w a ≠ w b := fun h => by have := hwinj a b (by omega) (by omega) h; omega
            rw [hS, Finset.prod_insert (by simp; exact ⟨hwa.symm, hwb.symm⟩),
              Finset.prod_insert (by simp; exact hab'), Finset.prod_singleton, hpd,
              hpw a ha1 (by omega), hpw b hb1 (by omega)]
            rw [if_neg (by omega), if_neg (by omega)]; try ring
      rw [hprodU, hprodS]
      simp only [hcoefL, if_pos hab]
    · simp only [hcoefL, if_neg hab]
      apply Finset.sum_eq_zero; intro A _
      rw [if_neg (fun h => hab h.2.1), mul_zero]
  have hLHS : aPrioriCost c pf (d :: R) =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), c (w a) (w b) * coefL a b := by
    unfold aPrioriCost
    rw [Finset.sum_congr rfl (fun A _ => hL1 A), Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b hb
    rw [← Finset.mul_sum, hL3 a ha b hb]
  rw [hLHS]
  -- RHS
  set φX : ℕ → ℕ → ℕ → ℝ := fun i a b =>
    (1 - p) ^ i * p ^ 2 * (if a < n ∧ b = min (a + (i + 1)) n then 1 else 0) with hφX
  set φY : ℕ → ℕ → ℕ → ℝ := fun i a b =>
    (1 - p) ^ i * p ^ 2 * (if a = 0 ∧ b < n ∧ b ≤ i then 1 else 0) with hφY
  have hR1 : ∀ i : ℕ, (1 - p) ^ i * (p ^ 2 * (∑ a ∈ range n, c (w a) (w (a + (i + 1))) +
      ∑ t ∈ range (i + 1), c (w 0) (w t))) =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), c (w a) (w b) * (φX i a b + φY i a b) := by
    intro i
    have hX : ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), c (w a) (w b) * φX i a b =
        (1 - p) ^ i * p ^ 2 * ∑ a ∈ range n, c (w a) (w (a + (i + 1))) := by
      rw [Finset.sum_range_succ]
      have hlast : ∑ b ∈ range (n + 1), c (w n) (w b) * φX i n b = 0 := by
        apply Finset.sum_eq_zero; intro b _
        simp only [hφX]; rw [if_neg (by omega)]; ring
      rw [hlast, add_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a ha
      simp only [Finset.mem_range] at ha
      have : ∀ b, c (w a) (w b) * φX i a b =
          if b = min (a + (i + 1)) n then (1 - p) ^ i * p ^ 2 * c (w a) (w b) else 0 := by
        intro b
        simp only [hφX]
        by_cases hb : b = min (a + (i + 1)) n
        · rw [if_pos ⟨ha, hb⟩, if_pos hb]; ring
        · rw [if_neg (fun h => hb h.2), if_neg hb]; ring
      rw [Finset.sum_congr rfl (fun b _ => this b), Finset.sum_ite_eq']
      rw [if_pos (by simp only [Finset.mem_range]; omega)]
      congr 2
      by_cases hle : a + (i + 1) ≤ n
      · rw [min_eq_left hle]
      · rw [min_eq_right (by omega), hwn n le_rfl, hwn (a + (i + 1)) (by omega)]; try rfl
    have hY : ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), c (w a) (w b) * φY i a b =
        (1 - p) ^ i * p ^ 2 * ∑ t ∈ range (i + 1), c (w 0) (w t) := by
      rw [Finset.sum_eq_single 0]
      · have e1 : ∑ b ∈ range (n + 1), c (w 0) (w b) * φY i 0 b =
            (1 - p) ^ i * p ^ 2 * ∑ t ∈ range (min n (i + 1)), c (w 0) (w t) := by
          rw [Finset.mul_sum]
          have : ∀ b, c (w 0) (w b) * φY i 0 b =
              if b < n ∧ b ≤ i then (1 - p) ^ i * p ^ 2 * c (w 0) (w b) else 0 := by
            intro b
            simp only [hφY]
            by_cases hb : b < n ∧ b ≤ i
            · rw [if_pos (by simp [hb]), if_pos hb]; ring
            · rw [if_neg (by simp [hb]), if_neg hb]; ring
          rw [Finset.sum_congr rfl (fun b _ => this b), ← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext t; simp; omega
        rw [e1]
        congr 1
        apply Finset.sum_subset
        · intro t ht; simp at ht ⊢; omega
        · intro t ht hnt
          simp at ht hnt
          rw [hw0, hwn t (by omega), hcdd]
      · intro a _ ha0
        apply Finset.sum_eq_zero; intro b _
        simp only [hφY]; rw [if_neg (by omega)]; ring
      · intro h; simp at h
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hX, hY]
    ring
  rw [tsum_congr hR1]
  have hsumφ : ∀ a b, Summable (fun i => φX i a b + φY i a b) := by
    intro a b
    have hr0 : 0 ≤ 1 - p := by linarith
    have hgs : Summable (fun i : ℕ => (1 - p) ^ i * p ^ 2) :=
      (summable_geometric_of_lt_one hr0 (by linarith)).mul_right _
    apply Summable.add
    · apply Summable.of_nonneg_of_le _ _ hgs
      · intro i; simp only [hφX]; split_ifs <;> positivity
      · intro i; simp only [hφX]; split_ifs <;> simp; positivity
    · apply Summable.of_nonneg_of_le _ _ hgs
      · intro i; simp only [hφY]; split_ifs <;> positivity
      · intro i; simp only [hφY]; split_ifs <;> simp; positivity
  rw [Summable.tsum_finsetSum (fun a _ => by
    apply summable_sum; intro b _; exact (hsumφ a b).mul_left _)]
  apply Finset.sum_congr rfl; intro a ha
  rw [Summable.tsum_finsetSum (fun b _ => (hsumφ a b).mul_left _)]
  apply Finset.sum_congr rfl; intro b hb
  simp only [Finset.mem_range] at ha hb
  rw [tsum_mul_left]
  have hsX : Summable (fun i => φX i a b) := by
    have hr0 : 0 ≤ 1 - p := by linarith
    apply Summable.of_nonneg_of_le _ _ ((summable_geometric_of_lt_one hr0 (by linarith)).mul_right (p ^ 2))
    · intro i; simp only [hφX]; split_ifs <;> positivity
    · intro i; simp only [hφX]; split_ifs <;> simp; positivity
  have hsY : Summable (fun i => φY i a b) := by
    have hr0 : 0 ≤ 1 - p := by linarith
    apply Summable.of_nonneg_of_le _ _ ((summable_geometric_of_lt_one hr0 (by linarith)).mul_right (p ^ 2))
    · intro i; simp only [hφY]; split_ifs <;> positivity
    · intro i; simp only [hφY]; split_ifs <;> simp; positivity
  rw [Summable.tsum_add hsX hsY]
  simp only [hφX, hφY]
  rw [kappaX p hp hp1 n a b, kappaY p hp hp1 n a b]
  -- compare coefficients
  by_cases h00 : a = 0 ∧ (b = 0 ∨ b = n)
  · obtain ⟨rfl, hb'⟩ := h00
    have : c (w 0) (w b) = 0 := by
      rcases hb' with rfl | rfl
      · rw [hw0, hcdd]
      · rw [hw0, hwn n le_rfl, hcdd]
    rw [this, zero_mul, zero_mul]
  · congr 1
    simp only [hcoefL, hρ]
    have hpow : ∀ m : ℕ, 1 ≤ m → (1 - p) ^ m = (1 - p) ^ (m - 1) * (1 - p) := by
      intro m hm; rw [← pow_succ]; congr 1; omega
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0
      have hb0 : b ≠ 0 := fun h => h00 ⟨rfl, Or.inl h⟩
      have hbn : b ≠ n := fun h => h00 ⟨rfl, Or.inr h⟩
      have hbn' : b < n := by omega
      rw [if_pos (show 0 < b by omega), if_pos (show 0 = 0 ∨ 0 = n from Or.inl rfl),
        if_neg (show ¬(b = 0 ∨ b = n) by omega), if_pos (show 0 < b ∧ b < n from ⟨by omega, hbn'⟩),
        if_pos (show 0 = 0 ∧ b < n from ⟨rfl, hbn'⟩)]
      rw [hpow b (by omega)]; simp only [Nat.sub_zero]; ring
    · by_cases hab : a < b
      · by_cases hbn : b < n
        · rw [if_pos hab, if_pos (show a < b ∧ b < n from ⟨hab, hbn⟩),
            if_neg (show ¬(a = 0 ∨ a = n) by omega), if_neg (show ¬(b = 0 ∨ b = n) by omega),
            if_neg (show ¬(a = 0 ∧ b < n) by omega)]
          ring
        · have hb : b = n := by omega
          rw [if_pos hab, if_neg (show ¬(a < b ∧ b < n) by omega),
            if_pos (show a < n ∧ b = n by omega), if_neg (show ¬(a = 0 ∨ a = n) by omega),
            if_pos (show b = 0 ∨ b = n by omega), if_neg (show ¬(a = 0 ∧ b < n) by omega), hb]
          ring
      · rw [if_neg hab, if_neg (show ¬(a < b ∧ b < n) by omega),
          if_neg (show ¬(a < n ∧ b = n) by omega), if_neg (show ¬(a = 0 ∧ b < n) by omega)]
        ring
