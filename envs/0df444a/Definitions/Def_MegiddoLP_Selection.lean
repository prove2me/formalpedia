-- Prove2me | Definitions.Def_MegiddoLP_Selection
-- name    : MegiddoLP_Selection
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-23T06:37:26.566144+00:00
-- url     : https://prove2.me/theorems/325efd48-f884-45c9-a6f9-68ad1a3ca926
-- title:
--   Deterministic linear-time selection on the real pointer machine
-- statement:
--   The median-of-medians program selects an order statistic from an array of real numbers. Its specification gives explicit instruction and memory bounds, including the handling of ties.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §2 and §5. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_MegiddoLP_MachineFrame
import Definitions.Def_MegiddoLP_VectorGadgets
import Mathlib.Tactic

/-!
# Deterministic Linear-Time Median Selection (Blum–Floyd–Pratt–Rivest–Tarjan) on `RAMProgram`

Implements iterative median-of-medians (`selectMedianStmt`) over `SmaleNinth.RAMInstr`
without floor/sort primitives, running in `≤ 110050 * (N + 1)` instructions on any array
of `N` reals and preserving all registers `< rMin`, pointers `< pMin`, and memory `< arena`.
-/

namespace MegiddoLP.Selection

open SmaleNinth MegiddoLP.MachineDSL MegiddoLP.VectorGadgets

/-! ## Pure Order-Statistic & Group-of-5 Theory on `List ℝ` -/

noncomputable def cntLt (xs : List ℝ) (c : ℝ) : ℕ := xs.countP (fun x => decide (x < c))
noncomputable def cntLe (xs : List ℝ) (c : ℝ) : ℕ := xs.countP (fun x => decide (x ≤ c))
noncomputable def cntGe (xs : List ℝ) (c : ℝ) : ℕ := xs.countP (fun x => decide (c ≤ x))
noncomputable def cntGt (xs : List ℝ) (c : ℝ) : ℕ := xs.countP (fun x => decide (c < x))

/-- `c` is a valid `k`-th order statistic (`0 ≤ k < xs.length`) of `xs`. -/
def IsKthOrder (xs : List ℝ) (k : ℕ) (c : ℝ) : Prop :=
  c ∈ xs ∧ cntLt xs c ≤ k ∧ k < cntLe xs c

theorem cntLt_add_cntGe (xs : List ℝ) (c : ℝ) :
    cntLt xs c + cntGe xs c = xs.length := by
  induction xs with
  | nil => simp [cntLt, cntGe]
  | cons x xs ih =>
    simp only [cntLt, cntGe, List.countP_cons, List.length_cons] at ih ⊢
    by_cases h : x < c
    · have h2 : ¬ c ≤ x := not_le.mpr h
      simp [h, h2]; omega
    · have h2 : c ≤ x := le_of_not_gt h
      simp [h, h2]; omega

theorem cntLe_add_cntGt (xs : List ℝ) (c : ℝ) :
    cntLe xs c + cntGt xs c = xs.length := by
  induction xs with
  | nil => simp [cntLe, cntGt]
  | cons x xs ih =>
    simp only [cntLe, cntGt, List.countP_cons, List.length_cons] at ih ⊢
    by_cases h : x ≤ c
    · have h2 : ¬ c < x := not_lt.mpr h
      simp [h, h2]; omega
    · have h2 : c < x := lt_of_not_ge h
      simp [h, h2]; omega

theorem median_of_isKthOrder {xs : List ℝ} {c : ℝ}
    (h : IsKthOrder xs (xs.length / 2) c) :
    2 * cntLt xs c ≤ xs.length ∧ 2 * cntGt xs c ≤ xs.length := by
  obtain ⟨_, hlt, hle⟩ := h
  have hsum := cntLe_add_cntGt xs c
  omega

theorem countP_mono_imp {xs : List ℝ} {p q : ℝ → Bool}
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons]
    have hx := h x List.mem_cons_self
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hp : p x <;> cases hq : q x
    · simp; omega
    · simp; omega
    · have := hx hp; rw [hq] at this; cases this
    · simp; omega

theorem countP_eq_length_of_all {xs : List ℝ} {p : ℝ → Bool}
    (h : ∀ x ∈ xs, p x = true) : xs.countP p = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp

theorem countP_eq_zero_of_none {xs : List ℝ} {p : ℝ → Bool}
    (h : ∀ x ∈ xs, p x = false) : xs.countP p = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp

/-- Every nonempty list `xs` and `k < xs.length` has an element `xs[i]` satisfying `IsKthOrder`. -/
theorem exists_index_isKthOrder (xs : List ℝ) (k : ℕ) (hk : k < xs.length) :
    ∃ i : Fin xs.length, IsKthOrder xs k xs[i.1] := by
  classical
  have : Nonempty (Fin xs.length) := ⟨⟨0, by omega⟩⟩
  set S : Finset (Fin xs.length) := Finset.univ.filter (fun j => k < cntLe xs xs[j.1])
  have hSne : S.Nonempty := by
    obtain ⟨jmax, _, hmax⟩ := Finset.univ.exists_max_image (fun j : Fin xs.length => xs[j.1])
      Finset.univ_nonempty
    refine ⟨jmax, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hall : cntLe xs xs[jmax.1] = xs.length := by
      apply countP_eq_length_of_all
      intro x hx
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hx
      simp [hmax ⟨m, hm⟩ (Finset.mem_univ _)]
    omega
  obtain ⟨imin, himin, hmin⟩ := S.exists_min_image (fun j : Fin xs.length => xs[j.1]) hSne
  refine ⟨imin, List.getElem_mem _, ?_, (Finset.mem_filter.mp himin).2⟩
  set B : Finset (Fin xs.length) := Finset.univ.filter (fun j => xs[j.1] < xs[imin.1])
  by_cases hB : B.Nonempty
  · obtain ⟨j1, hj1, hj1max⟩ := B.exists_max_image (fun j : Fin xs.length => xs[j.1]) hB
    have hj1lt : xs[j1.1] < xs[imin.1] := (Finset.mem_filter.mp hj1).2
    have hj1notS : j1 ∉ S := fun hmem => by linarith [hmin j1 hmem]
    have hj1le : cntLe xs xs[j1.1] ≤ k := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj1notS
      exact hj1notS
    refine le_trans ?_ hj1le
    apply countP_mono_imp
    intro x hx hlt
    simp only [decide_eq_true_eq] at hlt ⊢
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hx
    exact hj1max ⟨m, hm⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
  · have hzero : cntLt xs xs[imin.1] = 0 := by
      apply countP_eq_zero_of_none
      intro x hx
      simp only [decide_eq_false_iff_not]
      intro hlt
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hx
      exact hB ⟨⟨m, hm⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩
    omega

/-- Left filter reduction (`k < cntLt xs p`). -/
theorem isKthOrder_of_filter_lt {xs : List ℝ} {p ans : ℝ} {k : ℕ}
    (h : IsKthOrder (xs.filter (fun x => decide (x < p))) k ans) :
    IsKthOrder xs k ans := by
  obtain ⟨hmem, hlt, hle⟩ := h
  have hmem' := List.mem_filter.mp hmem
  have hans_lt : ans < p := of_decide_eq_true hmem'.2
  have heq : ∀ L : List ℝ,
      cntLt (L.filter (fun x => decide (x < p))) ans = cntLt L ans ∧
      cntLe (L.filter (fun x => decide (x < p))) ans = cntLe L ans := by
    intro L
    induction L with
    | nil => simp [cntLt, cntLe]
    | cons x L ih =>
      by_cases hxp : x < p
      · rw [List.filter_cons_of_pos (by simp [hxp])]
        simp only [cntLt, cntLe, List.countP_cons] at ih ⊢
        rw [ih.1, ih.2]; exact ⟨rfl, rfl⟩
      · have hxa1 : ¬ x < ans := by linarith
        have hxa2 : ¬ x ≤ ans := by linarith
        rw [List.filter_cons_of_neg (by simp [hxp])]
        simp only [cntLt, cntLe, List.countP_cons, decide_eq_true_eq] at ih ⊢
        rw [if_neg hxa1, if_neg hxa2, Nat.add_zero, Nat.add_zero]
        exact ih
  exact ⟨hmem'.1, (heq xs).1 ▸ hlt, (heq xs).2 ▸ hle⟩

/-- Right filter reduction (`cntLe xs p ≤ k`). -/
theorem isKthOrder_of_filter_gt {xs : List ℝ} {p ans : ℝ} {k : ℕ}
    (hk : cntLe xs p ≤ k)
    (h : IsKthOrder (xs.filter (fun x => decide (p < x))) (k - cntLe xs p) ans) :
    IsKthOrder xs k ans := by
  obtain ⟨hmem, hlt, hle⟩ := h
  have hmem' := List.mem_filter.mp hmem
  have hp_lt : p < ans := of_decide_eq_true hmem'.2
  have hadd : ∀ L : List ℝ,
      cntLt L ans = cntLe L p + cntLt (L.filter (fun x => decide (p < x))) ans ∧
      cntLe L ans = cntLe L p + cntLe (L.filter (fun x => decide (p < x))) ans := by
    intro L
    induction L with
    | nil => simp [cntLt, cntLe]
    | cons x L ih =>
      by_cases hxp : p < x
      · have hnotle : ¬ x ≤ p := not_le.mpr hxp
        rw [List.filter_cons_of_pos (by simp [hxp])]
        simp only [cntLt, cntLe, List.countP_cons, decide_eq_true_eq] at ih ⊢
        rw [if_neg hnotle, Nat.add_zero, ih.1, ih.2]
        exact ⟨by omega, by omega⟩
      · have hxle : x ≤ p := le_of_not_gt hxp
        have hxa1 : x < ans := lt_of_le_of_lt hxle hp_lt
        have hxa2 : x ≤ ans := le_of_lt hxa1
        rw [List.filter_cons_of_neg (by simp [hxp])]
        simp only [cntLt, cntLe, List.countP_cons, decide_eq_true_eq] at ih ⊢
        rw [if_pos hxle, if_pos hxa1, if_pos hxa2, ih.1, ih.2]
        exact ⟨by omega, by omega⟩
  have h1 := (hadd xs).1
  have h2 := (hadd xs).2
  exact ⟨hmem'.1, by omega, by omega⟩

/-! ## 5-Element Compare-Swap Median (`med5`) and BFPRT 3/10 Lemma -/

noncomputable def cswapPair (a b : ℝ) : ℝ × ℝ :=
  if b < a then (b, a) else (a, b)

theorem cswapPair_ord (a b : ℝ) :
    (cswapPair a b).1 ≤ (cswapPair a b).2 ∧
    a ≤ (cswapPair a b).2 ∧ b ≤ (cswapPair a b).2 ∧
    (∀ z, a ≤ z → b ≤ z → (cswapPair a b).1 ≤ z ∧ (cswapPair a b).2 ≤ z) := by
  unfold cswapPair
  split_ifs with h
  · exact ⟨le_of_lt h, le_rfl, le_of_lt h, fun z ha hb => ⟨hb, ha⟩⟩
  · exact ⟨le_of_not_gt h, le_of_not_gt h, le_rfl, fun z ha hb => ⟨ha, hb⟩⟩

theorem cswapPair_sum (f : ℝ → ℕ) (a b : ℝ) :
    f (cswapPair a b).1 + f (cswapPair a b).2 = f a + f b := by
  unfold cswapPair; split_ifs <;> simp [Nat.add_comm]

/-- 9-compare-swap median of 5 reals (3 partial bubble-sort passes placing exact median at slot 2). -/
noncomputable def med5 (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  let p1 := cswapPair x0 x1
  let p2 := cswapPair p1.2 x2
  let p3 := cswapPair p2.2 x3
  let p4 := cswapPair p3.2 x4
  let q1 := cswapPair p1.1 p2.1
  let q2 := cswapPair q1.2 p3.1
  let q3 := cswapPair q2.2 p4.1
  let r1 := cswapPair q1.1 q2.1
  let r2 := cswapPair r1.2 q3.1
  r2.2

theorem med5_props (x0 x1 x2 x3 x4 : ℝ) :
    med5 x0 x1 x2 x3 x4 ∈ [x0, x1, x2, x3, x4] ∧
    (∀ p, p ≤ med5 x0 x1 x2 x3 x4 → 3 ≤ cntGe [x0, x1, x2, x3, x4] p) ∧
    (∀ p, med5 x0 x1 x2 x3 x4 ≤ p → 3 ≤ cntLe [x0, x1, x2, x3, x4] p) := by
  set p1 := cswapPair x0 x1
  set p2 := cswapPair p1.2 x2
  set p3 := cswapPair p2.2 x3
  set p4 := cswapPair p3.2 x4
  set q1 := cswapPair p1.1 p2.1
  set q2 := cswapPair q1.2 p3.1
  set q3 := cswapPair q2.2 p4.1
  set r1 := cswapPair q1.1 q2.1
  set r2 := cswapPair r1.2 q3.1
  have hp1 := cswapPair_ord x0 x1
  have hp2 := cswapPair_ord p1.2 x2
  have hp3 := cswapPair_ord p2.2 x3
  have hp4 := cswapPair_ord p3.2 x4
  have hq1 := cswapPair_ord p1.1 p2.1
  have hq2 := cswapPair_ord q1.2 p3.1
  have hq3 := cswapPair_ord q2.2 p4.1
  have hr1' := cswapPair_ord q1.1 q2.1
  have hr2 := cswapPair_ord r1.2 q3.1
  have hp1_le_p4 : p1.1 ≤ p4.2 := by linarith [hp1.1, hp2.2.1, hp3.2.1, hp4.2.1]
  have hp2_le_p4 : p2.1 ≤ p4.2 := by linarith [hp2.1, hp3.2.1, hp4.2.1]
  have hp3_le_p4 : p3.1 ≤ p4.2 := by linarith [hp3.1, hp4.2.1]
  have hq1_le_p4 : q1.1 ≤ p4.2 ∧ q1.2 ≤ p4.2 := hq1.2.2.2 p4.2 hp1_le_p4 hp2_le_p4
  have hq2_le_p4 : q2.1 ≤ p4.2 ∧ q2.2 ≤ p4.2 := hq2.2.2.2 p4.2 hq1_le_p4.2 hp3_le_p4
  have hq3_le_p4 : q3.1 ≤ p4.2 ∧ q3.2 ≤ p4.2 := hq3.2.2.2 p4.2 hq2_le_p4.2 hp4.1
  have hq1_le_q3 : q1.1 ≤ q3.2 := by linarith [hq1.1, hq2.2.1, hq3.2.1]
  have hq2_le_q3 : q2.1 ≤ q3.2 := by linarith [hq2.1, hq3.2.1]
  have hr1_le_q3 : r1.1 ≤ q3.2 ∧ r1.2 ≤ q3.2 := hr1'.2.2.2 q3.2 hq1_le_q3 hq2_le_q3
  have hr2_le_q3 : r2.1 ≤ q3.2 ∧ r2.2 ≤ q3.2 := hr2.2.2.2 q3.2 hr1_le_q3.2 hq3.1
  have hr1_le_r2 : r1.1 ≤ r2.2 := by linarith [hr1'.1, hr2.2.1]
  have hsum : ∀ f : ℝ → ℕ,
      f x0 + f x1 + f x2 + f x3 + f x4 =
      f r1.1 + f r2.1 + f r2.2 + f q3.2 + f p4.2 := by
    intro f
    have s1 : f p1.1 + f p1.2 = f x0 + f x1 := cswapPair_sum f x0 x1
    have s2 : f p2.1 + f p2.2 = f p1.2 + f x2 := cswapPair_sum f p1.2 x2
    have s3 : f p3.1 + f p3.2 = f p2.2 + f x3 := cswapPair_sum f p2.2 x3
    have s4 : f p4.1 + f p4.2 = f p3.2 + f x4 := cswapPair_sum f p3.2 x4
    have s5 : f q1.1 + f q1.2 = f p1.1 + f p2.1 := cswapPair_sum f p1.1 p2.1
    have s6 : f q2.1 + f q2.2 = f q1.2 + f p3.1 := cswapPair_sum f q1.2 p3.1
    have s7 : f q3.1 + f q3.2 = f q2.2 + f p4.1 := cswapPair_sum f q2.2 p4.1
    have s8 : f r1.1 + f r1.2 = f q1.1 + f q2.1 := cswapPair_sum f q1.1 q2.1
    have s9 : f r2.1 + f r2.2 = f r1.2 + f q3.1 := cswapPair_sum f r1.2 q3.1
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- Membership `r2.2 ∈ [x0, x1, x2, x3, x4]`
    change r2.2 ∈ [x0, x1, x2, x3, x4]
    have mem_sub : ∀ {u v : ℝ} {L : List ℝ}, u ∈ L → v ∈ L →
        (cswapPair u v).1 ∈ L ∧ (cswapPair u v).2 ∈ L := by
      intro u v L hu hv; unfold cswapPair; split_ifs <;> exact ⟨‹_›, ‹_›⟩
    have m1 := mem_sub (L := [x0, x1, x2, x3, x4]) (by simp) (by simp) (u := x0) (v := x1)
    have m2 := mem_sub m1.2 (by simp) (u := p1.2) (v := x2)
    have m3 := mem_sub m2.2 (by simp) (u := p2.2) (v := x3)
    have m4 := mem_sub m3.2 (by simp) (u := p3.2) (v := x4)
    have m5 := mem_sub m1.1 m2.1 (u := p1.1) (v := p2.1)
    have m6 := mem_sub m5.2 m3.1 (u := q1.2) (v := p3.1)
    have m7 := mem_sub m6.2 m4.1 (u := q2.2) (v := p4.1)
    have m8 := mem_sub m5.1 m6.1 (u := q1.1) (v := q2.1)
    have m9 := mem_sub m8.2 m7.1 (u := r1.2) (v := q3.1)
    exact m9.2
  · intro p hp
    change p ≤ r2.2 at hp
    let f : ℝ → ℕ := fun x => if decide (p ≤ x) then 1 else 0
    have hcnt : cntGe [x0, x1, x2, x3, x4] p = f x0 + f x1 + f x2 + f x3 + f x4 := by
      simp only [cntGe, List.countP_cons, List.countP_nil, f]; omega
    rw [hcnt, hsum f]
    have hA : f r2.2 = 1 := by simp [f, hp]
    have hB : f q3.2 = 1 := by simp [f, show p ≤ q3.2 by linarith [hr2_le_q3.2]]
    have hC : f p4.2 = 1 := by simp [f, show p ≤ p4.2 by linarith [hr2_le_q3.2, hq3_le_p4.2]]
    omega
  · intro p hp
    change r2.2 ≤ p at hp
    let f : ℝ → ℕ := fun x => if decide (x ≤ p) then 1 else 0
    have hcnt : cntLe [x0, x1, x2, x3, x4] p = f x0 + f x1 + f x2 + f x3 + f x4 := by
      simp only [cntLe, List.countP_cons, List.countP_nil, f]; omega
    rw [hcnt, hsum f]
    have hA : f r1.1 = 1 := by simp [f, show r1.1 ≤ p by linarith [hr1_le_r2]]
    have hB : f r2.1 = 1 := by simp [f, show r2.1 ≤ p by linarith [hr2.1]]
    have hC : f r2.2 = 1 := by simp [f, hp]
    omega

/-- List of `xs.length / 5` group-of-5 medians of `xs`. -/
noncomputable def medsOf5 (xs : List ℝ) : List ℝ :=
  List.ofFn (fun m : Fin (xs.length / 5) =>
    have hm : 5 * m.1 + 4 < xs.length := by have := m.2; omega
    med5 xs[5 * m.1] xs[5 * m.1 + 1] xs[5 * m.1 + 2] xs[5 * m.1 + 3] xs[5 * m.1 + 4])

theorem medsOf5_subset {xs : List ℝ} {p : ℝ} (hp : p ∈ medsOf5 xs) : p ∈ xs := by
  unfold medsOf5 at hp
  rw [List.mem_ofFn] at hp
  obtain ⟨m, rfl⟩ := hp
  have hm : 5 * m.1 + 4 < xs.length := by have := m.2; omega
  have hmem5 := (med5_props xs[5 * m.1] xs[5 * m.1 + 1] xs[5 * m.1 + 2]
    xs[5 * m.1 + 3] xs[5 * m.1 + 4]).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem5
  rcases hmem5 with h | h | h | h | h <;> rw [h] <;> exact List.getElem_mem _

theorem take_five_succ (xs : List ℝ) (m : ℕ) (hm : 5 * (m + 1) ≤ xs.length) :
    xs.take (5 * (m + 1)) =
      xs.take (5 * m) ++ [xs[5 * m], xs[5 * m + 1], xs[5 * m + 2], xs[5 * m + 3], xs[5 * m + 4]] := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hm, Nat.min_eq_left (show 5 * m ≤ xs.length by omega)]; omega
  · intro i hi1 hi2
    simp only [List.length_take, Nat.min_eq_left hm] at hi1
    by_cases hlt : i < 5 * m
    · rw [List.getElem_take, List.getElem_append_left (by simp [Nat.min_eq_left (by omega : 5 * m ≤ xs.length)]; exact hlt),
        List.getElem_take]
    · rw [List.getElem_take, List.getElem_append_right (by simp [Nat.min_eq_left (by omega : 5 * m ≤ xs.length)]; omega)]
      have hlen : (xs.take (5 * m)).length = 5 * m := by simp [Nat.min_eq_left (by omega : 5 * m ≤ xs.length)]
      simp only [hlen]
      have hd : i = 5 * m ∨ i = 5 * m + 1 ∨ i = 5 * m + 2 ∨ i = 5 * m + 3 ∨ i = 5 * m + 4 := by omega
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp

theorem bfprt_three_tenths_bounds (xs : List ℝ) (p : ℝ)
    (hp : IsKthOrder (medsOf5 xs) ((xs.length / 5) / 2) p) :
    cntLt xs p ≤ xs.length - 3 * ((xs.length / 5) - (xs.length / 5) / 2) ∧
    cntGt xs p ≤ xs.length - 3 * ((xs.length / 5) / 2 + 1) := by
  set g := xs.length / 5
  have hprefix : ∀ m ≤ g,
      3 * cntGe ((medsOf5 xs).take m) p ≤ cntGe (xs.take (5 * m)) p ∧
      3 * cntLe ((medsOf5 xs).take m) p ≤ cntLe (xs.take (5 * m)) p := by
    intro m
    induction m with
    | zero => intro _; simp [cntGe, cntLe]
    | succ m ih =>
      intro hmg
      obtain ⟨ihGe, ihLe⟩ := ih (by omega)
      have hm_len : m < (medsOf5 xs).length := by simp [medsOf5]; omega
      have hmed_take : (medsOf5 xs).take (m + 1) = (medsOf5 xs).take m ++ [(medsOf5 xs)[m]] :=
        List.take_succ_eq_append_getElem hm_len
      have hmed_val : (medsOf5 xs)[m] =
          med5 xs[5 * m] xs[5 * m + 1] xs[5 * m + 2] xs[5 * m + 3] xs[5 * m + 4] := by
        simp [medsOf5]
      have hxs_take := take_five_succ xs m (by omega)
      have mp := med5_props xs[5 * m] xs[5 * m + 1] xs[5 * m + 2] xs[5 * m + 3] xs[5 * m + 4]
      constructor
      · simp only [cntGe, hmed_take, hxs_take, List.countP_append, List.countP_singleton] at ihGe ⊢
        by_cases hpm : p ≤ (medsOf5 xs)[m]
        · have h3 := mp.2.1 p (hmed_val ▸ hpm)
          simp only [cntGe] at h3
          simp [hpm]; omega
        · simp [hpm]; omega
      · simp only [cntLe, hmed_take, hxs_take, List.countP_append, List.countP_singleton] at ihLe ⊢
        by_cases hmp : (medsOf5 xs)[m] ≤ p
        · have h3 := mp.2.2 p (hmed_val ▸ hmp)
          simp only [cntLe] at h3
          simp [hmp]; omega
        · simp [hmp]; omega
  obtain ⟨hGe5g, hLe5g⟩ := hprefix g le_rfl
  have hmed_len : (medsOf5 xs).length = g := by simp [medsOf5, g]
  rw [List.take_of_length_le (by omega)] at hGe5g hLe5g
  have htake_le_all : ∀ q : ℝ → Bool, (xs.take (5 * g)).countP q ≤ xs.countP q := by
    intro q
    conv_rhs => rw [← List.take_append_drop (5 * g) xs]
    rw [List.countP_append]; omega
  have hGeAll : 3 * cntGe (medsOf5 xs) p ≤ cntGe xs p :=
    le_trans hGe5g (htake_le_all _)
  have hLeAll : 3 * cntLe (medsOf5 xs) p ≤ cntLe xs p :=
    le_trans hLe5g (htake_le_all _)
  have hsumMed := cntLt_add_cntGe (medsOf5 xs) p
  rw [hmed_len] at hsumMed
  have hsumXs1 := cntLt_add_cntGe xs p
  have hsumXs2 := cntLe_add_cntGt xs p
  obtain ⟨_, hpLt, hpLe⟩ := hp
  omega

/-! ## Memory List Predicate & Machine Sub-Gadgets -/

/-- `mem` stores `xs : List ℝ` at `[base .. base + xs.length)`. -/
def ListAt (mem : ℤ → ℝ) (base : ℤ) (xs : List ℝ) : Prop :=
  ∀ i (hi : i < xs.length), mem (base + (i : ℤ)) = xs[i]

theorem ListAt.of_mem_pres {bound base : ℤ} {m₁ m₂ : ℤ → ℝ} {xs : List ℝ}
    (h : ListAt m₁ base xs) (hm : MemPreservedBelow bound m₁ m₂)
    (hb : base + (xs.length : ℤ) ≤ bound) :
    ListAt m₂ base xs := by
  intro i hi
  exact (hm _ (by omega)).trans (h i hi)

theorem vecAt_iff_listAt {N : ℕ} (mem : ℤ → ℝ) (base : ℤ) (arr : Fin N → ℝ) :
    VecAt mem base arr ↔ ListAt mem base (List.ofFn arr) := by
  constructor
  · intro hv i hi
    simp only [List.length_ofFn] at hi
    simpa using hv ⟨i, hi⟩
  · intro hl j
    have := hl j.1 (by simp [j.2])
    simpa using this

/-- Non-store primitive `SpecRun` helper with automatic `WritesAbove` check. -/
theorem sprim {rMin pMin : ℕ} {memBound : ℤ} {p : Prim} {s : MState}
    (hw : p.WritesAbove rMin pMin := by dsimp [Prim.WritesAbove]; omega)
    (hns : ∀ q i, p ≠ .store q i := by intro _ _ e; cases e) :
    SpecRun rMin pMin memBound (.prim p) s (p.step s) 1 :=
  SpecRun.prim hw (fun q i h => absurd h (hns q i))

/-- Compare-swap two registers `rA` and `rB` in place (`≤ 9` steps). -/
noncomputable def cswapStmt (rA rB rDiff rTmp rZero : ℕ) : Stmt :=
  .seq (.prim (.sub rDiff rA rB))
    (.ifLeZero rDiff .skip
      (.seq (copyReg rTmp rA rZero)
        (.seq (copyReg rA rB rZero)
          (copyReg rB rTmp rZero))))

theorem cswapStmt_spec {rMin pMin : ℕ} {memBound : ℤ}
    {rA rB rDiff rTmp rZero : ℕ} {s : MState}
    (hA : rMin ≤ rA) (hB : rMin ≤ rB) (hD : rMin ≤ rDiff) (hT : rMin ≤ rTmp) (hZ : rMin ≤ rZero)
    (hAB : rA ≠ rB) (hAD : rA ≠ rDiff) (hBD : rB ≠ rDiff)
    (hAT : rA ≠ rTmp) (hBT : rB ≠ rTmp) (hAZ : rA ≠ rZero) (hBZ : rB ≠ rZero) (hTZ : rTmp ≠ rZero) :
    ∃ s', SpecRun rMin pMin memBound (cswapStmt rA rB rDiff rTmp rZero) s s' 9 ∧
      s'.regs rA = (cswapPair (s.regs rA) (s.regs rB)).1 ∧
      s'.regs rB = (cswapPair (s.regs rA) (s.regs rB)).2 ∧
      (∀ i, i ≠ rA → i ≠ rB → i ≠ rDiff → i ≠ rTmp → i ≠ rZero → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have p1 : SpecRun rMin pMin memBound (.prim (.sub rDiff rA rB)) s
      ((Prim.sub rDiff rA rB).step s) 1 :=
    SpecRun.prim hD (by intro _ _ h; cases h)
  set s₁ := (Prim.sub rDiff rA rB).step s
  by_cases hlt : s.regs rB < s.regs rA
  · have hcond : ¬ s₁.regs rDiff ≤ 0 := by
      simp only [s₁, Prim.step, Function.update_self]; linarith
    obtain ⟨s₂, q1, ht2, _, hoth2, hp2, hm2⟩ :=
      copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
        (rDst := rTmp) (rSrc := rA) (rZero := rZero) (s := s₁) hT hZ hAZ hTZ
    obtain ⟨s₃, q2, ha3, _, hoth3, hp3, hm3⟩ :=
      copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
        (rDst := rA) (rSrc := rB) (rZero := rZero) (s := s₂) hA hZ hBZ hAZ
    obtain ⟨s₄, q3, hb4, _, hoth4, hp4, hm4⟩ :=
      copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
        (rDst := rB) (rSrc := rTmp) (rZero := rZero) (s := s₃) hB hZ hTZ hBZ
    refine ⟨s₄, (p1.seq (SpecRun.ifLeZero_false (t := .skip) hcond (q1.seq (q2.seq q3)))).mono (by omega),
      ?_, ?_, ?_, hp4.trans (hp3.trans hp2), hm4.trans (hm3.trans hm2)⟩
    · rw [hoth4 rA hAB hAZ, ha3, hoth2 rB hBT hBZ]
      simp [s₁, Prim.step, Function.update_of_ne hBD, cswapPair, hlt]
    · rw [hb4, hoth3 rTmp hAT.symm hTZ, ht2]
      simp [s₁, Prim.step, Function.update_of_ne hAD, cswapPair, hlt]
    · intro i hiA hiB hiD hiT hiZ
      rw [hoth4 i hiB hiZ, hoth3 i hiA hiZ, hoth2 i hiT hiZ]
      simp [s₁, Prim.step, Function.update_of_ne hiD]
  · have hcond : s₁.regs rDiff ≤ 0 := by
      simp only [s₁, Prim.step, Function.update_self]; linarith
    have p2 := SpecRun.ifLeZero_true
      (e := .seq (copyReg rTmp rA rZero) (.seq (copyReg rA rB rZero) (copyReg rB rTmp rZero)))
      hcond (SpecRun.skip rMin pMin memBound s₁)
    refine ⟨s₁, (p1.seq p2).mono (by omega), ?_, ?_, ?_, rfl, rfl⟩
    · simp [s₁, Prim.step, Function.update_of_ne hAD, cswapPair, hlt]
    · simp [s₁, Prim.step, Function.update_of_ne hBD, cswapPair, hlt]
    · intro i _ _ hiD _ _
      simp [s₁, Prim.step, Function.update_of_ne hiD]

/-- Compute `med5` of `r5 .. r5 + 4` into `r5 + 2` using scratch `r5 + 5, r5 + 6, r5 + 7` (`81` steps). -/
noncomputable def med5Stmt (r5 : ℕ) : Stmt :=
  let cs (a b : ℕ) := cswapStmt (r5 + a) (r5 + b) (r5 + 5) (r5 + 6) (r5 + 7)
  Stmt.block [cs 0 1, cs 1 2, cs 2 3, cs 3 4, cs 0 1, cs 1 2, cs 2 3, cs 0 1, cs 1 2]

theorem med5Stmt_spec {rMin pMin : ℕ} {memBound : ℤ} {r5 : ℕ}
    (hr5 : rMin ≤ r5) (s : MState) :
    ∃ s', SpecRun rMin pMin memBound (med5Stmt r5) s s' 81 ∧
      s'.regs (r5 + 2) = med5 (s.regs r5) (s.regs (r5 + 1)) (s.regs (r5 + 2))
        (s.regs (r5 + 3)) (s.regs (r5 + 4)) ∧
      (∀ i, i < r5 ∨ r5 + 8 ≤ i → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have stepCS : ∀ (a b : ℕ) (st : MState), a < b → b ≤ 4 →
      ∃ st', SpecRun rMin pMin memBound
        (cswapStmt (r5 + a) (r5 + b) (r5 + 5) (r5 + 6) (r5 + 7)) st st' 9 ∧
        st'.regs (r5 + a) = (cswapPair (st.regs (r5 + a)) (st.regs (r5 + b))).1 ∧
        st'.regs (r5 + b) = (cswapPair (st.regs (r5 + a)) (st.regs (r5 + b))).2 ∧
        (∀ c ≤ 4, c ≠ a → c ≠ b → st'.regs (r5 + c) = st.regs (r5 + c)) ∧
        (∀ i, i < r5 ∨ r5 + 8 ≤ i → st'.regs i = st.regs i) ∧
        st'.ptrs = st.ptrs ∧ st'.mem = st.mem := by
    intro a b st hab hb4
    obtain ⟨st', hrun, h1, h2, hoth, hp, hm⟩ :=
      cswapStmt_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
        (rA := r5 + a) (rB := r5 + b) (rDiff := r5 + 5) (rTmp := r5 + 6) (rZero := r5 + 7)
        (s := st) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    exact ⟨st', hrun, h1, h2,
      fun c hc hca hcb => hoth (r5 + c) (by omega) (by omega) (by omega) (by omega) (by omega),
      fun i hi => hoth i (by omega) (by omega) (by omega) (by omega) (by omega), hp, hm⟩
  obtain ⟨s1, r1, a1, b1, o1, f1, hp1, hm1⟩ := stepCS 0 1 s (by omega) (by omega)
  obtain ⟨s2, r2, a2, b2, o2, f2, hp2, hm2⟩ := stepCS 1 2 s1 (by omega) (by omega)
  obtain ⟨s3, r3, a3, b3, o3, f3, hp3, hm3⟩ := stepCS 2 3 s2 (by omega) (by omega)
  obtain ⟨s4, r4, a4, b4, o4, f4, hp4, hm4⟩ := stepCS 3 4 s3 (by omega) (by omega)
  obtain ⟨s5, r5s, a5, b5, o5, f5, hp5, hm5⟩ := stepCS 0 1 s4 (by omega) (by omega)
  obtain ⟨s6, r6, a6, b6, o6, f6, hp6, hm6⟩ := stepCS 1 2 s5 (by omega) (by omega)
  obtain ⟨s7, r7, a7, b7, o7, f7, hp7, hm7⟩ := stepCS 2 3 s6 (by omega) (by omega)
  obtain ⟨s8, r8, a8, b8, o8, f8, hp8, hm8⟩ := stepCS 0 1 s7 (by omega) (by omega)
  obtain ⟨s9, r9, a9, b9, o9, f9, hp9, hm9⟩ := stepCS 1 2 s8 (by omega) (by omega)
  refine ⟨s9,
    (r1.seq (r2.seq (r3.seq (r4.seq (r5s.seq (r6.seq (r7.seq (r8.seq r9)))))))).mono (by omega),
    ?_, ?_, by simp [hp9, hp8, hp7, hp6, hp5, hp4, hp3, hp2, hp1],
    by simp [hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]⟩
  · -- Track the 5 slots cleanly through the 9 swaps
    have v1_0 : s1.regs (r5 + 0) = (cswapPair (s.regs r5) (s.regs (r5 + 1))).1 := by simpa using a1
    have v1_1 : s1.regs (r5 + 1) = (cswapPair (s.regs r5) (s.regs (r5 + 1))).2 := by simpa using b1
    have v4_0 : s4.regs (r5 + 0) = s1.regs (r5 + 0) := by
      rw [o4 0 (by omega) (by omega) (by omega), o3 0 (by omega) (by omega) (by omega),
          o2 0 (by omega) (by omega) (by omega)]
    have v2_1 : s2.regs (r5 + 1) = (cswapPair (s1.regs (r5 + 1)) (s.regs (r5 + 2))).1 := by
      rw [a2, o1 2 (by omega) (by omega) (by omega)]
    have v2_2 : s2.regs (r5 + 2) = (cswapPair (s1.regs (r5 + 1)) (s.regs (r5 + 2))).2 := by
      rw [b2, o1 2 (by omega) (by omega) (by omega)]
    have v4_1 : s4.regs (r5 + 1) = s2.regs (r5 + 1) := by
      rw [o4 1 (by omega) (by omega) (by omega), o3 1 (by omega) (by omega) (by omega)]
    have v3_2 : s3.regs (r5 + 2) = (cswapPair (s2.regs (r5 + 2)) (s.regs (r5 + 3))).1 := by
      rw [a3, o2 3 (by omega) (by omega) (by omega), o1 3 (by omega) (by omega) (by omega)]
    have v3_3 : s3.regs (r5 + 3) = (cswapPair (s2.regs (r5 + 2)) (s.regs (r5 + 3))).2 := by
      rw [b3, o2 3 (by omega) (by omega) (by omega), o1 3 (by omega) (by omega) (by omega)]
    have v4_2 : s4.regs (r5 + 2) = s3.regs (r5 + 2) := o4 2 (by omega) (by omega) (by omega)
    have v4_3 : s4.regs (r5 + 3) = (cswapPair (s3.regs (r5 + 3)) (s.regs (r5 + 4))).1 := by
      rw [a4, o3 4 (by omega) (by omega) (by omega), o2 4 (by omega) (by omega) (by omega),
          o1 4 (by omega) (by omega) (by omega)]
    have v5_0 := a5
    have v5_1 := b5
    have v5_2 : s5.regs (r5 + 2) = s4.regs (r5 + 2) := o5 2 (by omega) (by omega) (by omega)
    have v5_3 : s5.regs (r5 + 3) = s4.regs (r5 + 3) := o5 3 (by omega) (by omega) (by omega)
    have v7_0 : s7.regs (r5 + 0) = s5.regs (r5 + 0) := by
      rw [o7 0 (by omega) (by omega) (by omega), o6 0 (by omega) (by omega) (by omega)]
    have v6_1 := a6
    have v6_2 := b6
    have v6_3 : s6.regs (r5 + 3) = s5.regs (r5 + 3) := o6 3 (by omega) (by omega) (by omega)
    have v7_1 : s7.regs (r5 + 1) = s6.regs (r5 + 1) := o7 1 (by omega) (by omega) (by omega)
    have v7_2 := a7
    have v8_1 := b8
    have v8_2 : s8.regs (r5 + 2) = s7.regs (r5 + 2) := o8 2 (by omega) (by omega) (by omega)
    rw [b9, v8_1, v8_2, v7_0, v7_1, v7_2, v6_1, v6_2, v6_3, v5_0, v5_1, v5_2, v5_3,
        v4_0, v4_1, v4_2, v4_3, v3_2, v3_3, v2_1, v2_2, v1_0, v1_1]
    rfl
  · intro i hi
    rw [f9 i hi, f8 i hi, f7 i hi, f6 i hi, f5 i hi, f4 i hi, f3 i hi, f2 i hi, f1 i hi]

/-- Scan `ListAt s.mem (s.ptrs pStart) xs` (`pEnd = pStart + xs.length`), placing `(cntLt xs piv : ℝ)`
in `rLt` and `(cntLe xs piv : ℝ)` in `rLe` using 4 scratch regs `rScr .. rScr + 3` (`rOne, rVal, rDiff`). -/
noncomputable def countLtLeStmt (pStart pEnd pScan rPiv rLt rLe rScr : ℕ) : Stmt :=
  let rOne := rScr
  let rVal := rScr + 1
  let rDiff := rScr + 2
  .seq (Stmt.block [.prim (.const rOne 1), .prim (.const rLt 0), .prim (.const rLe 0),
      .prim (.pcopy pScan pStart)])
    (.whilePtrLt pScan pEnd
      (.seq (.seq (.prim (.load rVal pScan)) (.prim (.pinc pScan)))
        (.seq (.prim (.sub rDiff rPiv rVal))
          (.ifLeZero rDiff
            (.seq (.prim (.sub rDiff rVal rPiv))
              (.ifLeZero rDiff (.prim (.add rLe rLe rOne)) .skip))
            (.seq (.prim (.add rLt rLt rOne)) (.prim (.add rLe rLe rOne)))))))

theorem countLtLeStmt_spec {rMin pMin : ℕ} {memBound : ℤ}
    {pStart pEnd pScan rPiv rLt rLe rScr : ℕ} {xs : List ℝ} {s : MState}
    (hxs : ListAt s.mem (s.ptrs pStart) xs)
    (hEnd : s.ptrs pEnd = s.ptrs pStart + (xs.length : ℤ))
    (hLt : rMin ≤ rLt) (hLe : rMin ≤ rLe) (hScr : rMin ≤ rScr) (hpScan : pMin ≤ pScan)
    (_hScanS : pScan ≠ pStart) (hScanE : pScan ≠ pEnd)
    (hLtLe : rLt ≠ rLe) (hPivLt : rPiv ≠ rLt) (hPivLe : rPiv ≠ rLe)
    (hPivScr : rPiv < rScr ∨ rScr + 3 ≤ rPiv)
    (hLtScr : rLt < rScr ∨ rScr + 3 ≤ rLt)
    (hLeScr : rLe < rScr ∨ rScr + 3 ≤ rLe) :
    ∃ s', SpecRun rMin pMin memBound
        (countLtLeStmt pStart pEnd pScan rPiv rLt rLe rScr) s s' (10 * xs.length + 10) ∧
      s'.regs rLt = (cntLt xs (s.regs rPiv) : ℝ) ∧
      s'.regs rLe = (cntLe xs (s.regs rPiv) : ℝ) ∧
      (∀ i, i ≠ rLt → i ≠ rLe → (i < rScr ∨ rScr + 3 ≤ i) → s'.regs i = s.regs i) ∧
      (∀ q, q ≠ pScan → s'.ptrs q = s.ptrs q) ∧
      s'.mem = s.mem := by
  let rOne := rScr
  let rVal := rScr + 1
  let rDiff := rScr + 2
  set piv := s.regs rPiv
  set base := s.ptrs pStart
  have pInit1 : SpecRun rMin pMin memBound (.prim (.const rOne 1)) s _ 1 := sprim
  have pInit2 : SpecRun rMin pMin memBound (.prim (.const rLt 0))
      ((Prim.const rOne 1).step s) _ 1 := sprim
  have pInit3 : SpecRun rMin pMin memBound (.prim (.const rLe 0))
      ((Prim.const rLt 0).step ((Prim.const rOne 1).step s)) _ 1 := sprim
  have pInit4 : SpecRun rMin pMin memBound (.prim (.pcopy pScan pStart))
      ((Prim.const rLe 0).step ((Prim.const rLt 0).step ((Prim.const rOne 1).step s))) _ 1 := sprim
  set s₀ := (Prim.pcopy pScan pStart).step
    ((Prim.const rLe 0).step ((Prim.const rLt 0).step ((Prim.const rOne 1).step s)))
  have hs₀ : SpecRun rMin pMin memBound
      (Stmt.block [.prim (.const rOne 1), .prim (.const rLt 0), .prim (.const rLe 0),
        .prim (.pcopy pScan pStart)]) s s₀ 4 :=
    (pInit1.seq (pInit2.seq (pInit3.seq pInit4))).mono (by omega)
  let body : Stmt :=
    .seq (.seq (.prim (.load rVal pScan)) (.prim (.pinc pScan)))
      (.seq (.prim (.sub rDiff rPiv rVal))
        (.ifLeZero rDiff
          (.seq (.prim (.sub rDiff rVal rPiv))
            (.ifLeZero rDiff (.prim (.add rLe rLe rOne)) .skip))
          (.seq (.prim (.add rLt rLt rOne)) (.prim (.add rLe rLe rOne)))))
  let Inv : ℕ → MState → Prop := fun t st =>
    st.mem = s.mem ∧
    st.ptrs pScan = base + (t : ℤ) ∧
    (∀ q, q ≠ pScan → st.ptrs q = s.ptrs q) ∧
    st.regs rOne = 1 ∧
    st.regs rLt = (cntLt (xs.take t) piv : ℝ) ∧
    st.regs rLe = (cntLe (xs.take t) piv : ℝ) ∧
    (∀ i, i ≠ rLt → i ≠ rLe → (i < rScr ∨ rScr + 3 ≤ i) → st.regs i = s.regs i)
  have hInv0 : Inv 0 s₀ := by
    refine ⟨rfl, by simp [s₀, Prim.step, base], fun q hq => by simp [s₀, Prim.step, Function.update_of_ne hq],
      ?_, ?_, ?_, ?_⟩
    · simp [s₀, Prim.step, Function.update_of_ne (show rOne ≠ rLe by omega),
        Function.update_of_ne (show rOne ≠ rLt by omega)]
    · simp [s₀, Prim.step, cntLt, Function.update_of_ne hLtLe]
    · simp [s₀, Prim.step, cntLe]
    · intro i hiLt hiLe hiS
      simp [s₀, Prim.step, Function.update_of_ne hiLe, Function.update_of_ne hiLt,
        Function.update_of_ne (show i ≠ rOne by omega)]
  have hLoop := SpecRun.forLoop (rMin := rMin) (pMin := pMin) (memBound := memBound)
    (q₁ := pScan) (q₂ := pEnd) (body := body) xs.length 8 Inv
    (fun t ht st hInv => by
      obtain ⟨hmem, hpscan, hptrs, hone, hlt_v, hle_v, hregs⟩ := hInv
      have hpiv_st : st.regs rPiv = piv := hregs rPiv hPivLt hPivLe hPivScr
      have hval_mem : st.mem (st.ptrs pScan) = xs[t] := by
        rw [hmem, hpscan]; exact hxs t ht
      have htake : xs.take (t + 1) = xs.take t ++ [xs[t]] := List.take_succ_eq_append_getElem ht
      refine ⟨by rw [hpscan, hptrs pEnd hScanE.symm, hEnd]; omega, ?_⟩
      have b1 : SpecRun rMin pMin memBound (.prim (.load rVal pScan)) st _ 1 := sprim
      have b2 : SpecRun rMin pMin memBound (.prim (.pinc pScan))
          ((Prim.load rVal pScan).step st) _ 1 := sprim
      have b3 : SpecRun rMin pMin memBound (.prim (.sub rDiff rPiv rVal))
          ((Prim.pinc pScan).step ((Prim.load rVal pScan).step st)) _ 1 := sprim
      set st₃ := (Prim.sub rDiff rPiv rVal).step
        ((Prim.pinc pScan).step ((Prim.load rVal pScan).step st))
      have hst3_val : st₃.regs rVal = xs[t] := by
        simp [st₃, Prim.step, Function.update_of_ne (show rVal ≠ rDiff by omega), hval_mem]
      have hst3_diff : st₃.regs rDiff = piv - xs[t] := by
        simp [st₃, Prim.step, Function.update_of_ne (show rPiv ≠ rVal by omega), hpiv_st, hval_mem]
      by_cases hlt_x : xs[t] < piv
      · have hnotle : ¬ st₃.regs rDiff ≤ 0 := by rw [hst3_diff]; linarith
        have b4 : SpecRun rMin pMin memBound (.prim (.add rLt rLt rOne)) st₃ _ 1 := sprim
        have b5 : SpecRun rMin pMin memBound (.prim (.add rLe rLe rOne))
            ((Prim.add rLt rLt rOne).step st₃) _ 1 := sprim
        set st₅ := (Prim.add rLe rLe rOne).step ((Prim.add rLt rLt rOne).step st₃)
        have br := SpecRun.ifLeZero_false
          (t := .seq (.prim (.sub rDiff rVal rPiv)) (.ifLeZero rDiff (.prim (.add rLe rLe rOne)) .skip))
          hnotle (b4.seq b5)
        refine ⟨st₅, ((b1.seq b2).seq (b3.seq br)).mono (by omega), hmem,
          by simp [st₅, st₃, Prim.step, hpscan]; omega,
          fun q hq => by simp [st₅, st₃, Prim.step, Function.update_of_ne hq, hptrs q hq],
          by simp [st₅, st₃, Prim.step, Function.update_of_ne (show rOne ≠ rLe by omega),
              Function.update_of_ne (show rOne ≠ rLt by omega),
              Function.update_of_ne (show rOne ≠ rDiff by omega),
              Function.update_of_ne (show rOne ≠ rVal by omega), hone],
          ?_, ?_, ?_⟩
        · have hxle : xs[t] ≤ piv := le_of_lt hlt_x
          simp only [cntLt, htake, List.countP_append, List.countP_singleton, hlt_x, decide_true,
            ite_true, Nat.cast_add, Nat.cast_one]
          simp [st₅, st₃, Prim.step, Function.update_of_ne hLtLe,
            Function.update_of_ne (show rLt ≠ rDiff by omega),
            Function.update_of_ne (show rLt ≠ rVal by omega),
            Function.update_of_ne (show rOne ≠ rDiff by omega),
            Function.update_of_ne (show rOne ≠ rVal by omega), hlt_v, cntLt, hone]
        · have hxle : xs[t] ≤ piv := le_of_lt hlt_x
          simp only [cntLe, htake, List.countP_append, List.countP_singleton, hxle, decide_true,
            ite_true, Nat.cast_add, Nat.cast_one]
          simp [st₅, st₃, Prim.step, Function.update_of_ne hLtLe.symm,
            Function.update_of_ne (show rLe ≠ rDiff by omega),
            Function.update_of_ne (show rLe ≠ rVal by omega),
            Function.update_of_ne (show rOne ≠ rLt by omega),
            Function.update_of_ne (show rOne ≠ rDiff by omega),
            Function.update_of_ne (show rOne ≠ rVal by omega), hle_v, cntLe, hone]
        · intro i hiLt hiLe hiS
          simp [st₅, st₃, Prim.step, Function.update_of_ne hiLe, Function.update_of_ne hiLt,
            Function.update_of_ne (show i ≠ rDiff by omega),
            Function.update_of_ne (show i ≠ rVal by omega), hregs i hiLt hiLe hiS]
      · have hge_x : piv ≤ xs[t] := le_of_not_gt hlt_x
        have hle_diff : st₃.regs rDiff ≤ 0 := by rw [hst3_diff]; linarith
        have b4 : SpecRun rMin pMin memBound (.prim (.sub rDiff rVal rPiv)) st₃ _ 1 :=
          SpecRun.prim (show rMin ≤ rDiff by omega) (by intro _ _ h; cases h)
        set st₄ := (Prim.sub rDiff rVal rPiv).step st₃
        have hst4_diff : st₄.regs rDiff = xs[t] - piv := by
          simp [st₄, st₃, Prim.step, Function.update_of_ne (show rPiv ≠ rDiff by omega),
            Function.update_of_ne (show rPiv ≠ rVal by omega),
            Function.update_of_ne (show rVal ≠ rDiff by omega), hpiv_st, hval_mem]
        by_cases hle_x : xs[t] ≤ piv
        · have hd4 : st₄.regs rDiff ≤ 0 := by rw [hst4_diff]; linarith
          have b5 : SpecRun rMin pMin memBound (.prim (.add rLe rLe rOne)) st₄ _ 1 :=
            SpecRun.prim hLe (by intro _ _ h; cases h)
          set st₅ := (Prim.add rLe rLe rOne).step st₄
          have br := SpecRun.ifLeZero_true
            (e := .seq (.prim (.add rLt rLt rOne)) (.prim (.add rLe rLe rOne)))
            hle_diff (b4.seq (SpecRun.ifLeZero_true (e := .skip) hd4 b5))
          refine ⟨st₅, ((b1.seq b2).seq (b3.seq br)).mono (by omega), hmem,
            by simp [st₅, st₄, st₃, Prim.step, hpscan]; omega,
            fun q hq => by simp [st₅, st₄, st₃, Prim.step, Function.update_of_ne hq, hptrs q hq],
            by simp [st₅, st₄, st₃, Prim.step, Function.update_of_ne (show rOne ≠ rLe by omega),
                Function.update_of_ne (show rOne ≠ rDiff by omega),
                Function.update_of_ne (show rOne ≠ rVal by omega), hone],
            ?_, ?_, ?_⟩
          · simp only [cntLt, htake, List.countP_append, List.countP_singleton, hlt_x, decide_false]
            simp [st₅, st₄, st₃, Prim.step, Function.update_of_ne hLtLe,
              Function.update_of_ne (show rLt ≠ rDiff by omega),
              Function.update_of_ne (show rLt ≠ rVal by omega), hlt_v, cntLt]
          · simp only [cntLe, htake, List.countP_append, List.countP_singleton, hle_x, decide_true,
              ite_true, Nat.cast_add, Nat.cast_one]
            simp [st₅, st₄, st₃, Prim.step, Function.update_of_ne (show rLe ≠ rDiff by omega),
              Function.update_of_ne (show rLe ≠ rVal by omega),
              Function.update_of_ne (show rOne ≠ rDiff by omega),
              Function.update_of_ne (show rOne ≠ rVal by omega), hle_v, cntLe, hone]
          · intro i hiLt hiLe hiS
            simp [st₅, st₄, st₃, Prim.step, Function.update_of_ne hiLe,
              Function.update_of_ne (show i ≠ rDiff by omega),
              Function.update_of_ne (show i ≠ rVal by omega), hregs i hiLt hiLe hiS]
        · have hd4 : ¬ st₄.regs rDiff ≤ 0 := by rw [hst4_diff]; linarith
          have br := SpecRun.ifLeZero_true
            (e := .seq (.prim (.add rLt rLt rOne)) (.prim (.add rLe rLe rOne)))
            hle_diff (b4.seq (SpecRun.ifLeZero_false (t := .prim (.add rLe rLe rOne))
              hd4 (SpecRun.skip rMin pMin memBound st₄)))
          refine ⟨st₄, ((b1.seq b2).seq (b3.seq br)).mono (by omega), hmem,
            by simp [st₄, st₃, Prim.step, hpscan]; omega,
            fun q hq => by simp [st₄, st₃, Prim.step, Function.update_of_ne hq, hptrs q hq],
            by simp [st₄, st₃, Prim.step, Function.update_of_ne (show rOne ≠ rDiff by omega),
                Function.update_of_ne (show rOne ≠ rVal by omega), hone],
            ?_, ?_, ?_⟩
          · simp only [cntLt, htake, List.countP_append, List.countP_singleton, hlt_x, decide_false]
            simp [st₄, st₃, Prim.step, Function.update_of_ne (show rLt ≠ rDiff by omega),
              Function.update_of_ne (show rLt ≠ rVal by omega), hlt_v, cntLt]
          · simp only [cntLe, htake, List.countP_append, List.countP_singleton, hle_x, decide_false]
            simp [st₄, st₃, Prim.step, Function.update_of_ne (show rLe ≠ rDiff by omega),
              Function.update_of_ne (show rLe ≠ rVal by omega), hle_v, cntLe]
          · intro i hiLt hiLe hiS
            simp [st₄, st₃, Prim.step, Function.update_of_ne (show i ≠ rDiff by omega),
              Function.update_of_ne (show i ≠ rVal by omega), hregs i hiLt hiLe hiS])
    (fun st hInv => by
      obtain ⟨_, hpscan, hptrs, _⟩ := hInv
      rw [hpscan, hptrs pEnd hScanE.symm, hEnd])
    xs.length le_rfl s₀ (by simpa using hInv0)
  obtain ⟨s₁, hrun1, hmem1, _, hptrs1, _, hlt1, hle1, hregs1⟩ := hLoop
  rw [List.take_length] at hlt1 hle1
  exact ⟨s₁, (hs₀.seq hrun1).mono (by omega), hlt1, hle1, hregs1, hptrs1, hmem1⟩

/-- Base-case `O(N^2)` non-destructive exact `k`-th order selection (`k < xs.length`).
Scratch regs `rScr .. rScr + 6` (`rCand, rLt, rLe, rChk, rOne, rVal, rDiff`),
scratch ptrs `pOuter, pScan`. -/
noncomputable def baseSelectStmt (rOut pStart pEnd rK rScr pOuter pScan : ℕ) : Stmt :=
  let rCand := rScr
  let rLt := rScr + 1
  let rLe := rScr + 2
  let rChk := rScr + 3
  let rSubScr := rScr + 4 -- uses rScr + 4, + 5, + 6
  .seq (.prim (.pcopy pOuter pStart))
    (.whilePtrLt pOuter pEnd
      (.seq (.seq (.prim (.load rCand pOuter)) (.prim (.pinc pOuter)))
        (.seq (countLtLeStmt pStart pEnd pScan rCand rLt rLe rSubScr)
          (.seq (.prim (.sub rChk rLt rK))
            (.ifLeZero rChk
              (.seq (.prim (.sub rChk rLe rK))
                (.ifLeZero rChk .skip (copyReg rOut rCand rSubScr)))
              .skip)))))

theorem baseSelectStmt_spec {rMin pMin : ℕ} {memBound : ℤ}
    {rOut pStart pEnd rK rScr pOuter pScan : ℕ} {xs : List ℝ} {k : ℕ} {s : MState}
    (hxs : ListAt s.mem (s.ptrs pStart) xs)
    (hEnd : s.ptrs pEnd = s.ptrs pStart + (xs.length : ℤ))
    (hk : k < xs.length) (hrK : s.regs rK = (k : ℝ))
    (hOut : rMin ≤ rOut) (hScr : rMin ≤ rScr) (hpOut : pMin ≤ pOuter) (hpScan : pMin ≤ pScan)
    (hOS : pOuter ≠ pStart) (hOE : pOuter ≠ pEnd) (hSS : pScan ≠ pStart) (hSE : pScan ≠ pEnd)
    (hOP : pOuter ≠ pScan)
    (hOutK : rOut ≠ rK)
    (hOutScr : rOut < rScr ∨ rScr + 7 ≤ rOut)
    (hKScr : rK < rScr ∨ rScr + 7 ≤ rK) :
    ∃ s', SpecRun rMin pMin memBound
        (baseSelectStmt rOut pStart pEnd rK rScr pOuter pScan) s s'
        (xs.length * (10 * xs.length + 25) + 5) ∧
      IsKthOrder xs k (s'.regs rOut) ∧
      (∀ i, i ≠ rOut → (i < rScr ∨ rScr + 7 ≤ i) → s'.regs i = s.regs i) ∧
      (∀ q, q ≠ pOuter → q ≠ pScan → s'.ptrs q = s.ptrs q) ∧
      s'.mem = s.mem := by
  obtain ⟨i₀, hi₀⟩ := exists_index_isKthOrder xs k hk
  let rCand := rScr
  let rLt := rScr + 1
  let rLe := rScr + 2
  let rChk := rScr + 3
  let rSubScr := rScr + 4
  set base := s.ptrs pStart
  have p0 : SpecRun rMin pMin memBound (.prim (.pcopy pOuter pStart)) s _ 1 :=
    SpecRun.prim hpOut (by intro _ _ h; cases h)
  set s₀ := (Prim.pcopy pOuter pStart).step s
  let body : Stmt :=
    .seq (.seq (.prim (.load rCand pOuter)) (.prim (.pinc pOuter)))
      (.seq (countLtLeStmt pStart pEnd pScan rCand rLt rLe rSubScr)
        (.seq (.prim (.sub rChk rLt rK))
          (.ifLeZero rChk
            (.seq (.prim (.sub rChk rLe rK))
              (.ifLeZero rChk .skip (copyReg rOut rCand rSubScr)))
            .skip)))
  let Inv : ℕ → MState → Prop := fun t st =>
    st.mem = s.mem ∧
    st.ptrs pOuter = base + (t : ℤ) ∧
    (∀ q, q ≠ pOuter → q ≠ pScan → st.ptrs q = s.ptrs q) ∧
    (i₀.1 < t → IsKthOrder xs k (st.regs rOut)) ∧
    (∀ i, i ≠ rOut → (i < rScr ∨ rScr + 7 ≤ i) → st.regs i = s.regs i)
  have hInv0 : Inv 0 s₀ := by
    refine ⟨rfl, by simp [s₀, Prim.step, base],
      fun q hq1 _ => by simp [s₀, Prim.step, Function.update_of_ne hq1],
      fun h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  have hLoop := SpecRun.forLoop (rMin := rMin) (pMin := pMin) (memBound := memBound)
    (q₁ := pOuter) (q₂ := pEnd) (body := body) xs.length (10 * xs.length + 22) Inv
    (fun t ht st hInv => by
      obtain ⟨hmem, hpout, hptrs, hkth, hregs⟩ := hInv
      refine ⟨by rw [hpout, hptrs pEnd hOE.symm hSE.symm, hEnd]; omega, ?_⟩
      have b1 : SpecRun rMin pMin memBound (.prim (.load rCand pOuter)) st _ 1 := sprim
      have b2 : SpecRun rMin pMin memBound (.prim (.pinc pOuter))
          ((Prim.load rCand pOuter).step st) _ 1 := sprim
      set st₁ := (Prim.pinc pOuter).step ((Prim.load rCand pOuter).step st)
      have hcand1 : st₁.regs rCand = xs[t] := by
        simp [st₁, Prim.step, hmem, hpout, hxs t ht]
      have hxs1 : ListAt st₁.mem (st₁.ptrs pStart) xs := by
        simp only [st₁, Prim.step, hmem, Function.update_of_ne hOS.symm, hptrs pStart hOS.symm hSS.symm]
        exact hxs
      have hEnd1 : st₁.ptrs pEnd = st₁.ptrs pStart + (xs.length : ℤ) := by
        simp only [st₁, Prim.step, Function.update_of_ne hOE.symm, Function.update_of_ne hOS.symm,
          hptrs pEnd hOE.symm hSE.symm, hptrs pStart hOS.symm hSS.symm]
        exact hEnd
      obtain ⟨st₂, b3, hlt2, hle2, hregs2, hptrs2, hmem2⟩ :=
        countLtLeStmt_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
          (pStart := pStart) (pEnd := pEnd) (pScan := pScan)
          (rPiv := rCand) (rLt := rLt) (rLe := rLe) (rScr := rSubScr) (s := st₁)
          hxs1 hEnd1 (by omega) (by omega) (by omega) hpScan hSS hSE
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hcand1] at hlt2 hle2
      have hrK2 : st₂.regs rK = (k : ℝ) := by
        rw [hregs2 rK (by omega) (by omega) (by omega)]
        simp [st₁, Prim.step, Function.update_of_ne (show rK ≠ rCand by omega),
          hregs rK hOutK.symm hKScr, hrK]
      have b4 : SpecRun rMin pMin memBound (.prim (.sub rChk rLt rK)) st₂ _ 1 :=
        SpecRun.prim (show rMin ≤ rChk by omega) (by intro _ _ h; cases h)
      set st₃ := (Prim.sub rChk rLt rK).step st₂
      by_cases hcond1 : cntLt xs xs[t] ≤ k
      · have hchk1 : st₃.regs rChk ≤ 0 := by
          simp only [st₃, Prim.step, Function.update_self, hlt2, hrK2]
          have hcast : (cntLt xs xs[t] : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcond1
          linarith
        have b5 : SpecRun rMin pMin memBound (.prim (.sub rChk rLe rK)) st₃ _ 1 :=
          SpecRun.prim (show rMin ≤ rChk by omega) (by intro _ _ h; cases h)
        set st₄ := (Prim.sub rChk rLe rK).step st₃
        by_cases hcond2 : k < cntLe xs xs[t]
        · have hchk2 : ¬ st₄.regs rChk ≤ 0 := by
            simp only [st₄, st₃, Prim.step, Function.update_self,
              Function.update_of_ne (show rLe ≠ rChk by omega),
              Function.update_of_ne (show rK ≠ rChk by omega), hle2, hrK2]
            have hcast : (k : ℝ) + 1 ≤ (cntLe xs xs[t] : ℝ) := by exact_mod_cast hcond2
            linarith
          obtain ⟨st₅, b6, hout5, _, hoth5, hp5, hm5⟩ :=
            copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
              (rDst := rOut) (rSrc := rCand) (rZero := rSubScr) (s := st₄)
              hOut (by omega) (by omega) (by omega)
          have br := SpecRun.ifLeZero_true (e := .skip) hchk1
            (b5.seq (SpecRun.ifLeZero_false (t := .skip) hchk2 b6))
          refine ⟨st₅, ((b1.seq b2).seq (b3.seq (b4.seq br))).mono (by omega),
            by simp [hm5, st₄, st₃, Prim.step, hmem2, st₁, hmem],
            by rw [hp5]; simp [st₄, st₃, Prim.step, hptrs2 pOuter hOP, st₁, hpout]; omega,
            fun q hq1 hq2 => by
              rw [hp5]; simp [st₄, st₃, Prim.step, hptrs2 q hq2, st₁, Function.update_of_ne hq1, hptrs q hq1 hq2],
            fun _ => ?_, ?_⟩
          · rw [hout5]
            have hcand4 : st₄.regs rCand = xs[t] := by
              simp [st₄, st₃, Prim.step, Function.update_of_ne (show rCand ≠ rChk by omega),
                hregs2 rCand (by omega) (by omega) (by omega), hcand1]
            rw [hcand4]
            exact ⟨List.getElem_mem _, hcond1, hcond2⟩
          · intro i hiOut hiS
            rw [hoth5 i hiOut (by omega)]
            simp [st₄, st₃, Prim.step, Function.update_of_ne (show i ≠ rChk by omega),
              hregs2 i (by omega) (by omega) (by omega), st₁,
              Function.update_of_ne (show i ≠ rCand by omega), hregs i hiOut hiS]
        · have hchk2 : st₄.regs rChk ≤ 0 := by
            simp only [st₄, st₃, Prim.step, Function.update_self,
              Function.update_of_ne (show rLe ≠ rChk by omega),
              Function.update_of_ne (show rK ≠ rChk by omega), hle2, hrK2]
            have hcast : (cntLe xs xs[t] : ℝ) ≤ (k : ℝ) := by exact_mod_cast not_lt.mp hcond2
            linarith
          have br := SpecRun.ifLeZero_true (e := .skip) hchk1
            (b5.seq (SpecRun.ifLeZero_true (e := copyReg rOut rCand rSubScr) hchk2
              (SpecRun.skip rMin pMin memBound st₄)))
          have hti0 : t ≠ i₀.1 := fun heq => by subst heq; exact hcond2 hi₀.2.2
          refine ⟨st₄, ((b1.seq b2).seq (b3.seq (b4.seq br))).mono (by omega),
            by simp [st₄, st₃, Prim.step, hmem2, st₁, hmem],
            by simp [st₄, st₃, Prim.step, hptrs2 pOuter hOP, st₁, hpout]; omega,
            fun q hq1 hq2 => by
              simp [st₄, st₃, Prim.step, hptrs2 q hq2, st₁, Function.update_of_ne hq1, hptrs q hq1 hq2],
            fun hlt_t => ?_, ?_⟩
          · have hout4 : st₄.regs rOut = st.regs rOut := by
              simp [st₄, st₃, Prim.step, Function.update_of_ne (show rOut ≠ rChk by omega),
                hregs2 rOut (by omega) (by omega) (by omega), st₁,
                Function.update_of_ne (show rOut ≠ rCand by omega)]
            rw [hout4]; exact hkth (by omega)
          · intro i hiOut hiS
            simp [st₄, st₃, Prim.step, Function.update_of_ne (show i ≠ rChk by omega),
              hregs2 i (by omega) (by omega) (by omega), st₁,
              Function.update_of_ne (show i ≠ rCand by omega), hregs i hiOut hiS]
      · have hchk1 : ¬ st₃.regs rChk ≤ 0 := by
          simp only [st₃, Prim.step, Function.update_self, hlt2, hrK2]
          have hcast : (k : ℝ) < (cntLt xs xs[t] : ℝ) := by exact_mod_cast not_le.mp hcond1
          linarith
        have br := SpecRun.ifLeZero_false
          (t := .seq (.prim (.sub rChk rLe rK)) (.ifLeZero rChk .skip (copyReg rOut rCand rSubScr)))
          hchk1 (SpecRun.skip rMin pMin memBound st₃)
        have hti0 : t ≠ i₀.1 := fun heq => by subst heq; exact hcond1 hi₀.2.1
        refine ⟨st₃, ((b1.seq b2).seq (b3.seq (b4.seq br))).mono (by omega),
          by simp [st₃, Prim.step, hmem2, st₁, hmem],
          by simp [st₃, Prim.step, hptrs2 pOuter hOP, st₁, hpout]; omega,
          fun q hq1 hq2 => by
            simp [st₃, Prim.step, hptrs2 q hq2, st₁, Function.update_of_ne hq1, hptrs q hq1 hq2],
          fun hlt_t => ?_, ?_⟩
        · have hout3 : st₃.regs rOut = st.regs rOut := by
            simp [st₃, Prim.step, Function.update_of_ne (show rOut ≠ rChk by omega),
              hregs2 rOut (by omega) (by omega) (by omega), st₁,
              Function.update_of_ne (show rOut ≠ rCand by omega)]
          rw [hout3]; exact hkth (by omega)
        · intro i hiOut hiS
          simp [st₃, Prim.step, Function.update_of_ne (show i ≠ rChk by omega),
            hregs2 i (by omega) (by omega) (by omega), st₁,
            Function.update_of_ne (show i ≠ rCand by omega), hregs i hiOut hiS])
    (fun st hInv => by
      obtain ⟨_, hpout, hptrs, _⟩ := hInv
      rw [hpout, hptrs pEnd hOE.symm hSE.symm, hEnd])
    xs.length le_rfl s₀ (by simpa using hInv0)
  obtain ⟨s₁, hrun1, hmem1, _, hptrs1, hkth1, hregs1⟩ := hLoop
  refine ⟨s₁, (p0.seq hrun1).mono (by ring_nf; omega), hkth1 i₀.2, hregs1, hptrs1, hmem1⟩

/-- In-place filter `{x ∈ xs | x < piv}` (`isLt = true`) or `{x ∈ xs | piv < x}` (`isLt = false`)
into `[pStart .. pWrite)`. Needs 2 scratch regs `rScr, rScr + 1` (`rVal, rDiff`). -/
noncomputable def filterCmpStmt (isLt : Bool) (pStart pEnd pRead pWrite rPiv rScr : ℕ) : Stmt :=
  let rVal := rScr
  let rDiff := rScr + 1
  let subStmt := if isLt then Prim.sub rDiff rPiv rVal else Prim.sub rDiff rVal rPiv
  .seq (.seq (.prim (.pcopy pRead pStart)) (.prim (.pcopy pWrite pStart)))
    (.whilePtrLt pRead pEnd
      (.seq (.seq (.prim (.load rVal pRead)) (.prim (.pinc pRead)))
        (.seq (.prim subStmt)
          (.ifLeZero rDiff .skip
            (.seq (.prim (.store pWrite rVal)) (.prim (.pinc pWrite)))))))

theorem filterCmpStmt_spec {rMin pMin : ℕ} {memBound : ℤ}
    (isLt : Bool) {pStart pEnd pRead pWrite rPiv rScr : ℕ} {xs : List ℝ} {s : MState}
    (hxs : ListAt s.mem (s.ptrs pStart) xs)
    (hEnd : s.ptrs pEnd = s.ptrs pStart + (xs.length : ℤ))
    (hmB : memBound ≤ s.ptrs pStart)
    (hScr : rMin ≤ rScr) (hpR : pMin ≤ pRead) (hpW : pMin ≤ pWrite)
    (hRW : pRead ≠ pWrite) (_hRS : pRead ≠ pStart) (hRE : pRead ≠ pEnd)
    (_hWS : pWrite ≠ pStart) (hWE : pWrite ≠ pEnd)
    (hPivScr : rPiv < rScr ∨ rScr + 2 ≤ rPiv) :
    let P : ℝ → Bool := fun x => if isLt then decide (x < s.regs rPiv) else decide (s.regs rPiv < x)
    ∃ s', SpecRun rMin pMin memBound
        (filterCmpStmt isLt pStart pEnd pRead pWrite rPiv rScr) s s' (9 * xs.length + 5) ∧
      ListAt s'.mem (s.ptrs pStart) (xs.filter P) ∧
      s'.ptrs pWrite = s.ptrs pStart + ((xs.filter P).length : ℤ) ∧
      (∀ i, (i < rScr ∨ rScr + 2 ≤ i) → s'.regs i = s.regs i) ∧
      (∀ q, q ≠ pRead → q ≠ pWrite → s'.ptrs q = s.ptrs q) := by
  intro P
  let rVal := rScr
  let rDiff := rScr + 1
  let subStmt := if isLt then Prim.sub rDiff rPiv rVal else Prim.sub rDiff rVal rPiv
  set piv := s.regs rPiv
  set base := s.ptrs pStart
  have p1 : SpecRun rMin pMin memBound (.prim (.pcopy pRead pStart)) s _ 1 := sprim
  have p2 : SpecRun rMin pMin memBound (.prim (.pcopy pWrite pStart))
      ((Prim.pcopy pRead pStart).step s) _ 1 := sprim
  set s₀ := (Prim.pcopy pWrite pStart).step ((Prim.pcopy pRead pStart).step s)
  let body : Stmt :=
    .seq (.seq (.prim (.load rVal pRead)) (.prim (.pinc pRead)))
      (.seq (.prim subStmt)
        (.ifLeZero rDiff .skip
          (.seq (.prim (.store pWrite rVal)) (.prim (.pinc pWrite)))))
  let Inv : ℕ → MState → Prop := fun t st =>
    ListAt st.mem base ((xs.take t).filter P) ∧
    (∀ j, t ≤ j → (hj : j < xs.length) → st.mem (base + (j : ℤ)) = xs[j]) ∧
    st.ptrs pRead = base + (t : ℤ) ∧
    st.ptrs pWrite = base + (((xs.take t).filter P).length : ℤ) ∧
    (∀ q, q ≠ pRead → q ≠ pWrite → st.ptrs q = s.ptrs q) ∧
    (∀ i, (i < rScr ∨ rScr + 2 ≤ i) → st.regs i = s.regs i)
  have hInv0 : Inv 0 s₀ := by
    refine ⟨fun i hi => by simp at hi, fun j _ hj => hxs j hj,
      by simp [s₀, Prim.step, base, Function.update_of_ne hRW],
      by simp [s₀, Prim.step, base, Function.update_of_ne _hRS.symm],
      fun q hqR hqW => by simp [s₀, Prim.step, Function.update_of_ne hqW, Function.update_of_ne hqR],
      fun _ _ => rfl⟩
  have hLoop := SpecRun.forLoop (rMin := rMin) (pMin := pMin) (memBound := memBound)
    (q₁ := pRead) (q₂ := pEnd) (body := body) xs.length 7 Inv
    (fun t ht st hInv => by
      obtain ⟨hpref, hsuf, hpr, hpw, hptrs, hregs⟩ := hInv
      have hw_le_t : ((xs.take t).filter P).length ≤ t :=
        le_trans (List.length_filter_le _ _) (by simp [Nat.min_eq_left (le_of_lt ht)])
      have htake : xs.take (t + 1) = xs.take t ++ [xs[t]] := List.take_succ_eq_append_getElem ht
      refine ⟨by rw [hpr, hptrs pEnd hRE.symm hWE.symm, hEnd]; omega, ?_⟩
      have b1 : SpecRun rMin pMin memBound (.prim (.load rVal pRead)) st _ 1 := sprim
      have b2 : SpecRun rMin pMin memBound (.prim (.pinc pRead))
          ((Prim.load rVal pRead).step st) _ 1 := sprim
      have hSubW : subStmt.WritesAbove rMin pMin := by
        dsimp [subStmt]; split_ifs <;> show rMin ≤ rDiff <;> omega
      have b3 : SpecRun rMin pMin memBound (.prim subStmt)
          ((Prim.pinc pRead).step ((Prim.load rVal pRead).step st)) _ 1 :=
        SpecRun.prim hSubW (by intro _ _ h; cases isLt <;> simp [subStmt] at h)
      set st₃ := subStmt.step ((Prim.pinc pRead).step ((Prim.load rVal pRead).step st))
      have hval_st : st.mem (st.ptrs pRead) = xs[t] := by
        rw [hpr]; exact hsuf t le_rfl ht
      have hpiv_st : st.regs rPiv = piv := hregs rPiv hPivScr
      have hst3_val : st₃.regs rVal = xs[t] := by
        cases isLt <;> simp [st₃, subStmt, Prim.step,
          Function.update_of_ne (show rVal ≠ rDiff by omega), hval_st]
      have hst3_diff_neg_iff : (¬ st₃.regs rDiff ≤ 0) ↔ P xs[t] = true := by
        cases isLt
        · simp [st₃, subStmt, Prim.step, Function.update_of_ne (show rPiv ≠ rVal by omega),
            hpiv_st, hval_st, P]
          constructor <;> intro h <;> linarith
        · simp [st₃, subStmt, Prim.step, Function.update_of_ne (show rPiv ≠ rVal by omega),
            hpiv_st, hval_st, P]
          constructor <;> intro h <;> linarith
      by_cases hPx : P xs[t] = true
      · have hnotle : ¬ st₃.regs rDiff ≤ 0 := hst3_diff_neg_iff.mpr hPx
        have hst3_pw : st₃.ptrs pWrite = base + (((xs.take t).filter P).length : ℤ) := by
          cases isLt <;> simp [st₃, subStmt, Prim.step, Function.update_of_ne hRW.symm, hpw]
        have b4 : SpecRun rMin pMin memBound (.prim (.store pWrite rVal)) st₃ _ 1 :=
          SpecRun.prim trivial (by intro _ _ h; cases h; rw [hst3_pw]; omega)
        have b5 : SpecRun rMin pMin memBound (.prim (.pinc pWrite))
            ((Prim.store pWrite rVal).step st₃) _ 1 := sprim
        set st₅ := (Prim.pinc pWrite).step ((Prim.store pWrite rVal).step st₃)
        have br := SpecRun.ifLeZero_false (t := .skip) hnotle (b4.seq b5)
        refine ⟨st₅, ((b1.seq b2).seq (b3.seq br)).mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [htake, List.filter_append, List.filter_cons_of_pos hPx, List.filter_nil]
          intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlt_i : i < ((xs.take t).filter P).length
          · rw [List.getElem_append_left hlt_i]
            simp only [st₅, Prim.step, hst3_pw]
            rw [Function.update_of_ne (by omega)]
            have hm3 : st₃.mem = st.mem := by cases isLt <;> rfl
            rw [hm3]; exact hpref i hlt_i
          · have heq_i : i = ((xs.take t).filter P).length := by omega
            subst heq_i
            simp [st₅, Prim.step, hst3_pw, hst3_val]
        · intro j hj1 hj2
          simp only [st₅, Prim.step, hst3_pw]
          rw [Function.update_of_ne (by omega)]
          have hm3 : st₃.mem = st.mem := by cases isLt <;> rfl
          rw [hm3]; exact hsuf j (by omega) hj2
        · cases isLt <;> simp [st₅, st₃, subStmt, Prim.step, Function.update_of_ne hRW, hpr] <;> omega
        · rw [htake, List.filter_append, List.filter_cons_of_pos hPx, List.filter_nil]
          simp [st₅, Prim.step, hst3_pw]; omega
        · intro q hqR hqW
          cases isLt <;> simp [st₅, st₃, subStmt, Prim.step,
            Function.update_of_ne hqW, Function.update_of_ne hqR, hptrs q hqR hqW]
        · intro i hiS
          cases isLt <;> simp [st₅, st₃, subStmt, Prim.step,
            Function.update_of_ne (show i ≠ rDiff by omega),
            Function.update_of_ne (show i ≠ rVal by omega), hregs i hiS]
      · have hPxF : P xs[t] = false := Bool.eq_false_iff.mpr hPx
        have hle_d : st₃.regs rDiff ≤ 0 := not_not.mp (mt hst3_diff_neg_iff.mp hPx)
        have br := SpecRun.ifLeZero_true
          (e := .seq (.prim (.store pWrite rVal)) (.prim (.pinc pWrite)))
          hle_d (SpecRun.skip rMin pMin memBound st₃)
        have hm3 : st₃.mem = st.mem := by cases isLt <;> rfl
        refine ⟨st₃, ((b1.seq b2).seq (b3.seq br)).mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [htake, List.filter_append, List.filter_cons_of_neg (by simp [hPxF]), List.filter_nil,
            List.append_nil, hm3]
          exact hpref
        · intro j hj1 hj2; rw [hm3]; exact hsuf j (by omega) hj2
        · cases isLt <;> simp [st₃, subStmt, Prim.step, hpr] <;> omega
        · rw [htake, List.filter_append, List.filter_cons_of_neg (by simp [hPxF]), List.filter_nil,
            List.append_nil]
          cases isLt <;> simp [st₃, subStmt, Prim.step, Function.update_of_ne hRW.symm, hpw]
        · intro q hqR hqW
          cases isLt <;> simp [st₃, subStmt, Prim.step, Function.update_of_ne hqR, hptrs q hqR hqW]
        · intro i hiS
          cases isLt <;> simp [st₃, subStmt, Prim.step,
            Function.update_of_ne (show i ≠ rDiff by omega),
            Function.update_of_ne (show i ≠ rVal by omega), hregs i hiS])
    (fun st hInv => by
      obtain ⟨_, _, hpr, _, hptrs, _⟩ := hInv
      rw [hpr, hptrs pEnd hRE.symm hWE.symm, hEnd])
    xs.length le_rfl s₀ (by simpa using hInv0)
  obtain ⟨s₁, hrun1, hpref1, _, _, hpw1, hptrs1, hregs1⟩ := hLoop
  rw [List.take_length] at hpref1 hpw1
  exact ⟨s₁, ((p1.seq p2).seq hrun1).mono (by omega), hpref1, hpw1, hregs1, hptrs1⟩

/-! ## Iterative BFPRT Loop (`selectMedianStmt`) Verified via `LoopStep` -/

/-- Step-1 helper for `N > 100`: count `N`, push header `(1, N, k)` at `[pCurEnd .. pCurEnd + 3)`,
write `g = N / 5` medians to `[pCurEnd + 3 .. pCurEnd + 3 + g)`, set `pCurStart := pCurEnd + 3`,
`pCurEnd := pCurEnd + 3 + g`, `rK := g / 2`.
Uses `rScr .. rScr + 11` (`12` scratch regs) and `pScan1, pScan2, pLimit`. -/
noncomputable def pushMediansStmt (pCurStart pCurEnd rK rScr pScan1 pScan2 pLimit : ℕ) : Stmt :=
  let rOne := rScr
  let rCntN := rScr + 1
  let rPar := rScr + 2
  let rHalf := rScr + 3
  let r5 := rScr + 4 -- uses rScr + 4 .. rScr + 11 (8 regs for med5Stmt)
  let countNStmt : Stmt :=
    .seq (Stmt.block [.prim (.const rOne 1), .prim (.const rCntN 0), .prim (.pcopy pScan1 pCurStart)])
      (.whilePtrLt pScan1 pCurEnd
        (.seq (.prim (.pinc pScan1)) (.prim (.add rCntN rCntN rOne))))
  let storeHdrStmt : Stmt :=
    Stmt.block [
      .prim (.pcopy pScan2 pCurEnd),
      .prim (.store pScan2 rOne), .prim (.pinc pScan2),
      .prim (.store pScan2 rCntN), .prim (.pinc pScan2),
      .prim (.store pScan2 rK), .prim (.pinc pScan2)]
  let medLoopStmt : Stmt :=
    .seq (Stmt.block [
        .prim (.pcopy pScan1 pCurStart),
        .prim (.pcopy pLimit pCurEnd),
        retreatPtrByConst 4 pLimit,
        .prim (.const rPar 0),
        .prim (.const rHalf 0)])
      (.whilePtrLt pScan1 pLimit
        (.seq (loadVec 5 r5 pScan1)
          (.seq (med5Stmt r5)
            (.seq (.seq (.prim (.store pScan2 (r5 + 2))) (.prim (.pinc pScan2)))
              (.ifLeZero rPar
                (.prim (.const rPar 1))
                (.seq (.prim (.const rPar 0)) (.prim (.add rHalf rHalf rOne))))))))
  let finalizeStmt : Stmt :=
    Stmt.block [
      .prim (.pcopy pCurStart pCurEnd),
      advancePtrByConst 3 pCurStart,
      .prim (.pcopy pCurEnd pScan2),
      copyReg rK rHalf (r5 + 7)]
  Stmt.block [countNStmt, storeHdrStmt, medLoopStmt, finalizeStmt]

set_option maxHeartbeats 800000 in
theorem pushMediansStmt_spec {rMin pMin : ℕ} {memBound : ℤ}
    {pCurStart pCurEnd rK rScr pScan1 pScan2 pLimit : ℕ}
    {xs : List ℝ} {k : ℕ} {s : MState}
    (hxs : ListAt s.mem (s.ptrs pCurStart) xs)
    (hEnd : s.ptrs pCurEnd = s.ptrs pCurStart + (xs.length : ℤ))
    (hN5 : 5 ≤ xs.length)
    (hrK : s.regs rK = (k : ℝ))
    (hmB : memBound ≤ s.ptrs pCurStart)
    (hK : rMin ≤ rK) (hScr : rMin ≤ rScr)
    (hpCS : pMin ≤ pCurStart) (hpCE : pMin ≤ pCurEnd)
    (hp1 : pMin ≤ pScan1) (hp2 : pMin ≤ pScan2) (hpL : pMin ≤ pLimit)
    (hDistinctP : [pCurStart, pCurEnd, pScan1, pScan2, pLimit].Nodup)
    (hKScr : rK < rScr ∨ rScr + 12 ≤ rK) :
    let base := s.ptrs pCurStart
    let childBase := base + (xs.length : ℤ) + 3
    ∃ s', SpecRun rMin pMin memBound
        (pushMediansStmt pCurStart pCurEnd rK rScr pScan1 pScan2 pLimit) s s'
        (25 * xs.length + 50) ∧
      ListAt s'.mem base xs ∧
      s'.mem (base + (xs.length : ℤ)) = 1 ∧
      s'.mem (base + (xs.length : ℤ) + 1) = (xs.length : ℝ) ∧
      s'.mem (base + (xs.length : ℤ) + 2) = (k : ℝ) ∧
      ListAt s'.mem childBase (medsOf5 xs) ∧
      s'.ptrs pCurStart = childBase ∧
      s'.ptrs pCurEnd = childBase + ((xs.length / 5 : ℕ) : ℤ) ∧
      s'.regs rK = (((xs.length / 5) / 2 : ℕ) : ℝ) ∧
      (∀ i, i ≠ rK → (i < rScr ∨ rScr + 12 ≤ i) → s'.regs i = s.regs i) ∧
      (∀ q, q ∉ [pCurStart, pCurEnd, pScan1, pScan2, pLimit] → s'.ptrs q = s.ptrs q) := by
  intro base childBase
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true, ← ne_eq] at hDistinctP
  obtain ⟨⟨hCS_CE, hCS_1, hCS_2, hCS_L⟩, ⟨hCE_1, hCE_2, hCE_L⟩, ⟨h1_2, h1_L⟩, h2_L⟩ := hDistinctP
  let rOne := rScr
  let rCntN := rScr + 1
  let rPar := rScr + 2
  let rHalf := rScr + 3
  let r5 := rScr + 4
  -- Phase 1: countNStmt
  have c1 : SpecRun rMin pMin memBound (.prim (.const rOne 1)) s _ 1 := sprim
  have c2 : SpecRun rMin pMin memBound (.prim (.const rCntN 0))
      ((Prim.const rOne 1).step s) _ 1 := sprim
  have c3 : SpecRun rMin pMin memBound (.prim (.pcopy pScan1 pCurStart))
      ((Prim.const rCntN 0).step ((Prim.const rOne 1).step s)) _ 1 := sprim
  set sc₀ := (Prim.pcopy pScan1 pCurStart).step
    ((Prim.const rCntN 0).step ((Prim.const rOne 1).step s))
  let InvC : ℕ → MState → Prop := fun t st =>
    st.mem = s.mem ∧
    st.ptrs pScan1 = base + (t : ℤ) ∧
    (∀ q, q ≠ pScan1 → st.ptrs q = s.ptrs q) ∧
    st.regs rOne = 1 ∧
    st.regs rCntN = (t : ℝ) ∧
    (∀ i, i ≠ rOne → i ≠ rCntN → st.regs i = s.regs i)
  have hLoopC := SpecRun.forLoop (rMin := rMin) (pMin := pMin) (memBound := memBound)
    (q₁ := pScan1) (q₂ := pCurEnd)
    (body := .seq (.prim (.pinc pScan1)) (.prim (.add rCntN rCntN rOne)))
    xs.length 2 InvC
    (fun t ht st hInv => by
      obtain ⟨hm, hp, hpo, ho, hc, hr⟩ := hInv
      refine ⟨by rw [hp, hpo pCurEnd hCE_1, hEnd]; omega, ?_⟩
      have b1 : SpecRun rMin pMin memBound (.prim (.pinc pScan1)) st _ 1 := sprim
      have b2 : SpecRun rMin pMin memBound (.prim (.add rCntN rCntN rOne))
          ((Prim.pinc pScan1).step st) _ 1 := sprim
      refine ⟨_, b1.seq b2, hm, by simp [Prim.step, hp]; omega,
        fun q hq => by simp [Prim.step, Function.update_of_ne hq, hpo q hq],
        by simp [Prim.step, Function.update_of_ne (show rOne ≠ rCntN by omega), ho],
        by simp [Prim.step, hc, ho, Nat.cast_add],
        fun i hi1 hi2 => by simp [Prim.step, Function.update_of_ne hi2, hr i hi1 hi2]⟩)
    (fun st hInv => by
      obtain ⟨_, hp, hpo, _⟩ := hInv
      rw [hp, hpo pCurEnd hCE_1, hEnd])
    xs.length le_rfl sc₀
    ⟨rfl, by simp [sc₀, Prim.step, base],
     fun q hq => by simp [sc₀, Prim.step, Function.update_of_ne hq],
     by simp [sc₀, Prim.step, Function.update_of_ne (show rOne ≠ rCntN by omega)],
     by simp [sc₀, Prim.step],
     fun i hi1 hi2 => by simp [sc₀, Prim.step, Function.update_of_ne hi2, Function.update_of_ne hi1]⟩
  obtain ⟨s₁, hcRun, hm1, _, hpo1, ho1, hcnt1, hr1⟩ := hLoopC
  have hPhase1 : SpecRun rMin pMin memBound _ s s₁ (4 * xs.length + 4) :=
    ((c1.seq (c2.seq c3)).seq hcRun).mono (by omega)
  -- Phase 2: storeHdrStmt at `[base + N .. base + N + 3)`
  have hpCE1 : s₁.ptrs pCurEnd = base + (xs.length : ℤ) := by
    rw [hpo1 pCurEnd hCE_1, hEnd]
  have hrK1 : s₁.regs rK = (k : ℝ) := by
    rw [hr1 rK (by omega) (by omega), hrK]
  have h2_1 : SpecRun rMin pMin memBound (.prim (.pcopy pScan2 pCurEnd)) s₁ _ 1 :=
    SpecRun.prim hp2 (by intro _ _ h; cases h)
  set sh₁ := (Prim.pcopy pScan2 pCurEnd).step s₁
  have h2_2 : SpecRun rMin pMin memBound (.prim (.store pScan2 rOne)) sh₁ _ 1 :=
    SpecRun.prim trivial (by intro _ _ h; cases h; simp [sh₁, Prim.step, hpCE1]; omega)
  set sh₂ := (Prim.store pScan2 rOne).step sh₁
  have h2_3 : SpecRun rMin pMin memBound (.prim (.pinc pScan2)) sh₂ _ 1 :=
    SpecRun.prim hp2 (by intro _ _ h; cases h)
  set sh₃ := (Prim.pinc pScan2).step sh₂
  have h2_4 : SpecRun rMin pMin memBound (.prim (.store pScan2 rCntN)) sh₃ _ 1 :=
    SpecRun.prim trivial (by intro _ _ h; cases h; simp [sh₃, sh₂, sh₁, Prim.step, hpCE1]; omega)
  set sh₄ := (Prim.store pScan2 rCntN).step sh₃
  have h2_5 : SpecRun rMin pMin memBound (.prim (.pinc pScan2)) sh₄ _ 1 :=
    SpecRun.prim hp2 (by intro _ _ h; cases h)
  set sh₅ := (Prim.pinc pScan2).step sh₄
  have h2_6 : SpecRun rMin pMin memBound (.prim (.store pScan2 rK)) sh₅ _ 1 :=
    SpecRun.prim trivial (by intro _ _ h; cases h; simp [sh₅, sh₄, sh₃, sh₂, sh₁, Prim.step, hpCE1]; omega)
  set sh₆ := (Prim.store pScan2 rK).step sh₅
  have h2_7 : SpecRun rMin pMin memBound (.prim (.pinc pScan2)) sh₆ _ 1 :=
    SpecRun.prim hp2 (by intro _ _ h; cases h)
  set s₂ := (Prim.pinc pScan2).step sh₆
  have hPhase2 : SpecRun rMin pMin memBound _ s₁ s₂ 7 :=
    (h2_1.seq (h2_2.seq (h2_3.seq (h2_4.seq (h2_5.seq (h2_6.seq h2_7)))))).mono (by omega)
  have hs₂_xs : ListAt s₂.mem base xs := by
    intro i hi
    simp only [s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁, Prim.step, Function.update_self, hpCE1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hm1]
    exact hxs i hi
  have hs₂_hdr0 : s₂.mem (base + (xs.length : ℤ)) = 1 := by
    simp only [s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁, Prim.step, Function.update_self, hpCE1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self, ho1]
  have hs₂_hdr1 : s₂.mem (base + (xs.length : ℤ) + 1) = (xs.length : ℝ) := by
    simp only [s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁, Prim.step, Function.update_self, hpCE1]
    rw [Function.update_of_ne (by omega), Function.update_self, hcnt1]
  have hs₂_hdr2 : s₂.mem (base + (xs.length : ℤ) + 2) = (k : ℝ) := by
    have haddr : base + (xs.length : ℤ) + 1 + 1 = base + (xs.length : ℤ) + 2 := by ring
    simp [s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁, Prim.step, hpCE1, haddr, hrK1]
  have hs₂_p2 : s₂.ptrs pScan2 = childBase := by
    simp [s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁, Prim.step, hpCE1, childBase]; ring
  -- Phase 3: medLoopStmt (`g = xs.length / 5` iterations)
  set g := xs.length / 5
  have m1 : SpecRun rMin pMin memBound (.prim (.pcopy pScan1 pCurStart)) s₂ _ 1 := sprim
  have m2 : SpecRun rMin pMin memBound (.prim (.pcopy pLimit pCurEnd))
      ((Prim.pcopy pScan1 pCurStart).step s₂) _ 1 := sprim
  have m3 := retreatPtrByConst_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) 4 hpL
    ((Prim.pcopy pLimit pCurEnd).step ((Prim.pcopy pScan1 pCurStart).step s₂))
  set sm₃ : MState := ⟨s₂.regs,
    Function.update (Function.update (Function.update s₂.ptrs pScan1 (s₂.ptrs pCurStart))
      pLimit (s₂.ptrs pCurEnd)) pLimit (s₂.ptrs pCurEnd - 4), s₂.mem⟩
  have m4 : SpecRun rMin pMin memBound (.prim (.const rPar 0)) sm₃ _ 1 := sprim
  have m5 : SpecRun rMin pMin memBound (.prim (.const rHalf 0))
      ((Prim.const rPar 0).step sm₃) _ 1 := sprim
  set sm₀ := (Prim.const rHalf 0).step ((Prim.const rPar 0).step sm₃)
  have hmInit : SpecRun rMin pMin memBound
      (Stmt.block [.prim (.pcopy pScan1 pCurStart), .prim (.pcopy pLimit pCurEnd),
        retreatPtrByConst 4 pLimit, .prim (.const rPar 0), .prim (.const rHalf 0)]) s₂ sm₀ 8 := by
    have m3' : SpecRun rMin pMin memBound (retreatPtrByConst 4 pLimit)
        ((Prim.pcopy pLimit pCurEnd).step ((Prim.pcopy pScan1 pCurStart).step s₂)) sm₃ 4 := by
      simpa [sm₃, Prim.step, Function.update_idem, Function.update_of_ne hCE_1] using m3
    exact (m1.seq (m2.seq (m3'.seq (m4.seq m5)))).mono (by omega)
  let medBody : Stmt :=
    .seq (loadVec 5 r5 pScan1)
      (.seq (med5Stmt r5)
        (.seq (.seq (.prim (.store pScan2 (r5 + 2))) (.prim (.pinc pScan2)))
          (.ifLeZero rPar
            (.prim (.const rPar 1))
            (.seq (.prim (.const rPar 0)) (.prim (.add rHalf rHalf rOne))))))
  let InvM : ℕ → MState → Prop := fun m st =>
    MemPreservedBelow childBase s₂.mem st.mem ∧
    ListAt st.mem childBase ((medsOf5 xs).take m) ∧
    st.ptrs pScan1 = base + 5 * (m : ℤ) ∧
    st.ptrs pScan2 = childBase + (m : ℤ) ∧
    st.ptrs pLimit = base + (xs.length : ℤ) - 4 ∧
    (∀ q, q ≠ pScan1 → q ≠ pScan2 → q ≠ pLimit → st.ptrs q = s.ptrs q) ∧
    st.regs rOne = 1 ∧
    st.regs rPar = ((m % 2 : ℕ) : ℝ) ∧
    st.regs rHalf = ((m / 2 : ℕ) : ℝ) ∧
    (∀ i, (i < rScr ∨ rScr + 12 ≤ i) → st.regs i = s.regs i)
  have hs₂_pCS : s₂.ptrs pCurStart = base := by
    simp [s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁, Prim.step, Function.update_of_ne hCS_2,
      hpo1 pCurStart hCS_1, base]
  have hs₂_pCE : s₂.ptrs pCurEnd = base + (xs.length : ℤ) := by
    simp [s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁, Prim.step, Function.update_of_ne hCE_2, hpCE1]
  have hInvM0 : InvM 0 sm₀ := by
    refine ⟨MemPreservedBelow.refl _ _, fun i hi => by simp at hi,
      by simp [sm₀, sm₃, Prim.step, Function.update_of_ne h1_L, hs₂_pCS],
      by simp [sm₀, sm₃, Prim.step, Function.update_of_ne h2_L, Function.update_of_ne h1_2.symm, hs₂_p2],
      by simp [sm₀, sm₃, Prim.step, hs₂_pCE],
      fun q hq1 hq2 hqL => by
        simp [sm₀, sm₃, Prim.step, Function.update_of_ne hqL, Function.update_of_ne hq1,
          s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁, Function.update_of_ne hq2, hpo1 q hq1],
      by simp [sm₀, sm₃, Prim.step, Function.update_of_ne (show rOne ≠ rHalf by omega),
          Function.update_of_ne (show rOne ≠ rPar by omega), s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁, ho1],
      by simp [sm₀, sm₃, Prim.step, Function.update_of_ne (show rPar ≠ rHalf by omega)],
      by simp [sm₀, sm₃, Prim.step],
      fun i hi => by
        simp [sm₀, sm₃, Prim.step, Function.update_of_ne (show i ≠ rHalf by omega),
          Function.update_of_ne (show i ≠ rPar by omega), s₂, sh₆, sh₅, sh₄, sh₃, sh₂, sh₁,
          hr1 i (by omega) (by omega)]⟩
  have hLoopM := SpecRun.forLoop (rMin := rMin) (pMin := pMin) (memBound := memBound)
    (q₁ := pScan1) (q₂ := pLimit) (body := medBody) g 98 InvM
    (fun m hm st hInv => by
      obtain ⟨hmPres, hmeds, hp1_st, hp2_st, hpL_st, hpo, hone, hpar, hhalf, hregs⟩ := hInv
      have hm5 : 5 * m + 4 < xs.length := by omega
      refine ⟨by rw [hp1_st, hpL_st]; omega, ?_⟩
      let v5 : Fin 5 → ℝ := fun j => xs[5 * m + j.1]'(by have := j.2; omega)
      have hv5 : VecAt st.mem (st.ptrs pScan1) v5 := by
        intro j
        rw [hp1_st]
        have hlt_cb : base + 5 * (m : ℤ) + (j.1 : ℤ) < childBase := by
          dsimp [childBase]; have := j.2; omega
        rw [hmPres _ hlt_cb]
        have := hs₂_xs (5 * m + j.1) (by have := j.2; omega)
        simpa [v5, add_assoc] using this
      obtain ⟨st₁, q1, hvR1, hoth1, hptrs1, hmem1⟩ :=
        loadVec_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) 5
          (rDst := r5) (q := pScan1) hv5 (by omega) hp1
      obtain ⟨st₂, q2, hmed2, hoth2, hptrs2, hmem2⟩ :=
        med5Stmt_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) (r5 := r5) (by omega) st₁
      have hv0 : st₁.regs r5 = xs[5 * m] := by simpa [v5] using hvR1 0
      have hv1 : st₁.regs (r5 + 1) = xs[5 * m + 1] := by simpa [v5] using hvR1 1
      have hv2 : st₁.regs (r5 + 2) = xs[5 * m + 2] := by simpa [v5] using hvR1 2
      have hv3 : st₁.regs (r5 + 3) = xs[5 * m + 3] := by simpa [v5] using hvR1 3
      have hv4 : st₁.regs (r5 + 4) = xs[5 * m + 4] := by simpa [v5] using hvR1 4
      rw [hv0, hv1, hv2, hv3, hv4] at hmed2
      have hp2_st2 : st₂.ptrs pScan2 = childBase + (m : ℤ) := by
        rw [hptrs2, hptrs1, Function.update_of_ne h1_2.symm, hp2_st]
      have q3 : SpecRun rMin pMin memBound (.prim (.store pScan2 (r5 + 2))) st₂ _ 1 :=
        SpecRun.prim trivial (by intro _ _ h; cases h; rw [hp2_st2]; dsimp [childBase]; omega)
      have q4 : SpecRun rMin pMin memBound (.prim (.pinc pScan2))
          ((Prim.store pScan2 (r5 + 2)).step st₂) _ 1 := sprim
      set st₄ := (Prim.pinc pScan2).step ((Prim.store pScan2 (r5 + 2)).step st₂)
      have hpar4 : st₄.regs rPar = ((m % 2 : ℕ) : ℝ) := by
        simp [st₄, Prim.step, hoth2 rPar (by omega), hoth1 rPar (by omega), hpar]
      have hhalf4 : st₄.regs rHalf = ((m / 2 : ℕ) : ℝ) := by
        simp [st₄, Prim.step, hoth2 rHalf (by omega), hoth1 rHalf (by omega), hhalf]
      have hone4 : st₄.regs rOne = 1 := by
        simp [st₄, Prim.step, hoth2 rOne (by omega), hoth1 rOne (by omega), hone]
      have hmPres4 : MemPreservedBelow childBase s₂.mem st₄.mem := by
        intro a ha
        simp only [st₄, Prim.step, hp2_st2]
        rw [Function.update_of_ne (by omega), hmem2, hmem1]
        exact hmPres a ha
      have hmeds4 : ListAt st₄.mem childBase ((medsOf5 xs).take (m + 1)) := by
        have hm_len : m < (medsOf5 xs).length := by simp [medsOf5]; exact hm
        rw [List.take_succ_eq_append_getElem hm_len]
        intro i hi
        simp only [List.length_append, List.length_singleton, List.length_take,
          Nat.min_eq_left (le_of_lt hm_len)] at hi
        by_cases hlt_i : i < m
        · rw [List.getElem_append_left (by simp [Nat.min_eq_left (le_of_lt hm_len)]; exact hlt_i)]
          simp only [st₄, Prim.step, hp2_st2]
          rw [Function.update_of_ne (by omega), hmem2, hmem1]
          exact hmeds i (by simp [Nat.min_eq_left (le_of_lt hm_len)]; exact hlt_i)
        · have heq_i : i = m := by omega
          subst heq_i
          simp [st₄, Prim.step, hp2_st2, hmed2, medsOf5]
      by_cases hm_even : m % 2 = 0
      · have hle_p : st₄.regs rPar ≤ 0 := by rw [hpar4, hm_even]; simp
        have q5 : SpecRun rMin pMin memBound (.prim (.const rPar 1)) st₄ _ 1 :=
          SpecRun.prim (show rMin ≤ rPar by omega) (by intro _ _ h; cases h)
        set st₅ := (Prim.const rPar 1).step st₄
        have br := SpecRun.ifLeZero_true
          (e := .seq (.prim (.const rPar 0)) (.prim (.add rHalf rHalf rOne))) hle_p q5
        refine ⟨st₅, (q1.seq (q2.seq ((q3.seq q4).seq br))).mono (by omega),
          hmPres4, hmeds4,
          by simp [st₅, st₄, Prim.step, hptrs2, hptrs1, Function.update_of_ne h1_2, hp1_st]; ring,
          by simp [st₅, st₄, Prim.step, hp2_st2]; omega,
          by simp [st₅, st₄, Prim.step, hptrs2, hptrs1, Function.update_of_ne h2_L.symm,
              Function.update_of_ne h1_L.symm, hpL_st],
          fun q hq1 hq2 hqL => by
            simp [st₅, st₄, Prim.step, Function.update_of_ne hq2, hptrs2, hptrs1,
              Function.update_of_ne hq1, hpo q hq1 hq2 hqL],
          by simp [st₅, Prim.step, Function.update_of_ne (show rOne ≠ rPar by omega), hone4],
          by have : (m + 1) % 2 = 1 := by omega
             simp [st₅, Prim.step, this],
          by have : (m + 1) / 2 = m / 2 := by omega
             simp [st₅, Prim.step, Function.update_of_ne (show rHalf ≠ rPar by omega), hhalf4, this],
          fun i hi => by
            simp [st₅, st₄, Prim.step, Function.update_of_ne (show i ≠ rPar by omega),
              hoth2 i (by omega), hoth1 i (by omega), hregs i hi]⟩
      · have hm_odd : m % 2 = 1 := by omega
        have hnotle_p : ¬ st₄.regs rPar ≤ 0 := by rw [hpar4, hm_odd]; norm_num
        have q5 : SpecRun rMin pMin memBound (.prim (.const rPar 0)) st₄ _ 1 := sprim
        have q6 : SpecRun rMin pMin memBound (.prim (.add rHalf rHalf rOne))
            ((Prim.const rPar 0).step st₄) _ 1 := sprim
        set st₆ := (Prim.add rHalf rHalf rOne).step ((Prim.const rPar 0).step st₄)
        have br := SpecRun.ifLeZero_false (t := .prim (.const rPar 1)) hnotle_p (q5.seq q6)
        refine ⟨st₆, (q1.seq (q2.seq ((q3.seq q4).seq br))).mono (by omega),
          hmPres4, hmeds4,
          by simp [st₆, st₄, Prim.step, hptrs2, hptrs1, Function.update_of_ne h1_2, hp1_st]; ring,
          by simp [st₆, st₄, Prim.step, hp2_st2]; omega,
          by simp [st₆, st₄, Prim.step, hptrs2, hptrs1, Function.update_of_ne h2_L.symm,
              Function.update_of_ne h1_L.symm, hpL_st],
          fun q hq1 hq2 hqL => by
            simp [st₆, st₄, Prim.step, Function.update_of_ne hq2, hptrs2, hptrs1,
              Function.update_of_ne hq1, hpo q hq1 hq2 hqL],
          by simp [st₆, Prim.step, Function.update_of_ne (show rOne ≠ rHalf by omega),
              Function.update_of_ne (show rOne ≠ rPar by omega), hone4],
          by have : (m + 1) % 2 = 0 := by omega
             simp [st₆, Prim.step, Function.update_of_ne (show rPar ≠ rHalf by omega), this],
          by have : (m + 1) / 2 = m / 2 + 1 := by omega
             simp [st₆, Prim.step, Function.update_of_ne (show rHalf ≠ rPar by omega),
              Function.update_of_ne (show rOne ≠ rPar by omega), hhalf4, hone4, this, Nat.cast_add],
          fun i hi => by
            simp [st₆, st₄, Prim.step, Function.update_of_ne (show i ≠ rHalf by omega),
              Function.update_of_ne (show i ≠ rPar by omega),
              hoth2 i (by omega), hoth1 i (by omega), hregs i hi]⟩)
    (fun st hInv => by
      obtain ⟨_, _, hp1_st, _, hpL_st, _⟩ := hInv
      rw [hp1_st, hpL_st]; omega)
    g le_rfl sm₀ (by simpa using hInvM0)
  obtain ⟨s₃, hmRun, hmPres3, hmeds3, _, hp2_3, _, hpo3, _, _, hhalf3, hregs3⟩ := hLoopM
  rw [show (medsOf5 xs).take g = medsOf5 xs by simp [medsOf5, g]] at hmeds3
  have hPhase3 : SpecRun rMin pMin memBound _ s₂ s₃ (100 * g + 9) :=
    (hmInit.seq hmRun).mono (by omega)
  -- Phase 4: finalizeStmt
  have f1 : SpecRun rMin pMin memBound (.prim (.pcopy pCurStart pCurEnd)) s₃ _ 1 :=
    SpecRun.prim hpCS (by intro _ _ h; cases h)
  have f2 := advancePtrByConst_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) 3 hpCS
    ((Prim.pcopy pCurStart pCurEnd).step s₃)
  set sf₂ : MState := ⟨s₃.regs, Function.update s₃.ptrs pCurStart (s₃.ptrs pCurEnd + 3), s₃.mem⟩
  have f2' : SpecRun rMin pMin memBound (advancePtrByConst 3 pCurStart)
      ((Prim.pcopy pCurStart pCurEnd).step s₃) sf₂ 3 := by
    simpa [sf₂, Prim.step, Function.update_idem] using f2
  have f3 : SpecRun rMin pMin memBound (.prim (.pcopy pCurEnd pScan2)) sf₂ _ 1 :=
    SpecRun.prim hpCE (by intro _ _ h; cases h)
  set sf₃ := (Prim.pcopy pCurEnd pScan2).step sf₂
  obtain ⟨s₄, f4, hrK4, _, hoth4, hp4, hm4⟩ :=
    copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
      (rDst := rK) (rSrc := rHalf) (rZero := r5 + 7) (s := sf₃)
      hK (by omega) (by omega) (by omega)
  have hPhase4 : SpecRun rMin pMin memBound _ s₃ s₄ 7 :=
    (f1.seq (f2'.seq (f3.seq f4))).mono (by omega)
  have hs₃_pCE : s₃.ptrs pCurEnd = base + (xs.length : ℤ) := by
    rw [hpo3 pCurEnd hCE_1 hCE_2 hCE_L, hEnd]
  have hsf3_m : sf₃.mem = s₃.mem := rfl
  refine ⟨s₄, (hPhase1.seq (hPhase2.seq (hPhase3.seq hPhase4))).mono (by dsimp [g]; omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm4, hsf3_m]; exact hs₂_xs.of_mem_pres hmPres3 (by dsimp [childBase]; omega)
  · rw [hm4, hsf3_m, hmPres3 _ (by dsimp [childBase]; omega), hs₂_hdr0]
  · rw [hm4, hsf3_m, hmPres3 _ (by dsimp [childBase]; omega), hs₂_hdr1]
  · rw [hm4, hsf3_m, hmPres3 _ (by dsimp [childBase]; omega), hs₂_hdr2]
  · rw [hm4, hsf3_m]; exact hmeds3
  · rw [hp4]; simp [sf₃, sf₂, Prim.step, Function.update_of_ne hCS_CE, hs₃_pCE, childBase]
  · rw [hp4]; simp [sf₃, sf₂, Prim.step, Function.update_of_ne hCS_2.symm, hp2_3]
  · rw [hrK4]; exact hhalf3
  · intro i hiK hiS
    rw [hoth4 i hiK (by omega)]; exact hregs3 i hiS
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [hp4]
    simp [sf₃, sf₂, Prim.step, Function.update_of_ne hq.2.1, Function.update_of_ne hq.1,
      hpo3 q hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2]

/-- Mode-2 return step: reads 3-cell header `[pCurStart - 3 .. pCurStart)` (`has_parent, N, k`).
If `has_parent ≤ 0`, sets `rActive := 0`.
Otherwise pops parent `[parentBase .. parentBase + N)`, counts `cntLt` and `cntLe` vs `rOut`:
- `k < cntLt`: filters `< rOut` into `[parentBase ..)` and sets `rMode := 1`.
- `cntLt ≤ k < cntLe`: keeps `rOut` and `rMode := 2`.
- `cntLe ≤ k`: filters `> rOut` into `[parentBase ..)`, sets `rK := k - cntLe`, `rMode := 1`.
Uses `rScr .. rScr + 11` (`12` scratch regs) and `pScan1, pScan2`. -/
noncomputable def popOrPartitionStmt
    (rActive rMode rOut rK pCurStart pCurEnd rScr pScan1 pScan2 : ℕ) : Stmt :=
  let rHdr := rScr       -- rScr, rScr + 1, rScr + 2
  let rPiv := rScr + 3
  let rLt  := rScr + 4
  let rLe  := rScr + 5
  let rChk := rScr + 6
  let rOne := rScr + 7
  let rSub := rScr + 8   -- rScr + 8, + 9, + 10
  let walkBackStmt : Stmt :=
    Stmt.block [
      .prim (.pcopy pCurEnd pCurStart),
      retreatPtrByConst 3 pCurEnd,
      .prim (.pcopy pCurStart pCurEnd),
      .prim (.const rOne 1),
      .whilePos (rHdr + 1)
        (.seq (.prim (.pdec pCurStart)) (.prim (.sub (rHdr + 1) (rHdr + 1) rOne))),
      copyReg rK (rHdr + 2) rSub,
      copyReg rPiv rOut rSub,
      countLtLeStmt pCurStart pCurEnd pScan1 rPiv rLt rLe rSub]
  let partStmt : Stmt :=
    .seq (.prim (.sub rChk rLt rK))
      (.ifLeZero rChk
        (.seq (.prim (.sub rChk rLe rK))
          (.ifLeZero rChk
            (Stmt.block [
              filterCmpStmt false pCurStart pCurEnd pScan1 pScan2 rPiv rSub,
              .prim (.pcopy pCurEnd pScan2),
              .prim (.sub rK rK rLe),
              .prim (.const rMode 1)])
            (.prim (.const rMode 2))))
        (Stmt.block [
          filterCmpStmt true pCurStart pCurEnd pScan1 pScan2 rPiv rSub,
          .prim (.pcopy pCurEnd pScan2),
          .prim (.const rMode 1)]))
  Stmt.block [
    .prim (.pcopy pScan1 pCurStart),
    retreatPtrByConst 3 pScan1,
    loadVec 3 rHdr pScan1,
    .ifLeZero rHdr (.prim (.const rActive 0)) (.seq walkBackStmt partStmt)]

theorem popOrPartitionStmt_top_spec {rMin pMin : ℕ} {memBound : ℤ}
    {rActive rMode rOut rK pCurStart pCurEnd rScr pScan1 pScan2 : ℕ} {s : MState}
    (hHdr0 : s.mem (s.ptrs pCurStart - 3) ≤ 0)
    (hAct : rMin ≤ rActive) (hScr : rMin ≤ rScr) (hp1 : pMin ≤ pScan1)
    (_hCS1 : pCurStart ≠ pScan1)
    (hOutAct : rOut ≠ rActive)
    (hOutScr : rOut < rScr ∨ rScr + 11 ≤ rOut) :
    ∃ s', SpecRun rMin pMin memBound
        (popOrPartitionStmt rActive rMode rOut rK pCurStart pCurEnd rScr pScan1 pScan2) s s' 15 ∧
      s'.regs rActive ≤ 0 ∧
      s'.regs rOut = s.regs rOut := by
  have p1 : SpecRun rMin pMin memBound (.prim (.pcopy pScan1 pCurStart)) s _ 1 :=
    SpecRun.prim hp1 (by intro _ _ h; cases h)
  have p2 := retreatPtrByConst_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) 3 hp1
    ((Prim.pcopy pScan1 pCurStart).step s)
  set s₂ : MState := ⟨s.regs, Function.update s.ptrs pScan1 (s.ptrs pCurStart - 3), s.mem⟩
  have p2' : SpecRun rMin pMin memBound (retreatPtrByConst 3 pScan1)
      ((Prim.pcopy pScan1 pCurStart).step s) s₂ 3 := by
    simpa [s₂, Prim.step, Function.update_idem] using p2
  let v3 : Fin 3 → ℝ := fun j => s.mem (s.ptrs pCurStart - 3 + (j.1 : ℤ))
  have hv3 : VecAt s₂.mem (s₂.ptrs pScan1) v3 := by
    intro j; simp [s₂, v3]
  obtain ⟨s₃, p3, hvR3, hoth3, _, _⟩ :=
    loadVec_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) 3
      (rDst := rScr) (q := pScan1) hv3 hScr hp1
  have hcond : s₃.regs rScr ≤ 0 := by
    have h0 := hvR3 0
    simp only [Fin.val_zero, v3, Int.ofNat_zero, add_zero] at h0
    rw [h0]; exact hHdr0
  have p4 : SpecRun rMin pMin memBound (.prim (.const rActive 0)) s₃ _ 1 :=
    SpecRun.prim hAct (by intro _ _ h; cases h)
  set s₄ := (Prim.const rActive 0).step s₃
  refine ⟨s₄, (p1.seq (p2'.seq (p3.seq (SpecRun.ifLeZero_true (e := _) hcond p4)))).mono (by omega),
    by simp [s₄, Prim.step],
    by simp [s₄, s₂, Prim.step, Function.update_of_ne hOutAct, hoth3 rOut (by omega)]⟩

set_option maxHeartbeats 800000 in
theorem popOrPartitionStmt_parent_spec {rMin pMin : ℕ} {memBound : ℤ}
    {rActive rMode rOut rK pCurStart pCurEnd rScr pScan1 pScan2 : ℕ}
    {xs : List ℝ} {k : ℕ} {base : ℤ} {s : MState}
    (hChild : s.ptrs pCurStart = base + (xs.length : ℤ) + 3)
    (hxs : ListAt s.mem base xs)
    (hHdr0 : s.mem (base + (xs.length : ℤ)) = 1)
    (hHdr1 : s.mem (base + (xs.length : ℤ) + 1) = (xs.length : ℝ))
    (hHdr2 : s.mem (base + (xs.length : ℤ) + 2) = (k : ℝ))
    (hmB : memBound ≤ base)
    (hAct : s.regs rActive = 1)
    (hMode : rMin ≤ rMode) (hK : rMin ≤ rK) (hScr : rMin ≤ rScr)
    (hpCS : pMin ≤ pCurStart) (hpCE : pMin ≤ pCurEnd) (hp1 : pMin ≤ pScan1) (hp2 : pMin ≤ pScan2)
    (hDistinctP : [pCurStart, pCurEnd, pScan1, pScan2].Nodup)
    (hDistinctR : [rActive, rMode, rOut, rK].Nodup)
    (hRegsScr : ∀ r ∈ [rActive, rMode, rOut, rK], r < rScr ∨ rScr + 11 ≤ r) :
    let piv := s.regs rOut
    ∃ s', SpecRun rMin pMin memBound
        (popOrPartitionStmt rActive rMode rOut rK pCurStart pCurEnd rScr pScan1 pScan2) s s'
        (24 * xs.length + 50) ∧
      s'.regs rActive = 1 ∧
      s'.ptrs pCurStart = base ∧
      ((k < cntLt xs piv ∧
          s'.regs rMode = 1 ∧
          s'.regs rK = (k : ℝ) ∧
          ListAt s'.mem base (xs.filter (fun x => decide (x < piv))) ∧
          s'.ptrs pCurEnd = base + ((cntLt xs piv : ℕ) : ℤ)) ∨
       (cntLt xs piv ≤ k ∧ k < cntLe xs piv ∧
          s'.regs rMode = 2 ∧
          s'.regs rOut = piv ∧
          s'.mem = s.mem) ∨
       (cntLe xs piv ≤ k ∧
          s'.regs rMode = 1 ∧
          s'.regs rK = ((k - cntLe xs piv : ℕ) : ℝ) ∧
          ListAt s'.mem base (xs.filter (fun x => decide (piv < x))) ∧
          s'.ptrs pCurEnd = base + ((cntGt xs piv : ℕ) : ℤ))) := by
  intro piv
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true, ← ne_eq] at hDistinctP hDistinctR
  obtain ⟨⟨hCS_CE, hCS_1, hCS_2⟩, ⟨hCE_1, hCE_2⟩, h1_2⟩ := hDistinctP
  obtain ⟨⟨hAct_Mode, hAct_Out, hAct_K⟩, ⟨hMode_Out, hMode_K⟩, hOut_K⟩ := hDistinctR
  have hActS := hRegsScr rActive (by simp)
  have hModeS := hRegsScr rMode (by simp)
  have hOutS := hRegsScr rOut (by simp)
  have hKS := hRegsScr rK (by simp)
  let rHdr := rScr
  let rPiv := rScr + 3
  let rLt  := rScr + 4
  let rLe  := rScr + 5
  let rChk := rScr + 6
  let rOne := rScr + 7
  let rSub := rScr + 8
  -- Load 3-cell header
  have p1 : SpecRun rMin pMin memBound (.prim (.pcopy pScan1 pCurStart)) s _ 1 :=
    SpecRun.prim hp1 (by intro _ _ h; cases h)
  have p2 := retreatPtrByConst_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) 3 hp1
    ((Prim.pcopy pScan1 pCurStart).step s)
  set s₂ : MState := ⟨s.regs, Function.update s.ptrs pScan1 (base + (xs.length : ℤ)), s.mem⟩
  have p2' : SpecRun rMin pMin memBound (retreatPtrByConst 3 pScan1)
      ((Prim.pcopy pScan1 pCurStart).step s) s₂ 3 := by
    convert p2 using 1; simp [s₂, Prim.step, Function.update_idem, hChild]
  let v3 : Fin 3 → ℝ := ![1, (xs.length : ℝ), (k : ℝ)]
  have hv3 : VecAt s₂.mem (s₂.ptrs pScan1) v3 := by
    intro j
    fin_cases j
    · simpa [s₂, v3] using hHdr0
    · simpa [s₂, v3, add_assoc] using hHdr1
    · simpa [s₂, v3, add_assoc] using hHdr2
  obtain ⟨s₃, p3, hvR3, hoth3, hp3, hm3⟩ :=
    loadVec_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) 3
      (rDst := rHdr) (q := pScan1) hv3 hScr hp1
  have hnotle_hdr : ¬ s₃.regs rHdr ≤ 0 := by
    have := hvR3 0
    simp only [Fin.val_zero, Nat.add_zero, v3, Matrix.cons_val_zero] at this
    rw [this]; norm_num
  -- Walk back `pCurEnd := base + N` and `pCurStart := base`
  have w1 : SpecRun rMin pMin memBound (.prim (.pcopy pCurEnd pCurStart)) s₃ _ 1 :=
    SpecRun.prim hpCE (by intro _ _ h; cases h)
  have w2 := retreatPtrByConst_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) 3 hpCE
    ((Prim.pcopy pCurEnd pCurStart).step s₃)
  have hs3_pCS : s₃.ptrs pCurStart = base + (xs.length : ℤ) + 3 := by
    rw [hp3]; simp [s₂, Function.update_of_ne hCS_1, hChild]
  set sw₂ : MState := ⟨s₃.regs, Function.update s₃.ptrs pCurEnd (base + (xs.length : ℤ)), s₃.mem⟩
  have w2' : SpecRun rMin pMin memBound (retreatPtrByConst 3 pCurEnd)
      ((Prim.pcopy pCurEnd pCurStart).step s₃) sw₂ 3 := by
    convert w2 using 1; simp [sw₂, Prim.step, Function.update_idem, hs3_pCS]
  have w3 : SpecRun rMin pMin memBound (.prim (.pcopy pCurStart pCurEnd)) sw₂ _ 1 := sprim
  have w4 : SpecRun rMin pMin memBound (.prim (.const rOne 1))
      ((Prim.pcopy pCurStart pCurEnd).step sw₂) _ 1 := sprim
  set sw₄ := (Prim.const rOne 1).step ((Prim.pcopy pCurStart pCurEnd).step sw₂)
  -- Decrement loop on `rHdr + 1` (`xs.length` iterations)
  have hDecLoop : ∀ (n : ℕ) (st : MState),
      st.regs (rHdr + 1) = (n : ℝ) →
      st.regs rOne = 1 →
      ∃ st', SpecRun rMin pMin memBound
        (.whilePos (rHdr + 1) (.seq (.prim (.pdec pCurStart)) (.prim (.sub (rHdr + 1) (rHdr + 1) rOne))))
        st st' (4 * n + 1) ∧
        st'.ptrs pCurStart = st.ptrs pCurStart - (n : ℤ) ∧
        (∀ q, q ≠ pCurStart → st'.ptrs q = st.ptrs q) ∧
        (∀ i, i ≠ rHdr + 1 → st'.regs i = st.regs i) ∧
        st'.mem = st.mem := by
    intro n
    induction n with
    | zero =>
      intro st hn _
      refine ⟨st, SpecRun.whilePos_exit (by rw [hn]; simp), by simp,
        fun _ _ => rfl, fun _ _ => rfl, rfl⟩
    | succ n ih =>
      intro st hn hone
      have hpos : 0 < st.regs (rHdr + 1) := by rw [hn]; positivity
      have d1 : SpecRun rMin pMin memBound (.prim (.pdec pCurStart)) st _ 1 := sprim
      have d2 : SpecRun rMin pMin memBound (.prim (.sub (rHdr + 1) (rHdr + 1) rOne))
          ((Prim.pdec pCurStart).step st) _ 1 := sprim
      set st₁ := (Prim.sub (rHdr + 1) (rHdr + 1) rOne).step ((Prim.pdec pCurStart).step st)
      obtain ⟨st₂, hrest, hpcs2, hpo2, hr2, hm2⟩ := ih st₁
        (by simp [st₁, Prim.step, hn, hone])
        (by simp [st₁, Prim.step, Function.update_of_ne (show rOne ≠ rHdr + 1 by omega), hone])
      refine ⟨st₂, (SpecRun.whilePos_step hpos (d1.seq d2) hrest).mono (by omega),
        by rw [hpcs2]; simp [st₁, Prim.step]; ring,
        fun q hq => by rw [hpo2 q hq]; simp [st₁, Prim.step, Function.update_of_ne hq],
        fun i hi => by rw [hr2 i hi]; simp [st₁, Prim.step, Function.update_of_ne hi],
        hm2⟩
  have hsw4_n : sw₄.regs (rHdr + 1) = (xs.length : ℝ) := by
    simp only [sw₄, sw₂, Prim.step, Function.update_of_ne (show rHdr + 1 ≠ rOne by omega)]
    simpa [v3] using hvR3 1
  obtain ⟨sw₅, w5, hpcs5, hpo5, hr5, hm5⟩ := hDecLoop xs.length sw₄ hsw4_n (by simp [sw₄, Prim.step])
  have hpcs5_eq : sw₅.ptrs pCurStart = base := by
    rw [hpcs5]; simp [sw₄, sw₂, Prim.step]
  have hpce5_eq : sw₅.ptrs pCurEnd = base + (xs.length : ℤ) := by
    rw [hpo5 pCurEnd hCS_CE.symm]; simp [sw₄, sw₂, Prim.step, Function.update_of_ne hCS_CE.symm]
  obtain ⟨sw₆, w6, hrK6, _, hoth6, hp6, hm6⟩ :=
    copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
      (rDst := rK) (rSrc := rHdr + 2) (rZero := rSub) (s := sw₅)
      hK (by omega) (by omega) (by omega)
  have hrK6_val : sw₆.regs rK = (k : ℝ) := by
    rw [hrK6, hr5 (rHdr + 2) (by omega)]
    simp only [sw₄, sw₂, Prim.step, Function.update_of_ne (show rHdr + 2 ≠ rOne by omega)]
    simpa [v3] using hvR3 2
  obtain ⟨sw₇, w7, hrPiv7, _, hoth7, hp7, hm7⟩ :=
    copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
      (rDst := rPiv) (rSrc := rOut) (rZero := rSub) (s := sw₆)
      (by omega) (by omega) (by omega) (by omega)
  have hrPiv7_val : sw₇.regs rPiv = piv := by
    rw [hrPiv7, hoth6 rOut hOut_K (by omega), hr5 rOut (by omega)]
    simp [sw₄, sw₂, s₂, Prim.step, Function.update_of_ne (show rOut ≠ rOne by omega),
      hoth3 rOut (by omega), piv]
  have hmem7 : sw₇.mem = s.mem := by
    rw [hm7, hm6, hm5]; simp [sw₄, sw₂, Prim.step, hm3, s₂]
  have hpcs7 : sw₇.ptrs pCurStart = base := by rw [hp7, hp6, hpcs5_eq]
  have hpce7 : sw₇.ptrs pCurEnd = base + (xs.length : ℤ) := by rw [hp7, hp6, hpce5_eq]
  obtain ⟨sw₈, w8, hlt8, hle8, hregs8, hptrs8, hmem8⟩ :=
    countLtLeStmt_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
      (pStart := pCurStart) (pEnd := pCurEnd) (pScan := pScan1)
      (rPiv := rPiv) (rLt := rLt) (rLe := rLe) (rScr := rSub) (s := sw₇)
      (by rw [hmem7, hpcs7]; exact hxs) (by rw [hpce7, hpcs7])
      (by omega) (by omega) (by omega) hp1 hCS_1.symm hCE_1.symm
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hrPiv7_val] at hlt8 hle8
  have hWalk : SpecRun rMin pMin memBound _ s₃ sw₈ (14 * xs.length + 21) :=
    (w1.seq (w2'.seq (w3.seq (w4.seq (w5.seq (w6.seq (w7.seq w8))))))).mono (by omega)
  have hrK8 : sw₈.regs rK = (k : ℝ) := by
    rw [hregs8 rK (by omega) (by omega) (by omega), hoth7 rK (by omega) (by omega), hrK6_val]
  have hrAct8 : sw₈.regs rActive = 1 := by
    rw [hregs8 rActive (by omega) (by omega) (by omega), hoth7 rActive (by omega) (by omega),
        hoth6 rActive hAct_K (by omega), hr5 rActive (by omega)]
    simp [sw₄, sw₂, s₂, Prim.step, Function.update_of_ne (show rActive ≠ rOne by omega),
      hoth3 rActive (by omega), hAct]
  have hrOut8 : sw₈.regs rOut = piv := by
    rw [hregs8 rOut (by omega) (by omega) (by omega), hoth7 rOut (by omega) (by omega),
        hoth6 rOut hOut_K (by omega), hr5 rOut (by omega)]
    simp [sw₄, sw₂, s₂, Prim.step, Function.update_of_ne (show rOut ≠ rOne by omega),
      hoth3 rOut (by omega), piv]
  have hrPiv8 : sw₈.regs rPiv = piv := by
    rw [hregs8 rPiv (by omega) (by omega) (by omega), hrPiv7_val]
  have hpcs8 : sw₈.ptrs pCurStart = base := by rw [hptrs8 pCurStart hCS_1, hpcs7]
  have hpce8 : sw₈.ptrs pCurEnd = base + (xs.length : ℤ) := by rw [hptrs8 pCurEnd hCE_1, hpce7]
  have hmem8_eq : sw₈.mem = s.mem := hmem8.trans hmem7
  -- Partition check (`partStmt`)
  let partStmt : Stmt :=
    .seq (.prim (.sub rChk rLt rK))
      (.ifLeZero rChk
        (.seq (.prim (.sub rChk rLe rK))
          (.ifLeZero rChk
            (Stmt.block [
              filterCmpStmt false pCurStart pCurEnd pScan1 pScan2 rPiv rSub,
              .prim (.pcopy pCurEnd pScan2),
              .prim (.sub rK rK rLe),
              .prim (.const rMode 1)])
            (.prim (.const rMode 2))))
        (Stmt.block [
          filterCmpStmt true pCurStart pCurEnd pScan1 pScan2 rPiv rSub,
          .prim (.pcopy pCurEnd pScan2),
          .prim (.const rMode 1)]))
  have q0 : SpecRun rMin pMin memBound (.prim (.sub rChk rLt rK)) sw₈ _ 1 :=
    SpecRun.prim (show rMin ≤ rChk by omega) (by intro _ _ h; cases h)
  set sp₀ := (Prim.sub rChk rLt rK).step sw₈
  by_cases hkLt : k < cntLt xs piv
  · -- Branch 1: `k < cntLt xs piv`
    have hnotle0 : ¬ sp₀.regs rChk ≤ 0 := by
      simp only [sp₀, Prim.step, Function.update_self, hlt8, hrK8]
      have hc : (k : ℝ) + 1 ≤ (cntLt xs piv : ℝ) := by exact_mod_cast hkLt
      linarith
    obtain ⟨sp₁, qf, hfilt1, hpw1, hrf1, hpf1⟩ :=
      filterCmpStmt_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) true
        (pStart := pCurStart) (pEnd := pCurEnd) (pRead := pScan1) (pWrite := pScan2)
        (rPiv := rPiv) (rScr := rSub) (xs := xs) (s := sp₀)
        (by simp [sp₀, Prim.step, hpcs8, hmem8_eq]; exact hxs)
        (by simp [sp₀, Prim.step, hpce8, hpcs8])
        (by simp [sp₀, Prim.step, hpcs8]; exact hmB)
        (by omega) hp1 hp2 h1_2 hCS_1.symm hCE_1.symm hCS_2.symm hCE_2.symm (by omega)
    have qf2 : SpecRun rMin pMin memBound (.prim (.pcopy pCurEnd pScan2)) sp₁ _ 1 := sprim
    have qf3 : SpecRun rMin pMin memBound (.prim (.const rMode 1))
        ((Prim.pcopy pCurEnd pScan2).step sp₁) _ 1 := sprim
    set sp₃ := (Prim.const rMode 1).step ((Prim.pcopy pCurEnd pScan2).step sp₁)
    have hPart : SpecRun rMin pMin memBound partStmt sw₈ sp₃ _ :=
      q0.seq (SpecRun.ifLeZero_false (t := _) hnotle0 (qf.seq (qf2.seq qf3)))
    have hAll : SpecRun rMin pMin memBound _ s sp₃ (24 * xs.length + 50) :=
      (p1.seq (p2'.seq (p3.seq
        (SpecRun.ifLeZero_false (t := .prim (.const rActive 0)) hnotle_hdr (hWalk.seq hPart))))).mono
        (by omega)
    have hpiv_sp0 : sp₀.regs rPiv = piv := by
      simp [sp₀, Prim.step, Function.update_of_ne (show rPiv ≠ rChk by omega), hrPiv8]
    simp only [eq_self, if_true, hpiv_sp0] at hfilt1 hpw1
    have hlenL : (xs.filter (fun x => decide (x < piv))).length = cntLt xs piv := by
      simp [cntLt, List.countP_eq_length_filter]
    refine ⟨sp₃, hAll,
      by simp [sp₃, Prim.step, Function.update_of_ne hAct_Mode, hrf1 rActive (by omega),
          sp₀, Function.update_of_ne (show rActive ≠ rChk by omega), hrAct8],
      by simp [sp₃, Prim.step, Function.update_of_ne hCS_CE, hpf1 pCurStart hCS_1 hCS_2, sp₀, hpcs8],
      Or.inl ⟨hkLt, by simp [sp₃, Prim.step],
        by simp [sp₃, Prim.step, Function.update_of_ne hMode_K.symm, hrf1 rK (by omega),
            sp₀, Function.update_of_ne (show rK ≠ rChk by omega), hrK8],
        by simpa [sp₃, sp₀, Prim.step, hpcs8] using hfilt1,
        by simp [sp₃, Prim.step, hpw1, sp₀, hpcs8, hlenL]⟩⟩
  · -- `cntLt xs piv ≤ k`
    have hleLt : cntLt xs piv ≤ k := not_lt.mp hkLt
    have hle0 : sp₀.regs rChk ≤ 0 := by
      simp only [sp₀, Prim.step, Function.update_self, hlt8, hrK8]
      have hc : (cntLt xs piv : ℝ) ≤ (k : ℝ) := by exact_mod_cast hleLt
      linarith
    have q1 : SpecRun rMin pMin memBound (.prim (.sub rChk rLe rK)) sp₀ _ 1 :=
      SpecRun.prim (show rMin ≤ rChk by omega) (by intro _ _ h; cases h)
    set sp₁ := (Prim.sub rChk rLe rK).step sp₀
    by_cases hkLe : k < cntLe xs piv
    · -- Branch 2: `cntLt ≤ k < cntLe` (`pivot` already wins!)
      have hnotle1 : ¬ sp₁.regs rChk ≤ 0 := by
        simp only [sp₁, sp₀, Prim.step, Function.update_self,
          Function.update_of_ne (show rLe ≠ rChk by omega),
          Function.update_of_ne (show rK ≠ rChk by omega), hle8, hrK8]
        have hc : (k : ℝ) + 1 ≤ (cntLe xs piv : ℝ) := by exact_mod_cast hkLe
        linarith
      have q2 : SpecRun rMin pMin memBound (.prim (.const rMode 2)) sp₁ _ 1 :=
        SpecRun.prim hMode (by intro _ _ h; cases h)
      set sp₂ := (Prim.const rMode 2).step sp₁
      have hPart : SpecRun rMin pMin memBound partStmt sw₈ sp₂ _ :=
        q0.seq (SpecRun.ifLeZero_true (e := _) hle0
          (q1.seq (SpecRun.ifLeZero_false (t := _) hnotle1 q2)))
      have hAll : SpecRun rMin pMin memBound _ s sp₂ (24 * xs.length + 50) :=
        (p1.seq (p2'.seq (p3.seq
          (SpecRun.ifLeZero_false (t := .prim (.const rActive 0)) hnotle_hdr (hWalk.seq hPart))))).mono
          (by omega)
      refine ⟨sp₂, hAll,
        by simp [sp₂, sp₁, sp₀, Prim.step, Function.update_of_ne hAct_Mode,
            Function.update_of_ne (show rActive ≠ rChk by omega), hrAct8],
        by simp [sp₂, sp₁, sp₀, Prim.step, hpcs8],
        Or.inr (Or.inl ⟨hleLt, hkLe, by simp [sp₂, Prim.step],
          by simp [sp₂, sp₁, sp₀, Prim.step, Function.update_of_ne hMode_Out.symm,
              Function.update_of_ne (show rOut ≠ rChk by omega), hrOut8],
          by simp [sp₂, sp₁, sp₀, Prim.step, hmem8_eq]⟩)⟩
    · -- Branch 3: `cntLe xs piv ≤ k`
      have hleLe : cntLe xs piv ≤ k := not_lt.mp hkLe
      have hle1 : sp₁.regs rChk ≤ 0 := by
        simp only [sp₁, sp₀, Prim.step, Function.update_self,
          Function.update_of_ne (show rLe ≠ rChk by omega),
          Function.update_of_ne (show rK ≠ rChk by omega), hle8, hrK8]
        have hc : (cntLe xs piv : ℝ) ≤ (k : ℝ) := by exact_mod_cast hleLe
        linarith
      obtain ⟨sp₂, qf, hfilt2, hpw2, hrf2, hpf2⟩ :=
        filterCmpStmt_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) false
          (pStart := pCurStart) (pEnd := pCurEnd) (pRead := pScan1) (pWrite := pScan2)
          (rPiv := rPiv) (rScr := rSub) (xs := xs) (s := sp₁)
          (by simp [sp₁, sp₀, Prim.step, hpcs8, hmem8_eq]; exact hxs)
          (by simp [sp₁, sp₀, Prim.step, hpce8, hpcs8])
          (by simp [sp₁, sp₀, Prim.step, hpcs8]; exact hmB)
          (by omega) hp1 hp2 h1_2 hCS_1.symm hCE_1.symm hCS_2.symm hCE_2.symm (by omega)
      have qf2 : SpecRun rMin pMin memBound (.prim (.pcopy pCurEnd pScan2)) sp₂ _ 1 := sprim
      have qf3 : SpecRun rMin pMin memBound (.prim (.sub rK rK rLe))
          ((Prim.pcopy pCurEnd pScan2).step sp₂) _ 1 := sprim
      have qf4 : SpecRun rMin pMin memBound (.prim (.const rMode 1))
          ((Prim.sub rK rK rLe).step ((Prim.pcopy pCurEnd pScan2).step sp₂)) _ 1 := sprim
      set sp₄ := (Prim.const rMode 1).step
        ((Prim.sub rK rK rLe).step ((Prim.pcopy pCurEnd pScan2).step sp₂))
      have hPart : SpecRun rMin pMin memBound partStmt sw₈ sp₄ _ :=
        q0.seq (SpecRun.ifLeZero_true (e := _) hle0
          (q1.seq (SpecRun.ifLeZero_true (e := _) hle1 (qf.seq (qf2.seq (qf3.seq qf4))))))
      have hAll : SpecRun rMin pMin memBound _ s sp₄ (24 * xs.length + 50) :=
        (p1.seq (p2'.seq (p3.seq
          (SpecRun.ifLeZero_false (t := .prim (.const rActive 0)) hnotle_hdr (hWalk.seq hPart))))).mono
          (by omega)
      have hpiv_sp1 : sp₁.regs rPiv = piv := by
        simp [sp₁, sp₀, Prim.step, Function.update_of_ne (show rPiv ≠ rChk by omega), hrPiv8]
      simp only [Bool.false_eq_true, if_false, hpiv_sp1] at hfilt2 hpw2
      have hlenG : (xs.filter (fun x => decide (piv < x))).length = cntGt xs piv := by
        simp [cntGt, List.countP_eq_length_filter]
      have hsub_nat : (k : ℝ) - (cntLe xs piv : ℝ) = ((k - cntLe xs piv : ℕ) : ℝ) := by
        rw [Nat.cast_sub hleLe]
      refine ⟨sp₄, hAll,
        by simp [sp₄, Prim.step, Function.update_of_ne hAct_Mode, Function.update_of_ne hAct_K,
            hrf2 rActive (by omega), sp₁, sp₀, Function.update_of_ne (show rActive ≠ rChk by omega), hrAct8],
        by simp [sp₄, Prim.step, Function.update_of_ne hCS_CE, hpf2 pCurStart hCS_1 hCS_2, sp₁, sp₀, hpcs8],
        Or.inr (Or.inr ⟨hleLe, by simp [sp₄, Prim.step],
          by simp [sp₄, Prim.step, Function.update_of_ne hMode_K.symm,
              hrf2 rK (by omega), hrf2 rLe (by omega), sp₁, sp₀,
              Function.update_of_ne (show rK ≠ rChk by omega),
              Function.update_of_ne (show rLe ≠ rChk by omega), hrK8, hle8, hsub_nat],
          by simpa [sp₄, sp₁, sp₀, Prim.step, hpcs8] using hfilt2,
          by simp [sp₄, Prim.step, hpw2, sp₁, sp₀, hpcs8, hlenG]⟩)⟩

/-- Body of the single iterative BFPRT `whilePos rActive` loop.
Register layout starting at `rBase` (`16` regs: `rBase .. rBase + 15`):
- `rActive = rBase`
- `rMode   = rBase + 1` (`1` = SOLVE, `2` = RETURN)
- `rK      = rBase + 2`
- `rModeCh = rBase + 3`
- `rScr    = rBase + 4 .. rBase + 15` (`12` scratch regs)
Pointer layout starting at `pBase` (`5` ptrs: `pBase .. pBase + 4`):
- `pCurStart = pBase`, `pCurEnd = pBase + 1`, `pScan1 = pBase + 2`, `pScan2 = pBase + 3`, `pLimit = pBase + 4`. -/
noncomputable def bfprtLoopBody (rOut rBase pBase : ℕ) : Stmt :=
  let rActive := rBase
  let rMode   := rBase + 1
  let rK      := rBase + 2
  let rModeCh := rBase + 3
  let rScr    := rBase + 4
  let pCurStart := pBase
  let pCurEnd   := pBase + 1
  let pScan1    := pBase + 2
  let pScan2    := pBase + 3
  let pLimit    := pBase + 4
  let mode1Stmt : Stmt :=
    .seq (.seq (.prim (.pcopy pLimit pCurStart)) (advancePtrByConst 100 pLimit))
      (.ifPtrLe pCurEnd pLimit
        (.seq (baseSelectStmt rOut pCurStart pCurEnd rK rScr pScan1 pScan2)
          (.prim (.const rMode 2)))
        (pushMediansStmt pCurStart pCurEnd rK rScr pScan1 pScan2 pLimit))
  let mode2Stmt : Stmt :=
    popOrPartitionStmt rActive rMode rOut rK pCurStart pCurEnd rScr pScan1 pScan2
  .seq (.prim (.const rModeCh 1))
    (.seq (.prim (.sub rModeCh rMode rModeCh))
      (.ifLeZero rModeCh mode1Stmt mode2Stmt))

set_option maxHeartbeats 800000 in
/-- Strong-induction frame solver on `N = xs.length` inside `whilePos rActive (bfprtLoopBody ...)`. -/
theorem bfprt_solve_frame {rMin pMin rOut rBase pBase : ℕ}
    (hOut : rMin ≤ rOut) (hrB : rMin ≤ rBase) (hpB : pMin ≤ pBase)
    (hOutB : rOut < rBase) :
    ∀ (N : ℕ) (xs : List ℝ) (k : ℕ) (base : ℤ) (s : MState),
      xs.length = N →
      k < N →
      s.regs rBase = 1 →
      s.regs (rBase + 1) = 1 →
      s.regs (rBase + 2) = (k : ℝ) →
      s.ptrs pBase = base →
      s.ptrs (pBase + 1) = base + (N : ℤ) →
      ListAt s.mem base xs →
      ∃ s', LoopStep rMin pMin base rBase (bfprtLoopBody rOut rBase pBase)
          s s' (110000 * (N + 1)) ∧
        s'.regs rBase = 1 ∧
        s'.regs (rBase + 1) = 2 ∧
        s'.ptrs pBase = base ∧
        IsKthOrder xs k (s'.regs rOut) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro xs k base s hlen hk hAct hMode hrK hpCS hpCE hxs
    subst hlen
    let rActive := rBase
    let rMode   := rBase + 1
    let rK      := rBase + 2
    let rModeCh := rBase + 3
    let rScr    := rBase + 4
    let pCurStart := pBase
    let pCurEnd   := pBase + 1
    let pScan1    := pBase + 2
    let pScan2    := pBase + 3
    let pLimit    := pBase + 4
    have hposAct : 0 < s.regs rActive := by rw [hAct]; norm_num
    -- Prefix of `bfprtLoopBody`: check `rMode - 1 ≤ 0` (true since `rMode = 1`)
    have pre1 : SpecRun rMin pMin base (.prim (.const rModeCh 1)) s _ 1 := sprim
    have pre2 : SpecRun rMin pMin base (.prim (.sub rModeCh rMode rModeCh))
        ((Prim.const rModeCh 1).step s) _ 1 := sprim
    set s₀ := (Prim.sub rModeCh rMode rModeCh).step ((Prim.const rModeCh 1).step s)
    have hcondMode1 : s₀.regs rModeCh ≤ 0 := by
      simp [s₀, Prim.step, Function.update_of_ne (show rMode ≠ rModeCh by omega), rMode, hMode]
    -- Check `N ≤ 100`
    have cL1 : SpecRun rMin pMin base (.prim (.pcopy pLimit pCurStart)) s₀ _ 1 :=
      SpecRun.prim (show pMin ≤ pLimit by omega) (by intro _ _ h; cases h)
    have cL2 := advancePtrByConst_spec (rMin := rMin) (pMin := pMin) (memBound := base)
      100 (q := pLimit) (by omega) ((Prim.pcopy pLimit pCurStart).step s₀)
    set s₁ : MState := ⟨s₀.regs, Function.update s.ptrs pLimit (base + 100), s.mem⟩
    have cL2' : SpecRun rMin pMin base (advancePtrByConst 100 pLimit)
        ((Prim.pcopy pLimit pCurStart).step s₀) s₁ 100 := by
      convert cL2 using 1; simp [s₁, s₀, Prim.step, Function.update_idem, pCurStart, hpCS]
    by_cases hN100 : xs.length ≤ 100
    · -- Base case `N ≤ 100`: 1 loop iteration solves directly!
      have hptrLe : s₁.ptrs pCurEnd ≤ s₁.ptrs pLimit := by
        simp [s₁, Function.update_of_ne (show pCurEnd ≠ pLimit by omega), pCurEnd, hpCE]; omega
      obtain ⟨s₂, hBase, hkth2, hregs2, hptrs2, hmem2⟩ :=
        baseSelectStmt_spec (rMin := rMin) (pMin := pMin) (memBound := base)
          (rOut := rOut) (pStart := pCurStart) (pEnd := pCurEnd) (rK := rK)
          (rScr := rScr) (pOuter := pScan1) (pScan := pScan2) (xs := xs) (k := k) (s := s₁)
          (by simp [s₁, Function.update_of_ne (show pCurStart ≠ pLimit by omega), pCurStart, hpCS]; exact hxs)
          (by simp [s₁, Function.update_of_ne (show pCurEnd ≠ pLimit by omega),
              Function.update_of_ne (show pCurStart ≠ pLimit by omega), pCurEnd, pCurStart, hpCE, hpCS])
          hk (by simp [s₁, s₀, Prim.step, Function.update_of_ne (show rK ≠ rModeCh by omega), rK, hrK])
          hOut (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
      have setM2 : SpecRun rMin pMin base (.prim (.const rMode 2)) s₂ _ 1 :=
        SpecRun.prim (show rMin ≤ rMode by omega) (by intro _ _ h; cases h)
      set s₃ := (Prim.const rMode 2).step s₂
      have hBody : SpecRun rMin pMin base (bfprtLoopBody rOut rBase pBase) s s₃ _ :=
        pre1.seq (pre2.seq (SpecRun.ifLeZero_true (e := _) hcondMode1
          ((cL1.seq cL2').seq (SpecRun.ifPtrLe_true (e := _) hptrLe (hBase.seq setM2)))))
      have hBound : 1 + (1 + (1 + 100 + (xs.length * (10 * xs.length + 25) + 5 + 1 + 1) + 1)) + 2 ≤
          110000 * (xs.length + 1) := by clear * - hN100; nlinarith
      refine ⟨s₃, (LoopStep.single hposAct hBody).mono hBound,
        by simp [s₃, Prim.step, Function.update_of_ne (show rActive ≠ rMode by omega),
            hregs2 rActive (by omega) (by omega), s₁, s₀,
            Function.update_of_ne (show rActive ≠ rModeCh by omega), rActive, hAct],
        by simp [s₃, Prim.step, rMode],
        by simp [s₃, Prim.step, hptrs2 pCurStart (by omega) (by omega), s₁,
            Function.update_of_ne (show pCurStart ≠ pLimit by omega), pCurStart, hpCS],
        by simpa [s₃, Prim.step, Function.update_of_ne (show rOut ≠ rMode by omega)] using hkth2⟩
    · -- Recursive case `N > 100`:
      have hN101 : 101 ≤ xs.length := by omega
      have hptrGt : ¬ s₁.ptrs pCurEnd ≤ s₁.ptrs pLimit := by
        simp [s₁, Function.update_of_ne (show pCurEnd ≠ pLimit by omega), pCurEnd, hpCE]; omega
      -- Step A: `pushMediansStmt` (1 loop iteration)
      obtain ⟨sA, hPush, hxsA, hHdr0A, hHdr1A, hHdr2A, hmedsA, hpCSA, hpCEA, hrKA, hregsA, _⟩ :=
        pushMediansStmt_spec (rMin := rMin) (pMin := pMin) (memBound := base)
          (pCurStart := pCurStart) (pCurEnd := pCurEnd) (rK := rK) (rScr := rScr)
          (pScan1 := pScan1) (pScan2 := pScan2) (pLimit := pLimit)
          (xs := xs) (k := k) (s := s₁)
          (by simp [s₁, Function.update_of_ne (show pCurStart ≠ pLimit by omega), pCurStart, hpCS]; exact hxs)
          (by simp [s₁, Function.update_of_ne (show pCurEnd ≠ pLimit by omega),
              Function.update_of_ne (show pCurStart ≠ pLimit by omega), pCurEnd, pCurStart, hpCE, hpCS])
          (by omega)
          (by simp [s₁, s₀, Prim.step, Function.update_of_ne (show rK ≠ rModeCh by omega), rK, hrK])
          (by simp [s₁, Function.update_of_ne (show pCurStart ≠ pLimit by omega), pCurStart, hpCS])
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by simp [List.nodup_cons]; omega) (by omega)
      have hs1_pCS : s₁.ptrs pCurStart = base := by
        simp [s₁, Function.update_of_ne (show pCurStart ≠ pLimit by omega), pCurStart, hpCS]
      rw [hs1_pCS] at hxsA hHdr0A hHdr1A hHdr2A hmedsA hpCSA hpCEA
      set childBase := base + (xs.length : ℤ) + 3
      have hBodyA : SpecRun rMin pMin base (bfprtLoopBody rOut rBase pBase) s sA _ :=
        pre1.seq (pre2.seq (SpecRun.ifLeZero_true (e := _) hcondMode1
          ((cL1.seq cL2').seq (SpecRun.ifPtrLe_false (t := _) hptrGt hPush))))
      have hLoopA : LoopStep rMin pMin base rBase (bfprtLoopBody rOut rBase pBase) s sA
          (25 * xs.length + 160) :=
        (LoopStep.single hposAct hBodyA).mono (by omega)
      have hActA : sA.regs rActive = 1 := by
        rw [hregsA rActive (by omega) (by omega)]
        simp [s₁, s₀, Prim.step, Function.update_of_ne (show rActive ≠ rModeCh by omega), rActive, hAct]
      have hModeA : sA.regs rMode = 1 := by
        rw [hregsA rMode (by omega) (by omega)]
        simp [s₁, s₀, Prim.step, Function.update_of_ne (show rMode ≠ rModeCh by omega), rMode, hMode]
      -- Step B: IH Call 1 on `medsOf5 xs` (`g = xs.length / 5 < xs.length`)
      set g := xs.length / 5
      obtain ⟨sB, hLoopB_raw, hActB, hModeB, hpCSB, hkthPiv⟩ :=
        ih g (by omega) (medsOf5 xs) (g / 2) childBase sA
          (by simp [medsOf5, g]) (by omega) hActA hModeA hrKA hpCSA hpCEA hmedsA
      have hLoopB : LoopStep rMin pMin base rBase (bfprtLoopBody rOut rBase pBase) sA sB
          (110000 * (g + 1)) :=
        hLoopB_raw.weakenFrame le_rfl le_rfl (by dsimp [childBase]; omega)
      -- Because `hLoopB_raw` preserved `< childBase`, `xs` and parent header are untouched!
      have hxsB : ListAt sB.mem base xs :=
        hxsA.of_mem_pres hLoopB_raw.mem_pres (by dsimp [childBase]; omega)
      have hHdr0B : sB.mem (base + (xs.length : ℤ)) = 1 :=
        (hLoopB_raw.mem_pres _ (by dsimp [childBase]; omega)).trans hHdr0A
      have hHdr1B : sB.mem (base + (xs.length : ℤ) + 1) = (xs.length : ℝ) :=
        (hLoopB_raw.mem_pres _ (by dsimp [childBase]; omega)).trans hHdr1A
      have hHdr2B : sB.mem (base + (xs.length : ℤ) + 2) = (k : ℝ) :=
        (hLoopB_raw.mem_pres _ (by dsimp [childBase]; omega)).trans hHdr2A
      -- Step C: 1 loop iteration in Mode 2 (`popOrPartitionStmt`)
      set piv := sB.regs rOut
      obtain ⟨hBfprtLt, hBfprtGt⟩ := bfprt_three_tenths_bounds xs piv hkthPiv
      have hposActB : 0 < sB.regs rActive := by rw [hActB]; norm_num
      have preB1 : SpecRun rMin pMin base (.prim (.const rModeCh 1)) sB _ 1 := sprim
      have preB2 : SpecRun rMin pMin base (.prim (.sub rModeCh rMode rModeCh))
          ((Prim.const rModeCh 1).step sB) _ 1 := sprim
      set sB₀ := (Prim.sub rModeCh rMode rModeCh).step ((Prim.const rModeCh 1).step sB)
      have hcondMode2 : ¬ sB₀.regs rModeCh ≤ 0 := by
        simp [sB₀, Prim.step, Function.update_of_ne (show rMode ≠ rModeCh by omega), rMode, hModeB]
      obtain ⟨sC, hPop, hActC, hpCSC, hCases⟩ :=
        popOrPartitionStmt_parent_spec (rMin := rMin) (pMin := pMin) (memBound := base)
          (rActive := rActive) (rMode := rMode) (rOut := rOut) (rK := rK)
          (pCurStart := pCurStart) (pCurEnd := pCurEnd) (rScr := rScr)
          (pScan1 := pScan1) (pScan2 := pScan2) (xs := xs) (k := k) (base := base) (s := sB₀)
          (by simp [sB₀, Prim.step, pCurStart, hpCSB, childBase])
          (by simp [sB₀, Prim.step]; exact hxsB)
          (by simp [sB₀, Prim.step]; exact hHdr0B)
          (by simp [sB₀, Prim.step]; exact hHdr1B)
          (by simp [sB₀, Prim.step]; exact hHdr2B)
          le_rfl
          (by simp [sB₀, Prim.step, Function.update_of_ne (show rActive ≠ rModeCh by omega), rActive, hActB])
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by simp [List.nodup_cons]; omega)
          (by simp [List.nodup_cons]; omega)
          (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl <;> omega)
      have hpivB0 : sB₀.regs rOut = piv := by
        simp [sB₀, Prim.step, Function.update_of_ne (show rOut ≠ rModeCh by omega), piv]
      simp only [hpivB0] at hCases
      have hBodyC : SpecRun rMin pMin base (bfprtLoopBody rOut rBase pBase) sB sC _ :=
        preB1.seq (preB2.seq (SpecRun.ifLeZero_false (t := _) hcondMode2 hPop))
      have hLoopC_step : LoopStep rMin pMin base rBase (bfprtLoopBody rOut rBase pBase) sB sC
          (24 * xs.length + 60) :=
        (LoopStep.single hposActB hBodyC).mono (by omega)
      rcases hCases with ⟨hkLt, hModeC, hrKC, hfiltL, hpCEC⟩ |
                         ⟨hleLt, hkLe, hModeC, houtC, _⟩ |
                         ⟨hleLe, hModeC, hrKC, hfiltG, hpCEC⟩
      · -- Subcase C1: tail Call 2 on `xsL` (`cntLt xs piv ≤ 7 * N / 10 + 3 < N`)
        set NL := cntLt xs piv
        have hlenL : (xs.filter (fun x => decide (x < piv))).length = NL := by
          simp [NL, cntLt, List.countP_eq_length_filter]
        have hNL_bound : NL ≤ 7 * xs.length / 10 + 3 := by omega
        obtain ⟨sD, hLoopD, hActD, hModeD, hpCSD, hkthD⟩ :=
          ih NL (by omega) (xs.filter (fun x => decide (x < piv))) k base sC
            hlenL hkLt hActC hModeC hrKC hpCSC hpCEC hfiltL
        refine ⟨sD, ((hLoopA.trans hLoopB).trans (hLoopC_step.trans hLoopD)).mono (by omega),
          hActD, hModeD, hpCSD, isKthOrder_of_filter_lt hkthD⟩
      · -- Subcase C2: `piv` already wins!
        refine ⟨sC, ((hLoopA.trans hLoopB).trans hLoopC_step).mono (by omega),
          hActC, hModeC, hpCSC, ?_⟩
        rw [houtC]
        exact ⟨medsOf5_subset hkthPiv.1, hleLt, hkLe⟩
      · -- Subcase C3: tail Call 2 on `xsG` (`cntGt xs piv ≤ 7 * N / 10 + 3 < N`)
        set NG := cntGt xs piv
        have hlenG : (xs.filter (fun x => decide (piv < x))).length = NG := by
          simp [NG, cntGt, List.countP_eq_length_filter]
        have hsum := cntLe_add_cntGt xs piv
        have hkG : k - cntLe xs piv < NG := by omega
        have hNG_bound : NG ≤ 7 * xs.length / 10 + 3 := by omega
        obtain ⟨sD, hLoopD, hActD, hModeD, hpCSD, hkthD⟩ :=
          ih NG (by omega) (xs.filter (fun x => decide (piv < x))) (k - cntLe xs piv) base sC
            hlenG hkG hActC hModeC hrKC hpCSC hpCEC hfiltG
        refine ⟨sD, ((hLoopA.trans hLoopB).trans (hLoopC_step.trans hLoopD)).mono (by omega),
          hActD, hModeD, hpCSD, isKthOrder_of_filter_gt hleLe hkthD⟩

/-- Top-level deterministic linear-time median selector on `[pArrStart .. pArrEnd)`.
If `pArrEnd ≤ pArrStart` (`N = 0`), writes `0` to `rOut`.
Otherwise copies `[pArrStart .. pArrEnd)` into `[pArena + 3 .. pArena + 3 + N)` (with root
header `(0, 0, 0)` at `[pArena .. pArena + 3)`), computes `k₀ = N / 2`, runs the iterative
BFPRT loop, and puts `c` in `rOut` with `2 * #{< c} ≤ N` and `2 * #{> c} ≤ N`.
Requires `16` scratch regs `rBase .. rBase + 15` (`rOut < rBase`) and `5` scratch ptrs `pBase .. pBase + 4`. -/
noncomputable def selectMedianStmt (rOut pArrStart pArrEnd pArena rBase pBase : ℕ) : Stmt :=
  let rActive := rBase
  let rMode   := rBase + 1
  let rK      := rBase + 2
  let rOne    := rBase + 4
  let rPar    := rBase + 5
  let rVal    := rBase + 6
  let pCurStart := pBase
  let pCurEnd   := pBase + 1
  let pScan1    := pBase + 2
  let initPreStmt : Stmt :=
    Stmt.block [
      .prim (.pcopy pCurEnd pArena),
      .prim (.const rVal 0),
      .prim (.store pCurEnd rVal), .prim (.pinc pCurEnd),
      .prim (.store pCurEnd rVal), .prim (.pinc pCurEnd),
      .prim (.store pCurEnd rVal), .prim (.pinc pCurEnd),
      .prim (.pcopy pCurStart pCurEnd),
      .prim (.pcopy pScan1 pArrStart),
      .prim (.const rOne 1),
      .prim (.const rPar 0),
      .prim (.const rK 0)]
  let initCopyStmt : Stmt :=
    .seq initPreStmt
      (.seq
        (.whilePtrLt pScan1 pArrEnd
          (.seq (.seq (.prim (.load rVal pScan1)) (.prim (.pinc pScan1)))
            (.seq (.seq (.prim (.store pCurEnd rVal)) (.prim (.pinc pCurEnd)))
              (.ifLeZero rPar
                (.prim (.const rPar 1))
                (.seq (.prim (.const rPar 0)) (.prim (.add rK rK rOne)))))))
        (.seq (.prim (.const rActive 1)) (.prim (.const rMode 1))))
  .ifPtrLe pArrEnd pArrStart
    (.prim (.const rOut 0))
    (.seq initCopyStmt (.whilePos rActive (bfprtLoopBody rOut rBase pBase)))

/-- Constant factor of `selectMedianStmt`: `110050 * (N + 1)` steps. -/
def C_select : ℕ := 110050

private theorem sum_ite_eq_countP_ofFn : ∀ {N : ℕ} (arr : Fin N → ℝ) (q : ℝ → Bool),
    (∑ i : Fin N, if q (arr i) = true then (1 : ℕ) else 0) = (List.ofFn arr).countP q
  | 0, _, _ => by simp
  | _ + 1, arr, q => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.countP_cons,
      ← sum_ite_eq_countP_ofFn (fun j => arr j.succ) q]
    cases q (arr 0)
    · simp
    · simp; omega

set_option maxHeartbeats 800000 in
theorem selectMedianStmt_spec {rMin pMin N : ℕ} {memBound : ℤ}
    {rOut pArrStart pArrEnd pArena rBase pBase : ℕ}
    {arr : Fin N → ℝ} {s : MState}
    (hArr : VecAt s.mem (s.ptrs pArrStart) arr)
    (hEnd : s.ptrs pArrEnd = s.ptrs pArrStart + (N : ℤ))
    (hArrArena : s.ptrs pArrStart + (N : ℤ) ≤ s.ptrs pArena)
    (hmB : memBound ≤ s.ptrs pArena)
    (hOut : rMin ≤ rOut) (hrB : rOut < rBase) (hpB : pMin ≤ pBase)
    (hAS : pArrStart < pBase) (hAE : pArrEnd < pBase) (hAr : pArena < pBase) :
    ∃ s', SpecRun rMin pMin memBound
        (selectMedianStmt rOut pArrStart pArrEnd pArena rBase pBase) s s'
        (C_select * (N + 1)) ∧
      2 * (Finset.univ.filter fun i : Fin N => arr i < s'.regs rOut).card ≤ N ∧
      2 * (Finset.univ.filter fun i : Fin N => s'.regs rOut < arr i).card ≤ N ∧
      (∀ i < rOut, s'.regs i = s.regs i) ∧
      (∀ q < pBase, s'.ptrs q = s.ptrs q) ∧
      MemPreservedBelow (s.ptrs pArena) s.mem s'.mem := by
  suffices hMain : ∃ s', SpecRun rOut pBase (s.ptrs pArena)
        (selectMedianStmt rOut pArrStart pArrEnd pArena rBase pBase) s s'
        (C_select * (N + 1)) ∧
      2 * (Finset.univ.filter fun i : Fin N => arr i < s'.regs rOut).card ≤ N ∧
      2 * (Finset.univ.filter fun i : Fin N => s'.regs rOut < arr i).card ≤ N by
    obtain ⟨s', hrun, hL, hG⟩ := hMain
    exact ⟨s', hrun.weakenFrame hOut hpB hmB, hL, hG, hrun.regs_pres, hrun.ptrs_pres, hrun.mem_pres⟩
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have hle : s.ptrs pArrEnd ≤ s.ptrs pArrStart := by rw [hEnd]; omega
    have p1 : SpecRun rOut pBase (s.ptrs pArena) (.prim (.const rOut 0)) s _ 1 :=
      SpecRun.prim le_rfl (by intro _ _ h; cases h)
    exact ⟨_, (SpecRun.ifPtrLe_true (e := _) hle p1).mono (by unfold C_select; omega),
      by simp, by simp⟩
  · have hOutB : rOut < rBase := hrB
    have hgt : ¬ s.ptrs pArrEnd ≤ s.ptrs pArrStart := by rw [hEnd]; omega
    set arena := s.ptrs pArena
    set xs := List.ofFn arr
    have hxs_in : ListAt s.mem (s.ptrs pArrStart) xs := (vecAt_iff_listAt _ _ _).mp hArr
    have hxs_len : xs.length = N := List.length_ofFn
    let rActive := rBase
    let rMode   := rBase + 1
    let rK      := rBase + 2
    let rModeCh := rBase + 3
    let rOne    := rBase + 4
    let rPar    := rBase + 5
    let rVal    := rBase + 6
    let rScr    := rBase + 4
    let pCurStart := pBase
    let pCurEnd   := pBase + 1
    let pScan1    := pBase + 2
    let pScan2    := pBase + 3
    -- Root header `(0, 0, 0)` at `[arena .. arena + 3)`
    have i1 : SpecRun rBase pBase arena (.prim (.pcopy pCurEnd pArena)) s _ 1 := sprim
    have i2 : SpecRun rBase pBase arena (.prim (.const rVal 0))
        ((Prim.pcopy pCurEnd pArena).step s) _ 1 := sprim
    set si₂ := (Prim.const rVal 0).step ((Prim.pcopy pCurEnd pArena).step s)
    have i3 : SpecRun rBase pBase arena (.prim (.store pCurEnd rVal)) si₂ _ 1 :=
      SpecRun.prim trivial (by intro _ _ h; cases h; simp [si₂, Prim.step, arena])
    set si₃ := (Prim.store pCurEnd rVal).step si₂
    have i4 : SpecRun rBase pBase arena (.prim (.pinc pCurEnd)) si₃ _ 1 := sprim
    set si₄ := (Prim.pinc pCurEnd).step si₃
    have i5 : SpecRun rBase pBase arena (.prim (.store pCurEnd rVal)) si₄ _ 1 :=
      SpecRun.prim trivial (by intro _ _ h; cases h; simp only [si₄, si₃, si₂, Prim.step, Function.update_self, arena]; linarith)
    set si₅ := (Prim.store pCurEnd rVal).step si₄
    have i6 : SpecRun rBase pBase arena (.prim (.pinc pCurEnd)) si₅ _ 1 := sprim
    set si₆ := (Prim.pinc pCurEnd).step si₅
    have i7 : SpecRun rBase pBase arena (.prim (.store pCurEnd rVal)) si₆ _ 1 :=
      SpecRun.prim trivial (by intro _ _ h; cases h; simp only [si₆, si₅, si₄, si₃, si₂, Prim.step, Function.update_self, arena]; linarith)
    set si₇ := (Prim.store pCurEnd rVal).step si₆
    have i8 : SpecRun rBase pBase arena (.prim (.pinc pCurEnd)) si₇ _ 1 := sprim
    set si₈ := (Prim.pinc pCurEnd).step si₇
    have i9 : SpecRun rBase pBase arena (.prim (.pcopy pCurStart pCurEnd)) si₈ _ 1 := sprim
    set si₉ := (Prim.pcopy pCurStart pCurEnd).step si₈
    have i10 : SpecRun rBase pBase arena (.prim (.pcopy pScan1 pArrStart)) si₉ _ 1 := sprim
    set si₁₀ := (Prim.pcopy pScan1 pArrStart).step si₉
    have i11 : SpecRun rBase pBase arena (.prim (.const rOne 1)) si₁₀ _ 1 := sprim
    set si₁₁ := (Prim.const rOne 1).step si₁₀
    have i12 : SpecRun rBase pBase arena (.prim (.const rPar 0)) si₁₁ _ 1 := sprim
    set si₁₂ := (Prim.const rPar 0).step si₁₁
    have i13 : SpecRun rBase pBase arena (.prim (.const rK 0)) si₁₂ _ 1 := sprim
    set sc₀ := (Prim.const rK 0).step si₁₂
    have hInitPre : SpecRun rBase pBase arena _ s sc₀ 13 :=
      (i1.seq (i2.seq (i3.seq (i4.seq (i5.seq (i6.seq (i7.seq (i8.seq (i9.seq
        (i10.seq (i11.seq (i12.seq i13)))))))))))).mono (by omega)
    -- Copy loop (`N` iterations) into `[arena + 3 .. arena + 3 + N)`
    let copyBody : Stmt :=
      .seq (.seq (.prim (.load rVal pScan1)) (.prim (.pinc pScan1)))
        (.seq (.seq (.prim (.store pCurEnd rVal)) (.prim (.pinc pCurEnd)))
          (.ifLeZero rPar
            (.prim (.const rPar 1))
            (.seq (.prim (.const rPar 0)) (.prim (.add rK rK rOne)))))
    let InvCp : ℕ → MState → Prop := fun t st =>
      MemPreservedBelow arena s.mem st.mem ∧
      st.mem arena = 0 ∧
      ListAt st.mem (arena + 3) (xs.take t) ∧
      st.ptrs pCurStart = arena + 3 ∧
      st.ptrs pCurEnd = arena + 3 + (t : ℤ) ∧
      st.ptrs pScan1 = s.ptrs pArrStart + (t : ℤ) ∧
      (∀ q < pBase, st.ptrs q = s.ptrs q) ∧
      st.regs rOne = 1 ∧
      st.regs rPar = ((t % 2 : ℕ) : ℝ) ∧
      st.regs rK = ((t / 2 : ℕ) : ℝ)
    have hInvCp0 : InvCp 0 sc₀ := by
      refine ⟨hInitPre.mem_pres,
        by simp only [sc₀, si₁₂, si₁₁, si₁₀, si₉, si₈, si₇, si₆, si₅, si₄, si₃, si₂, Prim.step, Function.update_self, arena]
           rw [Function.update_of_ne (by linarith), Function.update_of_ne (by linarith), Function.update_self],
        fun i hi => by simp at hi,
        by simp [sc₀, si₁₂, si₁₁, si₁₀, si₉, si₈, si₇, si₆, si₅, si₄, si₃, si₂, Prim.step,
            Function.update_of_ne (show pCurStart ≠ pScan1 by omega), arena]; ring,
        by simp [sc₀, si₁₂, si₁₁, si₁₀, si₉, si₈, si₇, si₆, si₅, si₄, si₃, si₂, Prim.step,
            Function.update_of_ne (show pCurEnd ≠ pScan1 by omega),
            Function.update_of_ne (show pCurEnd ≠ pCurStart by omega), arena]; ring,
        by simp [sc₀, si₁₂, si₁₁, si₁₀, si₉, si₈, si₇, si₆, si₅, si₄, si₃, si₂, Prim.step,
            Function.update_of_ne (show pArrStart ≠ pCurStart by omega),
            Function.update_of_ne (show pArrStart ≠ pCurEnd by omega)],
        hInitPre.ptrs_pres,
        by simp [sc₀, si₁₂, si₁₁, Prim.step, Function.update_of_ne (show rOne ≠ rK by omega),
            Function.update_of_ne (show rOne ≠ rPar by omega)],
        by simp [sc₀, si₁₂, Prim.step, Function.update_of_ne (show rPar ≠ rK by omega)],
        by simp [sc₀, Prim.step]⟩
    have hCopyLoop := SpecRun.forLoop (rMin := rBase) (pMin := pBase) (memBound := arena)
      (q₁ := pScan1) (q₂ := pArrEnd) (body := copyBody) N 8 InvCp
      (fun t ht st hInv => by
        obtain ⟨hmPres, hm0, hlist, hpCS, hpCE, hp1, hpo, hone, hpar, hrk⟩ := hInv
        refine ⟨by rw [hp1, hpo pArrEnd hAE, hEnd]; omega, ?_⟩
        have hval_in : st.mem (st.ptrs pScan1) = xs[t]'(by omega) := by
          rw [hp1, hmPres _ (by omega)]
          exact hxs_in t (by omega)
        have b1 : SpecRun rBase pBase arena (.prim (.load rVal pScan1)) st _ 1 := sprim
        have b2 : SpecRun rBase pBase arena (.prim (.pinc pScan1))
            ((Prim.load rVal pScan1).step st) _ 1 := sprim
        set st₂ := (Prim.pinc pScan1).step ((Prim.load rVal pScan1).step st)
        have hpCE2 : st₂.ptrs pCurEnd = arena + 3 + (t : ℤ) := by
          simp [st₂, Prim.step, Function.update_of_ne (show pCurEnd ≠ pScan1 by omega), hpCE]
        have b3 : SpecRun rBase pBase arena (.prim (.store pCurEnd rVal)) st₂ _ 1 :=
          SpecRun.prim trivial (by intro _ _ h; cases h; rw [hpCE2]; omega)
        have b4 : SpecRun rBase pBase arena (.prim (.pinc pCurEnd))
            ((Prim.store pCurEnd rVal).step st₂) _ 1 := sprim
        set st₄ := (Prim.pinc pCurEnd).step ((Prim.store pCurEnd rVal).step st₂)
        have hlist4 : ListAt st₄.mem (arena + 3) (xs.take (t + 1)) := by
          rw [List.take_succ_eq_append_getElem (by omega)]
          intro i hi
          simp only [List.length_append, List.length_singleton, List.length_take,
            Nat.min_eq_left (show t ≤ xs.length by omega)] at hi
          have hm2 : st₂.mem = st.mem := rfl
          by_cases hlt_i : i < t
          · have htk_t : (xs.take t).length = t := by
              rw [List.length_take, Nat.min_eq_left (by omega)]
            rw [List.getElem_append_left (by omega)]
            simp only [st₄, Prim.step, hpCE2]
            rw [Function.update_of_ne (by omega), hm2]
            exact hlist i (by omega)
          · have heq_i : i = t := by omega
            subst heq_i
            have htk_i : (xs.take i).length = i := by
              rw [List.length_take, Nat.min_eq_left (by omega)]
            simp only [st₄, Prim.step, hpCE2, Function.update_self]
            rw [List.getElem_append_right (by omega)]
            simp only [htk_i, Nat.sub_self, List.getElem_singleton]
            simpa [st₂, Prim.step] using hval_in
        have hm0_4 : st₄.mem arena = 0 := by
          have hm2 : st₂.mem = st.mem := rfl
          simp only [st₄, Prim.step, hpCE2]
          rw [Function.update_of_ne (by omega), hm2, hm0]
        by_cases hpar_e : t % 2 = 0
        · have hle_p : st₄.regs rPar ≤ 0 := by
            simp [st₄, st₂, Prim.step, Function.update_of_ne (show rPar ≠ rVal by omega), hpar, hpar_e]
          have b5 : SpecRun rBase pBase arena (.prim (.const rPar 1)) st₄ _ 1 := sprim
          set st₅ := (Prim.const rPar 1).step st₄
          have hcStep : SpecRun rBase pBase arena copyBody st st₅ 8 :=
            ((b1.seq b2).seq ((b3.seq b4).seq
              (SpecRun.ifLeZero_true (e := _) hle_p b5))).mono (by omega)
          refine ⟨st₅, hcStep, hmPres.trans hcStep.mem_pres, hm0_4, hlist4,
            by simp [st₅, st₄, st₂, Prim.step,
                Function.update_of_ne (show pCurStart ≠ pCurEnd by omega),
                Function.update_of_ne (show pCurStart ≠ pScan1 by omega), hpCS],
            by simp [st₅, st₄, Prim.step, hpCE2]; omega,
            by simp [st₅, st₄, st₂, Prim.step,
                Function.update_of_ne (show pScan1 ≠ pCurEnd by omega), hp1]; omega,
            fun q hq => (hcStep.ptrs_pres q hq).trans (hpo q hq),
            by simp [st₅, st₄, st₂, Prim.step,
                Function.update_of_ne (show rOne ≠ rPar by omega),
                Function.update_of_ne (show rOne ≠ rVal by omega), hone],
            by have hmod1 : (t + 1) % 2 = 1 := by omega
               simp [st₅, Prim.step, hmod1],
            by have : (t + 1) / 2 = t / 2 := by omega
               simp [st₅, st₄, st₂, Prim.step,
                Function.update_of_ne (show rK ≠ rPar by omega),
                Function.update_of_ne (show rK ≠ rVal by omega), hrk, this]⟩
        · have hpar_o : t % 2 = 1 := by omega
          have hnotle_p : ¬ st₄.regs rPar ≤ 0 := by
            simp [st₄, st₂, Prim.step, Function.update_of_ne (show rPar ≠ rVal by omega), hpar, hpar_o]
          have b5 : SpecRun rBase pBase arena (.prim (.const rPar 0)) st₄ _ 1 := sprim
          have b6 : SpecRun rBase pBase arena (.prim (.add rK rK rOne))
              ((Prim.const rPar 0).step st₄) _ 1 := sprim
          set st₆ := (Prim.add rK rK rOne).step ((Prim.const rPar 0).step st₄)
          have hcStep : SpecRun rBase pBase arena copyBody st st₆ 8 :=
            ((b1.seq b2).seq ((b3.seq b4).seq
              (SpecRun.ifLeZero_false (t := _) hnotle_p (b5.seq b6)))).mono (by omega)
          refine ⟨st₆, hcStep, hmPres.trans hcStep.mem_pres, hm0_4, hlist4,
            by simp [st₆, st₄, st₂, Prim.step,
                Function.update_of_ne (show pCurStart ≠ pCurEnd by omega),
                Function.update_of_ne (show pCurStart ≠ pScan1 by omega), hpCS],
            by simp [st₆, st₄, Prim.step, hpCE2]; omega,
            by simp [st₆, st₄, st₂, Prim.step,
                Function.update_of_ne (show pScan1 ≠ pCurEnd by omega), hp1]; omega,
            fun q hq => (hcStep.ptrs_pres q hq).trans (hpo q hq),
            by simp [st₆, st₄, st₂, Prim.step,
                Function.update_of_ne (show rOne ≠ rK by omega),
                Function.update_of_ne (show rOne ≠ rPar by omega),
                Function.update_of_ne (show rOne ≠ rVal by omega), hone],
            by have : (t + 1) % 2 = 0 := by omega
               simp [st₆, Prim.step, Function.update_of_ne (show rPar ≠ rK by omega), this],
            by have : (t + 1) / 2 = t / 2 + 1 := by omega
               simp [st₆, st₄, st₂, Prim.step,
                Function.update_of_ne (show rK ≠ rPar by omega),
                Function.update_of_ne (show rK ≠ rVal by omega),
                Function.update_of_ne (show rOne ≠ rPar by omega),
                Function.update_of_ne (show rOne ≠ rVal by omega), hrk, hone, this, Nat.cast_add]⟩)
      (fun st hInv => by
        obtain ⟨_, _, _, _, _, hp1, hpo, _⟩ := hInv
        rw [hp1, hpo pArrEnd hAE, hEnd])
      N le_rfl sc₀ (by simpa using hInvCp0)
    obtain ⟨sc₁, hcRun, hmPres1, hm0_1, hlist1, hpCS1, hpCE1, _, _, _, _, hrK1⟩ := hCopyLoop
    rw [show xs.take N = xs by rw [← hxs_len, List.take_length]] at hlist1
    have i14 : SpecRun rBase pBase arena (.prim (.const rActive 1)) sc₁ _ 1 := sprim
    have i15 : SpecRun rBase pBase arena (.prim (.const rMode 1))
        ((Prim.const rActive 1).step sc₁) _ 1 := sprim
    set sInit := (Prim.const rMode 1).step ((Prim.const rActive 1).step sc₁)
    have hInitAll : SpecRun rOut pBase arena _ s sInit (10 * N + 16) :=
      ((hInitPre.seq (hcRun.seq (i14.seq i15))).weakenFrame (le_of_lt hOutB) le_rfl le_rfl).mono
        (by omega)
    -- Run `bfprt_solve_frame` (`arena + 3` protects `arena`!)
    obtain ⟨sSolved, hSolve_raw, hActS, hModeS, hpCSS, hkthS⟩ :=
      bfprt_solve_frame (rMin := rOut) (pMin := pBase)
        le_rfl (le_of_lt hOutB) le_rfl hOutB N xs (N / 2) (arena + 3) sInit
        hxs_len (Nat.div_lt_self hNpos (by decide))
        (by simp [sInit, Prim.step, rActive, rMode])
        (by simp [sInit, Prim.step, rMode])
        (by simp [sInit, Prim.step, rMode, rActive]; exact hrK1)
        (by simp [sInit, Prim.step]; exact hpCS1)
        (by simp [sInit, Prim.step]; exact hpCE1)
        (by simp [sInit, Prim.step]; exact hlist1)
    have hm0_S : sSolved.mem arena = 0 :=
      (hSolve_raw.mem_pres arena (by linarith)).trans (by simp [sInit, Prim.step, hm0_1])
    -- Final Mode-2 iteration sees `mem[arena] = 0 ≤ 0` and sets `rActive := 0`!
    have hposActS : 0 < sSolved.regs rActive := by rw [hActS]; norm_num
    have fin1 : SpecRun rOut pBase arena (.prim (.const rModeCh 1)) sSolved _ 1 := sprim
    have fin2 : SpecRun rOut pBase arena (.prim (.sub rModeCh rMode rModeCh))
        ((Prim.const rModeCh 1).step sSolved) _ 1 := sprim
    set sF₀ := (Prim.sub rModeCh rMode rModeCh).step ((Prim.const rModeCh 1).step sSolved)
    have hcondF : ¬ sF₀.regs rModeCh ≤ 0 := by
      simp [sF₀, Prim.step, Function.update_of_ne (show rMode ≠ rModeCh by omega), rMode, hModeS]
    obtain ⟨sEnd, hTopPop, hActEnd, houtEnd⟩ :=
      popOrPartitionStmt_top_spec (rMin := rOut) (pMin := pBase) (memBound := arena)
        (rActive := rActive) (rMode := rMode) (rOut := rOut) (rK := rK)
        (pCurStart := pCurStart) (pCurEnd := pCurEnd) (rScr := rScr)
        (pScan1 := pScan1) (pScan2 := pScan2) (s := sF₀)
        (by simp [sF₀, Prim.step, pCurStart, hpCSS, hm0_S])
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hBodyFin : SpecRun rOut pBase arena (bfprtLoopBody rOut rBase pBase) sSolved sEnd _ :=
      fin1.seq (fin2.seq (SpecRun.ifLeZero_false (t := _) hcondF hTopPop))
    have hFinLoop : LoopStep rOut pBase arena rActive (bfprtLoopBody rOut rBase pBase)
        sSolved sEnd 25 :=
      (LoopStep.single hposActS hBodyFin).mono (by omega)
    have hSolve : LoopStep rOut pBase arena rActive (bfprtLoopBody rOut rBase pBase)
        sInit sSolved (110000 * (N + 1)) :=
      hSolve_raw.weakenFrame le_rfl le_rfl (by linarith)
    have hWhile : SpecRun rOut pBase arena (.whilePos rActive (bfprtLoopBody rOut rBase pBase))
        sInit sEnd (110000 * (N + 1) + 26) :=
      ((hSolve.trans hFinLoop).finish hActEnd).mono (by omega)
    have hTotal : SpecRun rOut pBase arena
        (selectMedianStmt rOut pArrStart pArrEnd pArena rBase pBase) s sEnd
        (C_select * (N + 1)) :=
      (SpecRun.ifPtrLe_false (t := .prim (.const rOut 0)) hgt (hInitAll.seq hWhile)).mono
        (by unfold C_select; omega)
    have hout_eq : sEnd.regs rOut = sSolved.regs rOut := by
      rw [houtEnd]; simp [sF₀, Prim.step, Function.update_of_ne (show rOut ≠ rModeCh by omega)]
    rw [← hxs_len] at hkthS
    obtain ⟨hmedL, hmedG⟩ := median_of_isKthOrder hkthS
    rw [hxs_len, ← hout_eq] at hmedL hmedG
    have hcardL : (Finset.univ.filter fun i : Fin N => arr i < sEnd.regs rOut).card =
        cntLt xs (sEnd.regs rOut) := by
      rw [Finset.card_filter]
      simpa [xs, cntLt] using sum_ite_eq_countP_ofFn arr (fun x => decide (x < sEnd.regs rOut))
    have hcardG : (Finset.univ.filter fun i : Fin N => sEnd.regs rOut < arr i).card =
        cntGt xs (sEnd.regs rOut) := by
      rw [Finset.card_filter]
      simpa [xs, cntGt] using sum_ite_eq_countP_ofFn arr (fun x => decide (sEnd.regs rOut < x))
    exact ⟨sEnd, hTotal, hcardL ▸ hmedL, hcardG ▸ hmedG⟩

end MegiddoLP.Selection


