-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_PositiveRepair
-- name    : InfoLossLAR_Native_AFT_PositiveRepair
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:19:01.128936+00:00
-- url     : https://prove2.me/theorems/ccdc3ca9-2247-4652-ac9c-8e9b546e35a0
-- title:
--   Positive and negative parts of a finite signed mass
-- statement:
--   For a real signed mass $w$ on a finite set, define $$M_+(w)=\sum_x\max\{w(x),0\},\quad M_-(w)=\sum_x\max\{-w(x),0\},\quad M(w)=\sum_x w(x).$$ These satisfy $M_+(w)=M(w)+M_-(w)$. If $M(w)>0$, the positive part divided by $M_+(w)$ is a probability law. This supplies the normalization interface for clipping signed weights.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/PositiveRepair.lean; migrated source SHA256 9c03c408fe99f35f2581d5d2ebc00c23d73bd926bf820b258d79794cd8600350; byte-range skeleton from Lean AST, with original retained definitions and proofs.

import Mathlib


/-!
# Conditional positive repair

V7 Lemma 9.19 clips a signed weight separately at each retained skeleton.
Here `weight` is the signed mass function at any one fixed skeleton. The
identity below is exact and does not require that its entries be positive.
The separate task of bounding the physical moments is not assumed proved.
-/

namespace AFT

open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def positiveMass (weight : α → ℝ) : ℝ := ∑ a, max (weight a) 0
noncomputable def negativeMass (weight : α → ℝ) : ℝ := ∑ a, max (-weight a) 0
noncomputable def signedMass (weight : α → ℝ) : ℝ := ∑ a, weight a

theorem negativeMass_nonneg (weight : α → ℝ) : 0 ≤ negativeMass weight :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem positiveMass_eq (weight : α → ℝ) :
    positiveMass weight = signedMass weight + negativeMass weight := by
  rw [positiveMass, signedMass, negativeMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : 0 ≤ weight a
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
  · have hn : weight a ≤ 0 := le_of_not_ge h
    rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
    ring

theorem positiveMass_pos (weight : α → ℝ) (hmean : 0 < signedMass weight) :
    0 < positiveMass weight := by
  rw [positiveMass_eq]
  exact add_pos_of_pos_of_nonneg hmean (negativeMass_nonneg weight)





/-- The normalized positive part is a probability mass function. -/
theorem positive_repair_normalized (weight : α → ℝ) (hmean : 0 < signedMass weight) :
    (∀ a, 0 ≤ max (weight a) 0 / positiveMass weight) ∧
      (∑ a, max (weight a) 0 / positiveMass weight) = 1 := by
  have hpos := positiveMass_pos weight hmean
  constructor
  · intro a
    exact div_nonneg (le_max_right _ _) hpos.le
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)





end AFT


