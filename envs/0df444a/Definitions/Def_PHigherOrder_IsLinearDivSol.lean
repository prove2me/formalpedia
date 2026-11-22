-- Prove2me | Definitions.Def_PHigherOrder_IsLinearDivSol
-- name    : PHigherOrder_IsLinearDivSol
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:09:15.305962+00:00
-- url     : https://prove2.me/theorems/3d5943bd-fba6-4068-bad2-40dd139c29d2
-- title:
--   Is Linear Div Sol
-- statement:
--   Definitions and structural lemmas for Is Linear Div Sol, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IsLinearDivSol.lean

import Definitions.Def_PHigherOrder_Plane
set_option autoImplicit false
structure IsLinearDivSol (Ω : Set Plane) (A : Plane → (Plane →L[ℝ] Plane))
    (w : Plane → ℝ) (G : Plane → Plane) : Prop where
  contW : ContinuousOn w Ω
  measG : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict Ω)
  locSqIntG : ∀ K : Set Plane, K ⊆ Ω → IsCompact K →
      MeasureTheory.IntegrableOn (fun x => ‖G x‖ ^ 2) K
  weakGrad : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, w x • gradient φ x = - ∫ x in Ω, φ x • G x
  eqn : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, inner ℝ (A x (G x)) (gradient φ x) = (0 : ℝ)


