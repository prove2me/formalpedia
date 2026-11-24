-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:58.802863+00:00
-- url     : https://prove2.me/theorems/134f7981-e552-4069-a030-9506248e1611
-- title:
--   Statements Cone Sheet Area Lintegral
-- statement:
--   Definitions and structural lemmas for Statements Cone Sheet Area Lintegral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeSheetAreaLintegral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal
def ConeSheetAreaLintegral.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → Measurable F →
      AEMeasurable (fun x : Fin e → ℂ => ∑ᶠ w ∈ fibre P Ψ x, ∫⁻ t : ℂ,
          F (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) *
              gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)) ∧
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P), F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∫⁻ x : Fin e → ℂ, ∑ᶠ w ∈ fibre P Ψ x, ∫⁻ t : ℂ,
            F (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
              ENNReal.ofReal (‖t‖ ^ (2 * e) *
                gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)
end GroundTheory.Heights₂.Heights


