-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:23.516732+00:00
-- url     : https://prove2.me/theorems/eeb5c96a-3a15-4394-8d5a-f3b818d403da
-- title:
--   St Sheet Comass
-- statement:
--   Definitions and structural lemmas for St Sheet Comass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSheetComass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
variable {n d : ℕ}
def sheetJac (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ) : ℝ :=
  areaJacobian ((WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
    ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap)
def SheetComass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ), (∀ k, SmoothNear (zeroSet J) (φ k)) →
    ∃ C : ℝ, ∀ x ∈ zeroSet J ∩ Metric.closedBall 0 R, ∀ s : (Fin d → ℂ) → Fin n → ℂ, IsSheetAt J A x s →
      |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ x)| ≤ C * sheetJac s (A *ᵥ x)
end
end GroundTheory.Heights₂.Heights


