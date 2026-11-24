-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:25.569419+00:00
-- url     : https://prove2.me/theorems/4843ba13-e296-496b-b10e-8b43cbaf2700
-- title:
--   St Rat Chart Change Var
-- statement:
--   Definitions and structural lemmas for St Rat Chart Change Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StRatChartChangeVar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RatChartObjects
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
open MvPolynomial MeasureTheory
def RatChartChangeVar.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ComplexSets.IsFiniteProjection J A →
    q ∉ J → (∀ y, (RatChart.ratFibre J p q y).Finite) → Measurable f →
    (∀ k, SmoothNear (ComplexSets.zeroSet J) (φ k)) →
      AEStronglyMeasurable (RatChart.ratDens J p q f φ) volume ∧
      AEStronglyMeasurable (RatChart.ratAbsDens J p q f φ) volume ∧
      (Integrable (RatChart.ratAbsDens J p q f φ) →
        Integrable (chartAbsDens J A f φ) ∧ ∫ y, RatChart.ratDens J p q f φ y = chartInt J A f φ)
end GroundTheory.Heights₂.Heights


