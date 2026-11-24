-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:41.946945+00:00
-- url     : https://prove2.me/theorems/91861bf0-8b31-4b84-b1fa-207a3e3df12d
-- title:
--   Statements Graph Area Fibre
-- statement:
--   Definitions and structural lemmas for Statements Graph Area Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsGraphAreaFibre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
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
open MeasureTheory
open scoped ENNReal
noncomputable section
def graphBase {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k) (y : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i => y (e.symm (Sum.inl i))
def GraphAreaFibre.Statement : Prop :=
  ∀ (d k n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin k) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (Φ : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)),
    IsOpen Ω → DifferentiableOn ℂ Φ Ω →
    ∀ P ⊆ graphPt e Φ '' Ω, MeasurableSet P →
    ∀ T : EuclideanSpace ℂ (Fin n) → Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (∀ x ∈ Ω, graphPt e Φ x ∈ P → T (graphPt e Φ x) =
        LinearMap.range (fderiv ℂ (graphPt e Φ) x :
          EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) →
    ∀ π : Fin d → Fin n → ℂ,
      AEMeasurable (fun w : EuclideanSpace ℂ (Fin d) =>
          (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞)) ∧
        ∀ g : EuclideanSpace ℂ (Fin d) → ℝ≥0∞, Measurable g →
          volume (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) *
              ∫⁻ y in P, g (linProj π y) * ENNReal.ofReal (tangentJac π (T y))
                ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)) =
            Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) *
              ∫⁻ w : EuclideanSpace ℂ (Fin d),
                (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w
end
end GroundTheory.Heights₂.Heights


