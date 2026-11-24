-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamCritNull
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamCritNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:07.114164+00:00
-- url     : https://prove2.me/theorems/0e5194a1-7d05-4aec-8ad9-e94c45fc1faa
-- title:
--   St Param Crit Null
-- statement:
--   Definitions and structural lemmas for St Param Crit Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StParamCritNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamChartInt
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def ParamCritNull.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r : ℝ) (N : Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) → IsOpen N →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W) →
      volume {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} = 0
end
end GroundTheory.Heights₂.Heights


