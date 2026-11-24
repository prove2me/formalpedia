-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamOffRegularZero
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamOffRegularZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:07.069015+00:00
-- url     : https://prove2.me/theorems/b65fa027-9919-4647-8598-5f84b585bcec
-- title:
--   St Param Off Regular Zero
-- statement:
--   Definitions and structural lemmas for St Param Off Regular Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StParamOffRegularZero.lean

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
def ParamOffRegularZero.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r : ℝ) (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), tsupport f ⊆ N →
      chartInt W A ((σ '' {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0})ᶜ.indicator f)
        φ = 0
end
end GroundTheory.Heights₂.Heights


