-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamDensIntegrable
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamDensIntegrable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:44.997772+00:00
-- url     : https://prove2.me/theorems/4d852742-1747-48a1-aa0e-3aceb5ae3330
-- title:
--   St Param Dens Integrable
-- statement:
--   Definitions and structural lemmas for St Param Dens Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StParamDensIntegrable.lean

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
def ParamDensIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ)
    (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      Continuous f → tsupport f ⊆ N → (∀ i, SmoothNear (zeroSet W) (φ i)) →
        IntegrableOn (fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w)
          (Metric.ball (0 : Fin d → ℂ) r)
end
end GroundTheory.Heights₂.Heights


