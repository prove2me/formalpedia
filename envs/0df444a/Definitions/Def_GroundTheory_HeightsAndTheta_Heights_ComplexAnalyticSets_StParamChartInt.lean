-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamChartInt
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamChartInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:30.164251+00:00
-- url     : https://prove2.me/theorems/01f5609f-2767-4531-a8aa-fd224665d115
-- title:
--   St Param Chart Int
-- statement:
--   Definitions and structural lemmas for St Param Chart Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StParamChartInt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
def ParamChartInt.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ) (N : Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) →
    IsOpen N → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
      (∀ i, SmoothNear (zeroSet W) (φ i)) →
        chartInt W A f φ =
          ∫ w in Metric.ball (0 : Fin d → ℂ) r, f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w
end
end GroundTheory.Heights₂.Heights


