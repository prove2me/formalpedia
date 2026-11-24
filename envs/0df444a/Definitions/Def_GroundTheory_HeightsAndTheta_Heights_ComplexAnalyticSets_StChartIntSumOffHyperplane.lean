-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntSumOffHyperplane
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntSumOffHyperplane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:47.804494+00:00
-- url     : https://prove2.me/theorems/c5d57cdd-39de-4492-9bfe-5bd8d72abe1c
-- title:
--   St Chart Int Sum Off Hyperplane
-- statement:
--   Definitions and structural lemmas for St Chart Int Sum Off Hyperplane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StChartIntSumOffHyperplane.lean

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
noncomputable section
def ChartIntSumOffHyperplane.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (u : Fin n → ℂ)
    (m : ℕ) (f : (Fin n → ℂ) → ℝ) (F : Fin m → (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J →
    (∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, F b x) →
    (∀ b, Integrable (chartDens J A (F b) φ)) →
      chartInt J A f φ = ∑ b, chartInt J A (F b) φ
end
end GroundTheory.Heights₂.Heights


