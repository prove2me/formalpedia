-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:55.973087+00:00
-- url     : https://prove2.me/theorems/b605ec74-f532-4165-861b-48c716d2d2a9
-- title:
--   St Branch Chart Int
-- statement:
--   Definitions and structural lemmas for St Branch Chart Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchChartInt.lean

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
def BranchChartInt.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (p : Fin n → ℂ)
    (γ : VarBranch J d p) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    Continuous g → (∀ k, SmoothNear (zeroSet J) (φ k)) →
    (∃ K : Set (Fin d → ℂ), IsCompact K ∧ K ⊆ Metric.ball 0 γ.radius ∧
      ∀ t ∈ Metric.ball 0 γ.radius, t ∉ K → g (γ.toFun t) = 0) →
      Integrable (chartDens J A (γ.image.indicator g) φ) ∧
        chartInt J A (γ.image.indicator g) φ =
          ReciprocityTheory.AnForm.maInt (fun k => φ k ∘ γ.toFun) (g ∘ γ.toFun) (Metric.ball 0 γ.radius)
end
end GroundTheory.Heights₂.Heights


