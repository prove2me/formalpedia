-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:04.213376+00:00
-- url     : https://prove2.me/theorems/a4493032-71cc-4a51-a236-67d149628f86
-- title:
--   St Chart Int Count Add
-- statement:
--   Definitions and structural lemmas for St Chart Int Count Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StChartIntCountAdd.lean

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
def ChartIntCountAdd.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (E : ℕ → Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    Continuous f → HasCompactSupport f → (∀ k, SmoothNear (zeroSet W) (φ k)) →
    (∀ i, MeasurableSet (E i)) → Pairwise (Function.onFun Disjoint E) →
      HasSum (fun i => chartInt W A ((E i).indicator f) φ) (chartInt W A ((⋃ i, E i).indicator f) φ)
end
end GroundTheory.Heights₂.Heights


