-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:40.035589+00:00
-- url     : https://prove2.me/theorems/b8148b15-0ad6-4d8f-b9d2-ccf1f893faa2
-- title:
--   Statements Cone Smooth Local Graph
-- statement:
--   Definitions and structural lemmas for Statements Cone Smooth Local Graph, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeSmoothLocalGraph.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
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
open MvPolynomial Module
noncomputable section
def ConeSmoothLocalGraph.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = m →
    ∀ y ∈ coneSet h J, finrank ℂ (coneTangent h J y) = m →
      ∃ (e : Fin n ≃ Fin m ⊕ Fin (n - m)) (Ω : Set (EuclideanSpace ℂ (Fin m)))
        (Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)))
        (U : Set (EuclideanSpace ℂ (Fin n))),
        IsOpen U ∧ y ∈ U ∧ coneSet h J ∩ U ⊆ graphPt e Φ '' Ω ∧
        IsOpen Ω ∧ DifferentiableOn ℂ Φ Ω ∧ graphPt e Φ '' Ω ⊆ coneSet h J ∧
        ∀ x ∈ Ω, coneTangent h J (graphPt e Φ x) =
          LinearMap.range (fderiv ℂ (graphPt e Φ) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
end
end GroundTheory.Heights₂.Heights


