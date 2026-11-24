-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StContinuousRootHolomorphic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StContinuousRootHolomorphic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:03.243804+00:00
-- url     : https://prove2.me/theorems/faf4f083-e31b-452d-bb44-ccd1513e0d0d
-- title:
--   St Continuous Root Holomorphic
-- statement:
--   Definitions and structural lemmas for St Continuous Root Holomorphic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StContinuousRootHolomorphic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
noncomputable section
def ContinuousRootHolomorphic.Statement : Prop :=
  ∀ (k : ℕ) (Q : MvPolynomial (Fin (k + 1)) ℂ) (O : Set (Fin k → ℂ)) (h : (Fin k → ℂ) → ℂ),
    IsOpen O → ContinuousOn h O → (∀ t ∈ O, eval (Fin.cons (h t) t : Fin (k + 1) → ℂ) Q = 0) →
    ∀ y ∈ O, eval (Fin.cons (h y) y : Fin (k + 1) → ℂ) (pderiv 0 Q) ≠ 0 → DifferentiableAt ℂ h y
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


