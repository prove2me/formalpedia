-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:17.026364+00:00
-- url     : https://prove2.me/theorems/47c244c7-a130-4db1-9aee-66fee1974e52
-- title:
--   St Compact Holomorphic Fibre Finite
-- statement:
--   Definitions and structural lemmas for St Compact Holomorphic Fibre Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCompactHolomorphicFibreFinite.lean

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
open Topology Metric
def CompactHolomorphicFibreFinite.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ) (y : Fin m → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → IsCompact {v | v ∈ U ∧ f v = y} →
      {v | v ∈ U ∧ f v = y}.Finite
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


