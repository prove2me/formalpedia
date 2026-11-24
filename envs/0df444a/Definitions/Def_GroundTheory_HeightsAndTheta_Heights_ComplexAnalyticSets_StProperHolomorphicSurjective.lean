-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperHolomorphicSurjective
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperHolomorphicSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:23:23.043638+00:00
-- url     : https://prove2.me/theorems/4386a7a8-ff03-4c91-9e46-504c2c42be4e
-- title:
--   St Proper Holomorphic Surjective
-- statement:
--   Definitions and structural lemmas for St Proper Holomorphic Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StProperHolomorphicSurjective.lean

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
def ProperHolomorphicSurjective.Statement : Prop :=
  ∀ (k : ℕ) (Ω D : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen Ω → Ω.Nonempty → IsOpen D → IsPreconnected D → DifferentiableOn ℂ g Ω → Set.MapsTo g Ω D →
    (∀ L ⊆ D, IsCompact L → IsCompact (Ω ∩ g ⁻¹' L)) →
    g '' Ω = D
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


