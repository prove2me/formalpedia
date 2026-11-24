-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicIsolatedFibreOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicIsolatedFibreOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:05.530809+00:00
-- url     : https://prove2.me/theorems/89110a45-5144-4e04-9777-5dac4d28f3ca
-- title:
--   St Holomorphic Isolated Fibre Open
-- statement:
--   Definitions and structural lemmas for St Holomorphic Isolated Fibre Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHolomorphicIsolatedFibreOpen.lean

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
open Topology
def HolomorphicIsolatedFibreOpen.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin k → ℂ) (u : Fin k → ℂ),
    IsOpen U → u ∈ U → DifferentiableOn ℂ g U →
    (∃ W ∈ 𝓝 u, ∀ v ∈ W, v ∈ U → g v = g u → v = u) →
    ∀ V ∈ 𝓝 u, g '' V ∈ 𝓝 (g u)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


