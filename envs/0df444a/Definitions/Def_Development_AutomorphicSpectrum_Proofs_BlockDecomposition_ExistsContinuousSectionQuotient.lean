-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:31.438358+00:00
-- url     : https://prove2.me/theorems/805f88f5-7ee3-4530-99ec-d2a11c0af47e
-- title:
--   Exists Continuous Section Quotient
-- statement:
--   Definitions and structural lemmas for Exists Continuous Section Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousSectionQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
namespace GlobalTheory.CompanionTheory.LGroupSection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def cosetImage (H K : Subgroup G) (d : G) : Set (G ⧸ H) :=
  {x | ∃ k ∈ K, ((d * k : G) : G ⧸ H) = x}
end GlobalTheory.CompanionTheory.LGroupSection


