-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumDepthLower
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumDepthLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:48.596314+00:00
-- url     : https://prove2.me/theorems/1ad8e283-61eb-42f8-920b-fca92f2201af
-- title:
--   PAuslander Buchsbaum Depth Lower
-- statement:
--   Definitions and structural lemmas for PAuslander Buchsbaum Depth Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumDepthLower.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
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
open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence
universe u
namespace AuslanderBuchsbaumDepthLower
variable {R : Type u} [CommRing R] [IsLocalRing R]
noncomputable abbrev residueModule (R : Type u) [CommRing R] [IsLocalRing R] : ModuleCat.{u} R :=
  ModuleCat.of R (Shrink.{u} (R ⧸ maximalIdeal R))
instance (R : Type u) [CommRing R] [IsLocalRing R] : Module.Finite R (residueModule R) :=
  Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).symm
end AuslanderBuchsbaumDepthLower
end GroundTheory.Heights₂.Heights


