-- Prove2me | Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvUnifA
-- name    : Development_DiscreteGroups_GlobalIrreducibility_LConvUnifA
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:53.942134+00:00
-- url     : https://prove2.me/theorems/70c8bc89-b0d7-4ceb-a0b6-26cfb1f05871
-- title:
--   LConv Unif A
-- statement:
--   Definitions and structural lemmas for LConv Unif A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvUnifA.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_ReciprocityTheory_BurnsideSurjectivity_Burnside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace DiscreteGroups.sglob.LConvU
open GroundTheory.Automorphic Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo
variable (ρ) in

def hop (g : G) : Module.End ℂ (fixedVectors ρ K) :=
  (fixedProj ρ hρ hKc hKo) ∘ₗ (ρ g) ∘ₗ (fixedVectors ρ K).subtype
end DiscreteGroups.sglob.LConvU


