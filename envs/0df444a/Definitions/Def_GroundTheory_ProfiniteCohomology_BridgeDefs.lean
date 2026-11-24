-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_BridgeDefs
-- name    : GroundTheory_ProfiniteCohomology_BridgeDefs
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:17:09.187261+00:00
-- url     : https://prove2.me/theorems/06ee7289-95b5-4d2e-b143-24310b75c110
-- title:
--   Bridge Defs
-- statement:
--   Definitions and structural lemmas for Bridge Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/BridgeDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory
universe u
variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G]
abbrev underlyingRep (X : TopRep.{u} k G) : Rep.{u} k G :=
  Rep.of X.ρ.toRepresentation
@[simp]
theorem underlyingRep_ρ_apply (X : TopRep.{u} k G) (g : G) (x : X) :
    (underlyingRep X).ρ g x = X.ρ g x :=
  rfl
section Discrete
variable [DiscreteTopology k]
def discreteTopRep (A : Rep.{u} k G) : TopRep.{u} k G :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  haveI : ContinuousSMul k A := ⟨continuous_of_discreteTopology⟩
  haveI : IsTopologicalAddGroup A := ⟨⟩
  TopRep.of (X := A) <| ContRepresentation.ofMonoidHom
    { toFun g := { toLinearMap := A.ρ g, cont := continuous_of_discreteTopology }
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }
instance (A : Rep.{u} k G) : DiscreteTopology (discreteTopRep A) :=
  ⟨rfl⟩
variable [TopologicalSpace G]
instance (A : Rep.{u} k G) [IsDiscreteRep A] : IsDiscreteRep (underlyingRep (discreteTopRep A)) :=
  ‹IsDiscreteRep A›
end Discrete
end GroundTheory.ProfCoh


