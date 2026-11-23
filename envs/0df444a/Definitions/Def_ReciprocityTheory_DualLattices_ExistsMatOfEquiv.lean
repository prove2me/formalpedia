-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ExistsMatOfEquiv
-- name    : ReciprocityTheory_DualLattices_ExistsMatOfEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:38.712579+00:00
-- url     : https://prove2.me/theorems/a09aefbd-c8bd-4853-a563-3b3cab89ddf1
-- title:
--   Exists Mat Of Equiv
-- statement:
--   Definitions and structural lemmas for Exists Mat Of Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsMatOfEquiv.lean

import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
import Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_map_tensorSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
section Hopf
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
def pullHopf {N X : Type} [AddCommGroup N] [Fintype N] [DecidableEq N] [AddCommGroup X]
    [Fintype X] [DecidableEq X] (ψ : X →+ N) (AA : HopfOrder (C := C) R N)
    (hlat : IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ))) : HopfOrder (C := C) R X where
  carrier := AA.carrier.map (LinearMap.funLeft R C ψ)
  lat := hlat
  le_int := by
    rintro _ ⟨f, hf, rfl⟩ x
    exact AA.le_int hf (ψ x)
  one_mem := ⟨1, AA.one_mem, rfl⟩
  mul_mem := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, AA.mul_mem f g hf hg, rfl⟩
  comul := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← SecondCohomologyLattice.map_tensorSpan (⇑ψ) AA.carrier]
    refine ⟨addPull R N f, AA.comul f hf, ?_⟩
    funext x
    simp [addPull, LinearMap.funLeft_apply, map_add]
  antipode := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun x => f (-x), AA.antipode f hf, funext fun x => by simp [LinearMap.funLeft_apply]⟩
end Hopf
section Split
variable {S : Type} [CommRing S] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
end Split
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder


