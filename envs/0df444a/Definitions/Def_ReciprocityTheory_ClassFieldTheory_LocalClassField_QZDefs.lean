-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:27.587513+00:00
-- url     : https://prove2.me/theorems/5f8a47ab-fa0d-4dbb-a287-5e04ec525358
-- title:
--   QZDefs
-- statement:
--   Definitions and structural lemmas for QZDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/QZDefs.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
def trivRep (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] : TRep ℤ G :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  { V := A
    rho := 1
    cont := continuous_snd }
scoped instance (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] :
    DiscreteTopology (trivRep G A).V := ⟨rfl⟩
def trivMap (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Type} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) : Pair (trivRep G A) (trivRep G B) :=
  Pair.ofMap (M := trivRep G A) (M' := trivRep G B) f.toIntLinearMap continuous_of_discreteTopology
    fun _ _ => rfl
def charGrp (G : Type) [Group G] [TopologicalSpace G] : AddSubgroup (Additive G →+ QZ) where
  carrier := {χ | IsLocallyConstant fun g : G => χ (Additive.ofMul g)}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' := fun ha hb => IsLocallyConstant.add ha hb
  neg_mem' := fun ha => IsLocallyConstant.neg ha
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


