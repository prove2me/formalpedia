-- Prove2me | Definitions.Def_GroundTheory_LocalFields_OpenCompletion
-- name    : GroundTheory_LocalFields_OpenCompletion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:36.403183+00:00
-- url     : https://prove2.me/theorems/7da4f9c6-cd2c-402a-b4cb-7a8924c9718d
-- title:
--   Open Completion
-- statement:
--   Definitions and structural lemmas for Open Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/OpenCompletion.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
section Completion
variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
def openFiniteIndex : Set (Subgroup G) :=
  {H | IsOpen (H : Set G) ∧ H.FiniteIndex}
variable {G} in

def quotientMapOfLE {H H' : Subgroup G} (h : H ≤ H') : G ⧸ H →* G ⧸ H' :=
  QuotientGroup.map H H' (MonoidHom.id G) h
omit [TopologicalSpace G] [IsTopologicalGroup G] in
variable {G} in
@[simp]
theorem quotientMapOfLE_mk {H H' : Subgroup G} (h : H ≤ H') (x : G) :
    quotientMapOfLE h (x : G ⧸ H) = (x : G ⧸ H') :=
  rfl
def openCompletion : Subgroup (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) where
  carrier := {a | ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H'}
  one_mem' := fun H H' h => by simp
  mul_mem' := fun ha hb H H' h => by simp [map_mul, ha H H' h, hb H H' h]
  inv_mem' := fun ha H H' h => by simp [map_inv, ha H H' h]
namespace openCompletion
variable {G}
omit [IsTopologicalGroup G] in

theorem ext {a b : openCompletion G}
    (h : ∀ H : openFiniteIndex G, (a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H =
      (b : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H) : a = b :=
  Subtype.ext (funext h)
variable (G) in

def of : G →* openCompletion G :=
  MonoidHom.codRestrict (MonoidHom.pi fun H : openFiniteIndex G => QuotientGroup.mk' (H : Subgroup G))
    (openCompletion G) fun _ _ _ _ => rfl
omit [IsTopologicalGroup G] in
@[simp]
theorem of_apply (x : G) (H : openFiniteIndex G) :
    ((of G x : openCompletion G) : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H =
      (x : G ⧸ (H : Subgroup G)) :=
  rfl
theorem discreteTopology_quotient (H : openFiniteIndex G) : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
  QuotientGroup.discreteTopology H.2.1
theorem isClosed : IsClosed (openCompletion G : Set (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G))) := by
  have hset : (openCompletion G : Set (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G))) =
      ⋂ (H : openFiniteIndex G) (H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'),
        {a | quotientMapOfLE h (a H) = a H'} := by
    ext a
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    rfl
  rw [hset]
  refine isClosed_iInter fun H => isClosed_iInter fun H' => isClosed_iInter fun h => ?_
  have := discreteTopology_quotient H
  have := discreteTopology_quotient H'
  exact isClosed_eq ((continuous_of_discreteTopology (f := quotientMapOfLE h)).comp (continuous_apply H))
    (continuous_apply H')
instance : IsTopologicalGroup (openCompletion G) := inferInstance
instance : CompactSpace (openCompletion G) := by
  have : ∀ H : openFiniteIndex G, CompactSpace (G ⧸ (H : Subgroup G)) := fun H => by
    have := H.2.2
    infer_instance
  exact isCompact_iff_compactSpace.1 isClosed.isCompact
instance : T2Space (openCompletion G) := by
  have : ∀ H : openFiniteIndex G, T2Space (G ⧸ (H : Subgroup G)) := fun H => by
    have := discreteTopology_quotient H
    infer_instance
  infer_instance
end openCompletion
end Completion
end GroundTheory.LocalField


