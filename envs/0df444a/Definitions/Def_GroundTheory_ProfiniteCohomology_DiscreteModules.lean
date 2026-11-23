-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
-- name    : GroundTheory_ProfiniteCohomology_DiscreteModules
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:12.73803+00:00
-- url     : https://prove2.me/theorems/5fa1a268-0fa2-40c0-9743-e08720b67ba1
-- title:
--   Discrete Modules
-- statement:
--   Definitions and structural lemmas for Discrete Modules, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.ProfCoh
open CategoryTheory
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
def stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]
variable [TopologicalSpace G]
class IsDiscreteRep (A : Rep.{w} k G) : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (stabilizer A.ρ a : Set G)
variable (k G) in

def isDiscreteRep : ObjectProperty (Rep.{w} k G) := fun A => IsDiscreteRep A
variable (k G) in

abbrev DiscreteRep := (isDiscreteRep.{w} k G).FullSubcategory
instance (A : DiscreteRep.{w} k G) : IsDiscreteRep A.obj := A.property
end GroundTheory.ProfCoh


