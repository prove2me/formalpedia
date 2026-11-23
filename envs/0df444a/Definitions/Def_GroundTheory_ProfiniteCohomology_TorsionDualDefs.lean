-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
-- name    : GroundTheory_ProfiniteCohomology_TorsionDualDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:42.356555+00:00
-- url     : https://prove2.me/theorems/bdf8df13-2754-4194-b1a6-468efa57d9b3
-- title:
--   Torsion Dual Defs
-- statement:
--   Definitions and structural lemmas for Torsion Dual Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualDefs.lean

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
namespace GroundTheory.ProfCoh
open Topology
def QZ : Type := AddCircle (1 : ℚ)
namespace QZ
instance : AddCommGroup QZ := inferInstanceAs (AddCommGroup (AddCircle (1 : ℚ)))
instance : TopologicalSpace QZ := ⊥
instance : DiscreteTopology QZ := ⟨rfl⟩
instance : IsTopologicalAddGroup QZ where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology
def toAddCircle : QZ ≃+ AddCircle (1 : ℚ) := AddEquiv.refl _
def mk (q : ℚ) : QZ := toAddCircle.symm (q : AddCircle (1 : ℚ))
@[simp] theorem mk_add (p q : ℚ) : mk (p + q) = mk p + mk q := by
  simp [mk]
@[simp] theorem mk_zero : mk 0 = 0 := by simp [mk]
end QZ
abbrev QZDual (A : Type*) [AddCommGroup A] [TopologicalSpace A] : Type _ := A →ₜ+ QZ
namespace QZDual
variable {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
  [TopologicalSpace B] [AddCommGroup C] [TopologicalSpace C]
def map (f : A →ₜ+ B) : QZDual B →ₜ+ QZDual A :=
  ContinuousAddMonoidHom.compLeft QZ f
@[simp]
theorem map_apply (f : A →ₜ+ B) (χ : QZDual B) (a : A) : map f χ a = χ (f a) :=
  rfl
@[simp]
theorem map_id : map (ContinuousAddMonoidHom.id A) = ContinuousAddMonoidHom.id (QZDual A) :=
  rfl
def toAddMonoidHomEquiv [DiscreteTopology A] : QZDual A ≃+ (A →+ QZ) where
  toFun χ := χ.toAddMonoidHom
  invFun f := { f with continuous_toFun := continuous_of_discreteTopology }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
@[simp]
theorem toAddMonoidHomEquiv_apply [DiscreteTopology A] (χ : QZDual A) (a : A) :
    toAddMonoidHomEquiv χ a = χ a :=
  rfl
@[simp]
theorem toAddMonoidHomEquiv_symm_apply [DiscreteTopology A] (f : A →+ QZ) (a : A) :
    toAddMonoidHomEquiv.symm f a = f a :=
  rfl
variable (A) in

def eval : A →+ QZDual (QZDual A) where
  toFun a :=
    { toFun := fun χ => χ a
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_eval_const a }
  map_zero' := by ext χ; exact map_zero χ
  map_add' a b := by ext χ; exact map_add χ a b
end QZDual
end GroundTheory.ProfCoh


