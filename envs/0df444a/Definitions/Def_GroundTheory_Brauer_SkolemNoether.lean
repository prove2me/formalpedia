-- Prove2me | Definitions.Def_GroundTheory_Brauer_SkolemNoether
-- name    : GroundTheory_Brauer_SkolemNoether
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:10.910904+00:00
-- url     : https://prove2.me/theorems/58b73574-0c1b-4d7a-b794-4d1f38cc8d3a
-- title:
--   Skolem Noether
-- statement:
--   Definitions and structural lemmas for Skolem Noether, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Brauer
open TensorProduct
section Modules
end Modules
namespace SkolemNoether
section Twist
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
noncomputable def mulRightHom (f : B →ₐ[K] A) : Bᵐᵒᵖ →ₐ[K] Module.End K A where
  toFun b := LinearMap.mulRight K (f b.unop)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]
  commutes' c := by ext x; simp [Algebra.commutes, Algebra.smul_def]
noncomputable def bimoduleHom (f : B →ₐ[K] A) : A ⊗[K] Bᵐᵒᵖ →ₐ[K] Module.End K A :=
  Algebra.TensorProduct.lift (Algebra.lmul K A) (mulRightHom f) fun a b ↦ by
    ext x; simp [mulRightHom, mul_assoc]
def Twist (_f : B →ₐ[K] A) : Type _ := A
namespace Twist
variable (f : B →ₐ[K] A)
def of (x : A) : Twist f := x
def val {f : B →ₐ[K] A} (x : Twist f) : A := x
instance : AddCommGroup (Twist f) := inferInstanceAs (AddCommGroup A)
instance : Module K (Twist f) := inferInstanceAs (Module K A)
instance [FiniteDimensional K A] : FiniteDimensional K (Twist f) := inferInstanceAs (FiniteDimensional K A)
noncomputable instance : Module (A ⊗[K] Bᵐᵒᵖ) (Twist f) :=
  letI : Module (A ⊗[K] Bᵐᵒᵖ) A := Module.compHom A (bimoduleHom f).toRingHom
  inferInstanceAs (Module (A ⊗[K] Bᵐᵒᵖ) A)
instance : IsScalarTower K (A ⊗[K] Bᵐᵒᵖ) (Twist f) :=
  ⟨fun c r x ↦ by
    change bimoduleHom f (c • r) x.val = c • bimoduleHom f r x.val
    rw [map_smul]; rfl⟩
variable {f} {g : B →ₐ[K] A}
end Twist
end Twist
end SkolemNoether
section SkolemNoether
open SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
  [IsSimpleRing B] [FiniteDimensional K B]
end SkolemNoether
end GroundTheory.Brauer


