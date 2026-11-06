-- Prove2me | Definitions.Def_TC433_Algebra_Lie_BaseChange_Module_2c7e193348
-- name    : TC433_Algebra_Lie_BaseChange_Module_2c7e193348
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:31:57.684376+00:00
-- url     : https://prove2.me/theorems/11e92753-64d0-4c0c-b9bd-2be5a1b8277b
-- title:
--   TauCeti: Algebra / Lie / BaseChange / Module
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.BaseChange.Module for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/BaseChange/Module.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Definitions.Def_TC433_Compat4331_Tensor_6326550516

public import Mathlib.Algebra.Lie.BaseChange

/-!
# Extension of scalars for Lie-module maps

A Lie-module map remains equivariant after extending both the Lie algebra and its modules.
This transports an equivariant map together with the action, for example from an integral
Chevalley lattice to its modular short-root representation.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open LieModule
open scoped TensorProduct

namespace LieModuleHom

variable {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  (A : Type*) [CommRing A] [Algebra R A]

/-- Extending scalars preserves the equivariance of a Lie-module map. -/
@[simp] theorem baseChange_map_lie (f : M →ₗ⁅R,L⁆ N) (x : A ⊗[R] L) (m : A ⊗[R] M) :
    f.toLinearMap.baseChange A ⁅x, m⁆ = ⁅x, f.toLinearMap.baseChange A m⁆ := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [add_lie (L := A ⊗[R] L) (M := A ⊗[R] M),
        add_lie (L := A ⊗[R] L) (M := A ⊗[R] N), map_add, hx, hy]
  | tmul a x =>
      induction m using TensorProduct.inductionOn with
      | add m n hm hn => simp only [lie_add, map_add, hm, hn]
      | tmul b m => simp

/-- Extend scalars on a Lie-module morphism, including its acting Lie algebra. -/
def baseChange (f : M →ₗ⁅R,L⁆ N) :
    (A ⊗[R] M) →ₗ⁅A,A ⊗[R] L⁆ (A ⊗[R] N) where
  toLinearMap := f.toLinearMap.baseChange A
  map_lie' {x m} := baseChange_map_lie A f x m

/-- The underlying linear map of scalar extension is the linear scalar extension. -/
@[simp] theorem baseChange_toLinearMap (f : M →ₗ⁅R,L⁆ N) :
    (f.baseChange A).toLinearMap = f.toLinearMap.baseChange A := by
  rfl

end LieModuleHom


