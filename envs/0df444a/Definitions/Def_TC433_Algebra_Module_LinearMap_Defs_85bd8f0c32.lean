-- Prove2me | Definitions.Def_TC433_Algebra_Module_LinearMap_Defs_85bd8f0c32
-- name    : TC433_Algebra_Module_LinearMap_Defs_85bd8f0c32
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:17:09.819522+00:00
-- url     : https://prove2.me/theorems/e3fc140a-39d5-40fc-a7c3-b8bf7390af13
-- title:
--   TauCeti: Algebra / Module / LinearMap / Defs
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Module.LinearMap.Defs for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Module/LinearMap/Defs.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Additive maps underlying semilinear maps

Forgetting scalar compatibility commutes with composition of semilinear maps.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace LinearMap

variable {R S T M N P : Type*} [Semiring R] [Semiring S] [Semiring T]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module S N] [Module T P]
  {σ : R →+* S} {τ : S →+* T} {υ : R →+* T} [RingHomCompTriple σ τ υ]

/-- The additive map underlying a composite is the composite of the underlying additive maps. -/
@[simp] theorem toAddMonoidHom_comp (g : N →ₛₗ[τ] P) (f : M →ₛₗ[σ] N) :
    (g.comp f : M →ₛₗ[υ] P).toAddMonoidHom =
      g.toAddMonoidHom.comp f.toAddMonoidHom := rfl

end LinearMap


