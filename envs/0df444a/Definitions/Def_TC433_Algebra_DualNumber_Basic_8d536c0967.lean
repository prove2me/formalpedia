-- Prove2me | Definitions.Def_TC433_Algebra_DualNumber_Basic_8d536c0967
-- name    : TC433_Algebra_DualNumber_Basic_8d536c0967
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:20:07.35022+00:00
-- url     : https://prove2.me/theorems/b89a6165-acb8-4a86-a659-505b4721d316
-- title:
--   TauCeti: Algebra / DualNumber / Basic
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.DualNumber.Basic for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/DualNumber/Basic.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DualNumber

/-!
# Scalar compatibility for dual numbers

The coordinatewise scalar action on dual numbers commutes with multiplication. These
instances make bilinear multiplication and convolution available with that module structure.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

/-- Coordinatewise scalar multiplication associates with multiplication of dual numbers. -/
instance dualNumberIsScalarTower : IsScalarTower R (DualNumber B) (DualNumber B) where
  smul_assoc r x y := by
    ext <;> simp [smul_eq_mul, smul_add]

/-- Coordinatewise scalar multiplication commutes with left multiplication of dual numbers. -/
instance dualNumberSMulCommClass : SMulCommClass R (DualNumber B) (DualNumber B) where
  smul_comm r x y := by
    ext <;> simp [smul_eq_mul, smul_add]

end TauCeti


