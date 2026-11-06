-- Prove2me | Definitions.Def_TC433_Algebra_Coalgebra_Comodule_MatrixCoefficient_Finite_7b6e6efeb5
-- name    : TC433_Algebra_Coalgebra_Comodule_MatrixCoefficient_Finite_7b6e6efeb5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:07:46.332428+00:00
-- url     : https://prove2.me/theorems/364cf7e6-7378-4b45-92cb-76a0e87d59e7
-- title:
--   TauCeti: Algebra / Coalgebra / Comodule / MatrixCoefficient / Finite
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Finite for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Coalgebra/Comodule/MatrixCoefficient/Finite.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Definitions.Def_TC433_Algebra_Coalgebra_Comodule_MatrixCoefficient_Adjoin_cd9288a090

/-!
# Finite matrix-coefficient submodules

This file proves that the matrix-coefficient submodule of a finite projective right comodule
over a commutative semiring is finite.

This is the first finite-dimensionality step toward the fundamental theorem of comodules in
the reductive-groups roadmap. The next substantive step is to show that this finite submodule
is closed under comultiplication, making it a coefficient subcoalgebra.

## Main results

* `TauCeti.Comodule.matrixCoefficientSubmodule_finite`: a finite projective comodule has a
  finite matrix-coefficient submodule.

## References

The coefficient-space construction is standard; see Sweedler, *Hopf Algebras*, Chapter 2.
It advances `ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1,
"Finite-dimensional subcoalgebras (the fundamental theorem of comodules)".
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

namespace Comodule

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The matrix-coefficient submodule of a finite projective comodule is finite. -/
instance matrixCoefficientSubmodule_finite [Module.Finite R M] [Module.Projective R M] :
    Module.Finite R
      (matrixCoefficientSubmodule (R := R) (C := C) (M := M)) := by
  rw [← range_matrixCoefficientTensor]
  infer_instance

end Comodule

end TauCeti


