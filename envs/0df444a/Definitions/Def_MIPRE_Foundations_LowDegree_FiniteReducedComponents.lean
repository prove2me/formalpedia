-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
-- name    : MIPRE_Foundations_LowDegree_FiniteReducedComponents
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:52.959081+00:00
-- url     : https://prove2.me/theorems/03a4f5e8-43df-41df-8a76-fe5fa909f509
-- title:
--   Definitions of FiniteReducedComponents: Primitive components of a finite ring with bijective squaring This supplies the algebraic justification for splitting…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.FiniteReducedComponents` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Primitive components of a finite ring with bijective squaring. This supplies the algebraic justification for splitting the binary cyclic group algebra by its fixed vectors. The computations need only multiplication and linear algebra; the finite permutation argument below is a correctness proof, not an enumeration performed by the algorithm.
--
--   **Definitions** (1): `MIPRE.LowDegree.PrimitiveBinaryComponent` (A primitive nonzero idempotent sees every idempotent as either zero or itself.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.FiniteReducedComponents` (`MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-!
# Primitive components of a finite ring with bijective squaring

This supplies the algebraic justification for splitting the binary cyclic group
algebra by its fixed vectors. The computations need only multiplication and
linear algebra; the finite permutation argument below is a correctness proof,
not an enumeration performed by the algorithm.
-/

namespace MIPRE.LowDegree

variable {R : Type*} [CommRing R] [Finite R]

/-- A primitive nonzero idempotent sees every idempotent as either zero or itself. -/
def PrimitiveBinaryComponent (e : R) : Prop :=
  e ≠ 0 ∧ e * e = e ∧ ∀ u : R, u * u = u → e * u = 0 ∨ e * u = e

end MIPRE.LowDegree


