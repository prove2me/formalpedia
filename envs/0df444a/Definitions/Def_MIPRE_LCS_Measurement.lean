-- Prove2me | Definitions.Def_MIPRE_LCS_Measurement
-- name    : MIPRE_LCS_Measurement
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:44.201792+00:00
-- url     : https://prove2.me/theorems/bb0831bf-e9ca-4355-a56c-cdc05ec087a2
-- title:
--   Definitions of Measurement: Projector Measurement Systems This module defines the concept of a projector-valued measurement (PVM) in a general…
-- statement:
--   The definitions of the module `MIPRE.LCS.Measurement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Projector Measurement Systems. This module defines the concept of a projector-valued measurement (PVM) in a general star-ring. A measurement system is a family of self-adjoint, idempotent, and mutually orthogonal elements that sum to the identity.
--
--   The module belongs to the linear constraint system games development contributed by Sean Perazzolo, vendored with permission from [sean-prz/LCS_In_Lean](https://github.com/sean-prz/LCS_In_Lean) and adapted to this repository (Apache 2.0; the author is named in the file header).
--
--   **Definitions** (1): `MIPRE.LCS.IsMeasurementSystem` (A projector-valued measurement in a star-ring: a family of self-adjoint, idempotent, mutually orthogonal elements that sum to the identity.).
--
--   **Formalization Note** The bundle is the module `MIPRE.LCS.Measurement` (`MIPRE/LCS/Measurement.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/LCS/Measurement.lean

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Measurement.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_MIPRE_LCS_Basic

/-!
# Projector Measurement Systems

This module defines the concept of a projector-valued measurement (PVM) in a general star-ring.
A measurement system is a family of self-adjoint, idempotent, and mutually orthogonal elements
that sum to the identity.

## Key Definitions
- `IsMeasurementSystem`: A property of a family of elements $\{E_i\}_{i \in I}$ indicating
  they form a valid measurement system.
- `inducedMeasurementSystem`: A construction to build a measurement over a smaller outcome space
  given a function $g : I \to J$.

## Key Lemmas
- `IsMeasurementSystem.commute`: Projectors in a measurement system always commute with each other.
- `IsMeasurementSystem.sum_mul_sum`: The product of two sums of projectors corresponds to the sum
  over the intersection of the outcome sets.
-/

namespace MIPRE.LCS

variable {R : Type*} [Ring R] [StarRing R]

/-- A projector-valued measurement in a star-ring: a family of self-adjoint, idempotent,
mutually orthogonal elements that sum to the identity. -/
structure IsMeasurementSystem
  {I : Type*} [Fintype I]
  (f : I → R) : Prop where
  /-- The measurement operators sum to one. -/
  sum_one      : ∑ x, f x = 1
  /-- Each measurement operator is idempotent. -/
  idempotent   : ∀ x, f x * f x = f x
  /-- Distinct measurement operators are orthogonal. -/
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  /-- Each measurement operator is self-adjoint. -/
  self_adjoint : ∀ x, star (f x) = f x

end MIPRE.LCS


