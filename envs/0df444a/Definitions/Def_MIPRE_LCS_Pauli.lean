-- Prove2me | Definitions.Def_MIPRE_LCS_Pauli
-- name    : MIPRE_LCS_Pauli
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:34.700428+00:00
-- url     : https://prove2.me/theorems/f4dfdb84-61d9-491c-affa-7cb9c30272b1
-- title:
--   Definitions of Pauli: Pauli Matrices This module defines the single-qubit Pauli matrices `Pauli.I`, `Pauli.X`, `Pauli.Y`, `Pauli.Z`, together…
-- statement:
--   The definitions of the module `MIPRE.LCS.Pauli` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pauli Matrices. This module defines the single-qubit Pauli matrices `Pauli.I`, `Pauli.X`, `Pauli.Y`, `Pauli.Z`, together with their multiplication table, anticommutation relations, and observable structure. It also records the Kronecker-product lemmas used to combine commuting or anticommuting pairs into commuting two-qubit observables.
--
--   The module belongs to the linear constraint system games development contributed by Sean Perazzolo, vendored with permission from [sean-prz/LCS_In_Lean](https://github.com/sean-prz/LCS_In_Lean) and adapted to this repository (Apache 2.0; the author is named in the file header).
--
--   **Definitions** (3): `MIPRE.LCS.Pauli.X` (The Pauli `X` (bit-flip) matrix.); `MIPRE.LCS.Pauli.Y` (The Pauli `Y` matrix.); `MIPRE.LCS.Pauli.Z` (The Pauli `Z` (phase-flip) matrix.).
--
--   **Formalization Note** The bundle is the module `MIPRE.LCS.Pauli` (`MIPRE/LCS/Pauli.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 4 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/LCS/Pauli.lean

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Pauli.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable

/-!
# Pauli Matrices

This module defines the single-qubit Pauli matrices `Pauli.I`, `Pauli.X`, `Pauli.Y`,
`Pauli.Z`, together with their multiplication table, anticommutation relations, and
observable structure. It also records the Kronecker-product lemmas used to combine
commuting or anticommuting pairs into commuting two-qubit observables.
-/

namespace MIPRE.LCS

open Matrix
open scoped Kronecker

namespace Pauli

/-- The Pauli `X` (bit-flip) matrix. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` (phase-flip) matrix. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

end Pauli

end MIPRE.LCS


