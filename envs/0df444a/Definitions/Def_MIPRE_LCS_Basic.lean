-- Prove2me | Definitions.Def_MIPRE_LCS_Basic
-- name    : MIPRE_LCS_Basic
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:25.222224+00:00
-- url     : https://prove2.me/theorems/3123f2d8-e77e-41fb-9eae-f3343322ffcc
-- title:
--   Definitions of Basic: Linear Constraint System (LCS) Game Layout This module defines the basic geometric structure of a Linear Constraint…
-- statement:
--   The definitions of the module `MIPRE.LCS.Basic` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Linear Constraint System (LCS) Game Layout. This module defines the basic geometric structure of a Linear Constraint System (LCS) game. An LCS game is defined by a set of binary variables and a set of linear equations over $\mathbb{F}_2$.
--
--   The module belongs to the linear constraint system games development contributed by Sean Perazzolo, vendored with permission from [sean-prz/LCS_In_Lean](https://github.com/sean-prz/LCS_In_Lean) and adapted to this repository (Apache 2.0; the author is named in the file header).
--
--   **Definitions** (2): `MIPRE.LCS.Game` (An LCS game over the layout `G`, given by the right-hand sides of the equations.); `MIPRE.LCS.Layout` (The layout of a binary linear constraint system: `r` equations over `s` variables, with `V i` the set of variables occurring in equation…).
--
--   **Formalization Note** The bundle is the module `MIPRE.LCS.Basic` (`MIPRE/LCS/Basic.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/LCS/Basic.lean; blueprint def:lcs-instance

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Basic.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# Linear Constraint System (LCS) Game Layout

This module defines the basic geometric structure of a Linear Constraint System (LCS) game.
An LCS game is defined by a set of binary variables and a set of linear equations
over $\mathbb{F}_2$.

## Key Definitions
- `Layout`: The structure describing the relationship between equations and variables.
- `Layout.Assignment`: A local mapping of values to variables in a specific equation.
- `Game`: The specification of the right-hand sides of the linear equations.
-/

namespace MIPRE.LCS

/-- The layout of a binary linear constraint system: `r` equations over `s` variables,
with `V i` the set of variables occurring in equation `i`. -/
structure Layout where
  /-- The number of equations. -/
  r : ℕ
  /-- The number of variables. -/
  s : ℕ
  /-- The support of each equation: `V i` is the set of variables occurring in equation `i`. -/
  V : Fin r → Finset (Fin s)

/-- An LCS game over the layout `G`, given by the right-hand sides of the equations. -/
structure Game (G : Layout) where
  /-- The right-hand side of each equation. -/
  b : Fin G.r → ZMod 2

namespace Game

end Game

end MIPRE.LCS


