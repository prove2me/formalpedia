-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
-- name    : HlawkaSchatten_DiagonalConstruction_Basic
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T15:26:47.487067+00:00
-- url     : https://prove2.me/theorems/f124d0a8-a6cd-440e-88a6-7194d9e4a233
-- title:
--   The finite coordinate power functional and its norm range
-- statement:
--   For a finite index set $\iota$, a normed abelian group $E$ (`NormedAddCommGroup`), a real exponent $p$, and a family $x = (x_i)_{i\in\iota}$ with each $x_i \in E$, `lpNorm` defines
--
--   $$
--   \|x\|_p \;=\; \Big(\sum_{i\in\iota} \|x_i\|^p\Big)^{1/p}.
--   $$
--
--   The formula is defined for every real exponent $p$, using Lean's totalized real power and division. For $p\ge1$, it is a norm and satisfies the triangle inequality. The formula also has uses outside this norm range; no converse about a particular index set or space is asserted here.
--
--   This is the coordinate-explicit stand-in used throughout the diagonal construction for the exponent-indexed `PiLp` norm: writing the finite power sum directly, rather than through the `PiLp` type, keeps later constructions independent of that type's exponent index while still inheriting the same norm laws once $p\ge 1$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Basic.lean#L21-L23

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The finite coordinate `p`-norm, with a real exponent. -/
noncomputable def lpNorm (p : ℝ) (x : ι → E) : ℝ :=
  (∑ i, ‖x i‖ ^ p) ^ (1 / p)















































end HlawkaSchatten.DiagonalConstruction


