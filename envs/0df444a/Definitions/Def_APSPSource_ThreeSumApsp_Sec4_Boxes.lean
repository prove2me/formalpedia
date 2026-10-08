-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Boxes
-- name    : APSPSource_ThreeSumApsp_Sec4_Boxes
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:49:15.984417+00:00
-- url     : https://prove2.me/theorems/ef0f73ec-8d8d-4ed9-98f6-bc9d928c8751
-- title:
--   Constructing cubes from leaves and starred levels
-- statement:
--   Let $\Lambda$ be the ten-term alphabet, with distinguished term $P_0$. A cube is a length-$L$ string of terms and stars, while a leaf $\tau$ is a string of terms. A term symbol permits only that term at its level; a star permits every term.
--
--   The cube obtained from a leaf by starring a set of levels $F$ is
--
--   $$\operatorname{starAt}(F,\tau)_\ell=\begin{cases}*,&\ell\in F,\\\tau_\ell,&\ell\notin F.\end{cases}$$
--
--   The bundle also embeds a leaf as a cube with no stars. For a natural number $e$, it defines
--
--   $$\operatorname{starLowest}(e,\tau)=\operatorname{starAt}\bigl(\operatorname{lowest}_e\{\ell:\tau_\ell=P_0\},\tau\bigr),$$
--
--   where the lowest-level operator takes all available levels if there are fewer than $e$.
--
--   These constructors specify the cube and box representations used by the later enumeration and query procedures.
--
--   References:
--
--   1. [Source formalization, lines 88–91](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L88-L91).
--   2. [Source formalization, lines 113–115](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L113-L115).
--   3. [Source formalization, lines 171–173](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L171-L173).
--   4. [Source formalization, lines 374–376](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L374-L376).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L88-L91; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L113-L115; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L171-L173; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L374-L376

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Cubes and boxes (Section 4.2)

A cube is a string of `L` symbols, each of them one of the ten terms or a star, and its leaves are
obtained by replacing each star by any term. A box is a cube with at most `m - t` symbols `P₀` or
stars whose stars are all below its symbols `P₀`. This file proves what the paper says about cubes
and boxes before it turns to the boxes of one output string, in this order:

* from "Notions from Section 2": `M ≤ 10^L` (`M_le_ten_pow`);
* a cube with `e` stars has `10^e` leaves (`Cube.card_leaves`);
* the leaves, the stars and the symbols `P₀` of three cubes: a leaf read as a cube (`Cube.ofLeaf`),
  a cube with a star replaced by a term (`Cube.replace`), and a leaf with stars put at a set of
  levels (`Cube.starAt`); every cube that Section 4.2 makes from a leaf is of this third form;
* the leaves contributing to an output string `η` (w in the paper) are the leaves of the cube of `η`
  (`mem_leaves_cubeOf`), so the entry `(X_Q Y_Q)[η]` is the value of that cube
  (`mul_apply_eq_val_cubeOf`); Section 4.2 starts from this remark, and nothing else rests on it;
* the leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` where the cube has `P₀`
  or a star (`P0Levels_starsToP0`);
* a box only contains leaves of order at least `t` (`le_order_of_mem_leaves`);
* the `k` lowest levels of a set `S` lie below the other levels of `S` (`lowest_lt`), this property
  characterizes them (`eq_lowest_of_lt`), and there are `min k |S|` of them (`card_lowest`);
* a box is a leaf with its lowest symbols `P₀` replaced by stars (`eq_starLowest_starsToP0`), and
  every cube obtained in this way from a leaf with at most `m - t` symbols `P₀` is a box
  (`isBox_starLowest`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L : ℕ}








/-! ### Cubes and their leaves (Section 4.2) -/


































/-- The terms that a leaf of a cube may have at a level with the given symbol. -/
 def symbolTerms : CubeSymbol → Finset Term
  | .term lam => {lam}
  | .star => univ



















/-! ### A leaf as a cube without stars (Section 4.2) -/

/-- Section 4.2: "a cube without stars is a single leaf"; this is the cube without stars whose
single leaf is `τ`. -/
def Cube.ofLeaf (τ : Leaf L) : Cube L := fun ℓ => CubeSymbol.term (τ ℓ)




















/-! ### Replacing a star by a term (proof of Lemma 29) -/
































/-! ### Putting stars into a leaf (Section 4.2) -/

/-- The cube that agrees with the leaf `τ` except for stars at the levels of `F`. -/
def Cube.starAt (F : Finset (Fin L)) (τ : Leaf L) : Cube L :=
  fun ℓ => if ℓ ∈ F then CubeSymbol.star else CubeSymbol.term (τ ℓ)
































/-! ### The cube of an output string (Section 4.2)

Section 4.2 starts from this remark. Nothing else rests on it. -/




























/-! ### Replacing the stars of a cube with `P₀` (proof of Lemma 29) -/






































/-! ### A box only contains leaves of order at least `t` (Section 4.2) -/


























/-! ### The `k` lowest levels of a set (Section 4.2) -/



































































/-! ### Replacing the lowest symbols `P₀` of a leaf by stars (Section 4.2 and the proof of Lemma 29)
-/

/-- Section 4.2: the cube "obtained from a leaf […] by replacing its e lowest symbols P₀ […] by
stars". -/
def starLowest (e : ℕ) (τ : Leaf L) : Cube L := Cube.starAt (lowest e (P0Levels τ)) τ






































end ThreeSumApsp


