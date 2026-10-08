-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Levels
-- name    : APSPSource_ThreeSumApsp_Sec2_Levels
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:49:11.409152+00:00
-- url     : https://prove2.me/theorems/383db511-37df-4ff6-85df-834381b0e779
-- title:
--   Gluing inner and outer strings along selected levels
-- statement:
--   Let $Q\subseteq\{0,\ldots,L-1\}$ have cardinality $m$. Write $q_0<\cdots<q_{m-1}$ for its levels and $r_0<\cdots<r_{L-m-1}$ for the complementary levels. For strings $f$ of length $m$ and $g$ of length $L-m$ over the same alphabet, define their glued string by
--
--   $$\operatorname{glue}_Q(f,g)(q_i)=f_i,\qquad \operatorname{glue}_Q(f,g)(r_j)=g_j.$$
--
--   Specializations construct left strings with inner variables $p_{ij}$ at $Q$ and outer variables $x_i$ elsewhere, and right strings with inner variables $q_{ij}$ and outer variables $y_j$. An output string has the distinguished output symbol $z_0$ at $Q$ and symbol $z_{a_jb_j}$ at the $j$-th complementary level, for given outer row and column strings $a,b$.
--
--   These definitions assemble the string indices of a matrix block from a chosen set of inner levels and its row, column, and inner-coordinate data.
--
--   References:
--
--   1. [Source formalization, lines 100–105](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Levels.lean#L100-L105).
--   2. [Source formalization, lines 178–190](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Levels.lean#L178-L190).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Levels.lean#L100-L105; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Levels.lean#L178-L190

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Strings cut along a set of levels

Section 2.3.3 cuts a string of `L` variables along a set `Q` of `m` levels: its variables
at the levels of `Q`, in the order of the levels, form a string of length `m`, and its variables at
the other levels form a string of length `L - m`. The first three parts of this file hold for every
alphabet; the last part specializes them to left, right and output strings.

* Every level is the `k`-th lowest level of `Q` or the `k`-th lowest level outside `Q` for some `k`.
  So a statement about all levels is checked on these two kinds of levels (`forall_level_iff`), and
  so is the statement that a set of levels is `Q` (`filter_eq_iff_forall_level`).
* `glue Q hQ f g` is the string with the letters of `f` at the levels of `Q` and the letters of `g`
  at the other levels. It is the only such string (`eq_glue_iff`), and `f` and `g` can be read off
  it (`glue_inj`).
* If the letters are of two kinds, inner and outer, and each is given by its kind and an index, then
  a string can be rebuilt from its inner set and the indices of its letters (`glue_index`).
* "A string is determined by its inner set, its outer part, and its inner part": the strings
  `leftStrOf Q hQ r π`, `rightStrOf Q hQ π c` and `outStrOf Q hQ r c` have the parts that their
  names say, and no other string has them (`existsUnique_leftStr`, `existsUnique_rightStr`,
  `existsUnique_outStr`). No later proof uses these three statements; the later proofs use the
  lemmas from which they follow.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)

/-! ### The levels of a set and of its complement, in order -/






















































/-! ### Gluing two strings along a set of levels -/

variable {α : Type*}

/-- The string that has the letters of `f` at the levels of `Q` and the letters of `g` at the other
levels, both in the order of the levels. -/
def glue (f : Fin m → α) (g : Fin (L - m) → α) : Fin L → α :=
  fun ℓ =>
    if hℓ : ℓ ∈ Q then f ((Q.orderIsoOfFin hQ).symm ⟨ℓ, hℓ⟩)
    else g ((Qᶜ.orderIsoOfFin (card_compl_of_card_eq Q hQ)).symm ⟨ℓ, mem_compl.mpr hℓ⟩)




























variable {f f' : Fin m → α} {g g' : Fin (L - m) → α}


















/-! ### Alphabets with inner and outer letters -/

variable (IsInner : α → Prop) [DecidablePred IsInner]




















/-! ### Left, right and output strings with a given inner set, outer part and inner part -/

/-- The left string with inner set `Q`, outer part `r` and inner part `π`. -/
def leftStrOf (r : OuterStr L m) (π : InnerStr m) : LeftStr L :=
  glue Q hQ (fun k => .p (π k).1 (π k).2) (fun k => .x (r k))

/-- The right string with inner set `Q`, inner part `π` and outer part `c`. -/
def rightStrOf (π : InnerStr m) (c : OuterStr L m) : RightStr L :=
  glue Q hQ (fun k => .q (π k).1 (π k).2) (fun k => .y (c k))

/-- The output string with inner set `Q`, row `r` and column `c` (Section 2.3.3: "the output strings
with inner set Q index the entries of the product X_Q Y_Q"): it has `z₀` at the levels of `Q`, and
at the `k`-th lowest level outside `Q` it has `z_{r_k c_k}`. -/
def outStrOf (r c : OuterStr L m) : OutStr L :=
  glue Q hQ (fun _ => .z0) (fun k => .z (r k) (c k))
































































variable {Q}



































variable {hQ}

















variable (Q) (hQ)
include hQ




































end ThreeSumApsp


