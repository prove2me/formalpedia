-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
-- name    : APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:28:20.109374+00:00
-- url     : https://prove2.me/theorems/c2cea778-1e35-4055-bf13-6c3438f68b3f
-- title:
--   A computable block layout and its string codes
-- statement:
--   For $m\le L$, set $K_0=\lfloor\sqrt{\binom Lm}\rfloor$. Block pair $(g,h)$, with $g,h<K_0$, uses the subset of $m$ levels at rank $gK_0+h$ in the source's subset enumeration. The rank bound and injectivity proofs are included in the resulting layout value. Rows and columns use base-three strings; inner indices use base-four strings.
--
--   For a subset mask, output digits are nine at selected levels and $3r_j+c_j$ at other levels. Position $(I,J)$ chooses mask rank
--
--   $$((I/N_0)\bmod K_0)K_0+((J/N_0)\bmod K_0),$$
--
--   with outer digits from $I\bmod N_0$ and $J\bmod N_0$. Its output code is the base-ten value of these digits. Left and right codes similarly weave outer digits with inner digits increased by three, then evaluate in base seven.
--
--   References:
--
--   1. [Source formalization, lines 43–61](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L43-L61).
--   2. [Source formalization, lines 149–153](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L149-L153).
--   3. [Source formalization, lines 204–206](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L204-L206).
--   4. [Source formalization, lines 212–219](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L212-L219).
--   5. [Source formalization, lines 244–247](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L244-L247).
--   6. [Source formalization, lines 263–266](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L263-L266).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L43-L61; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L149-L153; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L204-L206; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L212-L219; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L244-L247; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Layout.lean#L263-L266

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Weave
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# One computable layout of the tiling

The statements of Section 2.3.4 about the tiling hold for every `Layout`: every numbering of the
rows and columns of a block by strings, and every table of `K₀²` subsets of size `m`.  A
program needs one layout that it can compute.  In `stdLayout` the rows and columns of a block are
numbered by the base-3 codes of their strings, the columns of `X` by base-4 codes, and the block
product `(g, h)` of a tile gets the subset number `g K₀ + h` of the enumeration `unrank`.

The strings of Lemma 9 are glued from an inner part, at the levels of a set `Q`, and an outer part,
at the other levels.  Their codes are formed digit by digit:

1. the digits of a glued string are the digits of its two parts, interleaved along the mask of `Q`
   by `weaveList` (`ofFn_glue`), because the `k`-th level of `Q` has exactly `k` levels of `Q` below
   it (`Finset.card_filter_lt_orderEmbOfFin`, `count_take_maskOf`);
2. so `outDigitsOfPos` lists the digits, and `outCodeOfPos` is the code, of the output string of a
   position `(I, J)` (Section 2.4.4, `codeO_outStrOfPos`, `digitList_outCodeOfPos`);
3. and `gluedCode` is the code of the left or right string with given parts (`codeL_leftStrOf`,
   `codeR_rightStrOf`).  The input array of a band holds the entries of `X` or `Y` at these codes
   and 0 elsewhere (`bandArrayL_at`, `bandArrayL_eq_zero`, and the same for `R`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The layout -/

/-- `g K₀ + h` is below `binom(L, m)` for `g, h < K₀`. -/
theorem tableIndex_lt (L m : ℕ) (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (gh.1 : ℕ) * K0 L m + gh.2 < L.choose m :=
  (Nat.mul_add_lt_mul gh.1.isLt gh.2.isLt).trans_le (Nat.sqrt_le _)

/-- The computable layout: the rows and columns of a block are numbered by the base-3 codes of their
strings, the columns of `X` by base-4 codes, and the block product `(g, h)` of a tile gets the
subset number `g K₀ + h` of the enumeration `unrank`. -/
def stdLayout {L m : ℕ} (hmL : m ≤ L) : Layout L m where
  hmL := hmL
  rowIdx := (codeEquiv 3 (L - m)).symm
  colIdx := (codeEquiv 3 (L - m)).symm
  innerIdx := (strEquiv pairEquiv m).symm
  table gh := maskSet L (unrank L m (gh.1 * K0 L m + gh.2))
  table_card gh := card_maskSet_unrank (tableIndex_lt L m gh)
  table_injective gh gh' h := by
    obtain ⟨hg, hh⟩ := Nat.mul_add_inj_of_lt gh.2.isLt gh'.2.isLt
      (eq_of_maskSet_unrank_eq (tableIndex_lt L m gh) (tableIndex_lt L m gh') h)
    exact Prod.ext (Fin.ext hg) (Fin.ext hh)

section
variable {L m : ℕ} (hmL : m ≤ L)
































end

/-! ## Counting the levels of a set below a level -/








/-! ## The code of a glued string -/



































/-! ## The digits and the code of the output string of a position -/

section outDigits
variable {m ℓ : ℕ} {mask : List Bool} {rI rJ : List ℕ}

/-- The digits of the output string whose inner set has the mask `mask`, with `m` levels, and whose
row and column have the digits `rI` and `rJ` in base 3: 9 at the levels of the set, and `3 x + y` at
the other levels, where `x` and `y` run through `rI` and `rJ`. -/
def outDigits (m : ℕ) (mask : List Bool) (rI rJ : List ℕ) : List ℕ :=
  weaveList mask (List.zipWith (fun x y => 3 * x + y) rI rJ) (List.replicate m 9)




































end outDigits













/-- The number, in the enumeration `unrank`, of the subset of the block product of the position
`(I, J)`. -/
def maskNo (L m I J : ℕ) : ℕ := I / N0 L m % K0 L m * K0 L m + J / N0 L m % K0 L m





/-- The digits of the output string of the position `(I, J)`, from the block numbers and the base-3
digits of the offsets of `I` and `J`. -/
def outDigitsOfPos (L m I J : ℕ) : List ℕ :=
  outDigits m (unrank L m (maskNo L m I J)) (digitList 3 (L - m) (I % N0 L m))
    (digitList 3 (L - m) (J % N0 L m))

/-- The code of the output string of the position `(I, J)`: Horner's rule on its digits. -/
def outCodeOfPos (L m I J : ℕ) : ℕ := ofDigitList 10 (outDigitsOfPos L m I J)






















/-! ## The codes of the left and right strings, and the input arrays of the bands -/

/-- The digits of the left string with inner set given by `mask`, outer part with the digits `o` and
inner part with the digits `i`: `o_j` at the `j`-th level outside the set, and `3 + i_j` at the
`j`-th level of the set.  The right string with the same parts has the same digits. -/
def gluedDigits (mask : List Bool) (o i : List ℕ) : List ℕ := weaveList mask o (i.map (3 + ·))















/-- The code of the left string, and of the right string, with inner set given by `mask`, outer part
with code `r` and inner part with code `k`. -/
def gluedCode (L m : ℕ) (mask : List Bool) (r k : ℕ) : ℕ :=
  ofDigitList 7 (gluedDigits mask (digitList 3 (L - m) r) (digitList 4 m k))





































section
variable {L m N : ℕ} (hmL : m ≤ L)









































end




















































end ThreeSumApsp.Spec


