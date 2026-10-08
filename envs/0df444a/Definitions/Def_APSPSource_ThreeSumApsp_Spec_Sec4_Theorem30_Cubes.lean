-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Cubes
-- name    : APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Cubes
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:28:38.107658+00:00
-- url     : https://prove2.me/theorems/4b24fe1a-8ec5-441a-8f43-964483e9cedd
-- title:
--   Digit representations and the ten-way recurrence for cube values
-- statement:
--   Cube symbols use digits zero through nine for the ten terms and digit ten for a star. Explicit inverse maps give an equivalence with the eleven digits; cubes, leaves, and output strings are then represented as digit lists.
--
--   The list operations count stars, replace the first $e$ nines by stars, replace all stars by nines, and locate the last star. Leaf products read the two encoded arrays at the base-ten code of a digit list, using zero for missing entries.
--
--   The digit recurrence is
--
--   $$V_0(l)=\operatorname{leafProduct}(\operatorname{starsToNines}(l)),\qquad
--   V_{e+1}(l)=\sum_{d=0}^{9}V_e(l[p\leftarrow d]),$$
--
--   where $p$ is the last star position; the positive-depth value is zero if no star exists. The stored value of a box is $V_{\#\text{stars}(l)}(l)$.
--
--   References:
--
--   1. [Source formalization, lines 39–69](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L39-L69).
--   2. [Source formalization, lines 109–110](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L109-L110).
--   3. [Source formalization, lines 174–179](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L174-L179).
--   4. [Source formalization, lines 214–215](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L214-L215).
--   5. [Source formalization, lines 257–264](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L257-L264).
--   6. [Source formalization, lines 310–325](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L310-L325).
--   7. [Source formalization, lines 334–341](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L334-L341).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L39-L69; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L109-L110; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L174-L179; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L214-L215; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L257-L264; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L310-L325; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Cubes.lean#L334-L341

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
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
# Cubes, leaves and output strings as lists of digits (Sections 4.2 and 4.3)

A term has the digit P_ij ↦ 3(i - 1) + (j - 1), P₀ ↦ 9, and an output variable the digit
z_ij ↦ 3(i - 1) + (j - 1), z₀ ↦ 9.  A symbol of a cube that is a term keeps the digit of the term,
and the star has the digit 10.  A cube, a leaf or an output string is handled as the list of its L
digits, level 1 first: `digitsC` for cubes, `digitsT` for strings of terms (leaves), `digitsO` for
output strings.  This file translates the notions of Sections 4.2 and 4.3 into operations on such
lists:

* the inner set of an output string η (the paper's w) is the positions of its digit 9, the stars of
  π are the positions of 10, the symbols P₀ of τ the positions of 9, and their numbers are counts
  (`card_innerSetO`, `card_starLevels`, `card_P0Levels`);
* "replacing its e lowest symbols P₀ […] by stars" is `starFirst` (`digitsC_starLowest`);
* "replacing its stars with P₀" is `starsToNines` (`digitsT_starsToP0`);
* "the highest level at which π has a star" is `lastStar` (`lastStar_digitsC`), and π[ℓ ← λ] is
  `List.set` (`digitsC_replace`);
* the dynamic program of Lemma 29 is `dpValueD` (`dpValueD_digitsC`): the product `leafProduct` for
  a list without stars, and the step `sumAtLastStar`; `storedD` is what it computes for a box, at
  the number of stars of the box.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Cubes, leaves and output strings -/

/-- The digit of a symbol of a cube: a term keeps its digit, the star has 10. -/
def cubeIdx : CubeSymbol → Fin 11
  | .term lam => ⟨termIdx lam, by have := (termIdx lam).isLt; omega⟩
  | .star => 10

/-- The symbol with a given digit. -/
def cubeOfIdx (k : Fin 11) : CubeSymbol :=
  if h : (k : ℕ) < 10 then .term (termOfIdx ⟨k, h⟩) else .star

/-- The symbols of cubes and their digits. -/
def cubeEquiv : CubeSymbol ≃ Fin 11 where
  toFun := cubeIdx
  invFun := cubeOfIdx
  left_inv := by
    intro s
    cases s with
    | term lam =>
      cases lam with
      | P i j => fin_cases i <;> fin_cases j <;> rfl
      | P0 => rfl
    | star => rfl
  right_inv := by
    intro k
    fin_cases k <;> rfl

/-- The digits of a cube, level 1 first. -/
def digitsC {L : ℕ} (π : Cube L) : List ℕ := digitsStr cubeEquiv π
/-- The digits of a leaf, level 1 first. -/
def digitsT {L : ℕ} (τ : Leaf L) : List ℕ := digitsStr termEquiv τ
/-- The digits of an output string, level 1 first. -/
def digitsO {L : ℕ} (η : OutStr L) : List ℕ := digitsStr outEquiv η

section

variable {L : ℕ} (π : Cube L) (τ : Leaf L) (η : OutStr L)






















end










/-! ## The levels of a symbol are the positions of its digit -/

/-- The number of stars in a list of digits: the star has the digit 10. -/
abbrev starCount (l : List ℕ) : ℕ := l.count 10






















section

variable {L : ℕ} (π : Cube L) (τ : Leaf L) (η : OutStr L)


































end

/-! ## The lowest symbols P₀ turned into stars -/

/-- The first e digits 9 turned into 10 (Section 4.2: "replacing its e lowest symbols P₀ […] by
stars"). -/
def starFirst : ℕ → List ℕ → List ℕ
  | 0, l => l
  | _ + 1, [] => []
  | e + 1, d :: l => if d = 9 then 10 :: starFirst e l else d :: starFirst (e + 1) l
































/-! ## Stars turned into P₀, and a symbol replaced by a term -/

/-- Stars turned into P₀ (proof of Lemma 29). -/
def starsToNines (l : List ℕ) : List ℕ := l.map fun d => if d = 10 then 9 else d







































/-! ## The highest star -/

/-- The position of the last digit 10, if there is one (proof of Lemma 29: "the highest level at
which π has a star"). -/
def lastStar : List ℕ → Option ℕ
  | [] => none
  | d :: l =>
    match lastStar l with
    | some p => some (p + 1)
    | none => if d = 10 then some 0 else none











































/-! ## The dynamic program of Lemma 29 on digits -/

/-- The product of the two numbers that the encodings have for the leaf with the digits l; the
encodings are arrays indexed by the codes of the leaves. -/
def leafProduct (encA encB : List ℤ) (l : List ℕ) : ℤ :=
  encA.getD (ofDigitList 10 l) 0 * encB.getD (ofDigitList 10 l) 0

/-- The values val(π[ℓ ← λ]) for the ten terms λ, in the order of their digits; l is the list of
digits of π, and p is the position ℓ. -/
def tenValues (val : List ℕ → ℤ) (l : List ℕ) (p : ℕ) : List ℤ :=
  (List.range 10).map fun d => val (l.set p d)

/-- The step of the dynamic program of Lemma 29: the sum ∑_λ val(π[ℓ ← λ]), where ℓ is "the highest
level at which π has a star".  For a list without a star it is 0. -/
def sumAtLastStar (val : List ℕ → ℤ) (l : List ℕ) : ℤ :=
  match lastStar l with
  | some p => (tenValues val l p).sum
  | none => 0








/-- The dynamic program of Lemma 29 on lists of digits; e is the number of stars. -/
def dpValueD (encA encB : List ℤ) : ℕ → List ℕ → ℤ
  | 0, l => leafProduct encA encB (starsToNines l)
  | e + 1, l => sumAtLastStar (dpValueD encA encB e) l

/-- The value that is stored for the box l: what the dynamic program of Lemma 29 computes for it, at
its number of stars. -/
def storedD (encA encB : List ℤ) (l : List ℕ) : ℤ := dpValueD encA encB (starCount l) l

























end ThreeSumApsp.Spec


