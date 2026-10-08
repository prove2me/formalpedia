-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
-- name    : APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:27:54.01163+00:00
-- url     : https://prove2.me/theorems/9e17ef9d-e239-483d-874f-414ca2b1e8d1
-- title:
--   Serializing arrays indexed by finite-alphabet strings
-- statement:
--   Let $e:A\simeq\{0,\ldots,b-1\}$ number a finite alphabet, and let $a:A^n\to\mathbb Z$ be an array. Its serialized list is
--
--   $$\operatorname{arrStr}(e,a)=[a(\operatorname{decode}_{e,n}(c)):0\le c<b^n].$$
--
--   Thus entries occur in increasing order of their base-$b$ string codes. Specializations serialize left and right variable strings using their seven-symbol alphabets, yielding $7^n$ entries, and term leaves using their ten-symbol alphabet, yielding $10^n$ entries. These lists are the concrete representations of the input arrays and leaf encodings.
--
--   References:
--
--   1. [Source formalization, lines 32–35](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Arrays.lean#L32-L35).
--   2. [Source formalization, lines 63–70](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Arrays.lean#L63-L70).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Arrays.lean#L32-L35; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Arrays.lean#L63-L70

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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Arrays on strings as lists

Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u that is
a left string of length L."  In a program such an array is a list: an array on the strings of length
`n` over an alphabet of `b` letters is the list of its `b^n` entries in the order of the codes
(`arrStr`), so the entry at a string is the entry of the list at the code of the string
(`getD_arrStr`), and an entry of the list is 0 if the array is 0 at the string with that code
(`getD_arrStr_eq_zero`).  The arrays on left strings, on right strings and on leaves are the cases
`arrL`, `arrR` and `arrT`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Arrays on the strings over any numbered alphabet -/

section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)

/-- An array on the strings of length `n` over an alphabet numbered by `e : α ≃ Fin b`, as the list
of its `b^n` entries in the order of the codes. -/
def arrStr : List ℤ :=
  (List.range (b ^ n)).map fun c => a (decodeStr e n c)























end

/-! ## The three kinds of arrays of Section 2 that the programs store -/

/-- An array on the left strings of length `n`, as the list of its `7^n` entries. -/
def arrL {n : ℕ} (a : LeftStr n → ℤ) : List ℤ := arrStr leftEquiv a

/-- An array on the right strings of length `n`, as the list of its `7^n` entries. -/
def arrR {n : ℕ} (b : RightStr n → ℤ) : List ℤ := arrStr rightEquiv b

/-- An array on the leaves (for example an encoding), as the list of its `10^n` entries. -/
def arrT {n : ℕ} (enc : Leaf n → ℤ) : List ℤ := arrStr termEquiv enc



























end ThreeSumApsp.Spec


