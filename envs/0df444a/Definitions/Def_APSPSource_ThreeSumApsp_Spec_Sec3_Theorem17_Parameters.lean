-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
-- name    : APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:22:26.769706+00:00
-- url     : https://prove2.me/theorems/cf241f92-2bf7-4ae5-b1b4-24e0e4350b88
-- title:
--   Integer parameter formulas for the Exact Triangle reduction
-- statement:
--   The bundle defines integer root functions by finite greatest-element searches. On the intended domain $e,t\ge1$, they give $\lfloor t^{1/e}\rfloor$ and $\lceil t^{1/e}\rceil$. The parameter functions used with Corollary 26 are
--
--   $$D(n)=\lfloor n^{1/18}\rfloor,\qquad g(D)=\lceil D^{63/2000}\rceil\quad(D\ge1).$$
--
--   For natural parameters $n,D,g$, the remaining definitions use integer square roots and ceiling division:
--
--   $$q(n,D)=\operatorname{isqrt}\!\left(\left\lfloor\frac{n^4}{D}\right\rfloor\right),\qquad s(D,g)=\left\lceil\frac{\operatorname{isqrt}(D)}{g}\right\rceil,\qquad h(n,D,g)=\left\lceil\frac{n}{s(D,g)}\right\rceil.$$
--
--   Here $\operatorname{isqrt}$ is the natural-number square root. In their positive-denominator uses, $q$ is the query capacity, $s$ the number of vertices in a piece, and $h$ the number of pieces.
--
--   The integer formulas make the parameter choices available to concrete routines. Their agreement with real-power formulas and the inequalities required by the reduction are established in later theorems.
--
--   **Formalization Note** The definitions are total at zero using Lean's finite-search, division, and ceiling-division conventions. In particular the ceiling-root definition is a greatest-element search plus one; the real-root interpretation above is restricted to positive $e,t$.
--
--   References:
--
--   1. [Source formalization: integer roots](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Parameters.lean#L40-L44).
--   2. [Source formalization: dimension and exponent parameters](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Parameters.lean#L99-L103).
--   3. [Source formalization: capacities and pieces](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Parameters.lean#L174-L181).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Parameters.lean#L40-L44; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Parameters.lean#L99-L103; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Parameters.lean#L174-L181

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The parameters of Theorems 17 and 19 in integer arithmetic

The proof of Theorem 19 chooses `D` and `g` as rounded real powers of `n`: "Let D be the largest
power of four with D ≤ n^{1/18}, […] and let g := ⌈D^{1/36}⌉" on the route through Theorem 5, and
"Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉" on the route through Corollary 26.  The reduction of
Theorem 17 cuts each residue class into chunks of at most `n²/√D` query pairs and splits `C` into
pieces of at most `⌈s/g⌉` vertices, where `s = ⌊√D⌋`.  A program finds all these numbers by
operations on natural numbers.

* `rootFloor e t` is `⌊t^{1/e}⌋` and `rootCeil e t` is `⌈t^{1/e}⌉` (`floor_rpow_inv`,
  `ceil_rpow_inv`); they are characterised by `x ≤ rootFloor e t ↔ x^e ≤ t` (`le_rootFloor_iff`) and
  `rootCeil e t ≤ g ↔ t ≤ g^e` (`rootCeil_le_iff`).
* The four functions `paramD₅Nat`, `paramG₅Nat`, `paramD₂₆Nat`, `paramG₂₆Nat` are the parameters
  of the proof of Theorem 19 (`paramD₅Nat_eq`, `paramG₅Nat_eq`, `paramD₂₆Nat_eq`, `paramG₂₆Nat_eq`);
  they are at least 1 and at most `n` or `D` (`paramD₂₆Nat_le`, `paramG₅Nat_le`, `paramG₂₆Nat_le`).
* The sizes of the proof of Theorem 17: `⌊n²/√D⌋ = ⌊√(n⁴/D)⌋` (`queryCapNat_eq`), `s` is the integer
  square root (`sOf_eq_sqrt`), and the rounded quotients are `a ⌈/⌉ b` (`pieceSizeNat_eq`,
  `numPiecesNat_eq`, `numChunks_eq`).  The middle part `C_k × ℤ_p` of an instance has at most `D`
  vertices (`pieceSize_mul_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Roots, rounded down and up -/

/-- The greatest `x ≤ t` with `x^e ≤ t`: `⌊t^{1/e}⌋` for `e ≥ 1`. -/
def rootFloor (e t : ℕ) : ℕ := Nat.findGreatest (fun x => x ^ e ≤ t) t

/-- The least `g` with `g^e ≥ t`, for `t ≥ 1` and `e ≥ 1`: `⌈t^{1/e}⌉`. -/
def rootCeil (e t : ℕ) : ℕ := Nat.findGreatest (fun g => g ^ e < t) t + 1














































/-! ## The parameters of the proof of Theorem 19 -/







/-- "Let D := ⌊n^{1/18}⌋". -/
def paramD₂₆Nat (n : ℕ) : ℕ := rootFloor 18 n

/-- "and g := ⌈D^{0.0315}⌉": the least `g` with `g^2000 ≥ D^63`. -/
def paramG₂₆Nat (D : ℕ) : ℕ := rootCeil 2000 (D ^ 63)




































































/-! ## The sizes of the instances of the proof of Theorem 17 -/

/-- `⌊n²/√D⌋`, the largest number of query pairs of an instance. -/
def queryCapNat (n D : ℕ) : ℕ := Nat.sqrt (n ^ 4 / D)

/-- The number of vertices `⌈s/g⌉` of a piece of `C`, with `s = ⌊√D⌋`. -/
def pieceSizeNat (D g : ℕ) : ℕ := Nat.sqrt D ⌈/⌉ g

/-- The number of pieces. -/
def numPiecesNat (n D g : ℕ) : ℕ := n ⌈/⌉ pieceSizeNat D g






























































end ThreeSumApsp.Spec


