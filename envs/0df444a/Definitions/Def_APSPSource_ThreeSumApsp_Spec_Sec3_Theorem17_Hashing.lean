-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
-- name    : APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:23:49.992185+00:00
-- url     : https://prove2.me/theorems/30675d42-756d-4bc6-826a-7031b70281c6
-- title:
--   Residue tables, doubling tables, and prime candidates
-- statement:
--   For a positive natural modulus $p$ and an integer $w$, the residue function gives the natural representative
--
--   $$r_p(w)=w\bmod p\in\{0,\ldots,p-1\}.$$
--
--   Applying it entrywise gives a residue list. For a length parameter $h$, a doubling table stores $p,2p,\ldots,2^hp$. The binary-length function is the number of binary digits of a natural number $U$, with length zero when $U=0$.
--
--   For a natural dimension $D$, the candidate-prime list is defined by integer tests:
--
--   $$\mathcal P_D=[p\in\{0,\ldots,D-1\}:p\text{ is prime},\ D\le4p^2,\ p^2<D].$$
--
--   These are the residue representations and finite search data used when selecting a modulus for the Exact Triangle reduction. The bundle defines the data; subsequent results justify its mathematical and machine-level uses.
--
--   **Formalization Note** The residue function is also defined at $p=0$ as the natural-number conversion of the integer remainder; the stated residue range requires $p>0$.
--
--   References:
--
--   1. [Source formalization: residues](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Hashing.lean#L30-L31).
--   2. [Source formalization: tables and binary length](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Hashing.lean#L56-L69).
--   3. [Source formalization: prime candidate list](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Hashing.lean#L96-L98).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Hashing.lean#L30-L31; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Hashing.lean#L56-L57; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Hashing.lean#L65-L69; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Hashing.lean#L96-L98

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
# Hashing modulo a prime (proof of Theorem 17), on numbers and lists

The reduction of Theorem 17 hashes the weights modulo a prime `p` of the window `√D/2 ≤ p < √D` and
selects the prime with the fewest triples `(a,b,c)` with `S(a,b,c) ≡ 0 (mod p)`, where
`S(a,b,c) = w(a,b) + w(b,c) + w(a,c)`.  This file has the parts of this step that a program
computes:

* the residue of a weight as a natural number below `p` (`resid`, `residList`);
* the entries of the matrices `P` and `Q` of the proof of Theorem 17 as unit vectors (`cycVec_matP`,
  `cycVec_matQ`), and the count of the triples, read off the vectors of `PQ` (`countZeroMod_eq`);
* the primes of the window by comparisons of integers (`primesList`, `primesInRange_eq`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Residues -/

/-- The residue of `w` modulo `p` in `{0, …, p − 1}`. -/
def resid (p : ℕ) (w : ℤ) : ℕ := (w % (p : ℤ)).toNat
























/-- The residues of a list. -/
def residList (p : ℕ) (l : List ℤ) : List ℕ := l.map (resid p)







/-- The table `p, 2p, 4p, …, 2^len p`. -/
def dblList (p len : ℕ) : List ℤ := (List.range (len + 1)).map fun j : ℕ => ((p * 2 ^ j : ℕ) : ℤ)

/-- The number of binary digits of `U`: the least `len` with `U < 2^len`. -/
def bitLen (U : ℕ) : ℕ := Nat.size U

/-! ## The count of the proof of Theorem 17 -/






















/-! ## The primes of the window -/

/-- The primes `p` with `√D/2 ≤ p < √D`, by integer comparisons: `D ≤ 4p²` and `p² < D`. -/
def primesList (D : ℕ) : List ℕ :=
  (List.range D).filter fun p => p.Prime ∧ D ≤ 4 * p ^ 2 ∧ p ^ 2 < D































end ThreeSumApsp.Spec


