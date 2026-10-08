-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
-- name    : APSPSource_ThreeSumApsp_Spec_Sec3_Problems
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:09:46.244632+00:00
-- url     : https://prove2.me/theorems/656fcba9-1579-466d-b3e4-0a773bf3c43d
-- title:
--   List representations of graph and min-plus inputs
-- statement:
--   For a matrix stored in an integer list $A$ with $n$ columns, define its entry by $A_{ij}=A[in+j]$, reading zero beyond the list. The bundle similarly views a list as a finite vector and three lists as the three edge-weight arrays of a complete tripartite graph. A directed graph encoded by adjacency list $E$ and weight list $W$ has weight $W[in+j]$ when $E[in+j]=1$ and $+\infty$ otherwise.
--
--   Further functions apply an affine map $x\mapsto mx+c$ entrywise and extract a specified square submatrix. For $n\ge1$, a running minimum specifies the integer min-plus entry
--
--   $$C_{ij}=\min_{0\le k<n}(A_{ik}+B_{kj}).$$
--
--   The output list contains these entries in row-major order and has length $n^2$. Included structural properties say that an entry is at most every candidate sum, equals some candidate when $n\ge1$, and is found at index $in+j$ for valid $i,j<n$. At $n=0$, the product list is empty; the total auxiliary entry function retains its initialized value.
--
--   These definitions connect mathematical problem instances with the lists read and written by concrete routines.
--
--   References:
--
--   1. [Source formalization, lines 32–33](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L32-L33).
--   2. [Source formalization, lines 40–54](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L40-L54).
--   3. [Source formalization, lines 66–67](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L66-L67).
--   4. [Source formalization, lines 73–76](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L73-L76).
--   5. [Source formalization, lines 96–120](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L96-L120).
--   6. [Source formalization, lines 132–137](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L132-L137).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L32-L33; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L40-L54; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L66-L67; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L73-L76; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L96-L120; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Problems.lean#L132-L137

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The problems for Section 3.4, read from lists of integers

A routine has its input in arrays.  Here an array is a list of integers, a matrix is stored row by
row, and a cell is read with `List.getD _ _ 0` (`entry`).  This file says which instance of Exact
Triangle, Negative Triangle, Convolution-3SUM, 3SUM or APSP such lists hold (`vecOf`, `triOf`,
`graphOf`), and what the (min,+)-product of two lists is (`minPlusEntry`, `minPlusList`).  Two
operations on matrices serve several reductions: `affL m c` replaces each entry `x` by `m x + c`,
and `subMat` cuts out a block.

An entry of the (min,+)-product is computed as a running minimum.  It is at most each of the sums
`A[i,k] + B[k,j]` (`minPlusEntry_le`) and it is one of them (`exists_minPlusEntry_eq`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Instances -/

/-- The entry `(i, j)` of a matrix with `n` columns that is stored in the list `L`, row by row. -/
abbrev entry (n : ℕ) (L : List ℤ) (i j : ℕ) : ℤ := L.getD (i * n + j) 0






/-- The `N` numbers in a list. -/
def vecOf (N : ℕ) (x : List ℤ) : Fin N → ℤ := fun i => x.getD i 0

/-- The complete tripartite graph with `n` vertices per part whose three weight matrices are in
three lists, row by row: the weight of `(a, b)` at `a n + b` of the first, of `(b, c)` at `b n + c`
of the second, of `(a, c)` at `a n + c` of the third. -/
def triOf (n : ℕ) (AB BC AC : List ℤ) : TriangleInstance ℤ n where
  wAB a b := AB.getD (a * n + b) 0
  wBC b c := BC.getD (b * n + c) 0
  wAC a c := AC.getD (a * n + c) 0

/-- The weight matrix of a directed graph on `n` vertices: the weight of the edge `(i, j)` is in
cell `i n + j` of `w` if cell `i n + j` of `adj` holds 1, and there is no edge otherwise. -/
def graphOf (n : ℕ) (adj w : List ℤ) : Fin n → Fin n → WithTop ℤ := fun i j =>
  if adj.getD (i * n + j) 0 = 1 then ((w.getD (i * n + j) 0 : ℤ) : WithTop ℤ) else ⊤









/-! ## Operations on matrices -/

/-- The list of the numbers `m x + c`. -/
def affL (m c : ℤ) (l : List ℤ) : List ℤ := l.map fun x => m * x + c





/-- The `h × h` block of an `s × s` matrix whose upper left corner is `(r0, c0)`; both row by
row. -/
def subMat (s h r0 c0 : ℕ) (L : List ℤ) : List ℤ :=
  (List.range (h * h)).map fun q => entry s L (r0 + q / h) (c0 + q % h)

















/-! ## The (min,+)-product -/

/-- The smallest of `A[i,k] + B[k,j]` over `k < n`, by one pass, for `n ≥ 1`. -/
def minPlusEntry (n : ℕ) (A B : List ℤ) (i j : ℕ) : ℤ :=
  (List.range (n - 1)).foldl
    (fun acc k => min acc (entry n A i (k + 1) + entry n B (k + 1) j))
    (entry n A i 0 + entry n B 0 j)

/-- The (min,+)-product of two `n × n` matrices, row by row. -/
def minPlusList (n : ℕ) (A B : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => minPlusEntry n A B (q / n) (q % n)

/-- The (min,+)-product has `n²` entries. -/
theorem length_minPlusList (n : ℕ) (A B : List ℤ) : (minPlusList n A B).length = n * n := by
  simp [minPlusList]

/-- An entry of the product is at most each of the sums. -/
theorem minPlusEntry_le (n : ℕ) (A B : List ℤ) (i j : ℕ) {k : ℕ} (hk : k < n) :
    minPlusEntry n A B i j ≤ entry n A i k + entry n B k j :=
  List.foldl_min_le (fun k => entry n A i k + entry n B k j) (n - 1) (by omega)

/-- An entry of the product is one of the sums. -/
theorem exists_minPlusEntry_eq {n : ℕ} (hn : 1 ≤ n) (A B : List ℤ) (i j : ℕ) :
    ∃ k < n, minPlusEntry n A B i j = entry n A i k + entry n B k j := by
  obtain ⟨k, hk, he⟩ :=
    List.exists_foldl_min_eq (fun k => entry n A i k + entry n B k j) (n - 1)
  exact ⟨k, by omega, he⟩











/-- The entry `(i, j)` of the product stands at the place `i n + j`. -/
theorem entry_minPlusList {n : ℕ} (A B : List ℤ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (minPlusList n A B) i j = minPlusEntry n A B i j := by
  rw [entry, minPlusList, List.getD_map_range _ (Nat.mul_add_lt_mul hi hj),
    Nat.mul_add_div_of_lt hj,
    Nat.mul_add_mod_of_lt hj]

end ThreeSumApsp.Spec


