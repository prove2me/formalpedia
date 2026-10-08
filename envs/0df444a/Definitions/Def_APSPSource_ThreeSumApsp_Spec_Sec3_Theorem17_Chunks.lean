-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Chunks
-- name    : APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Chunks
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:23:43.574988+00:00
-- url     : https://prove2.me/theorems/6da282df-2e95-43cc-93b3-f175b8a471a8
-- title:
--   Residue-class query lists and bounded chunks
-- statement:
--   Let $n,p$ be natural numbers and let $R$ be a row-major list of residues for $n^2$ ordered pairs. Missing list entries are read as zero. For each residue $\rho$, list its pair indices in increasing order and define its starting offset by
--
--   $$I_\rho=[i\in\{0,\ldots,n^2-1\}:R_i=\rho],\qquad s_\rho=\sum_{r<\rho}|I_r|.$$
--
--   Concatenating $I_0,\ldots,I_{p-1}$ gives the class-ordered query list. An index $i$ identifies row $\lfloor i/n\rfloor$ and column $i\bmod n$.
--
--   A chunk stores a residue, a starting position, and a length. For a positive capacity $q$, a class segment $[a,b)$ is divided into the chunks
--
--   $$\left(\rho,\ a+jq,\ \min\{q,b-a-jq\}\right),\qquad 0\le j<\left\lceil\frac{b-a}{q}\right\rceil.$$
--
--   Natural-number subtraction is truncated at zero. Chunk tables apply this construction to every consecutive pair of class offsets. A containment predicate records membership in a chunk's half-open interval; a separate fitting predicate requires residue below $p$, length between $1$ and $q$, and endpoint at most $n^2$.
--
--   These data specify the query batches in the Exact Triangle reduction. Coverage, uniqueness, and bounds on the number of chunks are separate correctness results.
--
--   References:
--
--   1. [Source formalization: class lists and offsets](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L38-L74).
--   2. [Source formalization: chunk records and tables](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L134-L169).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L38-L50; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L69-L74; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L134-L169

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The table of the chunks (proof of Theorem 17)

"For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod p), and cut it into
chunks of at most n²/√D query pairs."  The routine lists the pairs class after class (`sortedIdx`).
Then a class is a segment of the list, from `classStart ϱ` to `classStart (ϱ + 1)`, and a chunk is a
segment of a class.  The table `chunkTab` has one entry for each chunk: its residue, the place where
it starts, and its number of pairs.

* The list has every pair once (`sortedIdx_nodup`, `classStart_eq_sq`), and the places of a class
  hold pairs of that class (`getD_sortedIdx_class`).
* An entry of the table is a nonempty segment of at most `cap` places (`chunkTab_entry`) whose pairs
  have the residue of the entry (`chunkTab_class`).
* The chunks follow each other (`chunkTab_pairwise`), so every place lies in exactly one chunk
  (`chunkTab_cover`, `chunkTab_unique`).
* "There are at most p + √D ≤ 2√D chunks in all" (`length_chunkTab_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

variable {n p cap : ℕ} {RAB : List ℕ}

/-! ## The classes and the list of all the pairs -/

/-- The places `a n + b` of the pairs of the class `W_ϱ`, in increasing order; `RAB` holds the
residues. -/
def classIdx (n : ℕ) (RAB : List ℕ) (rho : ℕ) : List ℕ :=
  (List.range (n * n)).filter fun i => RAB.getD i 0 = rho

/-- All the places, class after class. -/
def sortedIdx (n p : ℕ) (RAB : List ℕ) : List ℕ := (List.range p).flatMap (classIdx n RAB)

/-- The rows of the pairs, class after class. -/
def queryRows (n p : ℕ) (RAB : List ℕ) : List ℕ := (sortedIdx n p RAB).map (· / n)

/-- The columns of the pairs, class after class. -/
def queryCols (n p : ℕ) (RAB : List ℕ) : List ℕ := (sortedIdx n p RAB).map (· % n)
















/-! ## The starts of the classes -/

/-- The place where the class `rho` starts: the number of pairs with a residue below `rho`. -/
def classStart (n : ℕ) (RAB : List ℕ) (rho : ℕ) : ℕ :=
  ((List.range rho).map fun r => (classIdx n RAB r).length).sum

/-- The table of the places where the classes start: entry `ϱ ≤ p` is `classStart n RAB ϱ`. -/
def classStarts (n p : ℕ) (RAB : List ℕ) : List ℕ := (List.range (p + 1)).map (classStart n RAB)

























































/-! ## The chunks -/

/-- A chunk: a segment of the list of all the pairs that lies within one class. -/
structure Chunk where
  /-- The residue of the class. -/
  residue : ℕ
  /-- The place in the list where the chunk starts. -/
  start : ℕ
  /-- The number of places of the chunk. -/
  len : ℕ

/-- The place `j` lies in the chunk. -/
def Chunk.Contains (x : Chunk) (j : ℕ) : Prop := x.start ≤ j ∧ j < x.start + x.len

/-- The chunk has a residue below `p`, and it is a nonempty segment of at most `cap` of the `n²`
places. -/
structure Chunk.Fits (x : Chunk) (n p cap : ℕ) : Prop where
  residue_lt : x.residue < p
  len_pos : 1 ≤ x.len
  len_le : x.len ≤ cap
  end_le : x.start + x.len ≤ n * n

/-- The segment `[lo, hi)` of the class `rho`, cut into chunks of `cap` places; the last one may be
shorter. -/
def chunksOf (cap lo hi rho : ℕ) : List Chunk :=
  (List.range ((hi - lo) ⌈/⌉ cap)).map fun i => ⟨rho, lo + i * cap, min cap (hi - lo - i * cap)⟩

/-- The chunks of `p` segments, of which number `rho` goes from entry `rho` to entry `rho + 1` of
the list `C`. -/
def chunkTabOf (p cap : ℕ) (C : List ℕ) : List Chunk :=
  (List.range p).flatMap fun rho => chunksOf cap (C.getD rho 0) (C.getD (rho + 1) 0) rho

/-- The table of the chunks, with one entry for each chunk of each class. -/
def chunkTab (n p cap : ℕ) (RAB : List ℕ) : List Chunk := chunkTabOf p cap (classStarts n p RAB)

/-- Chunk number `i` of the class `rho`. -/
def chunkAt (n cap : ℕ) (RAB : List ℕ) (rho i : ℕ) : Chunk :=
  ⟨rho, classStart n RAB rho + i * cap, min cap ((classIdx n RAB rho).length - i * cap)⟩



















































































































end ThreeSumApsp.Spec


