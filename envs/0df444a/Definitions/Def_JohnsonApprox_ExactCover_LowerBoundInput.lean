-- Prove2me | Definitions.Def_JohnsonApprox_ExactCover_LowerBoundInput
-- name    : JohnsonApprox_ExactCover_LowerBoundInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:30:44.050974+00:00
-- url     : https://prove2.me/theorems/ae35e4fb-6e54-44b3-8f9e-a08c1421c263
-- title:
--   The lower-bound input of Theorem 6: Fig. 1 with every set of F₁ filled out to k points
-- statement:
--   The lower bound of Theorem 6 "follows from an example much like that given in Fig. 1, except that all the sets in $F_1$ are filled out with points from segment $k$ so that each has exactly $k$ elements" (p. 271). Fig. 1 (pp. 265–266) is the following input for $k \ge 1$.
--
--   1. The covered set $T$ consists of $k \cdot k!$ points $(s, r)$, divided into $k$ **segments** $s = 1, \dots, k$ of $k!$ points each, $r = 0, \dots, k! - 1$.
--   2. $F_0$ consists of $k!$ disjoint sets $\{(1, r), (2, r), \dots, (k, r)\}$, one point from each segment.
--   3. For each $j = 1, \dots, k$, $F_1$ contains $k!/j$ disjoint $j$-element sets covering segment $j$: the $q$-th of them is $\{(j, qj), (j, qj+1), \dots, (j, qj + j - 1)\}$.
--
--   For Theorem 6 each $j$-element set of $F_1$ is filled out with the $k - j$ points $(k, 0), \dots, (k, k - j - 1)$ of segment $k$, so that every set of the family has exactly $k$ elements. The input is the family $F_0$ followed by $F_1$ (segment $1$ first, then segment $2$, …, segment $k$).
--
--   **Formalization Note** The paper does not say which points of segment $k$ fill a set; the first $k - j$ are used. At $k = 2$ one filled-out set of $F_1$ coincides with a set of $F_0$ (any choice of filler has this effect); the family is indexed, so the two copies are distinct members. The family is built as a `List` and indexed by `Fin` of its length.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 271, proof of Theorem 6 (lower bound); pp. 265–266, Fig. 1

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem

namespace JohnsonApprox.ExactCover

/-- The points are pairs `(s, r)`: segment `s ∈ {1, …, k}`, position `r ∈ {0, …, k! − 1}`.
`lbF0 k r` is the `r`-th set of `F₀`: one point `(s, r)` from each segment `s = 1, …, k`. -/
def lbF0 (k r : ℕ) : Finset (ℕ × ℕ) := (Finset.Icc 1 k).image (fun s => (s, r))

/-- `lbBlock k j q` is the `q`-th set of `F₁` covering segment `j` (`q < k!/j`): the `j` points
`(j, q·j), …, (j, q·j + j − 1)` of segment `j`, filled out with the `k − j` points
`(k, 0), …, (k, k − j − 1)` of segment `k`, so that it has exactly `k` elements. -/
def lbBlock (k j q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range j).image (fun t => (j, q * j + t)) ∪ (Finset.range (k - j)).image (fun t => (k, t))

/-- The family `F₀ ++ F₁`: the `k!` sets of `F₀`, then for `j = 1, …, k` the `k!/j` sets of `F₁`
covering segment `j`. -/
def lbSets (k : ℕ) : List (Finset (ℕ × ℕ)) :=
  (List.range k.factorial).map (lbF0 k) ++
    (List.range' 1 k).flatMap (fun j => (List.range (k.factorial / j)).map (lbBlock k j))

/-- The lower-bound input of Theorem 6 (Fig. 1 with every set of `F₁` filled out from segment `k`
to exactly `k` elements), as an EC input indexed by positions in `lbSets k`. -/
def lbInput (k : ℕ) : Input (ℕ × ℕ) := ⟨(lbSets k).length, fun i => (lbSets k).get i⟩

end JohnsonApprox.ExactCover


