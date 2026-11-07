-- Prove2me | Definitions.Def_AKSZigZag_IsStandard
-- name    : AKSZigZag_IsStandard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:11.767079+00:00
-- url     : https://prove2.me/theorems/f4b2b71f-6b4f-442c-809d-9150e3a134d6
-- title:
--   Standard comparator network: every switch $(i,j)$ has $i<j$
-- statement:
--   A comparator network on the registers $1,\dots,n$ is a fixed sequence of parallel steps, each a set of disjoint switches. A switch $(i,j)$ compares the contents of registers $i$ and $j$ and puts the smaller one into register $i$ and the larger one into register $j$.
--
--   The network is **standard** when every switch $(i,j)$ in it has
--   $$
--   i<j .
--   $$
--   So every switch sends the larger element to the higher register. This is the model of the paper: "a switch is a pair $(i,j)$, $1\le i<j\le n$".
--
--   Every network statement of the mission is about standard networks. Without this condition a network may also send the minimum to the higher register, and the headline result becomes the weaker form already posed on the platform.
--
--   **Formalization Note** The published `AKSSorting.Core.ComparatorNetwork` allows switches in either direction; this predicate restores the paper's model. Registers are `Fin n`, numbered from $0$.
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, Introduction, p.1

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork

namespace AKSZigZag

open AKSSorting.Core

/-- **Standard comparator networks** (Ajtai, Komlós, Szemerédi, *An O(n log n) Sorting Network*,
STOC 1983, doi:10.1145/800061.808726, Introduction, p.1): "a switch is a pair (i,j),
1 ≤ i < j ≤ n, and … puts the larger one into the jth register and the smaller one into the ith
register". A network is standard when every comparator `(i, j)` of every layer has `i < j`.

**Formalization Note.** The published `AKSSorting.Core.ComparatorNetwork` lets a comparator
`(i, j)` have `i > j` (the minimum then goes to the higher register); this predicate restores the
paper's model. Registers are `Fin n` (0-based) for the paper's `1, …, n`. -/
def IsStandard {n : ℕ} (N : ComparatorNetwork n) : Prop :=
  ∀ L ∈ N.layers, ∀ p ∈ L, p.1 < p.2

end AKSZigZag


