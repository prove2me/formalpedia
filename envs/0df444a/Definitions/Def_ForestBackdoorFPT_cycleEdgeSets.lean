-- Prove2me | Definitions.Def_ForestBackdoorFPT_cycleEdgeSets
-- name    : ForestBackdoorFPT_cycleEdgeSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:34.436198+00:00
-- url     : https://prove2.me/theorems/6332240d-1344-4e95-98cd-5623659b5385
-- title:
--   Distinct simple cycles of a graph
-- statement:
--   The **distinct simple cycles** of a graph $G$: each simple cycle of $G$ (a closed walk of length at least $3$ that repeats no edge and no vertex other than its endpoint) is recorded by its set of edges. Two walks around the same cycle (another start vertex or the other direction) give the same edge set, and two different simple cycles give different edge sets, so this set is in bijection with the distinct simple cycles of $G$.
--
--   Lemma 2.2 bounds the number of distinct simple cycles in the 2-core by $2^{\mathrm{cyc}(G)}-1$.
-- source:
--   Bilyk–Munduzbaev–Sharma–Siam, Strong Backdoor to Forests is FPT: Tight Linear-Time FPT for Essentially General SAT, STOC 2027 submission (manuscript sha256 7fd1a7a8…), Lemma 2.2, p.5 (PDF p.6)

import Mathlib

set_option autoImplicit false

namespace ForestBackdoorFPT

/-- The **distinct simple cycles** of a graph (Bilyk–Munduzbaev–Sharma–Siam, *Strong Backdoor to
Forests is FPT*, STOC 2027 submission (manuscript sha256 7fd1a7a8…), Lemma 2.2, p.5 (PDF p.6)),
each represented by its edge set.

**Formalization Note** A simple cycle is a closed walk `p` with `p.IsCycle` (Mathlib: a nonempty
trail whose only repeated vertex is its endpoint, so of length at least 3). The same cycle is
traversed by many walks (any start vertex, either direction); all of them have the same edge set,
and two different simple cycles have different edge sets. Counting edge sets therefore counts
distinct simple cycles once each. -/
def cycleEdgeSets {W : Type*} (G : SimpleGraph W) : Set (Set (Sym2 W)) :=
  {s | ∃ (v : W) (p : G.Walk v v), p.IsCycle ∧ {e | e ∈ p.edges} = s}

end ForestBackdoorFPT


