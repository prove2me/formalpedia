-- Prove2me | Definitions.Def_RobersonCx_IsCyclicInterval
-- name    : RobersonCx_IsCyclicInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:47.32239+00:00
-- url     : https://prove2.me/theorems/dfccfe9e-6707-450e-a58d-bd5cbfc35159
-- title:
--   Specified Hamilton cycles, cyclic intervals, and consecutive vertex sets
-- statement:
--   A **specified Hamilton cycle** $C$ of a graph $G$ on $N\ge3$ vertices is a cyclic ordering $c_0,c_1,\dots,c_{N-1}$ of all vertices with $c_ic_{i+1}\in E(G)$ for every $i$ (indices mod $N$); $E(C)=\{c_ic_{i+1}\}$.
--
--   A **cyclic interval** is a nonempty proper set of consecutive vertices in the cyclic order of $C$:
--   $$\{c_a,c_{a+1},\dots,c_{a+\ell-1}\},\qquad 0<\ell<N.$$
--   Two vertex sets are **consecutive around $C$** if some edge of $C$ has one endpoint in each.
--
--   Lemma 19 shows that, under treewidth conditions, every minor model partitions the host into cyclic intervals that follow the base Hamilton cycle.
--
--   **Formalization Note** The cycle is a bijection `c : ZMod N ≃ V` with `G.Adj (c i) (c (i + 1))` and `3 ≤ N` (`IsHamCycle`). For pairwise disjoint cyclic intervals covering the cycle, "consecutive" (`ConsecOnCycle`) is the same as one interval immediately following the other.
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. B, p.16 (PDF p.18)

import Mathlib

set_option autoImplicit false

namespace RobersonCx

/-- `c` lists a specified Hamilton cycle of `G` (App. B, p.16 (PDF p.18)): `c : ZMod N ≃ V` is a cyclic ordering
of all vertices with `c i` adjacent to `c (i + 1)` for every `i`, and `N ≥ 3`.

**Formalization Note** The cycle `C` is `c 0, c 1, …, c (N − 1), c 0`; its edge set is `cycleEdges c`. -/
def IsHamCycle {V : Type*} (G : SimpleGraph V) {N : ℕ} (c : ZMod N ≃ V) : Prop :=
  3 ≤ N ∧ ∀ i : ZMod N, G.Adj (c i) (c (i + 1))

/-- The edge set `E(C)` of the Hamilton cycle listed by `c`: the pairs `{c i, c (i + 1)}`. -/
def cycleEdges {V : Type*} {N : ℕ} (c : ZMod N ≃ V) : Set (Sym2 V) :=
  {e | ∃ i : ZMod N, e = s(c i, c (i + 1))}

/-- A cyclic interval on the cycle listed by `c` (App. B, p.16 (PDF p.18)): "a nonempty proper set of consecutive
vertices in the cyclic order of a specified Hamilton cycle", i.e. `{c a, c (a + 1), …, c (a + ℓ − 1)}` with
`0 < ℓ < N`. -/
def IsCyclicInterval {V : Type*} {N : ℕ} (c : ZMod N ≃ V) (S : Set V) : Prop :=
  ∃ (a : ZMod N) (ℓ : ℕ), 0 < ℓ ∧ ℓ < N ∧ S = {v | ∃ j < ℓ, v = c (a + (j : ZMod N))}

/-- Two vertex sets are consecutive around the cycle listed by `c` (Lemma 19, p.16): some edge of the cycle has
one endpoint in each.

**Formalization Note** For pairwise disjoint cyclic intervals covering the cycle, as in Lemma 19, this is the
same as one interval immediately following the other. -/
def ConsecOnCycle {V : Type*} {N : ℕ} (c : ZMod N ≃ V) (S S' : Set V) : Prop :=
  ∃ i : ZMod N, (c i ∈ S ∧ c (i + 1) ∈ S') ∨ (c i ∈ S' ∧ c (i + 1) ∈ S)

end RobersonCx


