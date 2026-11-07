-- Prove2me | Definitions.Def_PlantedIQP_IsVertexCover
-- name    : PlantedIQP_IsVertexCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:32.50469+00:00
-- url     : https://prove2.me/theorems/6b6c4bbd-25c8-4f21-b2a0-9a0e55ed2955
-- title:
--   The polynomial hypergraph $H(f)$ and its vertex covers
-- statement:
--   The **polynomial hypergraph** $H(f)$ of a cubic polynomial $f$ has vertex set $[n]$ and hyperedges
--
--   $$
--   E=\{\{i,j,k\}: F_{ijk}=1,\ i<j<k\}.
--   $$
--
--   A **vertex cover** of a hypergraph with hyperedge set $E$ is a set $C$ of vertices meeting every hyperedge: for every $e\in E$ there is $v\in e$ with $v\in C$.
--
--   A vertex cover of $H(f)$ leaves no cubic monomial among the uncovered variables, which is what makes the amplitude decomposition of Lemma 40 work.
--
--   **Formalization Note** The source writes $C\subset V$; it is read as $C\subseteq V$, since the proof of Theorem 41 uses $C=[h+1,\dots,n]$, which is all of $[n]$ when $h=0$.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Definition 21, p.16 and Definition 39, p.24

import Mathlib
import Definitions.Def_PlantedIQP_CubicPoly

set_option autoImplicit false

namespace PlantedIQP

/-!
# The polynomial hypergraph `H(f)` and its vertex covers

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), Definition 21, p.16: "Given a cubic polynomial
f ∈ 𝔽₂[x₁, …, xₙ], the hypergraph H(f) = (V, E) is defined by the trilinear coefficients F_ijk as
follows: Let V = [n] be the vertex set, and let the set of hyperedges be
E = {{i, j, k} : F_ijk = 1, i < j < k}." Definition 39, p.24: "Let H = (V, E) be a hypergraph.
Then a vertex cover is a set C ⊂ V satisfying ∀e ∈ E ∃v ∈ e : v ∈ C, i.e., every hyperedge overlaps
with C."

**Formalization Note.**
* A hypergraph on the vertex set `Fin n` is given by its set of hyperedges `E : Set (Finset (Fin n))`.
* The source's `C ⊂ V` is read as `C ⊆ V`: the proof of Theorem 41 uses the cover
  `C = [h + 1, …, n]`, which is all of `V` when `h = 0`.
-/

/-- The hyperedges of `H(f)`: the index sets `{i, j, k}` with `F_{ijk} = 1` (Definition 21). -/
def polyHypergraph {n : ℕ} (f : CubicPoly n) : Set (Finset (Fin n)) :=
  {e | ∃ S : Mono n 3, f.c3 S = 1 ∧ S.1 = e}

/-- `C` is a vertex cover of the hypergraph with hyperedge set `E`: every hyperedge meets `C`
(Definition 39). -/
def IsVertexCover {n : ℕ} (E : Set (Finset (Fin n))) (C : Finset (Fin n)) : Prop :=
  ∀ e ∈ E, ∃ v ∈ e, v ∈ C

end PlantedIQP


