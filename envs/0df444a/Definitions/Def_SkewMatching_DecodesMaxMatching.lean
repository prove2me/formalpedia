-- Prove2me | Definitions.Def_SkewMatching_DecodesMaxMatching
-- name    : SkewMatching_DecodesMaxMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:29.607618+00:00
-- url     : https://prove2.me/theorems/a7e7da0b-84fb-424f-ab46-b23ebd7c6f4d
-- title:
--   Matchings, edge listings, and the input and output layouts of Theorem 1
-- statement:
--   A **matching** of a graph $G$ is a set of edges of $G$ in which two distinct edges share no vertex; it is **maximum** if no matching of $G$ has more edges.
--
--   An **edge listing** of $G$ on the vertex set $\{0,\dots,n-1\}$ is a list of ordered pairs in which every pair is an edge of $G$ and every edge of $G$ occurs exactly once, in either orientation.
--
--   The input memory of Theorem 1 holds $n$ in cell $0$, the list length $L$ in cell $1$, and the two endpoints of the $j$-th listed edge in cells $2+2j$ and $3+2j$; all other cells hold $0$. The output is read from the memory of the halted machine: cell $-1$ holds $\ell$, cells $-2-2j$ and $-3-2j$ hold the endpoints of the $j$-th edge, and these $\ell$ pairs must be exactly the edges of a maximum matching of $G$, each once.
--
--   **Formalization Note** The paper fixes no format. An adjacency matrix would be equivalent up to $O(n^2)$ steps, which is within the time bound.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 1, p.1; Observation 6, p.3

import Mathlib
import Definitions.Def_SkewMatching_Machine

namespace SkewMatching

/-- A **matching** of `G`, as a finite set of edges of `G`: two distinct members share no vertex.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…), Theorem 1, p.1 and Observation 6, p.3. -/
def IsMatchingOf {V : Type*} (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → ∀ v, v ∈ e → v ∉ e'

/-- A **maximum matching** of `G`: a matching of largest cardinality. -/
def IsMaximumMatchingOf {V : Type*} (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  IsMatchingOf G M ∧ ∀ M' : Finset (Sym2 V), IsMatchingOf G M' → M'.card ≤ M.card

/-- `el` lists the edges of `G`: every listed pair is an edge, and every edge of `G` occurs exactly once,
in either orientation. -/
def IsEdgeListing {n : ℕ} (G : SimpleGraph (Fin n)) (el : List (Fin n × Fin n)) : Prop :=
  (el.map fun p => s(p.1, p.2)).Nodup ∧ ∀ e : Sym2 (Fin n), e ∈ G.edgeSet ↔ e ∈ el.map fun p => s(p.1, p.2)

/-- The input memory of Theorem 1: cell `0` holds `n`, cell `1` holds the length `L` of the edge list,
cells `2 + 2j`, `3 + 2j` hold the endpoints of the `j`-th listed edge; every other cell holds `0`. -/
def matchingMem {n : ℕ} (el : List (Fin n × Fin n)) (a : ℤ) : ℤ :=
  if a = 0 then (n : ℤ) else if a = 1 then (el.length : ℤ) else
    Machine.pairCells 2 (el.map fun p => ((p.1 : ℕ), (p.2 : ℕ))) a

/-- The output of Theorem 1, read from the memory `mem` of the halted machine: cell `−1` holds `ℓ`, cells
`−2 − 2j`, `−3 − 2j` hold the endpoints of the `j`-th edge, and these `ℓ` pairs are the edges of a maximum
matching of `G`, each once. -/
def DecodesMaxMatching {n : ℕ} (G : SimpleGraph (Fin n)) (mem : ℤ → ℤ) : Prop :=
  ∃ (ℓ : ℕ) (u v : Fin ℓ → Fin n), mem (-1) = (ℓ : ℤ) ∧
    (∀ j : Fin ℓ, mem (-2 - 2 * ((j : ℕ) : ℤ)) = ((u j : ℕ) : ℤ) ∧
      mem (-3 - 2 * ((j : ℕ) : ℤ)) = ((v j : ℕ) : ℤ)) ∧
    Function.Injective (fun j => s(u j, v j)) ∧
    IsMaximumMatchingOf G (Finset.univ.image fun j => s(u j, v j))

end SkewMatching


