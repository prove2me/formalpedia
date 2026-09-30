-- Prove2me | Definitions.Def_ConeLifts_StableSet_stab
-- name    : ConeLifts_StableSet_stab
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:14:50.425994+00:00
-- url     : https://prove2.me/theorems/e1bcb6f0-e314-4322-b210-adbcc654aff2
-- title:
--   Stable set polytope $\mathrm{STAB}(G) = \mathrm{conv}\{\chi_S : S \text{ stable}\}$
-- statement:
--   Let $G$ be a graph with vertex set $V = \{1, \dots, n\}$. A subset $S \subseteq V$ is **stable** if no edge of $G$ joins two elements of $S$. The **incidence vector** of $S$ is $\chi_S \in \{0,1\}^n$ with $(\chi_S)_i = 1$ if $i \in S$ and $(\chi_S)_i = 0$ otherwise. The **stable set polytope** of $G$ is
--
--   $$
--   \mathrm{STAB}(G) = \mathrm{conv}\{\chi_S : S \text{ is a stable set of } G\} \subseteq \mathbb R^n .
--   $$
--
--   Linear optimization over $\mathrm{STAB}(G)$ is the (weighted) maximum stable set problem, a classical NP-hard problem of combinatorial optimization.
--
--   **Formalization Note** Vertices are `Fin n` (the paper's vertex $i+1$ is `i : Fin n`), graphs are Mathlib's `SimpleGraph (Fin n)`, stability is `SimpleGraph.IsIndepSet`, and $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The file also defines the incidence vector `incidenceVector`.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 18, §5.1 (stable set polytope)

import Mathlib

namespace ConeLifts.StableSet

/-- The **incidence vector** `χ_S ∈ {0, 1}ⁿ` of a vertex set `S ⊆ V = {1, …, n}` (Gouveia,
Parrilo & Thomas, arXiv:1111.3164v2, §5.1, p. 18): `(χ_S)_i = 1` if `i ∈ S` and `(χ_S)_i = 0`
otherwise. The vertices are indexed by `Fin n` (vertex `i + 1` of the paper is `i : Fin n`), and
the vector lives in `ℝⁿ = EuclideanSpace ℝ (Fin n)`. -/
noncomputable def incidenceVector {n : ℕ} (S : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i ∈ S then (1 : ℝ) else 0)

/-- The **stable set polytope** of a graph `G` on the vertex set `V = {1, …, n}` (Gouveia,
Parrilo & Thomas, arXiv:1111.3164v2, §5.1, p. 18):
`STAB(G) = conv{χ_S : S is a stable set of G}`, where `S ⊆ V` is stable if there are no edges
between elements of `S` (Mathlib's `SimpleGraph.IsIndepSet`). -/
def stab {n : ℕ} (G : SimpleGraph (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ
    {x | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ x = incidenceVector S}

end ConeLifts.StableSet


