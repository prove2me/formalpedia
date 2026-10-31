-- Prove2me | Definitions.Def_KTSPBounds_kTSPLength
-- name    : KTSPBounds_kTSPLength
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:17.81317+00:00
-- url     : https://prove2.me/theorems/9a9b0719-6212-43fc-ab9c-bda7429a2647
-- title:
--   The $k$-TSP length $l_{TSP}(k,n)$
-- statement:
--   Given points $x_1,\dots,x_n \in \mathbb R^2$ and $k \le n$, the $k$-traveling salesman problem seeks a path through an endogenous subset of $k$ of the points. Its optimal value is
--
--   $$
--   l_{TSP}(k,n) = \min_{\sigma} \sum_{i=1}^{k-1} \lvert x_{\sigma(i+1)} - x_{\sigma(i)} \rvert,
--   $$
--
--   where the minimum runs over all injections $\sigma$ from $\{1,\dots,k\}$ to $\{1,\dots,n\}$, that is, over the choice of the $k$ vertices and their order.
--
--   The path is open: it does not return to its start. For $k = n$ this is the shortest Hamiltonian path, and for $k = 2$ the smallest pairwise distance.
--
--   **Formalization Note** The index type is `Fin k ↪ Fin n`, so the path runs through distinct sample indices and coincident points are not merged. It is nonempty exactly when $k \le n$, which every theorem assumes.
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, §2.1, eq. (2), p.4

import Mathlib
import Definitions.Def_KTSPBounds_Plane

namespace KTSPBounds

/-- The length `l_TSP(k, n)` of the `k`-TSP on the points `x 0, …, x (n-1)` (objective (2), p.4),
Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1: the minimum, over all choices of `k` distinct sample indices `σ 0, …, σ (k-1)`
in all orders, of the path length `∑_{i=1}^{k-1} |x_{i+1} - x_i|`.

**Formalization Note.** The path is open, not closed, and runs through distinct sample *indices*,
so coincident sample points are not collapsed. The embeddings `Fin k ↪ Fin n` form a finite set,
nonempty exactly when `k ≤ n`, so for `k ≤ n` the infimum is an attained minimum. For `k > n` the
real infimum over the empty type is the junk value `0`; every theorem of this mission assumes
`k ≤ n`. -/
noncomputable def kTSPLength {n : ℕ} (k : ℕ) (x : Fin n → Plane) : ℝ :=
  ⨅ σ : Fin k ↪ Fin n, ∑ i : Fin (k - 1),
    dist (x (σ ⟨i.1 + 1, by have := i.2; omega⟩)) (x (σ ⟨i.1, by have := i.2; omega⟩))

end KTSPBounds


