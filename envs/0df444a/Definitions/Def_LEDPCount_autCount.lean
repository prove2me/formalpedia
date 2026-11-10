-- Prove2me | Definitions.Def_LEDPCount_autCount
-- name    : LEDPCount_autCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:30.139835+00:00
-- url     : https://prove2.me/theorems/99500598-1976-4ccc-931e-b160b2466d5e
-- title:
--   Number of automorphisms $|\mathrm{Aut}(H)|$ of a pattern graph
-- statement:
--   Let $H$ be a pattern graph on the vertex set $V(H)$ with $k$ vertices. Its **automorphism group** $\mathrm{Aut}(H)$ is the set of permutations $\sigma$ of $V(H)$ such that, for all $u,v\in V(H)$,
--   $$
--   \{u,v\}\in E(H)\iff\{\sigma(u),\sigma(v)\}\in E(H).
--   $$
--   This definition records the number $|\mathrm{Aut}(H)|$, which normalizes the count of copies of $H$: every copy of $H$ in a graph is the image of exactly $|\mathrm{Aut}(H)|$ injections $V(H)\hookrightarrow[n]$.
--
--   **Formalization Note** The pattern is a simple graph on $\mathrm{Fin}\,k=\{0,\dots,k-1\}$; $|\mathrm{Aut}(H)|$ is the number of permutations of $\mathrm{Fin}\,k$ preserving adjacency in both directions.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), §2.1, p.14 (PDF p.16)

import Mathlib

namespace LEDPCount

/-- The number of automorphisms `|Aut(H)|` of a pattern graph `H` (Chen–Peng, *The Power of
Interaction in Locally Edge-Private Subgraph Counting*, arXiv:2611.05038, held version sha256 d18032b0…, §2.1, p.14, PDF p.16):
the number of permutations `σ` of `V(H)` such that `{u, v} ∈ E(H)` iff `{σ u, σ v} ∈ E(H)`
for all `u, v`.

**Formalization Note** The pattern is `H : SimpleGraph (Fin k)`, i.e. `V(H) = {0, …, k-1}`
(0-based); `{u, v} ∈ E(H)` is `H.Adj u v`. -/
def autCount {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin k) => ∀ u v, H.Adj u v ↔ H.Adj (σ u) (σ v)).card

end LEDPCount


