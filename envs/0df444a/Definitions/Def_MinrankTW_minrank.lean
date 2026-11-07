-- Prove2me | Definitions.Def_MinrankTW_minrank
-- name    : MinrankTW_minrank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:34.84657+00:00
-- url     : https://prove2.me/theorems/0de30c25-a385-44a6-b6b6-84db6eb024bc
-- title:
--   Minrank $\mathrm{minrank}_{\mathbb F}(G)$
-- statement:
--   The **minrank** of a graph $G$ on $[n]$ over a field $\mathbb F$ is
--   $$
--   \mathrm{minrank}_{\mathbb F}(G)=\min\{\operatorname{rank} M : M \text{ fits } G\}.
--   $$
--   The minimum is over all fitting matrices (nonzero diagonal), not only normalized ones.
--
--   It is the length of a shortest scalar linear index code for the knowledge graph $G$ and an upper bound on its Shannon capacity.
--
--   **Formalization Note** Written as the infimum of the set of ranks of fitting matrices. The identity matrix fits every graph, so the set is nonempty and the infimum is attained; for $n=0$ the value is $0$.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 1, p.2

import Mathlib
import Definitions.Def_MinrankTW_Fits

namespace MinrankTW

/-- The **minrank** of `G` over `F` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §1, p.2):
`minrank_F(G) = min {rank M : M fits G}`.

**Formalization Note** Written as `sInf` of the set of ranks of fitting matrices. The set is
never empty (the identity matrix fits every graph), so the infimum is the minimum; for `n = 0`
it is `0`. The minimum ranges over all fitting matrices (nonzero diagonal), not only
normalized ones. -/
noncomputable def minrank (F : Type*) [Field F] {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {r : ℕ | ∃ M : Matrix (Fin n) (Fin n) F, Fits G M ∧ M.rank = r}

end MinrankTW


