-- Prove2me | Definitions.Def_KVVMatching_UpperBound_Triangular
-- name    : KVVMatching_UpperBound_Triangular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:48:15.698015+00:00
-- url     : https://prove2.me/theorems/275c9b86-9d80-4701-8d42-511569931011
-- title:
--   Complete upper-triangular graph and row-permuted instances
-- statement:
--   The complete upper-triangular bipartite graph on $n$ rows and $n$ columns is
--
--   $$T_n=\{(i,j):i\le j\}.$$
--
--   For a row permutation $\pi$, the instance $T_\pi$ has edge $(r,c)$ exactly when $\pi^{-1}(r)\le c$. Thus it only relabels the boys and retains a perfect matching. The paper places the uniform distribution on these $n!$ instances for Lemma 13.
--
--   **Formalization Note** Indices are zero-based; the paper uses indices from $1$ through $n$.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 357, Definition preceding Lemma 13

import Mathlib
import Definitions.Def_KVVMatching_UpperBound_Graph

namespace KVVMatching.UpperBound

/-- The paper's complete upper-triangular graph, with zero-based indices. -/
def upperTriangular (n : ℕ) : Graph n :=
  {e | e.1 ≤ e.2}

/-- Relabel the rows of the complete upper-triangular graph. -/
def permutedTriangular {n : ℕ} (π : Equiv.Perm (Fin n)) : Graph n :=
  {e | π.symm e.1 ≤ e.2}

end KVVMatching.UpperBound


