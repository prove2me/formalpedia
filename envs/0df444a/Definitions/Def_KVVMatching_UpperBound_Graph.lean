-- Prove2me | Definitions.Def_KVVMatching_UpperBound_Graph
-- name    : KVVMatching_UpperBound_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:38:56.999057+00:00
-- url     : https://prove2.me/theorems/4a65ca3a-551e-4e7c-af71-3644b56f28d6
-- title:
--   Finite bipartite graph as an edge set
-- statement:
--   A bipartite graph with $n$ boys and $n$ girls is represented by an edge set
--
--   $$G\subseteq [n]\times[n],$$
--
--   where the first coordinate is a row and the second is a column. This general carrier is reused by the online matching model and by the paper's triangular hard instances.
--
--   **Formalization Note** Indices are zero-based; the paper uses indices from $1$ through $n$.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 352, Section 2 (Problem Statement)

import Mathlib

namespace KVVMatching.UpperBound

/-- The adjacency relation between the two sides of an `n` by `n` bipartite graph. -/
abbrev Graph (n : ℕ) := Set (Fin n × Fin n)

end KVVMatching.UpperBound


