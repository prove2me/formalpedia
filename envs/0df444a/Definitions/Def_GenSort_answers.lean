-- Prove2me | Definitions.Def_GenSort_answers
-- name    : GenSort_answers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:21.038999+00:00
-- url     : https://prove2.me/theorems/9b6960f5-a5e3-4ab4-b2b1-c0b36e5b876c
-- title:
--   Comparison oracle on the darts of $G$
-- statement:
--   In generalized sorting only the pairs joined by an edge of $G$ may be compared. A **query** is a directed edge (dart) $(u, v)$ of $G$; the oracle answers whether $u \prec_\pi v$ in the hidden order $\pi$:
--   $$
--   \mathrm{ans}_\pi(u, v) = \mathbf 1[u \prec_\pi v].
--   $$
--   Each query reveals exactly one comparison, and non-adjacent pairs cannot be queried.
--
--   **Formalization Note** $u \prec_\pi v$ is $\pi^{-1}(u) < \pi^{-1}(v)$ for $\pi$ a permutation of `Fin n` listing the vertices in increasing order. Queries are elements of `G.Dart` and answers are Booleans.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §1, p.1 (PDF p.3)

import Mathlib

namespace GenSort

/-- **The comparison oracle.** Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §1, p.1 (PDF p.3): a query compares the two endpoints of an
edge of `G` and reveals their relative order in the hidden ordering `π`. A query is a dart
`d = (u, v)` of `G` (an edge with a chosen direction); the answer is `true` iff `u ≺_π v`.

**Formalization Note.** `u ≺_π v` is `π.symm u < π.symm v` (`π i` is the vertex at position `i`).
Only darts of `G` can be queried, so pairs that are not edges cannot be compared, and one query
reveals exactly one comparison. -/
def answers {n : ℕ} {G : SimpleGraph (Fin n)} (π : Equiv.Perm (Fin n)) : G.Dart → Bool :=
  fun d => decide (π.symm d.fst < π.symm d.snd)

end GenSort


