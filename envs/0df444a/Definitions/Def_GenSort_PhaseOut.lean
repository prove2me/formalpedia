-- Prove2me | Definitions.Def_GenSort_PhaseOut
-- name    : GenSort_PhaseOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:47.508173+00:00
-- url     : https://prove2.me/theorems/8e11bbba-0026-4b33-ab8c-73010ff7e256
-- title:
--   Record of one phase of §3
-- statement:
--   The record of one phase of the prediction construction: the coarse prediction $\sigma$, the bipartite graph $H_0$ of §3.2, the edge set $H_1$ left after removing all edges at flagged vertices, the edge set $H_f$ left after the error isolation passes, and the total number of queries.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3, pp.5–12 (PDF pp.7–14)

import Mathlib

namespace GenSort

/-- **The record of one phase of §3**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3, pp.5–12 (PDF pp.7–14): the coarse prediction `σ`,
the bipartite graph `H₀` of §3.2, the edge set `H₁` left after removing the flagged vertices'
edges (§3.3), the edge set `Hf` left after the error isolation passes (§3.5), and the number of
queries made. -/
structure PhaseOut (n : ℕ) where
  /-- The coarse prediction. -/
  σ : Equiv.Perm (Fin n)
  /-- The bipartite graph of §3.2. -/
  H₀ : Finset ((Fin n × Fin n) × (Fin n × Fin n))
  /-- The edges left after flagging. -/
  H₁ : Finset ((Fin n × Fin n) × (Fin n × Fin n))
  /-- The edges left after the passes. -/
  Hf : Finset ((Fin n × Fin n) × (Fin n × Fin n))
  /-- The total number of queries. -/
  queries : ℕ

end GenSort


