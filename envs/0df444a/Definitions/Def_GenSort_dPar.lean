-- Prove2me | Definitions.Def_GenSort_dPar
-- name    : GenSort_dPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:21.947813+00:00
-- url     : https://prove2.me/theorems/c29f4ce3-0120-4ac4-bb20-963b45a6b181
-- title:
--   Degree bound $d = \lceil f/n \rceil$
-- statement:
--   For an edge set of size $f$ on $n$ vertices, $d = \lceil f/n \rceil$ is the average degree of the bipartite graph of §3.2, and the bound on the degree of every split vertex.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF p.8)

import Mathlib

namespace GenSort

/-- **The degree bound `d = ⌈f/n⌉`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF p.8), where `f = |F|`. -/
noncomputable def dPar (n f : ℕ) : ℕ := ⌈(f : ℝ) / n⌉₊

end GenSort


