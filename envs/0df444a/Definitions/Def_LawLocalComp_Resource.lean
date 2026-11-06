-- Prove2me | Definitions.Def_LawLocalComp_Resource
-- name    : LawLocalComp_Resource
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:55.590578+00:00
-- url     : https://prove2.me/theorems/c39d5a90-22db-4545-9249-13d84e80f331
-- title:
--   Supplied resources: horizon, rank, or both
-- statement:
--   A **resource** is the information a law-local map receives about future selections:
--   1. a horizon $N$ (at most $N$ jobs),
--   2. a rank promise $q$ (directions spanning at most $q$ dimensions, any number of jobs),
--   3. both $N$ and $q$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib

namespace LawLocalComp

/-- **The supplied resources.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("A horizon bounds selection size by N; a rank promise permits every finite
selection with dim span{aj} ≤ q"; "according to the supplied resources. With both …").

A resource is a horizon `N`, a rank promise `q`, or both. -/
inductive Resource where
  | horizon (N : ℕ)
  | rank (q : ℕ)
  | both (N q : ℕ)
  deriving DecidableEq

end LawLocalComp


