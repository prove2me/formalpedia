-- Prove2me | Definitions.Def_LawLocalComp_Resource_admits
-- name    : LawLocalComp_Resource_admits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:56.805872+00:00
-- url     : https://prove2.me/theorems/d7917d66-eeac-4714-8a1e-dc62425b81d0
-- title:
--   Selections admitted by a resource
-- statement:
--   A selection of $n$ jobs whose directions have rank $r$ is **admitted** by the horizon $N$ if $n\le N$, by the rank promise $q$ if $r\le q$, and by both if $n\le N$ and $r\le q$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib
import Definitions.Def_LawLocalComp_Resource

namespace LawLocalComp

/-- **Selections admitted by a resource.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2.

`R.admits n r`: a selection of `n` jobs whose directions have rank `r` is allowed — `n ≤ N` under a
horizon, `r ≤ q` under a rank promise (any number of jobs), both under both. -/
def Resource.admits : Resource → ℕ → ℕ → Prop
  | .horizon N, n, _ => n ≤ N
  | .rank q, _, r => r ≤ q
  | .both N q, n, r => n ≤ N ∧ r ≤ q

end LawLocalComp


