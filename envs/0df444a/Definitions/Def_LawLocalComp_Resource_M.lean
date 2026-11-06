-- Prove2me | Definitions.Def_LawLocalComp_Resource_M
-- name    : LawLocalComp_Resource_M
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:56.705851+00:00
-- url     : https://prove2.me/theorems/94a1555f-210e-49f1-9201-5c4f3a0c03e0
-- title:
--   Resource scale $M$
-- statement:
--   The **resource scale** is $M=N$ for a horizon, $M=q$ for a rank promise and $M=\min\{N,q\}$ for both, as in "For class-dependent results $M=N$, $q$, or $\min\{N,q\}$ according to the supplied resources."
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib
import Definitions.Def_LawLocalComp_Resource

namespace LawLocalComp

/-- **The resource scale `M`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("For class-dependent results M = N, q, or min{N, q} according to the supplied
resources"). -/
def Resource.M : Resource → ℕ
  | .horizon N => N
  | .rank q => q
  | .both N q => min N q

end LawLocalComp


