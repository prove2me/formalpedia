-- Prove2me | Definitions.Def_LawLocalComp_Jfun
-- name    : LawLocalComp_Jfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:14.14954+00:00
-- url     : https://prove2.me/theorems/6b502b6e-625f-426a-91c4-e24f0158e2fe
-- title:
--   Mixed atom order $J(\varepsilon,N,q)$
-- statement:
--   With $Q=\min\{N,q\}$,
--   $$J(\varepsilon,N,q)=\min\left\{\sqrt{\frac{\log(N+1)\log(Q+1)}{\varepsilon}},\ \frac{\log(Q+1)}{\varepsilon}\right\}.$$
--   It is the sharp atom order under both a horizon and a rank promise.
--
--   **Formalization Note** $\log$ is the natural logarithm; the base changes only absolute constants.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), (2), p.2

import Mathlib

namespace LawLocalComp

/-- **The mixed atom order `J(ε, N, q)`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), (2), p.2: with `Q = min{N, q}`,
`J(ε, N, q) = min{ √(log(N + 1) log(Q + 1)/ε), log(Q + 1)/ε }`.

**Formalization Note.** `log` is the natural logarithm; another base changes only absolute
constants. -/
noncomputable def Jfun (ε : ℝ) (N q : ℕ) : ℝ :=
  min (Real.sqrt (Real.log (N + 1) * Real.log ((min N q : ℕ) + 1) / ε))
    (Real.log ((min N q : ℕ) + 1) / ε)

end LawLocalComp


