-- Prove2me | Definitions.Def_LawLocalComp_activeMean
-- name    : LawLocalComp_activeMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:30.811854+00:00
-- url     : https://prove2.me/theorems/9a66dc4e-1ded-436a-b55e-8e2cd980a6f8
-- title:
--   Active mean $\nu=\mathbb E[R\mid R>0]$
-- statement:
--   For a law $X$ and a level $b$, the **active mean** is
--   $$\nu=\frac{\mathbb E[X-b]}{\mathbb P(X>b)},$$
--   which for $X\ge b$ is $\mathbb E[R\mid R>0]$, $R=X-b$. For $X=b+\Delta K$ it is $\mathbb E[\Delta K\mid K>0]$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §7, p.13; Lemma 8.1, p.14

import Mathlib
import Definitions.Def_LawLocalComp_activity

namespace LawLocalComp

/-- **The active mean `ν = E[R | R > 0]` of `X = b + R`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §7, p.13 ("ν = E[R | R > 0]; the unconditional mean may be arbitrarily smaller"); Lemma 8.1,
p.14 (`ν = E[∆K | K > 0]`).

`activeMean X b = E[X − b] / P(X > b)`; for `X ≥ b` this is `E[X − b | X > b]`. -/
noncomputable def activeMean (X : Law) (b : ℝ) : ℝ :=
  (∑ x ∈ X.w.support, (x - b) * X.w x) / activity X b

end LawLocalComp


