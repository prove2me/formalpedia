-- Prove2me | Definitions.Def_LawLocalComp_call
-- name    : LawLocalComp_call
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:17.152449+00:00
-- url     : https://prove2.me/theorems/e3a9da7e-2849-4bd1-a607-e43c064909e6
-- title:
--   Call function $C_X(t)=\mathbb E(X-t)_+$
-- statement:
--   The **call function** of a law $X$ is
--   $$C_X(t)=\mathbb E\,(X-t)_+=\sum_x \mathbb P(X=x)\max\{x-t,0\},\qquad t\in\mathbb R.$$
--   Differences of call functions $C_X-C_Y$ are the certificates of the cell lemmas (6), (10)–(12).
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §3, p.5

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The call function `C_X(t) = E (X − t)₊`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §3, p.5 ("Write Cµ(t) = ∫ (x−t)+ µ(dx)").

`call X t = ∑_x P(X = x) · max (x − t) 0`. -/
noncomputable def call (X : Law) (t : ℝ) : ℝ := ∑ x ∈ X.w.support, X.w x * max (x - t) 0

end LawLocalComp


