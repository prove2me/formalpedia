-- Prove2me | Definitions.Def_LawLocalComp_activity
-- name    : LawLocalComp_activity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:42.965804+00:00
-- url     : https://prove2.me/theorems/11ef7307-02be-4b30-a0c0-612ec7178289
-- title:
--   Activity $p=\mathbb P(R>0)$
-- statement:
--   For a law $X$ and a level $b$, the **activity** is $p=\mathbb P(X>b)$; for the baseline $b$ this is $\mathbb P(R>0)$ with $R=X-b$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §7, p.13

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The activity `p = P(R > 0)` of `X = b + R`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §7, p.13 ("For a nonconstant law let p = P(R > 0)").

`activity X b = P(X > b)`. -/
noncomputable def activity (X : Law) (b : ℝ) : ℝ := ∑ x ∈ X.w.support with b < x, X.w x

end LawLocalComp


