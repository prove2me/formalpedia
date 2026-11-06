-- Prove2me | Definitions.Def_LawLocalComp_mean
-- name    : LawLocalComp_mean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:32.944195+00:00
-- url     : https://prove2.me/theorems/4fe8f6de-cb4d-4059-bb1b-881935c7b2bc
-- title:
--   Mean $\mathbb E X$
-- statement:
--   The **mean** of a law $X$ is
--   $$\mathbb E X=\sum_x x\,\mathbb P(X=x),$$
--   the sum over the atoms of $X$. It is the quantity $\mu$ of §§2–4.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The mean `E X`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("They preserve means"); `µ` throughout §§2–4.

`mean X = ∑_x x · P(X = x)`. -/
noncomputable def mean (X : Law) : ℝ := ∑ x ∈ X.w.support, x * X.w x

end LawLocalComp


