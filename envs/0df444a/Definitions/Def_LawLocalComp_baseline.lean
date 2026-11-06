-- Prove2me | Definitions.Def_LawLocalComp_baseline
-- name    : LawLocalComp_baseline
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:42.600002+00:00
-- url     : https://prove2.me/theorems/b3638aa6-5ccd-4ad7-b62f-6ff069b481d6
-- title:
--   Baseline $b=\min\operatorname{supp}X$
-- statement:
--   The **baseline** of a law $X$ is its least atom $b=\min\operatorname{supp}X$, so $X=b+R$ with residual $R\ge0$ and $\mathbb P(R=0)>0$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §7, p.13

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The baseline `b = min supp X`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §7, p.13 ("Write X = b + R = b + ∆K"); Definition 9.1, p.16 ("b = min supp X").

`baseline X` is the least atom of `X` (the support is finite and nonempty). -/
noncomputable def baseline (X : Law) : ℝ := sInf (X.w.support : Set ℝ)

end LawLocalComp


