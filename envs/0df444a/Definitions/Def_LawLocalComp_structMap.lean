-- Prove2me | Definitions.Def_LawLocalComp_structMap
-- name    : LawLocalComp_structMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:15:28.985459+00:00
-- url     : https://prove2.me/theorems/4e6f8ce2-cfa6-4bfa-9d18-ec720084ac42
-- title:
--   Explicit structured map of Proposition 7.3
-- statement:
--   For rational $\varepsilon$ and a resource $R$, the **structured map** is the tail-transfer map $T_{r,\delta,\rho}$ of Lemma 7.2 with $\delta=\varepsilon/4$, $\rho=1+\delta$ and $r$ the truncation level of Proposition 7.3.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Proposition 7.3, p.13

import Mathlib
import Definitions.Def_LawLocalComp_tailMap
import Definitions.Def_LawLocalComp_structR

namespace LawLocalComp

/-- **The explicit structured map of Proposition 7.3.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Proposition 7.3, p.13.

`structMap ε R = tailMap r δ ρ` with `δ = ε/4`, `ρ = 1 + δ` and `r = structR ε R`. -/
noncomputable def structMap (ε : ℚ) (R : Resource) (X : Law) : Law :=
  tailMap (structR ε R) ((ε : ℝ) / 4) (1 + (ε : ℝ) / 4) X

end LawLocalComp


