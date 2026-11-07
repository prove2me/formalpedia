-- Prove2me | Definitions.Def_HZTractability_FvQ
-- name    : HZTractability_FvQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:10:30.390893+00:00
-- url     : https://prove2.me/theorems/c37d7406-a624-4385-affe-77df7a5a8665
-- title:
--   The floor population $F_v$ and $\theta$ (display (7))
-- statement:
--   With
--   $$
--   \theta=\min\Big\{a,\frac{1-a}{2}\Big\},\qquad F_v=\Big\lceil\frac{S_L+S_M}{\theta}\Big\rceil+1,
--   $$
--   the floor population at $v$ is so large that the targets cannot supply $\theta$ units to every floor buyer.
--
--   **Formalization Note** $S_L$, $S_M$ are the rational formulas of (17) at the outdegree $o_v$.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), display (7), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_HZTractability_bvQ

namespace HZTractability

/-- `θ = min{a, (1 − a)/2}` (display (7), p.13 (PDF 15)). -/
def theta (a : ℚ) : ℚ := min a ((1 - a) / 2)

/-- **The floor population** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held version,
sha256 74b7bf9f…, display (7), p.13 (PDF 15)): "θ = min{a, (1 − a)/2}, F_v = ⌈(S_L + S_M)/θ⌉ + 1",
with `S_L`, `S_M` from (17) at the outdegree `o = o_v`. -/
def FvQ (a : ℚ) (K o : ℕ) : ℚ := (⌈(SLQ a K o + SMQ a K o) / theta a⌉ : ℚ) + 1

end HZTractability


