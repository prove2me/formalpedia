-- Prove2me | Definitions.Def_OmniMix_dV
-- name    : OmniMix_dV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:54.881818+00:00
-- url     : https://prove2.me/theorems/af41b52b-7778-4204-94e5-b294ff7731f2
-- title:
--   Threshold properness gain $d_v(p,q)$
-- statement:
--   For a threshold $v$ and $p,q$,
--   $$
--   d_v(p,q)=|v-p|\,b_v(p,q)^2 .
--   $$
--   It is the closed form of the properness gain $d_{\lambda_v}$ of the V-shaped loss.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.10

import Mathlib
import Definitions.Def_OmniMix_bV

namespace OmniMix

/-- **Threshold properness gain `d_v(p, q)`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.10: "`d_v(p, q) = |v − p|b_v(p, q)²`",
the closed form of `d_{λ_v}`. -/
noncomputable def dV (v p q : ℝ) : ℝ := |v - p| * bV v p q ^ 2

end OmniMix


