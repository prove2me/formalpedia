-- Prove2me | Definitions.Def_OmniMix_deltaT
-- name    : OmniMix_deltaT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:21.50904+00:00
-- url     : https://prove2.me/theorems/6e63337e-4aee-48b3-8f25-6347fd83d511
-- title:
--   Clipping level $\delta=1/(2(T+1))$
-- statement:
--   For a horizon $T$, Algorithm 2 uses the clipping level $\delta=\dfrac{1}{2(T+1)}$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §3.2, p.13 and Algorithm 2, p.15

import Mathlib

namespace OmniMix

/-- **Algorithm 2's clipping level `δ = 1/(2(T + 1))`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §3.2, p.13 and Algorithm 2, p.15. -/
noncomputable def deltaT (T : ℕ) : ℝ := 1 / (2 * ((T : ℝ) + 1))

end OmniMix


