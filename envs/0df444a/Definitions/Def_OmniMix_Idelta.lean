-- Prove2me | Definitions.Def_OmniMix_Idelta
-- name    : OmniMix_Idelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:19.99598+00:00
-- url     : https://prove2.me/theorems/839dc4f5-ea68-4b98-9f23-8bd4a9d54e56
-- title:
--   The interval $I_\delta=[\delta,1-\delta]$
-- statement:
--   For $\delta\in[0,1/2)$, $I_\delta=[\delta,1-\delta]$. Algorithm 2 restricts its thresholds and forecasts to $I_\delta$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.10 and §3.2, p.13

import Mathlib

namespace OmniMix

/-- **The interval `I_δ = [δ, 1 − δ]`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.10 and §3.2, p.13. -/
def Idelta (δ : ℝ) : Set ℝ := Set.Icc δ (1 - δ)

end OmniMix


