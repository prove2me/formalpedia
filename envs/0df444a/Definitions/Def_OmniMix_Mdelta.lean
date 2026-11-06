-- Prove2me | Definitions.Def_OmniMix_Mdelta
-- name    : OmniMix_Mdelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:19.765548+00:00
-- url     : https://prove2.me/theorems/7033a869-a2ce-4a24-8309-e67440672e54
-- title:
--   Normalizing constant $M_\delta=2\log(2T+1)$
-- statement:
--   For a horizon $T$, Algorithm 2 uses $M_\delta=2\log(2T+1)$, the normalizing constant of the threshold prior $\mu_\delta(dv)=dv/(M_\delta v(1-v))$ on $I_\delta$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §3.2, p.13 and Algorithm 2, p.15

import Mathlib

namespace OmniMix

/-- **Algorithm 2's normalizing constant `M_δ = 2 log(2T + 1)`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §3.2, p.13 and
Algorithm 2, p.15 (its value as the integral `∫_{I_δ} [v(1−v)]⁻¹ dv` is the milestone `M_delta_eq`). -/
noncomputable def Mdelta (T : ℕ) : ℝ := 2 * Real.log (2 * (T : ℝ) + 1)

end OmniMix


