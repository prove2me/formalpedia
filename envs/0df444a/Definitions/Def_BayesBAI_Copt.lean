-- Prove2me | Definitions.Def_BayesBAI_Copt
-- name    : BayesBAI_Copt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:16.141918+00:00
-- url     : https://prove2.me/theorems/2cd063c2-b655-44eb-9972-cc952878ee53
-- title:
--   The constant $C_{\mathrm{opt}}$
-- statement:
--   The leading constant of Theorem 1 is
--   $$
--   C_{\mathrm{opt}}=\sum_{i\in[K]}\int_{[0,1]^{K-1}}\mu^*_{\setminus i}(1-\mu^*_{\setminus i})\,h_i(\mu^*_{\setminus i}\mid\mu_{\setminus i})\,dH_{\setminus i}(\mu_{\setminus i}).
--   $$
--   For the uniform prior on $[0,1]^K$, it equals $(K-1)/(K+1)$ (Example 2).
--
--   **Formalization Note.** Under `RegularPrior` the integrand is measurable and essentially bounded, so this is an integral of an integrable function.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Theorem 1, p.7

import Mathlib
import Definitions.Def_BayesBAI_maxOthers
import Definitions.Def_BayesBAI_dropOne

open MeasureTheory

namespace BayesBAI

/-- The constant `C_opt = Σ_i ∫ μ*_\i (1 - μ*_\i) h_i(μ*_\i | μ_\i) dH_\i(μ_\i)` of Theorem 1,
Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.7.

**Formalization Note.** Here `H_\i = H.map (dropOne i)`. This is a Bochner integral; under `RegularPrior`
the integrand is measurable and essentially bounded, so `Integrable` holds and the value is genuine
(`Solutions/verification/BayesBAI_sanity.lean`). -/
noncomputable def Copt {K : ℕ} (hK : 2 ≤ K) (H : Measure (Fin K → ℝ))
    (h : (i : Fin K) → ℝ → ({j : Fin K // j ≠ i} → ℝ) → ℝ) : ℝ :=
  ∑ i, ∫ ν, maxOthers hK ν * (1 - maxOthers hK ν) * h i (maxOthers hK ν) ν ∂(H.map (dropOne i))

end BayesBAI


