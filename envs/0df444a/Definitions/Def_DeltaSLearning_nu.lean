-- Prove2me | Definitions.Def_DeltaSLearning_nu
-- name    : DeltaSLearning_nu
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:19.025534+00:00
-- url     : https://prove2.me/theorems/8391f3a1-606e-4a49-8571-ad6ceabbe468
-- title:
--   Sub-exponential parameter $\nu$
-- statement:
--   The constant
--   $$\nu := 4\gamma\sqrt{\exp\Bigl(\frac{12\beta\rho p+2p}{h}\Bigr)},$$
--   with $\gamma$ from (10). It is the first sub-exponential parameter of the cycle length, cycle cost and stochastic gradient (Lemma 3) and enters the tuning constants $\xi$ and $\theta$ of Theorem 3.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (19), p.17, and eq. (31), p.23

import Mathlib
import Definitions.Def_DeltaSLearning_gamma

namespace DeltaSLearning

/-- The sub-exponential parameter `ν = 4γ √(exp((12βρp + 2p)/h))` of (19) and (31).
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (19),
p.17, and eq. (31), p.23. -/
noncomputable def nu (cp : Params) : ℝ :=
  4 * gamma cp * Real.sqrt (Real.exp ((12 * cp.β * cp.ρ * cp.p + 2 * cp.p) / cp.h))

end DeltaSLearning


