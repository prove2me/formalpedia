-- Prove2me | Definitions.Def_ImperfReport_Regulator_Variance
-- name    : ImperfReport_Regulator_Variance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:18.739601+00:00
-- url     : https://prove2.me/theorems/fd38af55-af6d-4a09-9ca3-5dc6d4810c93
-- title:
--   The regulator's expected posterior variance
-- statement:
--   The regulator's loss $\Psi(q,\hat\alpha)$ is the expected posterior variance of firm value after the mandatory report and any voluntary disclosure. It is represented by the law of total variance: the prior second moment minus the second moment of investors' posterior means. The regulator chooses a feasible reporting system, anticipating the firm's greatest best response, to minimize this loss.
--
--   The high-prior threshold $\alpha^\circ$ used in the goal is the corrected expected-variance comparison for $(1,k)$ and $(1,0)$. This definition supports the variance identities on pp. 34–35 and the main result. **Formalization Note** The paper's printed threshold omits the probability of nondisclosure when comparing an expected variance with its conditional counterpart; for uniform $\omega_2$ the corrected threshold is $1-k/3$.
-- source:
--   Friedman, Hughes, Michaeli, A Rationale for Imperfect Reporting Standards, SSRN 3636995 (version of November 24, 2020), pp. 13, 18, 34–35, regulator objective and corrected Proposition 1 threshold

import Definitions.Def_ImperfReport_Regulator_Report

set_option autoImplicit false
open MeasureTheory Set

namespace ImperfReport.Regulator

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020), p. 13, first moment of the
investors' posterior mean of the unreportable component. Disclosure is `s > t`. -/
noncomputable def EM (M : Model) (q : ℝ) : ℝ :=
  let t := tdag M q
  q * (∫ x in Set.Ioi t, x ∂M.mu) + (1 - q * M.mu.real (Set.Ioi t)) * t

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 13, second moment of the investors' posterior mean of the unreportable
component. -/
noncomputable def EM2 (M : Model) (q : ℝ) : ℝ :=
  let t := tdag M q
  q * (∫ x in Set.Ioi t, x ^ 2 ∂M.mu) + (1 - q * M.mu.real (Set.Ioi t)) * t ^ 2

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
pp. 9, 13, prior second moment of `ω = ω₁ + ω₂`, using independence and
`ω₁² = ω₁`. -/
noncomputable def Ew2 (M : Model) : ℝ :=
  M.alpha * (1 + 2 * beta M + m2 M) + (1 - M.alpha) * m2 M

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 13, regulator's expected posterior variance. Formalization Note: this is
the law-of-total-variance expression `E[ω²] − E[E[ω|r,m]²]`, not any target
closed form from Proposition 1. -/
noncomputable def Psi (M : Model) (r : Report) (q : ℝ) : ℝ :=
  Ew2 M -
    (pG M r * (r.aG ^ 2 + 2 * r.aG * EM M q + EM2 M q) +
      (1 - pG M r) * (r.aB ^ 2 + 2 * r.aB * EM M q + EM2 M q))

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 13, a regulator-optimal reporting system together with its induced firm
response. -/
noncomputable def RegOpt (M : Model) (r : Report) (q : ℝ) : Prop :=
  r.Valid M ∧ FirmBR M r q ∧
    ∀ r' q', r'.Valid M → FirmBR M r' q' → Psi M r q ≤ Psi M r' q'

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
pp. 18, 34–35, Proposition 1, corrected high-prior threshold. Formalization
Note: the printed formula divides the second moment difference by
`k(1 − q†(k)(1 − F(k)))` and places `+ k` outside; it compares a conditional
variance to an expected variance. The expected-variance comparison instead
gives `1 + k P − V/k`, with `P = 1 − q†(k)(1 − F(k))` and
`V = m₂ − q†(k) ∫_(k,1] x² dμ`. In the uniform case this is `1 − k/3`. -/
noncomputable def alphaO (M : Model) : ℝ :=
  1 + M.k * (1 - qdag M M.k * (1 - F M M.k)) -
    (m2 M - qdag M M.k * (∫ x in Set.Ioc M.k 1, x ^ 2 ∂M.mu)) / M.k

end ImperfReport.Regulator


