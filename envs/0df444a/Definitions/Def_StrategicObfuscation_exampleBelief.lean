-- Prove2me | Definitions.Def_StrategicObfuscation_exampleBelief
-- name    : StrategicObfuscation_exampleBelief
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:24.945656+00:00
-- url     : https://prove2.me/theorems/eb522166-6d1c-4b88-bf95-3d45860acedb
-- title:
--   The posterior of the worked example
-- statement:
--   At $p=1/2$, the posterior given by Bayes' rule (2) at the equilibrium effort, with the off-path belief at $\sigma=1$ set to $0$.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), eq. (2), p.10, for the π of §3.1, p.14

import Mathlib
import Definitions.Def_StrategicObfuscation_examplePi
import Definitions.Def_StrategicObfuscation_exampleEffort
import Definitions.Def_StrategicObfuscation_exampleAlpha

namespace StrategicObfuscation

/-- **The posterior in the worked example at `p = 1/2`, given by Bayes' rule (2).**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), eq. (2), p.10 (PDF p.10), for the `π` of §3.1, p.14
(PDF p.14), with `π(σ, 0) = σ`.

**Formalization Note** At `σ = 1` the equilibrium effort is `0`, the denominator of (2) vanishes and
the report is off path; the off-path belief is set to `0` explicitly. -/
noncomputable def exampleBelief (σ : ℝ) : ℝ :=
  if σ = 1 then 0
  else (1 - σ) * (1 / 2) /
    ((1 - σ) * (1 / 2) + (1 - examplePi σ (exampleEffort (exampleAlpha σ) σ)) * (1 / 2))

end StrategicObfuscation


