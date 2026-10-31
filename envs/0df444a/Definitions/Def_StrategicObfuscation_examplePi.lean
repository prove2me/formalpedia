-- Prove2me | Definitions.Def_StrategicObfuscation_examplePi
-- name    : StrategicObfuscation_examplePi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:16.688319+00:00
-- url     : https://prove2.me/theorems/3e7991b6-3356-4238-be4c-72cbcd89a5cb
-- title:
--   The detection probability $\pi(\sigma,e)=\sigma q(e)$ of the worked example
-- statement:
--   The paper's example of a detection probability for which more resources can backfire: $\pi(\sigma,e)=\sigma\,q(e)$.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), §3.1, p.14

import Mathlib
import Definitions.Def_StrategicObfuscation_exampleQ

namespace StrategicObfuscation

/-- **The detection probability of the worked example, `π(σ, e) = σ q(e)`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §3.1, p.14 (PDF p.14). -/
noncomputable def examplePi (σ e : ℝ) : ℝ :=
  σ * exampleQ e

end StrategicObfuscation


