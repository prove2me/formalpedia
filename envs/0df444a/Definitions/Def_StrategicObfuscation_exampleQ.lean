-- Prove2me | Definitions.Def_StrategicObfuscation_exampleQ
-- name    : StrategicObfuscation_exampleQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:22.565754+00:00
-- url     : https://prove2.me/theorems/70a02877-1e08-4951-9c8a-c6f35e068e3b
-- title:
--   The function $q$ of the worked example
-- statement:
--   $q(e)=1-\sqrt{2e}$ for $e\le 1/2$, and $q(e)=0$ otherwise.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), §3.1, p.14

import Mathlib

namespace StrategicObfuscation

/-- **The function `q` of the worked example.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §3.1, p.14 (PDF p.14): "q(e) = 1 − √(2e) for e ≤ 0.5 and
zero otherwise". -/
noncomputable def exampleQ (e : ℝ) : ℝ :=
  if e ≤ 1 / 2 then 1 - Real.sqrt (2 * e) else 0

end StrategicObfuscation


