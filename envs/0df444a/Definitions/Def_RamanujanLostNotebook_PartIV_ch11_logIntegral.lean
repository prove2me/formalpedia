-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch11_logIntegral
-- name    : RamanujanLostNotebook_PartIV_ch11_logIntegral
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T14:26:49.606877+00:00
-- url     : https://prove2.me/theorems/7f1c75cb-b53e-401b-ae9e-f99d0aea494d
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 11: logIntegral
-- statement:
--   The logarithmic integral `Li(y)`, the Cauchy principal value of `∫₀^y dt / log t`,
--   for `y > 0`, `y ≠ 1`, through the closed form
--   `Li(y) = γ + log |log y| + ∫₀^{log y} (e^u - 1)/u du`
--   (reference values: `Li(2) = 1.04516378…`, `Li(1000) = 177.60965799…`).
--   The integrand is bounded near `u = 0`; its junk value at `u = 0` sits on a null set.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 11.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- The logarithmic integral `Li(y)`, the Cauchy principal value of `∫₀^y dt / log t`,
for `y > 0`, `y ≠ 1`, through the closed form
`Li(y) = γ + log |log y| + ∫₀^{log y} (e^u - 1)/u du`
(reference values: `Li(2) = 1.04516378…`, `Li(1000) = 177.60965799…`).
The integrand is bounded near `u = 0`; its junk value at `u = 0` sits on a null set. -/
noncomputable def logIntegral (y : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log |Real.log y|
    + ∫ u in (0 : ℝ)..Real.log y, (Real.exp u - 1) / u

end RamanujanLostNotebook.PartIV


