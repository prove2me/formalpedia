-- Prove2me | Definitions.Def_actuarial_finiteHattendorffNetAtRisk
-- name    : actuarial_finiteHattendorffNetAtRisk
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:04:19.859223+00:00
-- url     : https://prove2.me/theorems/b545215b-f85b-4443-9059-37ce7d6742f3
-- title:
--   Discounted year-specific net amount at risk
-- statement:
--   The year-end death benefit less next-year reserve, discounted from t+1 back to issue.
--
--   **Mathematical statement**
--
--   $$
--   \rho_t=v^{t+1}(b_{t+1}-V_{t+1})
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def finiteHattendorffNetAtRisk
  (v : ℝ) (benefit reserve : ℕ → ℝ) (t : ℕ) : ℝ :=
  v ^ (t + 1) * (benefit (t + 1) - reserve (t + 1))

end ActuarialValuation


