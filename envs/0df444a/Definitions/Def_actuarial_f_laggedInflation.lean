-- Prove2me | Definitions.Def_actuarial_f_laggedInflation
-- name    : actuarial_f_laggedInflation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:38:25.799981+00:00
-- url     : https://prove2.me/theorems/6a880925-54aa-4fd4-ad4e-33bd68b059ab
-- title:
--   Scheme reference-index lookback
-- statement:
--   Select the inflation observation at a scheme-specified lag from an event date; guard natural subtraction if a non-saturating lookback is required.
--
--   The defining relationship is:
--
--   $$
--   \pi_{\mathrm{obs}}=\pi_{D-\ell}
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def laggedInflation (inflation : ℕ → ℝ)
    (event lag : ℕ) : ℝ := inflation (event - lag)
end ActuarialUnderpinsF


