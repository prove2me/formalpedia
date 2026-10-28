-- Prove2me | Definitions.Def_actuarial_f_linkedSpouseBasis
-- name    : actuarial_f_linkedSpouseBasis
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:39:03.418793+00:00
-- url     : https://prove2.me/theorems/ab6a7e58-57d8-494a-9240-0d917c8b1920
-- title:
--   Spouse basis fixed by selected member option
-- statement:
--   The spouse's pension follows the member option chosen at award, rather than independently taking the larger survivor benefit at member death.
--
--   The defining relationship is:
--
--   $$
--   S_{zi}=\begin{cases}S^B_{zi}&A_z\le B_z\\S^A_{zi}&A_z>B_z\end{cases}
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def linkedSpouseBasis (a b : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (z i : ℕ) : ℝ :=
  if a z ≤ b z then sb z i else sa z i
end ActuarialUnderpinsF


