-- Prove2me | Definitions.Def_actuarial_bFractionalPathPV
-- name    : actuarial_bFractionalPathPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:27:10.331733+00:00
-- url     : https://prove2.me/theorems/be9cf2b3-459f-436f-8487-a31d3a285295
-- title:
--   Actual realised micro-period life-annuity cashflow with nominal annualised benefit.
-- statement:
--   Actual realised micro-period life-annuity cashflow with nominal annualised benefit. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   Z^{(m)}_k=\frac1m\sum_qb_qw^{q+\delta}I_q(k)
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Actual realised micro-period life-annuity cashflow with nominal annualised benefit.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV

namespace ActuarialAnnuities

noncomputable def bFractionalPathPV (h a n g delta m : ℕ) (w : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ := bPathPV (h*m) (a*m) (n*m) g delta w (fun q => b q / (m : ℝ)) k

end ActuarialAnnuities


