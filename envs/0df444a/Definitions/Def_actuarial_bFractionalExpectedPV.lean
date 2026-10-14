-- Prove2me | Definitions.Def_actuarial_bFractionalExpectedPV
-- name    : actuarial_bFractionalExpectedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:27:29.48199+00:00
-- url     : https://prove2.me/theorems/96644762-0b4c-4989-b17a-dcc8b39b455e
-- title:
--   Expectation over actual finite micro-period lifetime states.
-- statement:
--   Expectation over actual finite micro-period lifetime states. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z^{(m)}]=\sum_kp^{(m)}_kZ^{(m)}_k
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Expectation over actual finite micro-period lifetime states.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bUDDMicroMass

namespace ActuarialAnnuities

noncomputable def bFractionalExpectedPV (h a n g delta m : ℕ) (w : ℝ) (b p : ℕ → ℝ) : ℝ := bExpectedPV (h*m) (a*m) (n*m) g delta w (fun q => b q / (m : ℝ)) (bUDDMicroMass h m p)

end ActuarialAnnuities


