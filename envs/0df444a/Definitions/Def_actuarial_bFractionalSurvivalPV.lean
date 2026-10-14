-- Prove2me | Definitions.Def_actuarial_bFractionalSurvivalPV
-- name    : actuarial_bFractionalSurvivalPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:27:46.228256+00:00
-- url     : https://prove2.me/theorems/d05777f1-d61b-4a25-8e40-f3a99887be2a
-- title:
--   Independently projected survivor-weighted subperiod payment value.
-- statement:
--   Independently projected survivor-weighted subperiod payment value. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   V^{(m)}=\sum_q(b_q/m)w^{q+\delta}S^{(m)}(r_q)
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Independently projected survivor-weighted subperiod payment value.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bUDDMicroMass

namespace ActuarialAnnuities

noncomputable def bFractionalSurvivalPV (h a n g delta m : ℕ) (w : ℝ) (b p : ℕ → ℝ) : ℝ := bSurvivalPV (h*m) (a*m) (n*m) g delta w (fun q => b q / (m : ℝ)) (bUDDMicroMass h m p)

end ActuarialAnnuities


