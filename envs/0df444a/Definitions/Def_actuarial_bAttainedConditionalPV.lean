-- Prove2me | Definitions.Def_actuarial_bAttainedConditionalPV
-- name    : actuarial_bAttainedConditionalPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:28:01.04779+00:00
-- url     : https://prove2.me/theorems/288a84c4-48f0-4a0d-b11c-5006410fd359
-- title:
--   Survivor-conditioned attained-age annuity value for a deferred commencement.
-- statement:
--   Survivor-conditioned attained-age annuity value for a deferred commencement. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   V_a=\sum_{j<n}b_{a+j}v^{j+\delta}\frac{S(a+j+\delta)}{S(a)}
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 157, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Survivor-conditioned attained-age annuity value for a deferred commencement.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival

namespace ActuarialAnnuities

noncomputable def bAttainedConditionalPV (h a n delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range n, b (a+j) * v^(j+delta) * (bSurvival h p (a+j+delta) / bSurvival h p a)

end ActuarialAnnuities


