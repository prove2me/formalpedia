-- Prove2me | Definitions.Def_actuarial_bProjectedSecondMoment
-- name    : actuarial_bProjectedSecondMoment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:24:41.675341+00:00
-- url     : https://prove2.me/theorems/56835194-6ed7-42a1-b61d-a21a9b7e857e
-- title:
--   Pairwise intersection survival representation of actual second moments.
-- statement:
--   Pairwise intersection survival representation of actual second moments. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   M_2=\sum_{i,j}c_ic_jS(\max(r_i,r_j))
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Squared present value in GBP²; first moments and benefit amounts are GBP.
-- source:
--   Original derived finite annuity result. Contextual source page 143, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Pairwise intersection survival representation of actual second moments.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bRequiredAge

namespace ActuarialAnnuities

noncomputable def bProjectedSecondMoment (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h, if (a ≤ i ∧ i < a+n) ∧ (a ≤ j ∧ j < a+n) then (b i * v^(i+delta)) * (b j * v^(j+delta)) * bSurvival h p (max (bRequiredAge a g delta i) (bRequiredAge a g delta j)) else 0

end ActuarialAnnuities


