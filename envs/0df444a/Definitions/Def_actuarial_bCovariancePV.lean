-- Prove2me | Definitions.Def_actuarial_bCovariancePV
-- name    : actuarial_bCovariancePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:25:18.648441+00:00
-- url     : https://prove2.me/theorems/de6dbc42-1e64-4a41-a7e5-e263f8249a3f
-- title:
--   Pairwise covariance formula induced by one common future lifetime.
-- statement:
--   Pairwise covariance formula induced by one common future lifetime. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   C=\sum_{i,j}c_ic_j[S(\max(r_i,r_j))-S(r_i)S(r_j)]
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Squared present value in GBP²; first moments and benefit amounts are GBP.
-- source:
--   Original derived finite annuity result. Contextual source page 143, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Pairwise covariance formula induced by one common future lifetime.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bRequiredAge

namespace ActuarialAnnuities

noncomputable def bCovariancePV (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h, if (a ≤ i ∧ i < a+n) ∧ (a ≤ j ∧ j < a+n) then (b i * v^(i+delta)) * (b j * v^(j+delta)) * (bSurvival h p (max (bRequiredAge a g delta i) (bRequiredAge a g delta j)) - bSurvival h p (bRequiredAge a g delta i) * bSurvival h p (bRequiredAge a g delta j)) else 0

end ActuarialAnnuities


