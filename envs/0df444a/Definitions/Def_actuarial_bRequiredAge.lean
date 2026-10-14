-- Prove2me | Definitions.Def_actuarial_bRequiredAge
-- name    : actuarial_bRequiredAge
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:22:02.267994+00:00
-- url     : https://prove2.me/theorems/53180af9-61b4-49d7-90e8-b62862981d3d
-- title:
--   Single event time whose survival activates each actual due or arrears instalment, accounting for guarantees.
-- statement:
--   Single event time whose survival activates each actual due or arrears instalment, accounting for guarantees. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   r_j=\begin{cases}a,&j<a+g\\j+\delta,&j\ge a+g\end{cases}
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Whole anniversary/payment index, dimensionless integer.
-- source:
--   Original derived finite annuity result. Contextual source page 159, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Single event time whose survival activates each actual due or arrears instalment, accounting for guarantees.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAnnuities

noncomputable def bRequiredAge (a g delta j : ℕ) : ℕ := if j < a+g then a else j+delta

end ActuarialAnnuities


