-- Prove2me | Definitions.Def_actuarial_bUDDMicroSurvival
-- name    : actuarial_bUDDMicroSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:26:58.817989+00:00
-- url     : https://prove2.me/theorems/b16cdfc2-c632-4c99-819f-8e85a89edcda
-- title:
--   Micro-anniversary survival derived by summing subperiod state masses.
-- statement:
--   Micro-anniversary survival derived by summing subperiod state masses. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   S^{(m)}(q)=\sum_{k\ge q}p^{(m)}_k
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Probability, dimensionless, indexed in whole micro-instalments.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Micro-anniversary survival derived by summing subperiod state masses.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bUDDMicroMass

namespace ActuarialAnnuities

noncomputable def bUDDMicroSurvival (h m : ℕ) (p : ℕ → ℝ) (q : ℕ) : ℝ := bSurvival (h*m) (bUDDMicroMass h m p) q

end ActuarialAnnuities


