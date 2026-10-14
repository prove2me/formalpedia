-- Prove2me | Definitions.Def_actuarial_bUDDMicroMass
-- name    : actuarial_bUDDMicroMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:26:46.151979+00:00
-- url     : https://prove2.me/theorems/96a15ea2-e8d4-4c31-b814-04a9665e6995
-- title:
--   True subperiod lifetime-state masses from uniform allocation of each annual death-year probability.
-- statement:
--   True subperiod lifetime-state masses from uniform allocation of each annual death-year probability. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   p^{(m)}_q=\frac{p_{\lfloor q/m\rfloor}}m\quad(q<hm)
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Probability, dimensionless, indexed in whole micro-instalments.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. True subperiod lifetime-state masses from uniform allocation of each annual death-year probability.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAnnuities

noncomputable def bUDDMicroMass (h m : ℕ) (p : ℕ → ℝ) (q : ℕ) : ℝ := if q < h*m then p (q/m) / (m : ℝ) else if q = h*m then p h else 0

end ActuarialAnnuities


