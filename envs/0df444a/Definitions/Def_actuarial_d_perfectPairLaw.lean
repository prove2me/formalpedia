-- Prove2me | Definitions.Def_actuarial_d_perfectPairLaw
-- name    : actuarial_d_perfectPairLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:49:33.721818+00:00
-- url     : https://prove2.me/theorems/40d8cbc8-6db1-4844-ae8b-12f974593562
-- title:
--   Perfectly dependent two-state law
-- statement:
--   Perfectly dependent two-state law. Equal one-year death-state outcomes: half both die and half both survive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{00}=p_{11}=\frac12,\quad p_{01}=p_{10}=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def perfectPairLaw (i j : ℕ) : ℝ := if i = j ∧ i < 2 then (1/2 : ℝ) else 0
end ActuarialJointD


