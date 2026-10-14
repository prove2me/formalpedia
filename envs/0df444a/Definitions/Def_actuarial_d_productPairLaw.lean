-- Prove2me | Definitions.Def_actuarial_d_productPairLaw
-- name    : actuarial_d_productPairLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:49:42.37017+00:00
-- url     : https://prove2.me/theorems/46e4a497-b4e9-49ce-a4ad-af2ff6270e14
-- title:
--   Independent two-state law
-- statement:
--   Independent two-state law. Uniform product death-state law with the same single-life margins as the dependent law. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{ij}=\frac14\quad (i,j\in\{0,1\})
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def productPairLaw (i j : ℕ) : ℝ := if i < 2 ∧ j < 2 then (1/4 : ℝ) else 0
end ActuarialJointD


