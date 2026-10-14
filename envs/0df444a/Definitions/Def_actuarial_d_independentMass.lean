-- Prove2me | Definitions.Def_actuarial_d_independentMass
-- name    : actuarial_d_independentMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:49:12.091985+00:00
-- url     : https://prove2.me/theorems/81234ed0-2115-4af3-b5f1-3528168da8b1
-- title:
--   Independent joint probability kernel
-- statement:
--   Independent joint probability kernel. A product of two full marginal death-year probability mass functions. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{ij}^{\text{ind}}=u_i v_j
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def independentMass (u v : ℕ → ℝ) (i j : ℕ) : ℝ := u i * v j
end ActuarialJointD


