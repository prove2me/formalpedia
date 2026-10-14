-- Prove2me | Definitions.Def_actuarial_d_annLast
-- name    : actuarial_d_annLast
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:35:15.794803+00:00
-- url     : https://prove2.me/theorems/c6a8ea3a-91eb-465b-afdd-8d8f46a8c95f
-- title:
--   Last-survivor annuity
-- statement:
--   Last-survivor annuity. Pays while one or both lives are alive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{\text{last}}=\sum_{t=0}^{n-1}d_tb_t S_{\text{last}}(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_last
import Definitions.Def_actuarial_d_annValue

namespace ActuarialJointD
noncomputable def annLast (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := annValue h n p d b last
end ActuarialJointD


