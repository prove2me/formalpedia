-- Prove2me | Definitions.Def_actuarial_d_arrearsY
-- name    : actuarial_d_arrearsY
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:48:01.111983+00:00
-- url     : https://prove2.me/theorems/6485a37c-5e59-43d1-ae13-c7affff56460
-- title:
--   Spouse life annuity in arrears
-- statement:
--   Spouse life annuity in arrears. Period-end instalments, conditional on the entitlement status at that date. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_y^{\text{arrears}}=\sum_{k=0}^{n-1}d_{k+1}b_{k+1}S_y(k+1)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_arrearsValue

namespace ActuarialJointD
noncomputable def arrearsY (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := arrearsValue h n p d b (fun i j t => alive j t)
end ActuarialJointD


