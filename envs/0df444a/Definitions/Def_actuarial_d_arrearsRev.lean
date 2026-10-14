-- Prove2me | Definitions.Def_actuarial_d_arrearsRev
-- name    : actuarial_d_arrearsRev
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:48:52.736975+00:00
-- url     : https://prove2.me/theorems/7f53612e-9dba-47e7-b311-3597ca6a1c01
-- title:
--   Reversionary spouse annuity in arrears
-- statement:
--   Reversionary spouse annuity in arrears. Period-end instalments, conditional on the entitlement status at that date. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{y\mid x}^{\text{arrears}}=\sum_{k=0}^{n-1}d_{k+1}b_{k+1}R_y(k+1)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_arrearsValue

namespace ActuarialJointD
noncomputable def arrearsRev (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := arrearsValue h n p d b (onlyY)
end ActuarialJointD


