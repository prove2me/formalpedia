-- Prove2me | Definitions.Def_actuarial_d_deferRev
-- name    : actuarial_d_deferRev
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:46:47.218801+00:00
-- url     : https://prove2.me/theorems/d1cde313-9314-49b9-8706-7527df539ab9
-- title:
--   Deferred spouse reversion
-- statement:
--   Deferred spouse reversion. Actual scheduled instalments during the deferred temporary cover, using one joint mortality law. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{y\mid x;a,n}=\sum_{k=0}^{n-1}d_{a+k}b_{a+k}R_y(a+k)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_deferValue

namespace ActuarialJointD
noncomputable def deferRev (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := deferValue h a n p d b (onlyY)
end ActuarialJointD


