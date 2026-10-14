-- Prove2me | Definitions.Def_actuarial_d_deferY
-- name    : actuarial_d_deferY
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:41:02.30642+00:00
-- url     : https://prove2.me/theorems/e641fad3-1a5b-4136-94bf-d15a37c7e89f
-- title:
--   Spouse deferred annuity
-- statement:
--   Spouse deferred annuity. Actual scheduled instalments during the deferred temporary cover, using one joint mortality law. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{y;a,n}=\sum_{k=0}^{n-1}d_{a+k}b_{a+k}S_y(a+k)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_deferValue

namespace ActuarialJointD
noncomputable def deferY (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := deferValue h a n p d b (fun i j t => alive j t)
end ActuarialJointD


