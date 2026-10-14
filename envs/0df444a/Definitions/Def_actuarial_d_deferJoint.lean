-- Prove2me | Definitions.Def_actuarial_d_deferJoint
-- name    : actuarial_d_deferJoint
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:41:14.697982+00:00
-- url     : https://prove2.me/theorems/9bcc3a1f-0a22-497d-bb54-eb64172082bd
-- title:
--   Deferred joint-life annuity
-- statement:
--   Deferred joint-life annuity. Actual scheduled instalments during the deferred temporary cover, using one joint mortality law. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{xy;a,n}=\sum_{k=0}^{n-1}d_{a+k}b_{a+k}S_{xy}(a+k)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_deferValue

namespace ActuarialJointD
noncomputable def deferJoint (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := deferValue h a n p d b (both)
end ActuarialJointD


