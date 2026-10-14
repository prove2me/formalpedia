-- Prove2me | Definitions.Def_actuarial_d_deferGuaranteed
-- name    : actuarial_d_deferGuaranteed
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:52:08.964618+00:00
-- url     : https://prove2.me/theorems/a2080873-9eae-4e6e-9191-48f174415522
-- title:
--   Deferred guaranteed member pension
-- statement:
--   Deferred guaranteed member pension. Values scheduled member/guarantee instalments across the actual deferred period. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{G;a,n}=\sum_{k=0}^{n-1}d_{a+k}b_{a+k}\mathbb E_p[G_g(i,a+k)]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferValue
import Definitions.Def_actuarial_d_guaranteeMember

namespace ActuarialJointD
noncomputable def deferGuaranteed (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := deferValue h a n p d b (fun i j t => guaranteeMember g i t)
end ActuarialJointD


