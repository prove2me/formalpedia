-- Prove2me | Definitions.Def_actuarial_d_deferTopup
-- name    : actuarial_d_deferTopup
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:52:24.334673+00:00
-- url     : https://prove2.me/theorems/c850bb32-ee1e-45da-97e9-3f7c3c36146d
-- title:
--   Value of the member-guarantee top-up
-- statement:
--   Value of the member-guarantee top-up. Incremental value of guaranteed member pension payments after death. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{U;a,n}=\sum_{k=0}^{n-1}d_{a+k}b_{a+k}\mathbb E_p[U_g(i,a+k)]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferValue
import Definitions.Def_actuarial_d_guaranteeTopup

namespace ActuarialJointD
noncomputable def deferTopup (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := deferValue h a n p d b (fun i j t => guaranteeTopup g i t)
end ActuarialJointD


