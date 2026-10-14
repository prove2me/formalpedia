-- Prove2me | Definitions.Def_actuarial_d_deferBlockedRev
-- name    : actuarial_d_deferBlockedRev
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:52:38.763576+00:00
-- url     : https://prove2.me/theorems/afd37210-b492-4d82-ad82-cf52278a8f93
-- title:
--   Deferred spouse reversion blocked by guarantee
-- statement:
--   Deferred spouse reversion blocked by guarantee. Spouse pension starts after both member death and expiry of the guaranteed payment window. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{R;a,n}=\sum_{k=0}^{n-1}d_{a+k}b_{a+k}\mathbb E_p[R_g(i,j,a+k)]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferValue
import Definitions.Def_actuarial_d_delayedSpouse

namespace ActuarialJointD
noncomputable def deferBlockedRev (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := deferValue h a n p d b (fun i j t => delayedSpouse g i j t)
end ActuarialJointD


