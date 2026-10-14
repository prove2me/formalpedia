-- Prove2me | Definitions.Def_actuarial_d_deferValue
-- name    : actuarial_d_deferValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:40:33.067834+00:00
-- url     : https://prove2.me/theorems/7ba0a498-e910-46b5-ab93-61c998cbeab5
-- title:
--   Deferred temporary occupation EPV
-- statement:
--   Deferred temporary occupation EPV. Averages realised status-tested instalments on the date range from a to a+n-1. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{a,n}=\mathbb E_p[Z_{a,n}]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_annRange

namespace ActuarialJointD
noncomputable def deferValue (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (s : ℕ → ℕ → ℕ → ℝ) : ℝ := expect h p (fun i j => annRange a n d b (s i j))
end ActuarialJointD


