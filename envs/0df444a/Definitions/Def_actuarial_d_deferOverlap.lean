-- Prove2me | Definitions.Def_actuarial_d_deferOverlap
-- name    : actuarial_d_deferOverlap
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:52:53.239457+00:00
-- url     : https://prove2.me/theorems/5acee8ea-49c4-4de0-9d4e-adee8998b798
-- title:
--   Deferred pension overlap removed
-- statement:
--   Deferred pension overlap removed. Value of spouse payments otherwise eligible during a guarantee period. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{O;a,n}=\sum_{\substack{0\leq k<n\\a+k<g}}d_{a+k}b_{a+k}R_y(a+k)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_deferValue

namespace ActuarialJointD
noncomputable def deferOverlap (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := deferValue h a n p d b (fun i j t => if t < g then onlyY i j t else 0)
end ActuarialJointD


