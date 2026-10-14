-- Prove2me | Definitions.Def_actuarial_d_ySecondPath
-- name    : actuarial_d_ySecondPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:36:52.272228+00:00
-- url     : https://prove2.me/theorems/215d6feb-b628-4885-98b9-f51b8c231708
-- title:
--   Spouse dies second
-- statement:
--   Spouse dies second. Spouse's later death after member dies first. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_{y\succ x}(i,j)=d_{j+1}\mathbf{1}_{\{i<j<h\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.2, p. 154. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def ySecondPath (h : ℕ) (d : ℕ → ℝ) (i j : ℕ) : ℝ := if i < j ∧ j < h then d (j+1) else 0
end ActuarialJointD


