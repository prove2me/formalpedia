-- Prove2me | Definitions.Def_actuarial_d_xSecondPath
-- name    : actuarial_d_xSecondPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:36:46.112193+00:00
-- url     : https://prove2.me/theorems/e1e99ed5-9733-4e86-9e06-f653f6a2b4a3
-- title:
--   Member dies second
-- statement:
--   Member dies second. Survivor's later death after spouse dies first. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_{x\succ y}(i,j)=d_{i+1}\mathbf{1}_{\{j<i<h\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.2, p. 154. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def xSecondPath (h : ℕ) (d : ℕ → ℝ) (i j : ℕ) : ℝ := if j < i ∧ i < h then d (i+1) else 0
end ActuarialJointD


