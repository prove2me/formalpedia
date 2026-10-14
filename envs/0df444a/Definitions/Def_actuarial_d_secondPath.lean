-- Prove2me | Definitions.Def_actuarial_d_secondPath
-- name    : actuarial_d_secondPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:36:10.504619+00:00
-- url     : https://prove2.me/theorems/4be913a5-4cba-443d-b2ca-7fd63e26952f
-- title:
--   Second-death lump sum
-- statement:
--   Second-death lump sum. Unit claim settled only if both deaths occur strictly before the censoring horizon. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_2(i,j)=d_{\max(i,j)+1}\mathbf{1}_{\{\max(i,j)<h\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.2, p. 154. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def secondPath (h : ℕ) (d : ℕ → ℝ) (i j : ℕ) : ℝ := if max i j < h then d (max i j+1) else 0
end ActuarialJointD


