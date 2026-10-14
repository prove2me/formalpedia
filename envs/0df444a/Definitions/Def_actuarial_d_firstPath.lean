-- Prove2me | Definitions.Def_actuarial_d_firstPath
-- name    : actuarial_d_firstPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:36:02.852313+00:00
-- url     : https://prove2.me/theorems/f4bf4108-0647-45c4-a560-2c15455cdc54
-- title:
--   First-death lump sum
-- statement:
--   First-death lump sum. Unit claim settled at the first death tick, with survival censored at h. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_1(i,j)=d_{\min(i,j)+1}\mathbf{1}_{\{\min(i,j)<h\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.1, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def firstPath (h : ℕ) (d : ℕ → ℝ) (i j : ℕ) : ℝ := if min i j < h then d (min i j+1) else 0
end ActuarialJointD


