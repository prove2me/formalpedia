-- Prove2me | Definitions.Def_actuarial_d_guaranteeOverlapPath
-- name    : actuarial_d_guaranteeOverlapPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:50:54.114009+00:00
-- url     : https://prove2.me/theorems/e1afb6e4-010d-489f-b353-9aaae658944a
-- title:
--   Overlapping guarantee and reversion cashflow
-- statement:
--   Overlapping guarantee and reversion cashflow. Eligible spouse dates during the guaranteed member payment window. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{\text{overlap}}=\sum_{t<g}d_tb_tI_{\text{y only}}(i,j,t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_annPath

namespace ActuarialJointD
noncomputable def guaranteeOverlapPath (n g : ℕ) (d b : ℕ → ℝ) (i j : ℕ) : ℝ := annPath n d b (fun t => if t < g then onlyY i j t else 0)
end ActuarialJointD


