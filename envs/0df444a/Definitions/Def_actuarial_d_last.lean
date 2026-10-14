-- Prove2me | Definitions.Def_actuarial_d_last
-- name    : actuarial_d_last
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:32:23.22599+00:00
-- url     : https://prove2.me/theorems/ad0275d7-c489-4d1c-bfbf-a3d5269bbf28
-- title:
--   At least one alive
-- statement:
--   At least one alive. Last-survivor status indicator, with the four states disjoint. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{last}}=I_{\text{both}}+I_{\text{x only}}+I_{\text{y only}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_onlyX
import Definitions.Def_actuarial_d_onlyY

namespace ActuarialJointD
noncomputable def last (i j t : ℕ) : ℝ := both i j t + onlyX i j t + onlyY i j t
end ActuarialJointD


