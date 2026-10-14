-- Prove2me | Definitions.Def_actuarial_d_pureX
-- name    : actuarial_d_pureX
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:38:44.977599+00:00
-- url     : https://prove2.me/theorems/606edce6-48f3-4985-9572-591db8cbe894
-- title:
--   Member pure endowment
-- statement:
--   Member pure endowment. Unit survivor-contingent maturity payment to the member at tick t. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   E_x(t)=d_tS_x(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.4, p. 147. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_px

namespace ActuarialJointD
noncomputable def pureX (h t : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := d t * px h p t
end ActuarialJointD


