-- Prove2me | Definitions.Def_actuarial_d_pureY
-- name    : actuarial_d_pureY
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:38:57.876051+00:00
-- url     : https://prove2.me/theorems/8fa977a5-2dc0-4793-a5a0-9657a26934ab
-- title:
--   Spouse pure endowment
-- statement:
--   Spouse pure endowment. Unit survivor-contingent maturity payment at tick t. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   E_y(t)=d_tS_y(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.4, p. 147. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_py

namespace ActuarialJointD
noncomputable def pureY (h t : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := d t * py h p t
end ActuarialJointD


