-- Prove2me | Definitions.Def_actuarial_d_pureLast
-- name    : actuarial_d_pureLast
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:39:37.427433+00:00
-- url     : https://prove2.me/theorems/03eca547-2b55-4f53-adc7-5c415fdc5e61
-- title:
--   Last-survivor pure endowment
-- statement:
--   Last-survivor pure endowment. Maturity amount if one or both lives are alive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   E_{\text{last}}(t)=d_tS_{\text{last}}(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.4, p. 147. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_plast

namespace ActuarialJointD
noncomputable def pureLast (h t : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := d t * plast h p t
end ActuarialJointD


