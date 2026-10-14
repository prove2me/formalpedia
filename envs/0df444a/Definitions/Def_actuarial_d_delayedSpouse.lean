-- Prove2me | Definitions.Def_actuarial_d_delayedSpouse
-- name    : actuarial_d_delayedSpouse
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:50:08.791831+00:00
-- url     : https://prove2.me/theorems/6a7a266c-8281-4663-af59-3d820ede722f
-- title:
--   Guarantee-blocked spouse entitlement
-- statement:
--   Guarantee-blocked spouse entitlement. Spouse reversion begins only when the guarantee period ends and spouse remains alive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   R_g(i,j,t)=I_{\{t\geq g\}}I_{\text{y only}}(i,j,t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY

namespace ActuarialJointD
noncomputable def delayedSpouse (g i j t : ℕ) : ℝ := if t < g then (0 : ℝ) else onlyY i j t
end ActuarialJointD


