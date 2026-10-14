-- Prove2me | Definitions.Def_actuarial_d_neither
-- name    : actuarial_d_neither
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:32:07.645314+00:00
-- url     : https://prove2.me/theorems/1ff5c51f-6098-4e33-a9bb-9208a183831a
-- title:
--   Neither life alive
-- statement:
--   Neither life alive. Joint absorbing state at payment anniversary t. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{neither}}(i,j,t)=[1-I_x(i,t)][1-I_y(j,t)]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_dead

namespace ActuarialJointD
noncomputable def neither (i j t : ℕ) : ℝ := dead i t * dead j t
end ActuarialJointD


