-- Prove2me | Definitions.Def_actuarial_d_onlyY
-- name    : actuarial_d_onlyY
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:31:45.141976+00:00
-- url     : https://prove2.me/theorems/72df404e-d88d-4e63-ad53-1046a3a9e354
-- title:
--   Only the spouse alive
-- statement:
--   Only the spouse alive. Spouse alive after member death, the reversionary occupation state. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{y only}}(i,j,t)=[1-I_x(i,t)]I_y(j,t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

namespace ActuarialJointD
noncomputable def onlyY (i j t : ℕ) : ℝ := dead i t * alive j t
end ActuarialJointD


