-- Prove2me | Definitions.Def_actuarial_d_prev
-- name    : actuarial_d_prev
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:33:27.071175+00:00
-- url     : https://prove2.me/theorems/94804be0-4433-48f0-b218-122a110d125f
-- title:
--   Reversionary spouse occupancy
-- statement:
--   Reversionary spouse occupancy. Member dead and spouse alive at the benefit date. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   R_y(t)=\sum_{i,j}p_{ij}[1-I_x(i,t)]I_y(j,t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_expect

namespace ActuarialJointD
noncomputable def prev (h : ℕ) (p : ℕ → ℕ → ℝ) (t : ℕ) : ℝ := expect h p (fun i j => onlyY i j t)
end ActuarialJointD


