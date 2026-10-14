-- Prove2me | Definitions.Def_actuarial_d_px
-- name    : actuarial_d_px
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:32:51.675903+00:00
-- url     : https://prove2.me/theorems/447ba9f9-7597-421c-9e3e-13d7dc12c1b7
-- title:
--   Member marginal survival
-- statement:
--   Member marginal survival. Member survival calculated by marginalising the genuine joint law. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   S_x(t)=\sum_{i,j}p_{ij}\mathbf{1}_{\{t\leq i\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_expect

namespace ActuarialJointD
noncomputable def px (h : ℕ) (p : ℕ → ℕ → ℝ) (t : ℕ) : ℝ := expect h p (fun i j => alive i t)
end ActuarialJointD


