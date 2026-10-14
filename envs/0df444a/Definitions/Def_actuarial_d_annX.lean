-- Prove2me | Definitions.Def_actuarial_d_annX
-- name    : actuarial_d_annX
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:34:18.366993+00:00
-- url     : https://prove2.me/theorems/4892e14e-3860-4b15-8708-67dfa4388fa8
-- title:
--   Member life annuity
-- statement:
--   Member life annuity. Pays each instalment while the member is alive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_x=\sum_{t=0}^{n-1}d_tb_t S_x(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_annValue

namespace ActuarialJointD
noncomputable def annX (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := annValue h n p d b (fun i j t => alive i t)
end ActuarialJointD


