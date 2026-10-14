-- Prove2me | Definitions.Def_actuarial_d_annRev
-- name    : actuarial_d_annRev
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:35:32.748729+00:00
-- url     : https://prove2.me/theorems/2ce70c95-9172-401c-8732-fe2456866ed8
-- title:
--   Reversionary spouse annuity
-- statement:
--   Reversionary spouse annuity. Pays to the spouse following member death, subject to spouse survival at the date. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{y\mid x}=\sum_{t=0}^{n-1}d_tb_t R_y(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_annValue

namespace ActuarialJointD
noncomputable def annRev (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := annValue h n p d b onlyY
end ActuarialJointD


