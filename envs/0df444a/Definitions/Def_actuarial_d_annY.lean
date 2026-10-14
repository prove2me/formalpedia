-- Prove2me | Definitions.Def_actuarial_d_annY
-- name    : actuarial_d_annY
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:34:38.42212+00:00
-- url     : https://prove2.me/theorems/38a4cde4-0462-46c1-a6e1-e82ae9cf82ef
-- title:
--   Spouse life annuity
-- statement:
--   Spouse life annuity. Pays each instalment while the spouse is alive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_y=\sum_{t=0}^{n-1}d_tb_t S_y(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_annValue

namespace ActuarialJointD
noncomputable def annY (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := annValue h n p d b (fun i j t => alive j t)
end ActuarialJointD


