-- Prove2me | Definitions.Def_actuarial_d_plast
-- name    : actuarial_d_plast
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:33:41.368979+00:00
-- url     : https://prove2.me/theorems/4e345568-2ef5-4595-8486-a1ef10f9a922
-- title:
--   Last-survivor probability
-- statement:
--   Last-survivor probability. At least one life is alive at the benefit date. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   S_{\text{last}}(t)=S_x(t)+S_y(t)-S_{xy}(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_last
import Definitions.Def_actuarial_d_expect

namespace ActuarialJointD
noncomputable def plast (h : ℕ) (p : ℕ → ℕ → ℝ) (t : ℕ) : ℝ := expect h p (fun i j => last i j t)
end ActuarialJointD


