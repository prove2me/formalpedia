-- Prove2me | Definitions.Def_actuarial_crExpected
-- name    : actuarial_crExpected
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:44.348964+00:00
-- url     : https://prove2.me/theorems/306a3529-0f46-41aa-99fe-db634f4971c0
-- title:
--   Actual finite loss distributions and scenario ambiguity: crExpected
-- statement:
--   Actual finite-scenario expected monetary loss with weights forming a probability distribution under explicit nonnegative normalisation.
--
--   Mathematical relation:
--
--   $$
--   ∑ i : Fin n, p i * X i
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def crExpected {n : ℕ} (p X : Fin n→ℝ) : ℝ := ∑ i : Fin n, p i * X i

end ActuarialValuation


