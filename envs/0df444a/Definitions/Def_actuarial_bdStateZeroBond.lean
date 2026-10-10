-- Prove2me | Definitions.Def_actuarial_bdStateZeroBond
-- name    : actuarial_bdStateZeroBond
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:17.373492+00:00
-- url     : https://prove2.me/theorems/36412b88-6616-483e-b9b3-f488221aae2b
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdStateZeroBond
-- statement:
--   Price of a unit fixed redemption under a random one-period stochastic pricing deflator.
--
--   Mathematical relation:
--
--   $$
--   bdStatePV p discount (fun \_ => 1)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV

namespace ActuarialValuation

noncomputable def bdStateZeroBond {m : ℕ} (p discount : Fin m → ℝ) : ℝ := bdStatePV p discount (fun _ => 1)

end ActuarialValuation


