-- Prove2me | Definitions.Def_actuarial_utExpectedStoploss
-- name    : actuarial_utExpectedStoploss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:02:27.300405+00:00
-- url     : https://prove2.me/theorems/2ae84972-f062-4513-b7dc-7f5157dca3c7
-- title:
--   Genuine pathwise coupling and finite first-order stochastic dominance: utExpectedStoploss
-- statement:
--   Actual finite stop-loss premium under a shared scenario mass. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   X\le Y\ \text{a.s.}\Longrightarrow \mathbb E[\phi(X)]\le\mathbb E[\phi(Y)]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 122. J. W. Pratt, Risk Aversion in the Small and in the Large, Econometrica (1964), https://doi.org/10.2307/1913738; Rothschild and Stiglitz, Increasing Risk I (1970), https://doi.org/10.1016/0022-0531(70)90038-4. Parent topic: CARA utility, Arrow-Pratt aversion, finite-scenario expected insurance utility, exact entropic premium indifference and monotone coupling risk orders. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/1913738

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utExpected
import Definitions.Def_actuarial_utPositiveStoploss

namespace ActuarialValuation

noncomputable def utExpectedStoploss {n : ℕ} (p : Fin n → ℝ) (loss : Fin n → ℝ) (retention : ℝ) : ℝ := utExpected p (fun k => utPositiveStoploss retention (loss k))

end ActuarialValuation


