-- Prove2me | Definitions.Def_actuarial_utDiscreteCDF
-- name    : actuarial_utDiscreteCDF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:02:01.34092+00:00
-- url     : https://prove2.me/theorems/ca38ab1f-8831-42a0-a3db-d74f60d957e3
-- title:
--   Genuine pathwise coupling and finite first-order stochastic dominance: utDiscreteCDF
-- statement:
--   Distribution of finite insured wealth or loss at a monetary threshold. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

namespace ActuarialValuation

noncomputable def utDiscreteCDF {n : ℕ} (p : Fin n → ℝ) (x : Fin n → ℝ) (threshold : ℝ) : ℝ := ∑ k : Fin n, if x k≤threshold then p k else 0

end ActuarialValuation


