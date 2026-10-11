-- Prove2me | Definitions.Def_actuarial_utExpectedUninsured
-- name    : actuarial_utExpectedUninsured
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:01:03.998313+00:00
-- url     : https://prove2.me/theorems/85651941-c670-44da-959b-9e4a5e54a8c9
-- title:
--   Actuarial insurance certainty equivalents and premium indifference: utExpectedUninsured
-- statement:
--   Policyholder expected utility with random uninsured loss. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \pi_a(X)=\frac{1}{a}\log\mathbb E[e^{aX}]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 122. J. W. Pratt, Risk Aversion in the Small and in the Large, Econometrica (1964), https://doi.org/10.2307/1913738; Rothschild and Stiglitz, Increasing Risk I (1970), https://doi.org/10.1016/0022-0531(70)90038-4. Parent topic: CARA utility, Arrow-Pratt aversion, finite-scenario expected insurance utility, exact entropic premium indifference and monotone coupling risk orders. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/1913738

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utCARA
import Definitions.Def_actuarial_utExpectedUtility

namespace ActuarialValuation

noncomputable def utExpectedUninsured {n : ℕ} (p : Fin n → ℝ) (loss : Fin n → ℝ) (a wealth : ℝ) : ℝ := utExpectedUtility p (fun k => wealth-loss k) (utCARA a)

end ActuarialValuation


