-- Prove2me | Definitions.Def_actuarial_utExpectedUtility
-- name    : actuarial_utExpectedUtility
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:59:44.117705+00:00
-- url     : https://prove2.me/theorems/66d6937c-f5f9-4e9b-8b8c-5e350ff6e22f
-- title:
--   Expected exponential utility and absolute risk aversion: utExpectedUtility
-- statement:
--   Actual weighted utility averaged across insurance-loss scenarios. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   u_a(w)=-e^{-aw},\quad A(w)=-u''_a(w)/u'_a(w)=a
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 122. J. W. Pratt, Risk Aversion in the Small and in the Large, Econometrica (1964), https://doi.org/10.2307/1913738; Rothschild and Stiglitz, Increasing Risk I (1970), https://doi.org/10.1016/0022-0531(70)90038-4. Parent topic: CARA utility, Arrow-Pratt aversion, finite-scenario expected insurance utility, exact entropic premium indifference and monotone coupling risk orders. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/1913738

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utExpected

namespace ActuarialValuation

noncomputable def utExpectedUtility {n : ℕ} (p : Fin n → ℝ) (wealth : Fin n → ℝ) (u : ℝ → ℝ) : ℝ := utExpected p (fun k => u (wealth k))

end ActuarialValuation


