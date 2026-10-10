-- Prove2me | Definitions.Def_actuarial_tailCVaRObjective
-- name    : actuarial_tailCVaRObjective
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:17:56.075548+00:00
-- url     : https://prove2.me/theorems/b3251797-bf2a-4437-8e9e-d0e720240f9c
-- title:
--   Finite stop-loss and Rockafellar-Uryasev threshold objective: tailCVaRObjective
-- statement:
--   The algebraic Rockafellar-Uryasev auxiliary objective uses a threshold and denominator 1-alpha; its financial CVaR interpretation additionally requires normalised probability weights and a confidence level in the unit interval. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_\alpha(t)=t+SL_n(t)/(1-\alpha)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailStopLoss

namespace ActuarialValuation

noncomputable def tailCVaRObjective (p : ℕ → ℝ) (n : ℕ) (alpha threshold : ℝ) : ℝ := threshold + tailStopLoss p n threshold / (1-alpha)

end ActuarialValuation


