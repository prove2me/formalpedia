-- Prove2me | Definitions.Def_actuarial_tailShiftObjective
-- name    : actuarial_tailShiftObjective
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:28:55.920057+00:00
-- url     : https://prove2.me/theorems/350c7151-d73a-47ad-9432-bc6d192560b6
-- title:
--   Discrete cumulative tails, thresholds and monetary shifts: tailShiftObjective
-- statement:
--   Shifted loss objective tracks the translation-invariance of CVaR's threshold formulation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_\alpha^{shift}(t+s)=t+s+SL_n(t)/(1-\alpha)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailShiftExcess

namespace ActuarialValuation

noncomputable def tailShiftObjective (p : ℕ → ℝ) (n : ℕ) (alpha threshold shift : ℝ) : ℝ := (threshold+shift) + (∑ k ∈ Finset.range (n+1), tailShiftExcess (k : ℝ) shift threshold * p k) / (1-alpha)

end ActuarialValuation


