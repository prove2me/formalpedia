-- Prove2me | Definitions.Def_actuarial_tailStopLoss
-- name    : actuarial_tailStopLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:17:37.215162+00:00
-- url     : https://prove2.me/theorems/7c4c91ce-997e-4d1d-a68f-8f13ad7909ce
-- title:
--   Finite stop-loss and Rockafellar-Uryasev threshold objective: tailStopLoss
-- statement:
--   The stop-loss payout sum is a genuine expected excess payment when the scenario weights have unit total mass. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL_n(t)=\sum_{k=0}^n(k-t)_+p_k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailExcess

namespace ActuarialValuation

noncomputable def tailStopLoss (p : ℕ → ℝ) (n : ℕ) (threshold : ℝ) : ℝ := ∑ k ∈ Finset.range (n+1), tailExcess (k : ℝ) threshold * p k

end ActuarialValuation


