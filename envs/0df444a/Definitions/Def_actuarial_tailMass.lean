-- Prove2me | Definitions.Def_actuarial_tailMass
-- name    : actuarial_tailMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T08:43:59.683176+00:00
-- url     : https://prove2.me/theorems/43057697-d0ea-4ec5-9885-ec2e9c7b0de8
-- title:
--   Finite scenario probabilities, losses and positive-part payouts: tailMass
-- statement:
--   Finite nonnegative scenario weights form a genuine loss probability distribution only when their total mass is one. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M_n=\sum_{k=0}^{n}p_k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def tailMass (p : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1), p k

end ActuarialValuation


