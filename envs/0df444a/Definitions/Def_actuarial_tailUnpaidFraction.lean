-- Prove2me | Definitions.Def_actuarial_tailUnpaidFraction
-- name    : actuarial_tailUnpaidFraction
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:22:18.127698+00:00
-- url     : https://prove2.me/theorems/2b4cae9c-3956-40e9-9e24-eef61b5e8dbd
-- title:
--   Finite stop-loss and Rockafellar-Uryasev threshold objective: tailUnpaidFraction
-- statement:
--   Tail probability mass scale must be strictly positive for the auxiliary CVaR formula. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \tau=1-\alpha
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def tailUnpaidFraction (alpha : ℝ) : ℝ := 1-alpha

end ActuarialValuation


