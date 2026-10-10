-- Prove2me | Definitions.Def_actuarial_tailExcess
-- name    : actuarial_tailExcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T08:44:20.811985+00:00
-- url     : https://prove2.me/theorems/0eb7c2fe-1b4c-46e5-88f1-32c8754a0cb9
-- title:
--   Finite scenario probabilities, losses and positive-part payouts: tailExcess
-- statement:
--   An excess-of-loss indemnity is the positive part of insured loss after retention. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (x-t)_+=\max(x-t,0)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def tailExcess (loss threshold : ℝ) : ℝ := max (loss - threshold) 0

end ActuarialValuation


