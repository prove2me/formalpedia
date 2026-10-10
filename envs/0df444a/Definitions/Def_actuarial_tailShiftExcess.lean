-- Prove2me | Definitions.Def_actuarial_tailShiftExcess
-- name    : actuarial_tailShiftExcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:28:42.75552+00:00
-- url     : https://prove2.me/theorems/01a1fc14-a604-4128-b688-865048f4981a
-- title:
--   Discrete cumulative tails, thresholds and monetary shifts: tailShiftExcess
-- statement:
--   Uniformly shifting both claims and retention preserves the individual excess loss. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (x+s-(t+s))_+=(x-t)_+
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. Rockafellar and Uryasev, Optimization of Conditional Value-at-Risk (1999 preprint, later Journal of Risk 2000), equation 4 and Theorem 1, page 5, https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf; Rockafellar and Uryasev, Journal of Risk (2000), https://econpapers.repec.org/RePEc:rsk:journ4:2161159. Parent topic: Finite discrete loss distributions, excess-of-loss functionals and Rockafellar-Uryasev conditional value-at-risk auxiliary threshold objective. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://sites.math.washington.edu/~rtr/papers/rtr179-CVaR1.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailExcess

namespace ActuarialValuation

noncomputable def tailShiftExcess (loss shift threshold : ℝ) : ℝ := tailExcess (loss+shift) (threshold+shift)

end ActuarialValuation


