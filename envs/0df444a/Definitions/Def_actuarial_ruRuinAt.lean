-- Prove2me | Definitions.Def_actuarial_ruRuinAt
-- name    : actuarial_ruRuinAt
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:51:42.639169+00:00
-- url     : https://prove2.me/theorems/3a9ca2d5-e6c7-452b-9623-78d42dabb97b
-- title:
--   First passage and deficit at ruin: ruRuinAt
-- statement:
--   Event that period-end insurer surplus is strictly negative. Zero surplus is not a ruin event. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_n<0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus

namespace ActuarialValuation

def ruRuinAt (initial premium : ℝ) (claim : ℕ → ℝ) (n : ℕ) : Prop := ruPathSurplus initial premium claim n < 0

end ActuarialValuation


