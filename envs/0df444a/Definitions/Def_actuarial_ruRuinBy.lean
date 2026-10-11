-- Prove2me | Definitions.Def_actuarial_ruRuinBy
-- name    : actuarial_ruRuinBy
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:52:05.02225+00:00
-- url     : https://prove2.me/theorems/f9eb7649-e6ee-4ad2-bc6e-d5bd89b56c73
-- title:
--   First passage and deficit at ruin: ruRuinBy
-- statement:
--   Finite-horizon ruin event: surplus becomes strictly negative at some observation boundary at or before n. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   ∃ k≤n, U_k<0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRuinAt

namespace ActuarialValuation

def ruRuinBy (initial premium : ℝ) (claim : ℕ → ℝ) (n : ℕ) : Prop := ∃ k : ℕ, k ≤ n ∧ ruRuinAt initial premium claim k

end ActuarialValuation


