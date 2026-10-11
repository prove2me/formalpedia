-- Prove2me | Definitions.Def_actuarial_ruFirstRuin
-- name    : actuarial_ruFirstRuin
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:52:21.422794+00:00
-- url     : https://prove2.me/theorems/21c4b2d4-688b-4cce-a111-282c17064b41
-- title:
--   First passage and deficit at ruin: ruFirstRuin
-- statement:
--   First-passage event at a specified period n, excluding any earlier failed surplus states. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   τ=n iff U_n<0 and U_k≥0 for k<n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRuinAt

namespace ActuarialValuation

def ruFirstRuin (initial premium : ℝ) (claim : ℕ → ℝ) (n : ℕ) : Prop := ruRuinAt initial premium claim n ∧ ∀ k : ℕ, k < n → ¬ ruRuinAt initial premium claim k

end ActuarialValuation


