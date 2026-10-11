-- Prove2me | Definitions.Def_actuarial_ruDeficit
-- name    : actuarial_ruDeficit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:52:32.462164+00:00
-- url     : https://prove2.me/theorems/b9465818-c530-4144-88aa-0ec7f1377793
-- title:
--   First passage and deficit at ruin: ruDeficit
-- statement:
--   Nonnegative shortfall at a nominated period. It equals the deficit at ruin on the first-passage event. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_n=max(0,-U_n)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus

namespace ActuarialValuation

noncomputable def ruDeficit (initial premium : ℝ) (claim : ℕ → ℝ) (n : ℕ) : ℝ := max 0 (-ruPathSurplus initial premium claim n)

end ActuarialValuation


