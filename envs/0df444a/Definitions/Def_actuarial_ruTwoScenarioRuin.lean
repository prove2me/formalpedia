-- Prove2me | Definitions.Def_actuarial_ruTwoScenarioRuin
-- name    : actuarial_ruTwoScenarioRuin
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:53:33.782978+00:00
-- url     : https://prove2.me/theorems/2964f275-9dea-409c-9e4e-0cedcf1f87a8
-- title:
--   Stop-loss reinsurance, retained deficit and pathwise capital: ruTwoScenarioRuin
-- statement:
--   Exact finite-scenario ruin probability from two mutually exclusive model outcomes with Boolean ruin indicators. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P(ruin)=p 1_A+q 1_B
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ruTwoScenarioRuin (p q : ℝ) (a b : Bool) : ℝ := (if a then p else 0)+(if b then q else 0)

end ActuarialValuation


