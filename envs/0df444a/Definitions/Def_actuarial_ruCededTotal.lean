-- Prove2me | Definitions.Def_actuarial_ruCededTotal
-- name    : actuarial_ruCededTotal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:53:27.619111+00:00
-- url     : https://prove2.me/theorems/4d527c53-23a8-4602-85f8-5d419bc55b48
-- title:
--   Stop-loss reinsurance, retained deficit and pathwise capital: ruCededTotal
-- statement:
--   Aggregate stop-loss recoveries earned from the reinsurer along the observed claim path. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_n^{ceded}=Σ(X_k-d)^+
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruStopLoss

namespace ActuarialValuation

noncomputable def ruCededTotal (claim : ℕ → ℝ) (retention : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, ruStopLoss (claim k) retention

end ActuarialValuation


