-- Prove2me | Definitions.Def_actuarial_ruClaimTotal
-- name    : actuarial_ruClaimTotal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:50:52.020616+00:00
-- url     : https://prove2.me/theorems/22b4b2d3-ec3d-4cd8-8b49-12328d3a5cb4
-- title:
--   Premium and claim surplus cash-flow recursion: ruClaimTotal
-- statement:
--   Total insurer claim outgo over a finite half-open observation horizon, with claims at period ends. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_n=Σ_{k<n}X_k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ruClaimTotal (claim : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, claim k

end ActuarialValuation


