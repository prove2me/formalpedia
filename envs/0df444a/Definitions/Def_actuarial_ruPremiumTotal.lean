-- Prove2me | Definitions.Def_actuarial_ruPremiumTotal
-- name    : actuarial_ruPremiumTotal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:50:57.932737+00:00
-- url     : https://prove2.me/theorems/e9bd8a36-b177-4ebe-9704-d794e416ef3d
-- title:
--   Premium and claim surplus cash-flow recursion: ruPremiumTotal
-- statement:
--   Deterministic cumulative premium receipts for a constant period contribution rate. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P_n=nc
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ruPremiumTotal (rate : ℝ) (n : ℕ) : ℝ := (n:ℝ)*rate

end ActuarialValuation


