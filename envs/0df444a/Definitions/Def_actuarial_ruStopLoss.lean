-- Prove2me | Definitions.Def_actuarial_ruStopLoss
-- name    : actuarial_ruStopLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:52:52.207124+00:00
-- url     : https://prove2.me/theorems/c7902fc6-2be0-4bb0-9394-5dac79d0a0ea
-- title:
--   Stop-loss reinsurance, retained deficit and pathwise capital: ruStopLoss
-- statement:
--   Nonnegative excess-of-loss reinsurer payment above an attachment point d. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Y=(X-d)^+
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ruStopLoss (claim retention : ℝ) : ℝ := max 0 (claim-retention)

end ActuarialValuation


