-- Prove2me | Definitions.Def_actuarial_ruRetained
-- name    : actuarial_ruRetained
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:53:00.707813+00:00
-- url     : https://prove2.me/theorems/c509badc-2244-4817-83b9-6f0c29b280c0
-- title:
--   Stop-loss reinsurance, retained deficit and pathwise capital: ruRetained
-- statement:
--   Retained individual claim under nonnegative policy attachment; comparison remains algebraic for all reals. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   X^R=min(X,d)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ruRetained (claim retention : ℝ) : ℝ := min claim retention

end ActuarialValuation


