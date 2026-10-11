-- Prove2me | Definitions.Def_actuarial_ruNetClaim
-- name    : actuarial_ruNetClaim
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:51:15.576032+00:00
-- url     : https://prove2.me/theorems/b3f98cd5-20e4-4a7c-9c07-5305f0967551
-- title:
--   Premium and claim surplus cash-flow recursion: ruNetClaim
-- statement:
--   Net claim drain after period premium receipt. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Y_k=X_k-c
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ruNetClaim (claim premium : ℝ) : ℝ := claim-premium

end ActuarialValuation


