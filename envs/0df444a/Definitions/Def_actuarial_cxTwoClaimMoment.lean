-- Prove2me | Definitions.Def_actuarial_cxTwoClaimMoment
-- name    : actuarial_cxTwoClaimMoment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:52:20.817158+00:00
-- url     : https://prove2.me/theorems/07e24f4d-3497-4d57-8b4a-0757e11bca0b
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxTwoClaimMoment
-- statement:
--   Aggregate raw second moment for a count supported on 0,1,2 independent identically distributed severity draws. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E[S²]=E[N]E[X²]+E[N(N-1)](E[X])²
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cxTwoClaimMoment (mean rawSecond p1 p2 : ℝ) : ℝ := (p1+2*p2)*rawSecond+2*p2*mean^2

end ActuarialValuation


