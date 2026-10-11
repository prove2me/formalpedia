-- Prove2me | Definitions.Def_actuarial_cxBernAggregateMass
-- name    : actuarial_cxBernAggregateMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:51:51.492258+00:00
-- url     : https://prove2.me/theorems/8e45f5df-52c2-4fc5-8c8c-f28655ca5048
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxBernAggregateMass
-- statement:
--   Exact aggregate probability with independent Bernoulli count N in {0,1}. Claims of zero monetary size contribute when N=1. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_0=p_0+p_1 f_0; g_k=p_1 f_k (k>0)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cxBernAggregateMass (p0 p1 : ℝ) (f : ℕ → ℝ) (k : ℕ) : ℝ := if k=0 then p0+p1*f 0 else p1*f k

end ActuarialValuation


