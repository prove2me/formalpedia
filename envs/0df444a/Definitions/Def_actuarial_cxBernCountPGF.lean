-- Prove2me | Definitions.Def_actuarial_cxBernCountPGF
-- name    : actuarial_cxBernCountPGF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:52:13.441895+00:00
-- url     : https://prove2.me/theorems/4d452734-0be6-41df-8977-ecae575470f7
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxBernCountPGF
-- statement:
--   Count generating function for at most one claim. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_N(z)=p_0+p_1 z
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cxBernCountPGF (p0 p1 z : ℝ) : ℝ := p0+p1*z

end ActuarialValuation


