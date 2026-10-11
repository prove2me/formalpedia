-- Prove2me | Definitions.Def_actuarial_cxPanjerB
-- name    : actuarial_cxPanjerB
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:52:45.082046+00:00
-- url     : https://prove2.me/theorems/5d97a949-a032-48ed-b64f-2e6773c298d7
-- title:
--   Panjer adjustment with mass at zero: cxPanjerB
-- statement:
--   Companion Bernoulli Panjer recurrence coefficient. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   b=2p_1/p_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cxPanjerB (p0 p1 : ℝ) : ℝ := 2*p1/p0

end ActuarialValuation


