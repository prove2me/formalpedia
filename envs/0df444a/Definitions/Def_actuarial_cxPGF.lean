-- Prove2me | Definitions.Def_actuarial_cxPGF
-- name    : actuarial_cxPGF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:50:55.935668+00:00
-- url     : https://prove2.me/theorems/6960a2ed-d7f3-4b5a-832d-b2db65c5047f
-- title:
--   Finite count, severity and convolution transforms: cxPGF
-- statement:
--   Finite polynomial probability generating transform, whose horizon is an exclusive upper bound on claim-size categories. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G(z)=Σ_{k<n}p_k z^k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cxPGF (mass : ℕ → ℝ) (n : ℕ) (z : ℝ) : ℝ := ∑ k ∈ Finset.range n, mass k * z^k

end ActuarialValuation


