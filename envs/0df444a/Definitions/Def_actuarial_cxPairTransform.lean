-- Prove2me | Definitions.Def_actuarial_cxPairTransform
-- name    : actuarial_cxPairTransform
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:51:20.051436+00:00
-- url     : https://prove2.me/theorems/bd49dfd0-c9c6-4709-b2ed-dbd24bd17ce3
-- title:
--   Finite count, severity and convolution transforms: cxPairTransform
-- statement:
--   Joint sum transform of two independent finite integer-valued claim severities, implemented by product probabilities. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E[z^{X+Y}]=Σ_iΣ_j f_ig_j z^{i+j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cxPairTransform (f g : ℕ → ℝ) (n m : ℕ) (z : ℝ) : ℝ := ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f i * g j * z^(i+j)

end ActuarialValuation


