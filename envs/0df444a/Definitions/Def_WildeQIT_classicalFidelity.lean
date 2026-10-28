-- Prove2me | Definitions.Def_WildeQIT_classicalFidelity
-- name    : WildeQIT_classicalFidelity
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T06:40:24.863715+00:00
-- url     : https://prove2.me/theorems/5c44ec1c-7d80-4659-a5df-e60ad0afe1c1
-- title:
--   Classical fidelity $F(p,q) = [\sum_x \sqrt{p(x) q(x)}]^2$
-- statement:
--   **Definition 9.2.4 (Classical Fidelity).** Let $p$ and $q$ be probability distributions defined over a finite alphabet $\mathcal{X}$. The classical fidelity $F(p, q)$ is
--
--   $$
--   F(p, q) \equiv \left[ \sum_{x \in \mathcal{X}} \sqrt{p(x)\, q(x)} \right]^2 ,
--   $$
--
--   the squared Bhattacharyya overlap. It is the special case of the quantum fidelity for commuting states (Exercise 9.2.11) and the quantity minimized over measurements in Theorem 9.2.2.
--
--   **Formalization Note.** `WildeQIT.classicalFidelity p q = (∑ x, Real.sqrt (p x * q x)) ^ 2` for `p q : X → ℝ`; hypotheses that $p, q$ are probability distributions are added by the theorems that use it.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.2.5 "A Measurement Achieves the Fidelity", Definition 9.2.4 (Classical Fidelity).

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.2.5, Definition 9.2.4 (Classical Fidelity).

Let `p` and `q` be probability distributions defined over a finite alphabet `𝒳`. The classical
fidelity is `F(p, q) ≡ [∑ₓ √(p(x) q(x))]²` (the squared Bhattacharyya overlap).
-/

namespace WildeQIT

/-- **Definition 9.2.4 (Classical Fidelity).** `classicalFidelity p q = (∑ₓ √(p(x) q(x)))²`
for `p q : X → ℝ` on a finite alphabet `X`. -/
noncomputable def classicalFidelity {X : Type} [Fintype X] (p q : X → ℝ) : ℝ :=
  (∑ x, Real.sqrt (p x * q x)) ^ 2

end WildeQIT


