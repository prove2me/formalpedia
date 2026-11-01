-- Prove2me | Definitions.Def_RelaxRoundPoA_IsObliviousRounding
-- name    : RelaxRoundPoA_IsObliviousRounding
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:16.342727+00:00
-- url     : https://prove2.me/theorems/a05db312-e2c3-41a9-b87d-882708f0b7e1
-- title:
--   $\alpha$-approximate oblivious rounding scheme
-- statement:
--   Let $\Omega\subseteq\Omega'$ be the original outcomes inside the relaxed outcome space. A randomized rounding scheme maps a relaxed solution $x'\in\Omega'$ to a random outcome $x$ with law $R(x')$. It is an **$\alpha$-approximate oblivious rounding scheme** if
--
--   1. $\alpha\ge1$;
--   2. $R(x')$ is a probability measure for every $x'$, depending measurably on $x'$;
--   3. for every $x'$ the rounded outcome lies in $\Omega$ almost surely;
--   4. for every $x'$, every agent $i$ and every weight $w\in\mathcal V_i$,
--
--   $$
--   w(x')\le\alpha\cdot\mathbf E_{x\sim R(x')}\bigl[w(x)\bigr].
--   $$
--
--   The rounding is **oblivious**: one scheme $R$ serves all weights, and it sees the relaxed solution $x'$ only, never the objective. Combined with an exact relaxed solver it is an $\alpha$-approximation algorithm.
--
--   **Formalization Note** The guarantee is required for each agent's weight separately, as on p.3 ("each agent is guaranteed"), which is how the proof of Theorem 3′ uses it. The expectation is a lower Lebesgue integral in $[0,\infty]$, defined for every nonnegative function.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §2, p.6; §1.1.1, p.3

import Mathlib

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RelaxRoundPoA

/-- **α-approximate oblivious rounding scheme.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §2, p.6: "A rounding algorithm is oblivious if it
does not require knowledge of the actual objective function `w`, beyond the fact that `x'` was
optimized with respect to `w`. Formally, a rounding scheme is an α-approximate oblivious rounding
scheme if, given some relaxed solution `x'`, it computes a solution `x` such that for all `w`,
`E[w(x)] ≥ (1/α) w(x')`." With p.3: `α ≥ 1`, and "for all possible valuation profiles each agent is
guaranteed to get, in expectation, a `1/α`-fraction of the value that it would have had for the
solution to the relaxed problem."

`IsObliviousRounding Val Ω α R`, for a kernel `R` from the relaxed outcome space `Ω'` to itself,
says:
1. `1 ≤ α`;
2. `R` is a Markov kernel: `R x'` is a probability measure, the law of the rounded solution `x`;
3. for every relaxed solution `x'`, the rounded solution lies in `Ω` almost surely;
4. for every `x'`, every agent `i` and every weight `w ∈ Val i`, `w(x') ≤ α · E_{x∼R x'}[w(x)]`.

**Formalization Note** `R` is a single kernel fixed before any weight and its argument is `x'` alone,
which is what "oblivious" means. The guarantee is per agent (p.3), which the proof of Theorem 3′
uses (p.9). The expectation is a `lintegral` in `ℝ≥0∞`, meaningful for every nonnegative function;
for a non-measurable `w` it is the lower integral. -/
def IsObliviousRounding {N : Type*} {Ω' : Type*} [MeasurableSpace Ω'] (Val : N → Set (Ω' → ℝ≥0))
    (Ω : Set Ω') (α : ℝ) (R : Kernel Ω' Ω') : Prop :=
  1 ≤ α ∧ IsMarkovKernel R ∧ (∀ x', ∀ᵐ x ∂(R x'), x ∈ Ω) ∧
    ∀ x' i, ∀ w ∈ Val i, (w x' : ℝ≥0∞) ≤ ENNReal.ofReal α * ∫⁻ x, (w x : ℝ≥0∞) ∂(R x')

end RelaxRoundPoA


