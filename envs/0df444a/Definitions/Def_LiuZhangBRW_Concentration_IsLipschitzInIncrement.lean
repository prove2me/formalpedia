-- Prove2me | Definitions.Def_LiuZhangBRW_Concentration_IsLipschitzInIncrement
-- name    : LiuZhangBRW_Concentration_IsLipschitzInIncrement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:13.379464+00:00
-- url     : https://prove2.me/theorems/813eb67d-c2b9-4065-8f0f-547fe7d11ba8
-- title:
--   The L-Lipschitz condition (5.5): $|\mathbb E_{i-1}(X_\ell\mid X_i)-\mathbb E_{i-1}(X_\ell\mid X_i')|\le\kappa|X_i-X_i'|$
-- statement:
--   Let $1\le i<\ell$ and $\kappa\ge 0$ (the paper takes $\kappa=L/N$). Let $X_i'$ be a conditionally independent copy of $X_i$ given $(X_1,\dots,X_{i-1})$, that is, $X_i'\sim\mathcal L(X_i\mid X_1,\dots,X_{i-1})$. The **L-Lipschitz condition** of the paper is
--   $$
--   \bigl|\mathbb E_{i-1}(X_\ell\mid X_i)-\mathbb E_{i-1}(X_\ell\mid X_i')\bigr|\le \kappa\,|X_i-X_i'| .
--   $$
--   Precisely: there is a jointly measurable $g(p,x)$, with $p=(X_1,\dots,X_{i-1})$ the past and $x$ the value of $X_i$, such that
--
--   1. $\mathbb E_i X_\ell=g(X_1,\dots,X_{i-1},X_i)$ almost surely, so $g(p,x)$ is $\mathbb E_{i-1}(X_\ell\mid X_i=x)$ at the past $p$; and
--   2. for almost every past $p$, the inequality $|g(p,x)-g(p,x')|\le\kappa|x-x'|$ holds for almost every pair $(x,x')$ drawn independently from the conditional law $\nu_p$ of $X_i$ given $p$.
--
--   The condition replaces independence and the martingale-difference property: both imply it with $\kappa=0$. It says that the drift of the future increments depends on the current increment in a Lipschitz way.
--
--   **Formalization Note** The bound is required almost surely under the coupling of $X_i$ with its conditionally independent copy, which is how the proof of Lemma 5.2 uses it, and not for every $x,x'$ of one fixed version of $g$. The conditional law $\nu_p$ is Mathlib's `condDistrib`. Clause 1 ties $g$ to the conditional expectation, so the existential is not vacuous.
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), (5.5) p. 9, (5.7) p. 10, (6.9) p. 24; the conditionally independent copy X′_i, proof of Lemma 5.2, p. 9

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_natF

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- The L-Lipschitz condition of Lemma 5.2 (Liu, Zhang, *Concentration Inequalities for
Branching Random Walks with Applications to Phase Transitions in CSPs*, arXiv:1601.04794,
artifact sha256 7499631b…bdcb, (5.5) p. 9, (5.7) p. 10, (6.9) p. 24), with constant `κ`
(the paper's `κ = L/N`):
`|E_{i−1}(X_ℓ | X_i) − E_{i−1}(X_ℓ | X′_i)| ≤ κ |X_i − X′_i|`, where `X′_i` is a conditionally
independent copy of `X_i` given `(X_1, …, X_{i−1})`, `X′_i ∼ 𝓛(X_i | X_1, …, X_{i−1})` (p. 9).

`IsLipschitzInIncrement μ X i ℓ κ` says: there is a jointly measurable `g(p, x)`, with `p` the
past `(X_1, …, X_{i−1})` and `x` the value of `X_i`, such that
1. `E_i X_ℓ = g(X_1, …, X_{i−1}, X_i)` almost surely (so `g(p, x)` is `E_{i−1}(X_ℓ | X_i = x)`
   at the past `p`), and
2. for almost every past `p` (under the law of `(X_1, …, X_{i−1})`), the bound
   `|g(p, x) − g(p, x′)| ≤ κ |x − x′|` holds for almost every pair `(x, x′)` drawn independently
   from the conditional law of `X_i` given the past `p`.

**Formalization Note** This is the paper's condition read almost surely under the coupling of
`X_i` with its conditionally independent copy, which is how the proof of Lemma 5.2 (pp. 9–10)
uses it; it is not required for every `x, x′` of one fixed version `g`, which would be a stronger
hypothesis. Any two versions of `g` agree almost surely under that coupling, so the
existential is no loophole: `g` is tied to the conditional expectation by clause 1. The
conditional law is Mathlib's `condDistrib`. It is meaningful for `1 ≤ i`; `i - 1` is
natural-number subtraction. -/
def IsLipschitzInIncrement {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (i ℓ : ℕ) (κ : ℝ) : Prop :=
  ∃ g : (Fin (i - 1) → ℝ) → ℝ → ℝ, Measurable (Function.uncurry g) ∧
    condExp (natF X i) μ (X ℓ) =ᵐ[μ] (fun ω => g (pastVec X (i - 1) ω) (X i ω)) ∧
    ∀ᵐ p ∂(μ.map (pastVec X (i - 1))),
      ∀ᵐ q ∂((ProbabilityTheory.condDistrib (X i) (pastVec X (i - 1)) μ p).prod
              (ProbabilityTheory.condDistrib (X i) (pastVec X (i - 1)) μ p)),
        |g p q.1 - g p q.2| ≤ κ * |q.1 - q.2|

end LiuZhangBRW.Concentration


