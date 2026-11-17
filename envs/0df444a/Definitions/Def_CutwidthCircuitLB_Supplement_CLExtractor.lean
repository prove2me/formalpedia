-- Prove2me | Definitions.Def_CutwidthCircuitLB_Supplement_CLExtractor
-- name    : CutwidthCircuitLB_Supplement_CLExtractor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:13:12.641196+00:00
-- url     : https://prove2.me/theorems/4940e90a-b549-48b9-91ff-d3e48509418c
-- title:
--   The Chattopadhyay–Liao sumset-extractor property with constants $\kappa,\mu$ (Theorem 1.7)
-- statement:
--   Let $\kappa,\mu\in\mathbb R$ and let $H=(H_n)_{n\ge0}$ be a family of Boolean functions $H_n:\{0,1\}^n\to\{0,1\}$. The family has the **sumset-extractor property with constants $\kappa,\mu$** if for all sufficiently large $n$ and all sets $A,B\subseteq\{0,1\}^n$ with $|A|,|B|\ge 2^{(\log n)^\kappa}$,
--
--   $$
--   \Big|\Pr_{a\in A,\,b\in B}\big[H_n(a\oplus b)=1\big]-\frac12\Big|\le n^{-\mu},
--   $$
--
--   where $a\oplus b$ is the bitwise XOR and $a,b$ are drawn uniformly and independently from $A$ and $B$, i.e. the probability is $\frac{1}{|A||B|}\sum_{a\in A}\sum_{b\in B}[H_n(a\oplus b)=1]$.
--
--   This is the conclusion of the Chattopadhyay–Liao theorem (Theorem 1.7 of the paper, Theorem 1 of [CL22] restricted to the first output bit), which asserts that some uniformly polynomial-time computable family has the property for some $\kappa,\mu>0$. It is the hypothesis of the paper's average-case circuit lower bound, Theorem 5.4.
--
--   **Formalization Note** Logarithms are base 2, as everywhere in the paper; $2^{(\log n)^\kappa}$ and $n^{-\mu}$ are real powers. The threshold is at least $1$, so $A$ and $B$ are nonempty and the average is well defined. Positivity of $\kappa,\mu$ and polynomial-time computability of $H$ are not part of the property; they are separate hypotheses where it is used.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Theorem 1.7, p.5; logarithms base 2, p.6

import Mathlib

namespace CutwidthCircuitLB

namespace Supplement

/-- The **sumset-extractor property of Theorem 1.7** (Chattopadhyay–Liao [CL22]) with constants
`κ` and `μ` for a family `Hₙ : {0,1}ⁿ → {0,1}` (McGuire–Schlesinger–Williams, *Explicit functions
requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3),
Theorem 1.7, p.5): for all large `n` and all `A, B ⊆ {0,1}ⁿ` with `|A|, |B| ≥ 2^{(log n)^κ}`,
`| Pr_{a ∈ A, b ∈ B} [Hₙ(a ⊕ b) = 1] − 1/2 | ≤ n^{−μ}`, where `⊕` is bitwise XOR.

**Formalization Note** `log` is base 2 (p.6, "All logarithms are base 2"), `Real.logb 2`;
`2^{(log n)^κ}` and `n^{−μ}` are real powers. `Pr_{a ∈ A, b ∈ B}` is the uniform average over the
product `A × B`: `(1/(|A||B|)) ∑_{a ∈ A} ∑_{b ∈ B} [Hₙ(a ⊕ b) = 1]`, as in the published
`CutwidthCircuitLB.SumsetBalanced`. "For all large `n`" is `∃ N, ∀ n ≥ N`. The positivity of `κ`,
`μ` and the uniform polynomial-time computability of `Hₙ` are not part of this property; they are
separate hypotheses wherever the property is used. -/
def CLExtractor (κ μ : ℝ) (H : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ A B : Finset (Fin n → Bool),
    (2 : ℝ) ^ ((Real.logb 2 n) ^ κ) ≤ (A.card : ℝ) →
    (2 : ℝ) ^ ((Real.logb 2 n) ^ κ) ≤ (B.card : ℝ) →
      |1 / ((A.card : ℝ) * B.card) *
          ∑ a ∈ A, ∑ b ∈ B, (if H n (fun i => xor (a i) (b i)) then (1 : ℝ) else 0) - 1 / 2|
        ≤ (n : ℝ) ^ (-μ)

end Supplement

end CutwidthCircuitLB


