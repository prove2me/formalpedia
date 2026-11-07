-- Prove2me | Definitions.Def_CutwidthCircuitLB_SumsetBalanced
-- name    : CutwidthCircuitLB_SumsetBalanced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:27.050572+00:00
-- url     : https://prove2.me/theorems/5f4d8837-8726-4730-9370-ff1f8359c538
-- title:
--   The sumset property of Li's function with exponent $c$
-- statement:
--   A family $F_n : \{0,1\}^n \to \{0,1\}$ $(n \ge 0)$ has the **sumset property with exponent $c$** if for all sufficiently large $n$ and all $A, B \subseteq \{0,1\}^n$ with $|A|, |B| \ge n^c$,
--   $$
--   \frac38 \;\le\; \frac{1}{|A|\,|B|} \sum_{a \in A,\, b \in B} F_n(a \oplus b) \;\le\; \frac58 ,
--   $$
--   where $\oplus$ is bitwise XOR. Theorem 1.6 (Li) asserts a uniformly polynomial-time family with this property for some $c > 1$.
--
--   **Formalization Note** $n^c$ is the real power; $F_n(a \oplus b)$ is counted as $1$ or $0$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Theorem 1.6, p.4

import Mathlib

namespace CutwidthCircuitLB

/-- The **sumset property of Theorem 1.6** with exponent `c` for a family `Fₙ : {0,1}ⁿ → {0,1}`
(McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Theorem 1.6, p.4): for all large `n` and all `A, B ⊆ {0,1}ⁿ` with `|A|, |B| ≥ n^c`,
`3/8 ≤ (1/(|A||B|)) ∑_(a ∈ A, b ∈ B) Fₙ(a ⊕ b) ≤ 5/8`, where `⊕` is bitwise XOR.

**Formalization Note** `n^c` is the real power (`c : ℝ`); `Fₙ(a ⊕ b)` is counted as `1` or `0`.
"For all large `n`" is `∃ N, ∀ n ≥ N`. -/
def SumsetBalanced (c : ℝ) (F : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ A B : Finset (Fin n → Bool),
    (n : ℝ) ^ c ≤ (A.card : ℝ) → (n : ℝ) ^ c ≤ (B.card : ℝ) →
      (3 / 8 : ℝ) ≤ 1 / ((A.card : ℝ) * B.card) *
          ∑ a ∈ A, ∑ b ∈ B, (if F n (fun i => xor (a i) (b i)) then (1 : ℝ) else 0) ∧
        1 / ((A.card : ℝ) * B.card) *
          ∑ a ∈ A, ∑ b ∈ B, (if F n (fun i => xor (a i) (b i)) then (1 : ℝ) else 0) ≤ 5 / 8

end CutwidthCircuitLB


