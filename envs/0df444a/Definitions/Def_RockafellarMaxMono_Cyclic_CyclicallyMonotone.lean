-- Prove2me | Definitions.Def_RockafellarMaxMono_Cyclic_CyclicallyMonotone
-- name    : RockafellarMaxMono_Cyclic_CyclicallyMonotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:09:40.43306+00:00
-- url     : https://prove2.me/theorems/68c6ab04-3791-4498-8f50-5f52a84fee8a
-- title:
--   Cyclically monotone and maximal cyclically monotone operators $V \rightrightarrows V^*$
-- statement:
--   Let $V$ be a real normed space with dual $V^*$, and let $T : V \to V^*$ be a multivalued mapping, i.e. $T(x) \subseteq V^*$ for every $x \in V$. Then $T$ is a **cyclically monotone operator** if
--
--   $$
--   \langle x_0 - x_1, x_0^* \rangle + \cdots + \langle x_{n-1} - x_n, x_{n-1}^* \rangle + \langle x_n - x_0, x_n^* \rangle \ \ge\ 0
--   $$
--
--   whenever $x_i^* \in T(x_i)$, $i = 0, \dots, n$, for every $n$ and every choice of points $x_0, \dots, x_n \in V$. Each term pairs $x_i^*$ with $x_i - x_{i+1}$, and the last term closes the cycle.
--
--   $T$ is a **maximal cyclically monotone operator** if, in addition, its graph $G(T) = \{(x, x^*) \mid x^* \in T(x)\} \subset V \times V^*$ is not properly contained in the graph of any other cyclically monotone operator $T' : V \to V^*$.
--
--   With $n = 1$ the condition reduces to monotonicity, $\langle x_0 - x_1, x_0^* - x_1^* \rangle \ge 0$. Maximality here is among **cyclically monotone** operators, not among monotone ones. Theorem B states that these operators are exactly the subdifferentials of lower semicontinuous proper convex functions.
--
--   **Formalization Note** The paper leaves the range of $n$ implicit; the Lean statement quantifies over every $n \in \mathbb{N}$ (the case $n = 0$ is the trivial cycle $\langle x_0 - x_0, x_0^* \rangle = 0$). The points are indexed by `Fin (n + 1)`, whose addition wraps around, so the term for $i = n$ is $\langle x_n - x_0, x_n^* \rangle$. Maximality is written in the equivalent form: every cyclically monotone $T'$ with $T(x) \subseteq T'(x)$ for all $x$ satisfies $T' = T$. The Lean names are `IsCyclicallyMonotone` and `IsMaximalCyclicallyMonotone`.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 209, definitions of cyclically monotone and maximal cyclically monotone operators

import Mathlib

namespace RockafellarMaxMono.Cyclic

/-- Rockafellar (1970), p. 209: a multivalued mapping `T : V → V*` (encoded as
`V → Set (StrongDual ℝ V)`) is a *cyclically monotone operator* if
`⟨x₀ − x₁, x₀*⟩ + ⋯ + ⟨xₙ₋₁ − xₙ, xₙ₋₁*⟩ + ⟨xₙ − x₀, xₙ*⟩ ≥ 0` whenever `xᵢ* ∈ T(xᵢ)`,
`i = 0, …, n`. The points are indexed by `Fin (n + 1)`, whose addition wraps around, so the
term for `i = n` is `⟨xₙ − x₀, xₙ*⟩`; the pairing `⟨xᵢ − xᵢ₊₁, xᵢ*⟩` is `x' i (x i - x (i + 1))`. -/
def IsCyclicallyMonotone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  ∀ (n : ℕ) (x : Fin (n + 1) → V) (x' : Fin (n + 1) → StrongDual ℝ V),
    (∀ i, x' i ∈ T (x i)) → 0 ≤ ∑ i, x' i (x i - x (i + 1))

/-- Rockafellar (1970), p. 209: a cyclically monotone operator `T : V → V*` is *maximal
cyclically monotone* if its graph `G(T) = {(x, x*) | x* ∈ T(x)}` is not properly contained in
the graph of any other cyclically monotone operator `T' : V → V*`; equivalently, every
cyclically monotone `T'` whose graph contains the graph of `T` coincides with `T`. -/
def IsMaximalCyclicallyMonotone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  IsCyclicallyMonotone T ∧
    ∀ T' : V → Set (StrongDual ℝ V), IsCyclicallyMonotone T' → (∀ x, T x ⊆ T' x) →
      ∀ x, T' x = T x

end RockafellarMaxMono.Cyclic


