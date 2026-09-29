-- Prove2me | Definitions.Def_RockafellarMaxMono_Maximality_MonotoneOperator
-- name    : RockafellarMaxMono_Maximality_MonotoneOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:00:56.755133+00:00
-- url     : https://prove2.me/theorems/921b3fd2-135d-4e05-9a76-bb4ec775f087
-- title:
--   Monotone and maximal monotone operators $V \rightrightarrows V^*$
-- statement:
--   Let $V$ be a real normed space with dual $V^*$. A multivalued mapping $T : V \to V^*$ (a map assigning to each $x \in V$ a subset $T(x) \subseteq V^*$) is a **monotone operator** if
--
--   $$
--   \langle x_0 - x_1,\ x_0^* - x_1^* \rangle \ge 0 \quad \text{whenever } x_0^* \in T(x_0),\ x_1^* \in T(x_1).
--   $$
--
--   It is a **maximal monotone operator** if, in addition, its graph $G(T) = \{(x,x^*) \mid x^* \in T(x)\} \subseteq V \times V^*$ is not properly contained in the graph of any other monotone operator $T' : V \to V^*$.
--
--   Maximal monotone operators are the central objects of monotone operator theory; Rockafellar's Theorem A asserts that subdifferentials of lower semicontinuous proper convex functions belong to this class.
--
--   **Formalization Note** Multivalued maps are functions `V → Set (StrongDual ℝ V)`. Maximality is stated as graph inclusion, literally: `T` is monotone and every monotone `T'` with $T(x) \subseteq T'(x)$ for all $x$ satisfies $T'(x) = T(x)$ for all $x$. The comparison ranges over all monotone operators $T'$, not only subdifferentials.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 209, definitions of monotone and maximal monotone operators

import Mathlib

namespace RockafellarMaxMono.Maximality

/-- Rockafellar (1970), p. 209: a multivalued mapping `T : V → V*` (encoded as
`V → Set (StrongDual ℝ V)`) is a *monotone operator* if
`⟨x₀ − x₁, x₀* − x₁*⟩ ≥ 0` whenever `x₀* ∈ T(x₀)` and `x₁* ∈ T(x₁)`. -/
def IsMonotoneOp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  ∀ (x₀ x₁ : V) (x₀' x₁' : StrongDual ℝ V), x₀' ∈ T x₀ → x₁' ∈ T x₁ →
    0 ≤ (x₀' - x₁') (x₀ - x₁)

/-- Rockafellar (1970), p. 209: a monotone operator `T : V → V*` is *maximal monotone* if its
graph `G(T) = {(x, x*) | x* ∈ T(x)}` is not properly contained in the graph of any other
monotone operator `T' : V → V*`; equivalently, every monotone `T'` whose graph contains the
graph of `T` coincides with `T`. -/
def IsMaximalMonotone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  IsMonotoneOp T ∧
    ∀ T' : V → Set (StrongDual ℝ V), IsMonotoneOp T' → (∀ x, T x ⊆ T' x) → ∀ x, T' x = T x

end RockafellarMaxMono.Maximality


