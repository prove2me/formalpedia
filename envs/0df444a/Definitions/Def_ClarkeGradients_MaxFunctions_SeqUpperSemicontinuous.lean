-- Prove2me | Definitions.Def_ClarkeGradients_MaxFunctions_SeqUpperSemicontinuous
-- name    : ClarkeGradients_MaxFunctions_SeqUpperSemicontinuous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:41:07.402508+00:00
-- url     : https://prove2.me/theorems/d6f0c112-4263-41b9-b2ee-9cbc498e8555
-- title:
--   Upper semicontinuity of a multifunction (sequential closed graph)
-- statement:
--   Let $X$ be a topological space and $\Phi$ a multifunction assigning to each $x\in X$ a subset $\Phi(x)\subseteq\mathbb R^n$. Following Clarke, $\Phi$ is **upper semicontinuous** if for all sequences $x_i\to x$ in $X$ and $v_i\to v$ in $\mathbb R^n$,
--
--   $$
--   v_i\in\Phi(x_i)\ \text{for each } i\quad\Longrightarrow\quad v\in\Phi(x).
--   $$
--
--   The paper observes that $x\mapsto\partial f(x)$ has this property, and hypothesis (d) of Theorem (2.1) asks it of $(x,u)\mapsto\partial_x g(x,u)$ on $\mathbb R^n\times U$.
--
--   **Formalization Note** This is the paper's sequential closed-graph condition, not Mathlib's `UpperHemicontinuous` (an open-neighbourhood condition).
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 248, paragraph after Definition (1.1)

import Mathlib

open Filter Topology

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), p. 248: a multifunction `Φ` from `X` to the subsets of `ℝⁿ` is
*upper semicontinuous* if, whenever `xᵢ → x`, `vᵢ → v` and `vᵢ ∈ Φ(xᵢ)` for each `i`,
then `v ∈ Φ(x)` (a sequential closed-graph condition). -/
def SeqUpperSemicontinuous {X : Type*} [TopologicalSpace X] {n : ℕ}
    (Φ : X → Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ (xs : ℕ → X) (x : X) (vs : ℕ → EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n)),
    Tendsto xs atTop (𝓝 x) → Tendsto vs atTop (𝓝 v) → (∀ i, vs i ∈ Φ (xs i)) → v ∈ Φ x

end ClarkeGradients.MaxFunctions


