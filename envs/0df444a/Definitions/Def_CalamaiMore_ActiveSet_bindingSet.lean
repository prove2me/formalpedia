-- Prove2me | Definitions.Def_CalamaiMore_ActiveSet_bindingSet
-- name    : CalamaiMore_ActiveSet_bindingSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:52:55.093376+00:00
-- url     : https://prove2.me/theorems/df643c9c-1f4f-445c-9007-44ffa720ca48
-- title:
--   Binding constraints (4.4) and consistent multiplier estimates
-- statement:
--   Let $\Omega = \{x : \langle c_j, x \rangle \ge \delta_j,\ j = 1, \dots, m\}$ be polyhedral with active sets $A(x)$, let $f : E \to \mathbb{R}$, and let $\lambda(\cdot)$ be a **Lagrange multiplier estimate**, a map assigning to each $x$ a vector $\lambda(x) = (\lambda_1(x), \dots, \lambda_m(x))$.
--
--   1. The **set of binding constraints** at $x$ is
--   $$
--   B(x) = \{j : j \in A(x),\ \lambda_j(x) \ge 0\}.
--   $$
--   2. The estimate is **consistent** if, whenever a sequence $\{x_k\} \subseteq \Omega$ converges to a nondegenerate Kuhn–Tucker point $x^*$ with $A(x_k) = A(x^*)$ for every $k$, then $\lambda_j(x_k) \to \lambda_j(x^*)$ for every $j \in A(x^*)$.
--
--   The least-squares estimate, $\lambda(x)$ minimising $\|\nabla f(x) - \sum_{j \in A(x)} \lambda_j c_j\|$ over $\lambda_j \in \mathbb{R}$, is consistent when $\nabla f$ is continuous. Binding sets are the constraints an active-set method keeps when it decides which constraints to release.
--
--   **Formalization Note** The estimate is `lam : E → Fin m → ℝ`. Consistency is required only along sequences in $\Omega$ and only for the coordinates $j \in A(x^*)$ (the only ones that enter $B$); this is the weakest reading of the source's definition, so a theorem that assumes consistency is at least as strong as the source's.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 107, Eq. (4.4) and Definition (consistent multiplier estimate)

import Mathlib
import Definitions.Def_CalamaiMore_ActiveSet_IsNondegenerate

namespace CalamaiMore.ActiveSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open Classical in
/-- The set of binding constraints, Calamai–Moré Eq. (4.4):
`B(x) = {j : j ∈ A(x), λ_j(x) ≥ 0}`, for a Lagrange multiplier estimate `λ(·)`. -/
noncomputable def bindingSet {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (lam : E → Fin m → ℝ)
    (x : E) : Finset (Fin m) :=
  (activeSet c δ x).filter (fun j => 0 ≤ lam x j)

/-- A consistent Lagrange multiplier estimate (Calamai–Moré, Definition on p. 107): whenever a
sequence `{x_k}` in `Ω` converges to a nondegenerate Kuhn–Tucker point `x*` with
`A(x_k) = A(x*)` for every `k`, then `λ_j(x_k) → λ_j(x*)` for every `j ∈ A(x*)`. -/
def IsConsistentEstimate {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (f : E → ℝ)
    (lam : E → Fin m → ℝ) : Prop :=
  ∀ (y : ℕ → E) (xs : E), (∀ k, y k ∈ polyhedron c δ) → IsNondegenerate c δ f xs →
    Filter.Tendsto y Filter.atTop (nhds xs) →
    (∀ k, activeSet c δ (y k) = activeSet c δ xs) →
    ∀ j ∈ activeSet c δ xs, Filter.Tendsto (fun k => lam (y k) j) Filter.atTop (nhds (lam xs j))

end CalamaiMore.ActiveSet


