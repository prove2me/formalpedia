-- Prove2me | Definitions.Def_ClarkeGradients_Shared_generalizedGradient
-- name    : ClarkeGradients_Shared_generalizedGradient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:39:57.502275+00:00
-- url     : https://prove2.me/theorems/1ff628de-1264-4838-9d37-374f43d93cde
-- title:
--   Definition (1.1) — the generalized gradient ∂f(x)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and $x\in\mathbb R^n$. Consider all vectors $\zeta$ that arise as limits
--
--   $$
--   \zeta=\lim_{i\to\infty}\nabla f(x+h_i),
--   $$
--
--   where $h_i\to 0$, $f$ is differentiable at every point $x+h_i$, and the gradients $\nabla f(x+h_i)$ converge. The **generalized gradient** of $f$ at $x$, written $\partial f(x)$, is the convex hull of the set of all such limits.
--
--   For a locally Lipschitz function the gradient exists almost everywhere and is bounded near $x$, so $\partial f(x)$ is a nonempty convex compact set; for a $C^1$ function it is $\{\nabla f(x)\}$, and for a convex function it is the subdifferential of convex analysis. It is the basic object of the paper.
--
--   It serves chunk 01-max-functions (Clarke p. 248, Definition (1.1); used in Proposition (1.4) p. 248, Corollary (1.10) p. 249 and Theorem (2.1) pp. 251–252) and chunk 02-flow-invariance (Clarke p. 248, Definition (1.1); used in Proposition (1.4) p. 248 and Corollary (2.5) p. 253, and applied to $d_E$ to define the normal cone, Definition (3.1) p. 254).
--
--   **Formalization Note** The auxiliary set `gradientLimits f x` collects the limits; `generalizedGradient f x` is its (plain, not closed) convex hull, as in the paper. The requirement that $f$ be differentiable at each $x+h_i$ is explicit: Mathlib's `gradient` returns $0$ at points of non-differentiability, and without the requirement $0$ would spuriously belong to $\partial f(x)$. The definition is stated for every $f$; the Lipschitz assumption is carried by the theorems.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 248, Definition (1.1)

import Mathlib

open Filter Topology

namespace ClarkeGradients.Shared

/-- The set of limits `lim ∇f(x + hᵢ)` of Clarke (1975), Definition (1.1): all `ζ` such that
for some sequence `hᵢ → 0`, `f` is differentiable at every `x + hᵢ` and `∇f(x + hᵢ) → ζ`. -/
def gradientLimits {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {ζ | ∃ h : ℕ → EuclideanSpace ℝ (Fin n), Tendsto h atTop (𝓝 0) ∧
    (∀ i, DifferentiableAt ℝ f (x + h i)) ∧
    Tendsto (fun i => gradient f (x + h i)) atTop (𝓝 ζ)}

/-- Clarke (1975), Definition (1.1): the *generalized gradient* `∂f(x)` is the convex hull of
the set of limits of the form `lim ∇f(x + hᵢ)`, where `hᵢ → 0`. -/
def generalizedGradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ (gradientLimits f x)

end ClarkeGradients.Shared


