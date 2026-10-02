-- Prove2me | Definitions.Def_TeschlODE_Stability_IsStable
-- name    : TeschlODE_Stability_IsStable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:57:22.002211+00:00
-- url     : https://prove2.me/theorems/8ef0c39d-2e3f-4e1c-935c-4c2ffeb17565
-- title:
--   (Liapunov) stable fixed point
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ and let $\Phi$ be a flow on $M$ with maximal intervals $I_x$. A point $x_0$ is **(Liapunov) stable** if for every neighborhood $U$ of $x_0$ there is a neighborhood $V \subseteq U$ of $x_0$, contained in $M$, such that for every $x \in V$ the solution $\Phi(\cdot, x)$ exists for all $t \ge 0$ and
--   $$\Phi(t, x) \in U \qquad \text{for all } t \ge 0 .$$
--
--   **Formalization Note.** The book's "any solution starting in $V(x_0)$ remains in $U(x_0)$ for all $t \ge 0$" is read as: the maximal solution exists on $[0, \infty)$ ($t \in I_x$ for every $t \ge 0$) and stays in $U$. By uniqueness (the flow is the maximal solution) "any solution" and "the maximal solution" agree. $V \subseteq M$ only removes points where the flow is undefined; since $M$ is open and $x_0 \in M$ this is no restriction on neighborhoods. The book applies the notion to fixed points; that is assumed in the theorems.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 198, §6.5, definition of (Liapunov) stable

import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.5, p. 198: the fixed point `x₀` is (Liapunov) stable for the flow `Φ` (with
maximal time intervals `I`) on `M`: for every neighborhood `U` of `x₀` there is a neighborhood
`V ⊆ U` of `x₀`, contained in `M`, such that the solution starting at any `x ∈ V` exists for all
`t ≥ 0` and remains in `U` for all `t ≥ 0`. -/
def IsStable {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ U ∈ nhds x₀, ∃ V ∈ nhds x₀, V ⊆ U ∧ V ⊆ M ∧
    ∀ x ∈ V, ∀ t : ℝ, 0 ≤ t → t ∈ I x ∧ Φ t x ∈ U

end TeschlODE.Stability


