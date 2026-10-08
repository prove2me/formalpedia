-- Prove2me | Definitions.Def_AdamDyn_ODEConv_StrictLyapunov
-- name    : AdamDyn_ODEConv_StrictLyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:05:55.541982+00:00
-- url     : https://prove2.me/theorems/fb0e1119-cd3f-4c24-9fba-7943d2d59b01
-- title:
--   Equilibrium points, Lyapunov functions and strict Lyapunov functions of a semiflow
-- statement:
--   Let $(E, d)$ be a metric (or topological) space. A **semiflow** on $E$ is a continuous map $\Psi : [0,+\infty) \times E \to E$, $(t, z) \mapsto \Psi_t(z)$, such that $\Psi_0$ is the identity and $\Psi_{t+s} = \Psi_t \circ \Psi_s$ for all $t, s \ge 0$.
--
--   1. A point $z \in E$ is an **equilibrium point** of $\Psi$ if $\Psi_t(z) = z$ for all $t \ge 0$. The set of equilibrium points is denoted $\Lambda_\Psi$.
--   2. A continuous function $\mathsf V : E \to \mathbb R$ is a **Lyapunov function** for $\Psi$ if $\mathsf V(\Psi_t(z)) \le \mathsf V(z)$ for all $z \in E$ and all $t \ge 0$.
--   3. A Lyapunov function $\mathsf V$ is a **strict Lyapunov function** for $\Psi$ if, moreover,
--   $$\{ z \in E : \mathsf V(\Psi_t(z)) = \mathsf V(z) \ \text{for all } t \ge 0 \} = \Lambda_\Psi .$$
--
--   These are the notions used in the abstract limit-set theorem (Proposition 7.14) and in the construction of the strict Lyapunov function $W_\delta$ for the autonomous Adam system (Proposition 7.15).
--
--   **Formalization Note** A semiflow is Mathlib's `Flow ℝ≥0 E` (jointly continuous, `Φ 0 = id`, `Φ (t + s) = Φ t ∘ Φ s`). The strict notion only asks for non-increase along orbits together with the set equality; it is weaker than a "Lyapunov function for $\Lambda$" in Benaïm's sense, which requires strict decrease off $\Lambda$ at every positive time.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 17, §7.2.3 (semiflow) and §7.3.1 (equilibrium points, Lyapunov and strict Lyapunov functions)

import Mathlib

open scoped NNReal

namespace AdamDyn.ODEConv

/-- The set `Λ_Ψ` of *equilibrium points* of a semiflow `Ψ` on `E` (Barakat & Bianchi,
arXiv:1810.02263v4, §7.3.1, p. 17): the points `z` with `Ψ_t(z) = z` for all `t ≥ 0`.
A semiflow is Mathlib's `Flow ℝ≥0 E`: a jointly continuous `Ψ : [0,∞) × E → E` with
`Ψ_0 = id` and `Ψ_{t+s} = Ψ_t ∘ Ψ_s`. -/
def equilibria {E : Type*} [TopologicalSpace E] (Ψ : Flow ℝ≥0 E) : Set E :=
  {z | ∀ t : ℝ≥0, Ψ t z = z}

/-- A *Lyapunov function* for the semiflow `Ψ` (p. 17): a continuous `V : E → ℝ` with
`V(Ψ_t(z)) ≤ V(z)` for all `z ∈ E` and all `t ≥ 0`. -/
def IsLyapunovFunction {E : Type*} [TopologicalSpace E] (Ψ : Flow ℝ≥0 E) (V : E → ℝ) : Prop :=
  Continuous V ∧ ∀ z : E, ∀ t : ℝ≥0, V (Ψ t z) ≤ V z

/-- A *strict Lyapunov function* for the semiflow `Ψ` (p. 17): a Lyapunov function such that
moreover `{z ∈ E : ∀ t ≥ 0, V(Ψ_t(z)) = V(z)} = Λ_Ψ`. -/
def IsStrictLyapunovFunction {E : Type*} [TopologicalSpace E] (Ψ : Flow ℝ≥0 E) (V : E → ℝ) :
    Prop :=
  IsLyapunovFunction Ψ V ∧ {z : E | ∀ t : ℝ≥0, V (Ψ t z) = V z} = equilibria Ψ

end AdamDyn.ODEConv


