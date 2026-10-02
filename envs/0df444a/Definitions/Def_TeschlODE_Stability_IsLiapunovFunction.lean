-- Prove2me | Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
-- name    : TeschlODE_Stability_IsLiapunovFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:32:53.492964+00:00
-- url     : https://prove2.me/theorems/b0b59c07-3a04-410d-8955-63295ca99935
-- title:
--   Liapunov function $L : U(x_0) \to \mathbb{R}$ (6.35)–(6.36)
-- statement:
--   Let $M \subseteq \mathbb{R}^n$, $f : \mathbb{R}^n \to \mathbb{R}^n$ and $x_0 \in \mathbb{R}^n$. A function $L$ is a **Liapunov function** at $x_0$ on the open neighborhood $U = U(x_0) \subseteq M$ if $U$ is open, $x_0 \in U$, $U \subseteq M$, $L$ is continuous on $U$, $L(x_0) = 0$, $L(x) > 0$ for $x \in U \setminus \{x_0\}$, and for **every** integral curve $\varphi$ of $\dot x = f(x)$ in $M$ on an open interval $J$,
--   $$L(\varphi(t_0)) \ge L(\varphi(t_1)) \quad\text{whenever } t_0 < t_1,\ t_0, t_1 \in J,\ \varphi(t_0), \varphi(t_1) \in U \setminus \{x_0\}. \qquad (6.36)$$
--
--   Only the two endpoint values are required to lie in $U \setminus \{x_0\}$, exactly as in (6.36); the curve may leave $U$ in between. $L$ is only continuous, not differentiable: the Lie-derivative criterion $\nabla L \cdot f \le 0$ (6.40) is a sufficient condition, not the definition. In the book $x_0$ is a fixed point; that is assumed in every theorem using this notion.
--
--   **Formalization Note.** $L$ is a total function $\mathbb{R}^n \to \mathbb{R}$ and only its values on $U$ are read. "Open neighborhood $U(x_0)$" is `IsOpen U ∧ x₀ ∈ U`; $U \subseteq M$ is the book's implicit convention that everything lives in the phase space $M$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), pp. 200–201, §6.6, Eqs. (6.35)–(6.36)

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve

namespace TeschlODE.Stability

/-- Teschl, §6.6, pp. 200–201, (6.35)–(6.36): `L` is a Liapunov function for `ẋ = f(x)` at
`x₀` on the open neighborhood `U` of `x₀` (with `U ⊆ M`): `L` is continuous on `U`, zero at
`x₀`, positive on `U \ {x₀}`, and for every solution `φ` (integral curve on an open interval
`J`) and all `t₀ < t₁` in `J` with `φ t₀, φ t₁ ∈ U \ {x₀}` we have `L (φ t₀) ≥ L (φ t₁)`.
Only the values of `L` on `U` matter. -/
def IsLiapunovFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsOpen U ∧ x₀ ∈ U ∧ U ⊆ M ∧ ContinuousOn L U ∧ L x₀ = 0 ∧
  (∀ x ∈ U, x ≠ x₀ → 0 < L x) ∧
  ∀ (J : Set ℝ) (φ : ℝ → EuclideanSpace ℝ (Fin n)), IsIntegralCurve f M J φ →
    ∀ t₀ ∈ J, ∀ t₁ ∈ J, t₀ < t₁ → φ t₀ ∈ U \ {x₀} → φ t₁ ∈ U \ {x₀} →
      L (φ t₁) ≤ L (φ t₀)

end TeschlODE.Stability


