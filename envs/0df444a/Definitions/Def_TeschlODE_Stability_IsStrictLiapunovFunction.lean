-- Prove2me | Definitions.Def_TeschlODE_Stability_IsStrictLiapunovFunction
-- name    : TeschlODE_Stability_IsStrictLiapunovFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:40:29.780747+00:00
-- url     : https://prove2.me/theorems/852729e1-b48b-4681-8f5b-9b1f29bcb375
-- title:
--   Strict Liapunov function (equality in (6.36) never occurs)
-- statement:
--   A Liapunov function $L$ at $x_0$ on $U$ (in the sense of (6.35)–(6.36)) is **strict** if equality in (6.36) never occurs: for every integral curve $\varphi$ of $\dot x = f(x)$ in $M$ on an open interval $J$,
--   $$L(\varphi(t_0)) > L(\varphi(t_1)) \quad\text{whenever } t_0 < t_1,\ t_0, t_1 \in J,\ \varphi(t_0), \varphi(t_1) \in U \setminus \{x_0\}.$$
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 201, §6.6, definition of strict Liapunov function

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction

namespace TeschlODE.Stability

/-- Teschl, §6.6, p. 201: a strict Liapunov function is a Liapunov function for which
equality in (6.36) never occurs: for every solution `φ` on an open interval `J` and all
`t₀ < t₁` in `J` with `φ t₀, φ t₁ ∈ U \ {x₀}` we have `L (φ t₁) < L (φ t₀)`. -/
def IsStrictLiapunovFunction {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsLiapunovFunction f M x₀ U L ∧
  ∀ (J : Set ℝ) (φ : ℝ → EuclideanSpace ℝ (Fin n)), IsIntegralCurve f M J φ →
    ∀ t₀ ∈ J, ∀ t₁ ∈ J, t₀ < t₁ → φ t₀ ∈ U \ {x₀} → φ t₁ ∈ U \ {x₀} →
      L (φ t₁) < L (φ t₀)

end TeschlODE.Stability


