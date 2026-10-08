-- Prove2me | Definitions.Def_BellmanDP_ContGoldMining_Switching
-- name    : BellmanDP_ContGoldMining_Switching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T17:15:34.553137+00:00
-- url     : https://prove2.me/theorems/76f5c5f8-5e2f-4f49-b3c0-6efe4ef10169
-- title:
--   Switching functions $K_i$, the lines $C_1, C_2, C_3$, the quantity $D$, and optimal controls
-- statement:
--   This file adds the objects of §§ 12–14 of Chapter VIII of Bellman's *Dynamic Programming* to the continuous gold-mining process (controls $\varphi$, states $x(t), y(t)$, survival probability $p(t)$, gold rate $f'(t)$, returns $f(T)$ and $f(\infty)$).
--
--   1. The rate of the survival probability, $p'(t) = -p(t)\,[\varphi_1(t) q_1 + \varphi_2(t) q_2 + \varphi_3(t) q_3]$.
--   2. For a horizon $T$, the **switching functions** of Eq. (12.5), computed along a control $\varphi$:
--   $$\begin{aligned} K_1(t) &= -q_1 \int_t^T f'(s)\,ds + r_1 p(T) x(T) - r_1 \int_t^T p'(s) x(s)\,ds,\\ K_2(t) &= -q_2 \int_t^T f'(s)\,ds + r_2 p(T) y(T) - r_2 \int_t^T p'(s) y(s)\,ds,\\ K_3(t) &= -q_3 \int_t^T f'(s)\,ds + p(T)[r_3 x(T) + r_4 y(T)] - \int_t^T p'(s)[r_3 x(s) + r_4 y(s)]\,ds. \end{aligned}$$
--   3. The linear forms of Eq. (13.2) and the quantity of Eq. (13.3):
--   $$C_1 = q_1 r_2 y - q_2 r_1 x,\qquad C_2 = q_1 r_4 y - (q_3 r_1 - q_1 r_3) x,\qquad C_3 = (q_3 r_2 - q_2 r_4) y - q_2 r_3 x,$$
--   $$D = q_1 r_2 r_3 + q_2 r_1 r_4 - q_3 r_1 r_2.$$
--   3′. For $T = \infty$ (the case § 12 considers) the switching functions are Eq. (12.5) with $T = \infty$, the boundary terms $p(T)[\dots]$ tending to $0$:
--   $$K_i(t) = -q_i \int_t^\infty f'(s)\,ds - \int_t^\infty p'(s)\,[a_i x(s) + b_i y(s)]\,ds.$$
--   4. A control is **optimal for the horizon $T$** if it is admissible and its $f(T)$ is at least $f(T)$ of every admissible control; it is **optimal for $T = \infty$** if the same holds for $f(\infty)$.
--
--   The switching functions are the first variation of $f(T)$: perturbing $\varphi_i$ by $\varepsilon \beta_i$ with $\sum_i \beta_i = 0$ changes $f(T)$ by $\varepsilon \int_0^T \sum_i K_i \beta_i\,dt + o(\varepsilon)$ (Eq. (12.4)), which is why the lemmas of § 13 compare them.
--
--   **Formalization Note** Decisions are indexed `0, 1, 2` for $A, B, C$, so `switchingFn … i` is $K_{i+1}$. One formula covers the three switching functions: $K_i(t) = -q_i\int_t^T f' + p(T)[a_i x(T) + b_i y(T)] - \int_t^T p'(s)[a_i x(s) + b_i y(s)]\,ds$ with $(a_i, b_i) = (r_1, 0), (0, r_2), (r_3, r_4)$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 12, Eq. (12.5), p. 234; § 13, Eqs. (13.2)-(13.3), pp. 234-235; § 8, Eq. (8.6), p. 229

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- The rate `p′(t) = −p(t) [φ₁ q₁ + φ₂ q₂ + φ₃ q₃]` of the survival probability
(third line of Eqs. (7.2), (12.1)). -/
noncomputable def survivalRate (P : Params) (φ : Control) (t : ℝ) : ℝ :=
  -(survival P φ t * ∑ i, P.q i * φ i t)

/-- Ch. VIII, § 12, Eq. (12.5), p. 234 (and Eq. (8.6), p. 229): the switching function of
decision `i` for horizon `T`, computed along the control `φ`,
`K_i(t) = −q_i ∫ₜᵀ f′(s) ds + p(T) [a_i x(T) + b_i y(T)] − ∫ₜᵀ p′(s) [a_i x(s) + b_i y(s)] ds`,
where `(a_i, b_i) = (r₁, 0), (0, r₂), (r₃, r₄)` for `A, B, C`. -/
noncomputable def switchingFn (P : Params) (x₀ y₀ : ℝ) (φ : Control) (T : ℝ) (i : Fin 3)
    (t : ℝ) : ℝ :=
  -(P.q i * ∫ s in t..T, goldRate P x₀ y₀ φ s)
    + survival P φ T * (P.a i * stateX P x₀ φ T + P.b i * stateY P y₀ φ T)
    - ∫ s in t..T, survivalRate P φ s * (P.a i * stateX P x₀ φ s + P.b i * stateY P y₀ φ s)

/-- The switching function of decision `i` for the horizon `T = ∞` (the case § 12 considers,
p. 233), i.e. Eq. (12.5) with `T = ∞`, where the boundary term `p(T) [a_i x(T) + b_i y(T)]`
tends to `0`:
`K_i(t) = −q_i ∫ₜ^∞ f′(s) ds − ∫ₜ^∞ p′(s) [a_i x(s) + b_i y(s)] ds`. -/
noncomputable def switchingFnInfty (P : Params) (x₀ y₀ : ℝ) (φ : Control) (i : Fin 3)
    (t : ℝ) : ℝ :=
  -(P.q i * ∫ s in Set.Ioi t, goldRate P x₀ y₀ φ s)
    - ∫ s in Set.Ioi t, survivalRate P φ s * (P.a i * stateX P x₀ φ s + P.b i * stateY P y₀ φ s)

/-- Ch. VIII, § 13, Eq. (13.2), p. 234: `C₁ = q₁ r₂ y − q₂ r₁ x`. -/
def C₁ (P : Params) (x y : ℝ) : ℝ := P.q₁ * P.r₂ * y - P.q₂ * P.r₁ * x

/-- Eq. (13.2): `C₂ = q₁ r₄ y − (q₃ r₁ − q₁ r₃) x`. -/
def C₂ (P : Params) (x y : ℝ) : ℝ := P.q₁ * P.r₄ * y - (P.q₃ * P.r₁ - P.q₁ * P.r₃) * x

/-- Eq. (13.2): `C₃ = (q₃ r₂ − q₂ r₄) y − q₂ r₃ x`. -/
def C₃ (P : Params) (x y : ℝ) : ℝ := (P.q₃ * P.r₂ - P.q₂ * P.r₄) * y - P.q₂ * P.r₃ * x

/-- Ch. VIII, § 13, Eq. (13.3), p. 235: `D = q₁ r₂ r₃ + q₂ r₁ r₄ − q₃ r₁ r₂`. -/
def D (P : Params) : ℝ := P.q₁ * P.r₂ * P.r₃ + P.q₂ * P.r₁ * P.r₄ - P.q₃ * P.r₁ * P.r₂

/-- `φ` is an optimal control of the three-choice process for the horizon `T`: it is admissible
and `f(T)` under `φ` is at least `f(T)` under every admissible control. -/
def IsOptimalOn (P : Params) (x₀ y₀ T : ℝ) (φ : Control) : Prop :=
  Admissible φ ∧ ∀ ψ : Control, Admissible ψ → gold P x₀ y₀ ψ T ≤ gold P x₀ y₀ φ T

/-- `φ` is an optimal control of the three-choice process for `T = ∞`: it is admissible and
`f(∞)` under `φ` is at least `f(∞)` under every admissible control. -/
def IsOptimalInfty (P : Params) (x₀ y₀ : ℝ) (φ : Control) : Prop :=
  Admissible φ ∧ ∀ ψ : Control, Admissible ψ → goldInfty P x₀ y₀ ψ ≤ goldInfty P x₀ y₀ φ

end BellmanDP.ContGoldMining


