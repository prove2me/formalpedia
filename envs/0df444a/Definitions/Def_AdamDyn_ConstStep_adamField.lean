-- Prove2me | Definitions.Def_AdamDyn_ConstStep_adamField
-- name    : AdamDyn_ConstStep_adamField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:56.228844+00:00
-- url     : https://prove2.me/theorems/6ce65dff-b7cd-45d6-aafb-53819eeb0819
-- title:
--   The continuous-time Adam vector field $h(t,z)$ (3.3), the Euclidean norm of $\mathcal Z$, and solutions of $(\mathrm{ODE}_\eta)$
-- statement:
--   Fix $d$ and write $\mathcal Z := \mathbb R^d\times\mathbb R^d\times\mathbb R^d$, with points $z=(x,m,v)$, and $\mathcal Z_+ := \mathbb R^d\times\mathbb R^d\times[0,+\infty)^d$. The norm $\|z\|$ of a point of $\mathcal Z$ is the Euclidean norm of $\mathbb R^{3d}$, $\|z\| = (\|x\|^2+\|m\|^2+\|v\|^2)^{1/2}$.
--
--   Let $a,b,\varepsilon$ be real constants (positive in every theorem), let $F:\mathbb R^d\to\mathbb R$ have gradient $\nabla F$, and let $S:\mathbb R^d\to\mathbb R^d$. The **continuous-time Adam vector field** (declared in the imported module of the Adam field, `AdamDyn.WellPosed.adamField`) is, for $t>0$ and $z=(x,m,v)$,
--
--   $$
--   h(t,z) = \left( -\frac{(1-e^{-at})^{-1}\, m}{\varepsilon + \sqrt{(1-e^{-bt})^{-1}\,|v|}},\; a(\nabla F(x)-m),\; b(S(x)-|v|) \right),
--   $$
--
--   where the first block, the absolute value and the square root act coordinatewise. On $\mathcal Z_+$ this is the field (3.3) of the paper; off $\mathcal Z_+$ it is the paper's extension $h(t,(x,m,v)) := h(t,(x,m,|v|))$.
--
--   For $\eta\ge 0$ and $T\in(0,+\infty]$, a map $z$ is a **solution to $(\mathrm{ODE}_\eta)$, $\dot z(t) = h(t+\eta,z(t))$, on $[0,T)$ with initial condition $z_0$** if $z$ is continuous on $[0,T)$, continuously differentiable on $(0,T)$, satisfies the equation at every $t\in(0,T)$ and $z(0)=z_0$; the set of such maps is $Z^\eta_T(z_0)$. A **global solution to $(\mathrm{ODE})$ with initial condition $(x_0,0,0)$** is a solution of $(\mathrm{ODE}_0)$ on $[0,+\infty)$ with that initial condition and values in $\mathcal Z_+$.
--
--   These objects describe the deterministic limit of the Adam iterates as the step size tends to zero.
--
--   **Formalization Note** Maps are functions $\mathbb R\to\mathcal Z$ whose values at negative times are irrelevant; the equation is only imposed at $t>0$, where $h$ is defined. $\mathcal Z$ is the Lean product `E d × E d × E d` with `E d = EuclideanSpace ℝ (Fin d)`; because Lean's norm on a product is the max norm, the Euclidean norm of $\mathcal Z$ is the separate function `zNorm`. $F$ and $S$ are arbitrary here; the stochastic statements instantiate them by (2.2). The debiasing map $\bar e$ (p. 13) used by the stochastic statements is `AdamDyn.ODEConv.ebar`.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 5, Eq. (3.3) and the definition of global solution; p. 12, extension of h and the sets Z^η_T(z0)

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField
import Definitions.Def_AdamDyn_WellPosed_lyapunov

open Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

/-- The Euclidean space `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The space `𝒵 = ℝ^d × ℝ^d × ℝ^d`; a point is `z = (x, m, v)`. -/
abbrev Z (d : ℕ) := E d × E d × E d

/-- `z = (x, m, v) ∈ 𝒵₊ = ℝ^d × ℝ^d × [0, +∞)^d`. -/
def InZplus {d : ℕ} (z : Z d) : Prop := ∀ i, 0 ≤ z.2.2 i

/-- The Euclidean norm of `𝒵` viewed as `ℝ^{3d}` (Mathlib's norm on a product is the max norm,
so the paper's `‖z‖` is written out explicitly). -/
noncomputable def zNorm {d : ℕ} (z : Z d) : ℝ :=
  Real.sqrt (‖z.1‖ ^ 2 + ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2)

/-- The interval `[0, T)` for `T ∈ (0, +∞]` (with `T = ⊤` it is `[0, +∞)`). -/
def Ico0 (T : ℝ≥0∞) : Set ℝ := {t | 0 ≤ t ∧ ENNReal.ofReal t < T}

/-- `z` is a solution to `(ODE_η)  ż(t) = h(t + η, z(t))` on `[0, T)` with initial condition
`z0`, p. 12: `z` is continuous on `[0, T)`, continuously differentiable on `(0, T)`, the equation
holds at every `t ∈ (0, T)`, and `z(0) = z0`. The set of such maps is `Z^η_T(z0)`. Values of `z`
outside `[0, T)` are irrelevant. -/
def IsSolutionOn {d : ℕ} (a b ε : ℝ) (F : E d → ℝ) (S : E d → E d) (η : ℝ) (T : ℝ≥0∞)
    (z0 : Z d) (z : ℝ → Z d) : Prop :=
  ContinuousOn z (Ico0 T) ∧
  ContDiffOn ℝ 1 z {t | 0 < t ∧ ENNReal.ofReal t < T} ∧
  (∀ t : ℝ, 0 < t → ENNReal.ofReal t < T → HasDerivAt z (AdamDyn.WellPosed.adamField a b ε F S (t + η) (z t)) t) ∧
  z 0 = z0

/-- A global solution to `(ODE)` with initial condition `(x0, 0, 0)`, p. 5: a continuous map
`z : [0, +∞) → 𝒵₊`, continuously differentiable on `(0, +∞)`, with `ż(t) = h(t, z(t))` for all
`t > 0` and `z(0) = (x0, 0, 0)`. -/
def IsGlobalSolution {d : ℕ} (a b ε : ℝ) (F : E d → ℝ) (S : E d → E d) (x0 : E d)
    (z : ℝ → Z d) : Prop :=
  IsSolutionOn a b ε F S 0 ⊤ (x0, 0, 0) z ∧ ∀ t : ℝ, 0 ≤ t → InZplus (z t)

end AdamDyn.ConstStep


