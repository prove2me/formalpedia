-- Prove2me | Definitions.Def_AdamDyn_WellPosed_adamField
-- name    : AdamDyn_WellPosed_adamField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:05:57.981862+00:00
-- url     : https://prove2.me/theorems/e4f637b7-498b-4abb-a74b-d9194d6d761d
-- title:
--   The continuous-time Adam vector field $h(t,z)$ (3.3), its limit $h_\infty$ (7.1), and the solution sets $Z^\eta_T(z_0)$
-- statement:
--   Fix an integer $d$, write $\mathbb R^d$ for the Euclidean space of dimension $d$, and let the state space be $\mathcal Z := \mathbb R^d \times \mathbb R^d \times \mathbb R^d$, whose points are written $z = (x, m, v)$. Set
--   $$\mathcal Z_+ := \mathbb R^d \times \mathbb R^d \times [0,+\infty)^d,\qquad \mathcal Z_+^* := \mathbb R^d \times \mathbb R^d \times (0,+\infty)^d,\qquad \mathcal Z_0 := \{(x,0,0) : x \in \mathbb R^d\}.$$
--
--   Let $a, b, \varepsilon$ be real constants, $F : \mathbb R^d \to \mathbb R$ a function with gradient $\nabla F$, and $S : \mathbb R^d \to \mathbb R^d$ a map. All operations on vectors below (products, quotients, square roots, absolute values) are coordinatewise. The **continuous-time Adam vector field** is, for $t > 0$ and $z = (x,m,v) \in \mathcal Z$,
--   $$h(t, z) = \left( -\frac{(1-e^{-at})^{-1}\, m}{\varepsilon + \sqrt{(1-e^{-bt})^{-1}\,|v|}},\ a(\nabla F(x) - m),\ b(S(x) - |v|) \right),$$
--   which is the field (3.3) of the paper on $\mathcal Z_+$, extended to all of $\mathcal Z$ by $h(t,(x,m,v)) := h(t,(x,m,|v|))$. Its limit as $t \to \infty$ is
--   $$h_\infty(x,m,v) = \left( -\frac{m}{\varepsilon + \sqrt{|v|}},\ a(\nabla F(x) - m),\ b(S(x) - |v|) \right),$$
--   extended to $\mathcal Z$ in the same way. For $\eta \in [0,+\infty]$, the equation $(\mathrm{ODE}_\eta)$ is $\dot z(t) = h(t+\eta, z(t))$ when $\eta$ is finite and $\dot z(t) = h_\infty(z(t))$ when $\eta = +\infty$; $\eta = 0$ is the Adam equation (ODE) $\dot z(t) = h(t, z(t))$.
--
--   For $T \in (0,+\infty]$ and $z_0 \in \mathcal Z_+$, a map $z$ is a **solution of $(\mathrm{ODE}_\eta)$ on $[0,T)$ with initial condition $z_0$** if it is continuous on $[0,T)$, continuously differentiable on $(0,T)$, satisfies $(\mathrm{ODE}_\eta)$ at every $t \in (0,T)$, and $z(0) = z_0$. The set of such solutions is $Z^\eta_T(z_0)$. Finally, a **global solution of (ODE) with initial condition $(x_0,0,0)$** is a map $z$ that is continuous on $[0,+\infty)$ with values in $\mathcal Z_+$, continuously differentiable on $(0,+\infty)$, satisfies $\dot z(t) = h(t, z(t))$ for every $t > 0$, and has $z(0) = (x_0, 0, 0)$.
--
--   These are the objects of the existence and uniqueness theory for the continuous-time limit of the Adam optimizer: the field is singular at $t = 0$ (the bias-correction factors blow up) and not Lipschitz in $v$ at $v = 0$, so standard ODE theorems do not apply directly.
--
--   **Formalization Note.** Vectors live in `EuclideanSpace ℝ (Fin d)` and states in its triple product (Lean's product norm is the max of the three Euclidean norms). The field is never used at $t \le 0$: the solution notions only require the equation for $t > 0$. Solutions are maps $\mathbb R \to \mathcal Z$ whose values outside $[0,T)$ are irrelevant; $\eta$ ranges over `WithTop ℝ≥0` (with $\top = +\infty$) and $T$ over `WithTop ℝ`. Solutions in $Z^\eta_T(z_0)$ are $\mathcal Z$-valued, as on p. 12 of the paper; a global solution (p. 5) is required to take values in $\mathcal Z_+$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 3 (𝒵, 𝒵₊, 𝒵₊*), p. 5 (Eq. (3.3), (ODE), global solution), pp. 11–12 ((ODE_η), (ODE_∞), Eq. (7.1), |v| extension, Z^η_T(z0)), p. 13 (𝒵₀)

import Mathlib

open scoped NNReal

namespace AdamDyn.WellPosed

/-- The parameter space `ℝ^d`, with its Euclidean structure. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The state space `𝒵 = ℝ^d × ℝ^d × ℝ^d`; a point is `z = (x, m, v)`. -/
abbrev State (d : ℕ) := Vec d × Vec d × Vec d

variable {d : ℕ}

/-- `𝒵₊ = ℝ^d × ℝ^d × [0, +∞)^d` (p. 3). -/
def Zplus : Set (State d) := {z | ∀ i, 0 ≤ z.2.2 i}

/-- `𝒵₊* = ℝ^d × ℝ^d × (0, +∞)^d` (p. 3). -/
def ZplusStar : Set (State d) := {z | ∀ i, 0 < z.2.2 i}

/-- `𝒵₀ = {(x, 0, 0) : x ∈ ℝ^d}` (p. 13). -/
def Zzero : Set (State d) := {z | z.2.1 = 0 ∧ z.2.2 = 0}

/-- The continuous-time Adam vector field `h(t, z)` of (3.3), for `t > 0`, extended to all of `𝒵`
by `h(t, (x, m, v)) := h(t, (x, m, |v|))` (p. 12):
`h(t, z) = ( −(1 − e^{−at})⁻¹ m / (ε + √((1 − e^{−bt})⁻¹ |v|)), a(∇F(x) − m), b(S(x) − |v|) )`,
the first and the absolute values coordinatewise. It is only ever evaluated at `t > 0`. -/
noncomputable def adamField (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d) (t : ℝ)
    (z : State d) : State d :=
  ( WithLp.toLp 2 (fun i => -((1 - Real.exp (-(a * t)))⁻¹ * z.2.1 i) /
        (ε + Real.sqrt ((1 - Real.exp (-(b * t)))⁻¹ * |z.2.2 i|))),
    a • (gradient F z.1 - z.2.1),
    b • (S z.1 - WithLp.toLp 2 (fun i => |z.2.2 i|)) )

/-- The limit field `h∞(z) = lim_{t→∞} h(t, z)` of (7.1), extended by `h∞(x, m, v) := h∞(x, m, |v|)`
(p. 12): `h∞(x, m, v) = ( −m / (ε + √|v|), a(∇F(x) − m), b(S(x) − |v|) )`. -/
noncomputable def adamFieldInf (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (z : State d) : State d :=
  ( WithLp.toLp 2 (fun i => -z.2.1 i / (ε + Real.sqrt |z.2.2 i|)),
    a • (gradient F z.1 - z.2.1),
    b • (S z.1 - WithLp.toLp 2 (fun i => |z.2.2 i|)) )

/-- The field of `(ODE_η)`, `η ∈ [0, +∞]` (p. 11): `ż(t) = h(t + η, z(t))` for finite `η`, and
`ż(t) = h∞(z(t))` for `η = +∞`. -/
noncomputable def fieldEta (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (η : WithTop ℝ≥0) (t : ℝ) (z : State d) : State d :=
  match η with
  | ⊤ => adamFieldInf a b ε F S z
  | (e : ℝ≥0) => adamField a b ε F S (t + (e : ℝ)) z

/-- The time interval `[0, T)` for `T ∈ (0, +∞]` (`T = ⊤` gives `[0, +∞)`). -/
def timeIco (T : WithTop ℝ) : Set ℝ := {t | 0 ≤ t ∧ (t : WithTop ℝ) < T}

/-- The time interval `(0, T)` for `T ∈ (0, +∞]` (`T = ⊤` gives `(0, +∞)`). -/
def timeIoo (T : WithTop ℝ) : Set ℝ := {t | 0 < t ∧ (t : WithTop ℝ) < T}

/-- `z ∈ Z^η_T(z0)` (p. 12): `z` is a solution of `(ODE_η)` on `[0, T)` with initial condition `z0`,
i.e. `z` is continuous on `[0, T)`, continuously differentiable on `(0, T)`, satisfies
`ż(t) = h(t + η, z(t))` (resp. `h∞(z(t))` if `η = +∞`) for every `t ∈ (0, T)`, and `z(0) = z0`.
Solutions are `𝒵`-valued; the values of `z` outside `[0, T)` play no role. -/
structure IsSolutionOn (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (η : WithTop ℝ≥0) (T : WithTop ℝ) (z0 : State d) (z : ℝ → State d) : Prop where
  continuousOn : ContinuousOn z (timeIco T)
  contDiffOn : ContDiffOn ℝ 1 z (timeIoo T)
  hasDerivAt : ∀ t ∈ timeIoo T, HasDerivAt z (fieldEta a b ε F S η t (z t)) t
  init : z 0 = z0

/-- Global solution of `(ODE)` with initial condition `(x0, 0, 0)` (p. 5): a map `z` continuous on
`[0, +∞)` with values in `𝒵₊` there, continuously differentiable on `(0, +∞)`, with
`ż(t) = h(t, z(t))` for all `t > 0`, and `z(0) = (x0, 0, 0)`. -/
structure IsGlobalSolution (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d) (x0 : Vec d)
    (z : ℝ → State d) : Prop where
  continuousOn : ContinuousOn z (Set.Ici 0)
  mem_Zplus : ∀ t, 0 ≤ t → z t ∈ Zplus
  contDiffOn : ContDiffOn ℝ 1 z (Set.Ioi 0)
  hasDerivAt : ∀ t, 0 < t → HasDerivAt z (adamField a b ε F S t (z t)) t
  init : z 0 = (x0, 0, 0)

end AdamDyn.WellPosed


