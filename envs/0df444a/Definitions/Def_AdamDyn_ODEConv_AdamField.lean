-- Prove2me | Definitions.Def_AdamDyn_ODEConv_AdamField
-- name    : AdamDyn_ODEConv_AdamField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:14.123696+00:00
-- url     : https://prove2.me/theorems/8bae749c-9bd3-4b29-ad56-eabd217b8f65
-- title:
--   The continuous-time Adam fields $h(t,z)$ (3.3) and $h_\infty$ (7.1), their solutions, and the semiflow of (ODE$_\infty$)
-- statement:
--   Fix $d \ge 0$ and constants $a, b, \varepsilon \in \mathbb R$ (in the theorems $a, b, \varepsilon > 0$), a function $F : \mathbb R^d \to \mathbb R$ and a map $S : \mathbb R^d \to \mathbb R^d$. The state space is $\mathcal Z = \mathbb R^d \times \mathbb R^d \times \mathbb R^d$, with points $z = (x, m, v)$; write $\mathcal Z_+ = \mathbb R^d \times \mathbb R^d \times [0,+\infty)^d$ and $\mathcal Z_+^* = \mathbb R^d \times \mathbb R^d \times (0,+\infty)^d$. All operations on vectors below are coordinatewise.
--
--   1. The **Adam vector field** of (3.3), for $t > 0$, extended to all of $\mathcal Z$ by replacing $v$ with $|v|$:
--   $$h(t, z) = \Big( -\frac{(1-e^{-at})^{-1}\, m}{\varepsilon + \sqrt{(1-e^{-bt})^{-1} |v|}},\ a(\nabla F(x) - m),\ b(S(x) - |v|) \Big).$$
--   2. The **autonomous field** of (7.1), $h_\infty(z) = \lim_{t\to\infty} h(t,z)$:
--   $$h_\infty(x, m, v) = \Big( -\frac{m}{\varepsilon + \sqrt{|v|}},\ a(\nabla F(x) - m),\ b(S(x) - |v|) \Big).$$
--   3. For $T \in (0, +\infty]$ and $\eta \in [0, +\infty)$, a map $z$ is a **solution of** $(\mathrm{ODE}_\eta)$ $\dot z(t) = h(t+\eta, z(t))$ **on** $[0,T)$ with initial condition $z_0$ if $z$ is continuous on $[0,T)$, continuously differentiable on $(0,T)$, the equation holds for every $t \in (0,T)$ and $z(0) = z_0$. The set of such solutions is $Z^\eta_T(z_0)$. Solutions of $(\mathrm{ODE}_\infty)$ $\dot z = h_\infty(z)$ on $[0,T)$, forming $Z^\infty_T(z_0)$, are defined in the same way.
--   4. A **global solution to (ODE) with initial condition** $(x_0, 0, 0)$ is a map $z : [0,+\infty) \to \mathcal Z_+$, continuous, continuously differentiable on $(0,+\infty)$, with $\dot z(t) = h(t, z(t))$ for all $t > 0$ and $z(0) = (x_0, 0, 0)$.
--   5. A semiflow $\Phi$ on $\mathcal Z_+$ is **the semiflow of** $(\mathrm{ODE}_\infty)$, (7.8), if for every $z_0 \in \mathcal Z_+$ the path $t \mapsto \Phi_t(z_0)$ belongs to $Z^\infty_\infty(z_0)$.
--   6. The **debiasing map** $\bar e(t, z) = \big(x, m/(1-e^{-at}), v/(1-e^{-bt})\big)$ for $t > 0$, and, for $K \subseteq \mathcal Z_+$, $v_{\min}(K) = \inf\{ v_i : (x,m,v) \in K,\ i \in \{1,\dots,d\}\}$.
--
--   These objects carry every statement of the mission: the goal is about global solutions of (ODE), and the proof compares them with the semiflow of $(\mathrm{ODE}_\infty)$.
--
--   **Formalization Note** Each block is `EuclideanSpace ℝ (Fin d)` and $\mathcal Z$ is the product of three such spaces, whose Mathlib norm is the maximum of the three Euclidean norms (equivalent to the Euclidean norm of $\mathbb R^{3d}$). $\mathcal Z_+$ is the subtype of points with $v \ge 0$. Solutions are maps $\mathbb R \to \mathcal Z$ whose values outside $[0,T)$ are ignored; the time intervals $[0,T)$ and $(0,T)$ are written with $T \in [0,+\infty]$ as an extended non-negative real. The path of the semiflow is read at $\max(t, 0)$. The map `toZplus` $(x,m,v) \mapsto (x,m,|v|)$ views a $\mathcal Z_+$-valued path in the subtype. $\nabla F$ is Mathlib's `gradient`. The field $h$ is never evaluated at $t = 0$ in any statement.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 3 (spaces), p. 5 (Eq. (3.3), global solution), p. 12 (Eq. (7.1), |v| extension, Z^η_T), p. 13 (ē), p. 14 (v_min), p. 17 (Eq. (7.8))

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField

open scoped NNReal ENNReal

namespace AdamDyn.ODEConv

/-- The closed set `𝒵₊ = ℝ^d × ℝ^d × [0,+∞)^d` (p. 3), as a subtype of `𝒵` with the induced
metric. -/
abbrev Zplus (d : ℕ) : Type := {z : AdamDyn.WellPosed.State d // ∀ i, 0 ≤ z.2.2 i}

/-- Membership in `𝒵₊* = ℝ^d × ℝ^d × (0,+∞)^d` (p. 3). -/
def InZplusStar {d : ℕ} (z : AdamDyn.WellPosed.State d) : Prop := ∀ i, 0 < z.2.2 i

/-- The Adam vector field `h(t, z)` of (3.3) (p. 5), for `t > 0`, extended from `𝒵₊` to `𝒵` by
`h(t, (x, m, v)) := h(t, (x, m, |v|))` (p. 12):
`h(t, z) = ( −(1 − e^{−at})^{−1} m / (ε + √((1 − e^{−bt})^{−1} |v|)), a(∇F(x) − m), b(S(x) − |v|) )`,
the first block coordinatewise. It is only ever evaluated at `t > 0`. -/
noncomputable def adamField {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d) (t : ℝ)
    (z : AdamDyn.WellPosed.State d) : AdamDyn.WellPosed.State d :=
  (WithLp.toLp 2 (fun i => -((1 - Real.exp (-a * t))⁻¹ * z.2.1 i /
      (ε + Real.sqrt ((1 - Real.exp (-b * t))⁻¹ * |z.2.2 i|)))),
    a • (gradient F z.1 - z.2.1),
    b • (S z.1 - WithLp.toLp 2 (fun i => |z.2.2 i|)))

/-- The autonomous field `h∞(z) = lim_{t→∞} h(t, z)` of (7.1) (p. 12), with the same `|v|`
extension: `h∞(x, m, v) = ( −m/(ε + √|v|), a(∇F(x) − m), b(S(x) − |v|) )`. -/
noncomputable def adamFieldInf {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (z : AdamDyn.WellPosed.State d) : AdamDyn.WellPosed.State d :=
  (WithLp.toLp 2 (fun i => -(z.2.1 i / (ε + Real.sqrt |z.2.2 i|))),
    a • (gradient F z.1 - z.2.1),
    b • (S z.1 - WithLp.toLp 2 (fun i => |z.2.2 i|)))

/-- The time interval `[0, T)` for `T ∈ (0, +∞]` (`T = ⊤` gives `[0, +∞)`). -/
def timeIco (T : ℝ≥0∞) : Set ℝ := {t | 0 ≤ t ∧ ENNReal.ofReal t < T}

/-- The open time interval `(0, T)` for `T ∈ (0, +∞]`. -/
def timeIoo (T : ℝ≥0∞) : Set ℝ := {t | 0 < t ∧ ENNReal.ofReal t < T}

/-- `z` is a solution on `[0, T)` of `ż(t) = g(t, z(t))` with initial condition `z0` (p. 12):
`z` is continuous on `[0, T)`, continuously differentiable on `(0, T)`, the equation holds at
every `t ∈ (0, T)`, and `z(0) = z0`. Values of `z` at times outside `[0, T)` are irrelevant. -/
def IsSolutionOn {d : ℕ} (g : ℝ → AdamDyn.WellPosed.State d → AdamDyn.WellPosed.State d) (T : ℝ≥0∞) (z0 : AdamDyn.WellPosed.State d)
    (z : ℝ → AdamDyn.WellPosed.State d) : Prop :=
  ContinuousOn z (timeIco T) ∧ ContDiffOn ℝ 1 z (timeIoo T) ∧
    (∀ t ∈ timeIoo T, HasDerivAt z (g t (z t)) t) ∧ z 0 = z0

/-- `z ∈ Z^η_T(z0)` for `η ∈ [0, +∞)` (p. 12): a solution on `[0, T)` of
`(ODE_η) ż(t) = h(t + η, z(t))` with initial condition `z0`. -/
def IsSolutionEta {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d) (η : ℝ)
    (T : ℝ≥0∞) (z0 : AdamDyn.WellPosed.State d) (z : ℝ → AdamDyn.WellPosed.State d) : Prop :=
  IsSolutionOn (fun t => adamField a b ε F S (t + η)) T z0 z

/-- `z ∈ Z^∞_T(z0)` (p. 12): a solution on `[0, T)` of `(ODE_∞) ż(t) = h∞(z(t))` with initial
condition `z0`. -/
def IsSolutionInf {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d) (T : ℝ≥0∞)
    (z0 : AdamDyn.WellPosed.State d) (z : ℝ → AdamDyn.WellPosed.State d) : Prop :=
  IsSolutionOn (fun _ => adamFieldInf a b ε F S) T z0 z

/-- A *global solution to (ODE) with initial condition `(x0, 0, 0)`* (p. 5): `z` is continuous
on `[0, +∞)` with values in `𝒵₊`, continuously differentiable on `(0, +∞)`,
`ż(t) = h(t, z(t))` for all `t > 0`, and `z(0) = (x0, 0, 0)`. -/
def IsGlobalSolution {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d) (x0 : AdamDyn.WellPosed.Vec d)
    (z : ℝ → AdamDyn.WellPosed.State d) : Prop :=
  ContinuousOn z (Set.Ici 0) ∧ (∀ t, 0 ≤ t → ∀ i, 0 ≤ (z t).2.2 i) ∧
    ContDiffOn ℝ 1 z (Set.Ioi 0) ∧
    (∀ t, 0 < t → HasDerivAt z (adamField a b ε F S t (z t)) t) ∧ z 0 = (x0, 0, 0)

/-- The map `(x, m, v) ↦ (x, m, |v|)` from `𝒵` to `𝒵₊`; the identity on `𝒵₊`. Used to view a
path with values in `𝒵₊` as a path in the subtype. -/
def toZplus {d : ℕ} (z : AdamDyn.WellPosed.State d) : Zplus d :=
  ⟨(z.1, z.2.1, WithLp.toLp 2 (fun i => |z.2.2 i|)), fun i => by simp⟩

/-- `Φ` is the semiflow `(t, z) ↦ Z^∞_∞(z)(t)` of (7.8) (p. 17): for every `z0 ∈ 𝒵₊`, the path
`t ↦ Φ_t(z0)` (read at `max t 0`) is a global solution of `(ODE_∞)` with initial condition `z0`. -/
def IsODEInfSemiflow {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (Φ : Flow ℝ≥0 (Zplus d)) : Prop :=
  ∀ z0 : Zplus d, IsSolutionInf a b ε F S ⊤ z0.1 (fun t => (Φ (Real.toNNReal t) z0).1)

/-- The debiasing map `ē(t, z) = (x, m/(1 − e^{−at}), v/(1 − e^{−bt}))` (p. 13), for `t > 0`. -/
noncomputable def ebar {d : ℕ} (a b t : ℝ) (z : AdamDyn.WellPosed.State d) : AdamDyn.WellPosed.State d :=
  (z.1, (1 - Real.exp (-a * t))⁻¹ • z.2.1, (1 - Real.exp (-b * t))⁻¹ • z.2.2)

/-- `v_min(K) = inf{vᵢ : (x, m, v) ∈ K, i ∈ {1, …, d}}` (p. 14), for `K ⊆ 𝒵₊`. -/
noncomputable def vmin {d : ℕ} (K : Set (AdamDyn.WellPosed.State d)) : ℝ :=
  sInf {r : ℝ | ∃ z ∈ K, ∃ i, z.2.2 i = r}

end AdamDyn.ODEConv


