-- Prove2me | Definitions.Def_ClassicalDynamics_core
-- name    : ClassicalDynamics_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T23:34:44.32225+00:00
-- url     : https://prove2.me/theorems/48bc409c-b951-4c93-b31a-a178b4ca6894
-- title:
--   Lagrangian mechanics on $\mathbb{R}^n$: action, Lagrange's equations, constants of the motion
-- statement:
--   The definition layer for Tong's Section 2, on an $n$-dimensional configuration space $\mathbb{R}^n$ (represented as functions $\{0,\dots,n-1\} \to \mathbb{R}$).
--
--   A **Lagrangian** is a function $L(t, q, v)$ of time, position and velocity; it is *smooth* when it is $C^\infty$ jointly in all arguments. The **velocity** of a path $q$ is the coordinatewise derivative $\dot q_i(t)$. Partial derivatives $\partial L/\partial q_i$ and $\partial L/\partial \dot q_i$ are one-dimensional derivatives in a single coordinate slot, obtained by varying the $i$-th entry and holding the others fixed.
--
--   A path is a **motion** when Lagrange's equations (Tong eq. 2.43) hold,
--   $$\frac{d}{dt}\left(\frac{\partial L}{\partial \dot q_i}\right) = \frac{\partial L}{\partial q_i},$$
--   for every coordinate and every time, the time derivative being asserted to exist. The **generalised momentum** is $p_i = \partial L/\partial \dot q_i$ (eq. 2.44) evaluated along a path, the **Hamiltonian** is $H = \sum_j \dot q_j\, \partial L/\partial \dot q_j - L$ (eq. 2.47), and the **action** over $[t_1,t_2]$ is $\int_{t_1}^{t_2} L(t,q(t),\dot q(t))\,dt$ (eq. 2.3).
--
--   A function of time is a **constant of the motion** when it takes the same value at all times (eq. 2.46). A one-parameter family of paths $Q(s,t)$ is a **continuous symmetry** of $L$ when $\partial_s L(t, Q(s,t), \dot Q(s,t)) = 0$ for all $s$ and $t$ (eq. 2.52), and the associated **Noether charge** is $\sum_i (\partial L/\partial \dot q_i)\,(\partial Q_i/\partial s)$ evaluated at $s = 0$ along the path $Q(0,\cdot)$ (eq. 2.54).
-- source:
--   D. Tong, Classical Dynamics, University of Cambridge Part II Mathematical Tripos, Michaelmas 2004/2005, https://www.damtp.cam.ac.uk/user/tong/dynamics.html, Section 2 (pp. 10-25), eqs. (2.3), (2.43), (2.44), (2.46), (2.47), (2.52), (2.54)

import Mathlib

namespace ClassicalDynamics

/-- A Lagrangian `L(t, q, q̇)` on an `n`-dimensional configuration space `ℝⁿ`.
Tong writes it as `L(qᵢ, q̇ᵢ, t)`; here the time argument comes first. -/
abbrev Lagrangian (n : ℕ) : Type := ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ

/-- Smoothness of a Lagrangian, jointly in all of its arguments. -/
def IsSmoothLagrangian {n : ℕ} (L : Lagrangian n) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => L p.1 p.2.1 p.2.2)

/-- The velocity `q̇(t)` of a path `q : ℝ → ℝⁿ`, computed coordinatewise. -/
noncomputable def vel {n : ℕ} (q : ℝ → Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun i => deriv (fun s => q s i) t

/-- The partial derivative `∂L/∂qᵢ` of a Lagrangian with respect to the `i`-th
coordinate, evaluated at `(t, q, v)`. -/
noncomputable def dLdq {n : ℕ} (L : Lagrangian n) (i : Fin n)
    (t : ℝ) (q v : Fin n → ℝ) : ℝ :=
  deriv (fun x : ℝ => L t (Function.update q i x) v) (q i)

/-- The partial derivative `∂L/∂q̇ᵢ` of a Lagrangian with respect to the `i`-th
velocity, evaluated at `(t, q, v)`. -/
noncomputable def dLdv {n : ℕ} (L : Lagrangian n) (i : Fin n)
    (t : ℝ) (q v : Fin n → ℝ) : ℝ :=
  deriv (fun x : ℝ => L t q (Function.update v i x)) (v i)

/-- The partial derivative `∂f/∂qᵢ` of a function `f(t, q)` of time and position. -/
noncomputable def dfdq {n : ℕ} (f : ℝ → (Fin n → ℝ) → ℝ) (i : Fin n)
    (t : ℝ) (q : Fin n → ℝ) : ℝ :=
  deriv (fun x : ℝ => f t (Function.update q i x)) (q i)

/-- Lagrange's equations (Tong, eq. 2.43): the path `q` satisfies
`d/dt (∂L/∂q̇ᵢ) = ∂L/∂qᵢ` at every time and in every coordinate, the derivative
being asserted to exist. -/
def IsMotion {n : ℕ} (L : Lagrangian n) (q : ℝ → Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (t : ℝ),
    HasDerivAt (fun s : ℝ => dLdv L i s (q s) (vel q s))
      (dLdq L i t (q t) (vel q t)) t

/-- The generalised momentum `pᵢ = ∂L/∂q̇ᵢ` (Tong, eq. 2.44) evaluated along a path. -/
noncomputable def momentum {n : ℕ} (L : Lagrangian n) (i : Fin n)
    (q : ℝ → Fin n → ℝ) (t : ℝ) : ℝ :=
  dLdv L i t (q t) (vel q t)

/-- The Hamiltonian `H = Σⱼ q̇ⱼ ∂L/∂q̇ⱼ − L` (Tong, eq. 2.47). -/
noncomputable def hamiltonian {n : ℕ} (L : Lagrangian n)
    (t : ℝ) (q v : Fin n → ℝ) : ℝ :=
  (∑ j : Fin n, v j * dLdv L j t q v) - L t q v

/-- The action `S = ∫ L dt` of a path over the time interval `[t₁, t₂]`
(Tong, eq. 2.3). -/
noncomputable def action {n : ℕ} (L : Lagrangian n) (q : ℝ → Fin n → ℝ)
    (t₁ t₂ : ℝ) : ℝ :=
  ∫ t in t₁..t₂, L t (q t) (vel q t)

/-- A real-valued function of time is a constant of the motion when it takes the
same value at all times (Tong, eq. 2.46). -/
def IsConstantInTime (F : ℝ → ℝ) : Prop := ∀ t₁ t₂ : ℝ, F t₁ = F t₂

/-- A one-parameter family of paths `Q(s, t)` is a continuous symmetry of `L`
when `∂/∂s L(Q(s,t), Q̇(s,t), t) = 0` (Tong, eq. 2.52). -/
def IsContinuousSymmetry {n : ℕ} (L : Lagrangian n) (Q : ℝ → ℝ → Fin n → ℝ) : Prop :=
  ∀ s t : ℝ, deriv (fun u : ℝ => L t (Q u t) (vel (Q u) t)) s = 0

/-- The Noether charge `Σᵢ (∂L/∂q̇ᵢ)(∂Qᵢ/∂s)`, evaluated at `s = 0` along the
reference path `Q(0, ·)` (Tong, eq. 2.54). -/
noncomputable def noetherCharge {n : ℕ} (L : Lagrangian n)
    (Q : ℝ → ℝ → Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin n, dLdv L i t (Q 0 t) (vel (Q 0) t) * deriv (fun u : ℝ => Q u t i) 0

end ClassicalDynamics


