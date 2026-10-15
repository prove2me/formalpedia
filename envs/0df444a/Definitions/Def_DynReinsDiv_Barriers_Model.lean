-- Prove2me | Definitions.Def_DynReinsDiv_Barriers_Model
-- name    : DynReinsDiv_Barriers_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:54.937049+00:00
-- url     : https://prove2.me/theorems/463dc2d7-4a19-4e32-8a2e-ead02a69f458
-- title:
--   Claim law, A, B, f, the operator 𝓛 (3.2), the variational inequality (3.1) and the conclusion of Theorem 3.1 (pp. 8–10, 21–23)
-- statement:
--   This file fixes the model of Guan, Xu and Zhou's finite-horizon optimal reinsurance and dividend-payout problem and the object that Section 4 of the paper studies: the solution $v$ of the time-reversed HJB variational inequality, together with the properties that Theorem 3.1 of the paper establishes for it.
--
--   **Data.** Claims are i.i.d. copies of a nonnegative random variable $Z_1$ with law $\mu$ and distribution function $F(z)=\mathbb P(Z_1\le z)$, so $F(0-)=0$. The reinsurance loading is $\gamma>0$, the discount rate is $c>0$ and the horizon is $T>0$. The tail assumption (3.3) of the paper is imposed:
--   $$z^3\bigl(1-F(z)\bigr)\ \text{is bounded on }[0,\infty).$$
--   Write $\mu_1=\int_0^\infty z\,dF(z)$ and $\mu_2=\int_0^\infty z^2\,dF(z)$ (A.1). Section 4 of the paper assumes $0<\gamma<\mu_1$ (for $\gamma\ge\mu_1$ the solution is $v\equiv x$ and the problem is trivial); this is part of the model.
--
--   **Auxiliary functions.** For $y>0$,
--   $$A(y)=\int_0^{1/y} z\bigl(1-F(z)\bigr)\,dz,\qquad B(y)=\int_0^{1/y}\bigl(1-F(z)\bigr)\,dz,$$
--   and $A(y)=\tfrac12\mu_2$, $B(y)=\mu_1$ for $y\le 0$ ((A.5), (A.6)). The function $f(y)=-yA(y)+B(y)-\gamma$ (A.12) has a unique positive root, denoted $\lambda$.
--
--   **The operator and the variational inequality.** With $\mathcal H$ the set of measurable $H$ with $0\le H(z)\le z$ for $z\ge 0$,
--   $$\mathcal L v=\sup_{H\in\mathcal H}\Bigl(\frac{v_{xx}}{2}\int_0^\infty H(z)^2\,dF(z)+v_x\int_0^\infty H(z)\,dF(z)\Bigr)-\gamma v_x-cv, \tag{3.2}$$
--   and $v$ solves
--   $$\min\{v_t-\mathcal Lv,\ v_x-1\}=0\ \text{ in }(0,\infty)\times(0,T],\qquad v(0,t)=0\ (0<t\le T),\qquad v(x,0)=x\ (x>0). \tag{3.1}$$
--   Here $t$ is time to maturity; Section 4 of the paper calls it $\tau$.
--
--   **The solution of Theorem 3.1.** A function $v$, together with functions $v_x, v_{xx}, v_t$, is *the solution of Theorem 3.1* when:
--   1. $v$ is continuous on $\bar{\mathcal Q}_T=[0,\infty)\times[0,T]$, and $v_x,v_{xx},v_t$ are continuous on $\bar{\mathcal Q}_T\setminus\{(0,0)\}$ and are the partial derivatives $\partial_x v$, $\partial_x v_x$, $\partial_t v$ at every point with $x>0$, $0<t<T$ (this is the class $C^{2,1}(\bar{\mathcal Q}_T\setminus\{(0,0)\})\cap C(\bar{\mathcal Q}_T)$; boundary values of the derivatives are their continuous extensions);
--   2. $v$ satisfies (3.1);
--   3. on $(0,\infty)\times(0,T]$: $v_x\ge1$ (3.4), $v_t\ge0$ (3.5), $v_{xx}\le0$ (3.6), $x\mapsto v_{xx}(x,t)$ is nondecreasing (3.7, "$v_{xxx}\ge0$ in the weak sense"), $t\mapsto v_x(x,t)$ is nondecreasing on $(0,T]$ (3.8, "$v_{xt}\ge0$"), and $\lambda v_x+v_{xx}\ge0$ for every positive root $\lambda$ of $f$ (3.9).
--
--   Theorem 3.1 of the paper shows that exactly one such $v$ exists. Every statement of this mission is about this $v$ ("From now on, we fix $v$ as in Theorem 3.1", p. 10).
--
--   **Formalization Note** The claim law is a probability measure `μ` on $\mathbb R$ with `μ (Set.Iio 0) = 0` and $F(z)$ is `(μ (Set.Iic z)).toReal`; no density is assumed. $\mu_1,\mu_2$ are Bochner integrals, finite by (3.3). $\mathcal L$ is the supremum (3.2) as a function `Lop q p w` of the numbers $q=v_{xx}$, $p=v_x$, $w=v$; it is not defined through the closed form (A.10). The derivative witnesses `vx vxx vt` are explicit arguments because Section 4 uses them by name. These definitions restate, in the namespace `DynReinsDiv.Barriers`, the model of the companion mission on Theorem 3.1.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, pp. 8–10 ((3.1)–(3.3), Theorem 3.1, standing assumption 0 < γ < µ1 of Sec. 4) and pp. 21–23 ((A.1), (A.5), (A.6), (A.12))

import Mathlib

namespace DynReinsDiv.Barriers

open MeasureTheory

/-- The data of the time-reversed HJB variational inequality (3.1) of Guan, Xu & Zhou
(arXiv:2008.00391v3, Sec. 3, pp. 8–9, and the standing hypothesis of Sec. 4, p. 10): the claim law
`μ` (a probability measure on `[0, ∞)`), the reinsurance loading `γ`, the discount rate `c` and the
horizon `T`. The tail assumption (3.3) says `z³(1 − F(z))` is bounded on `[0, ∞)`, where
`F z = μ((−∞, z])` is the claim CDF. Section 4 assumes `0 < γ < μ₁`, `μ₁ = ∫ z dF(z)`. -/
structure Model where
  μ : Measure ℝ
  γ : ℝ
  c : ℝ
  T : ℝ
  isProb : IsProbabilityMeasure μ
  nonneg : μ (Set.Iio 0) = 0
  tail : ∃ C : ℝ, ∀ z : ℝ, 0 ≤ z → z ^ 3 * (1 - (μ (Set.Iic z)).toReal) ≤ C
  γ_pos : 0 < γ
  c_pos : 0 < c
  T_pos : 0 < T
  γ_lt_μ₁ : γ < ∫ z, z ∂μ

namespace Model

variable (M : Model)

/-- The claim CDF `F(z) = ℙ(Z₁ ≤ z)`. -/
noncomputable def F (z : ℝ) : ℝ := (M.μ (Set.Iic z)).toReal

/-- First moment `μ₁ = ∫₀^∞ z dF(z)` (A.1). -/
noncomputable def μ₁ : ℝ := ∫ z, z ∂M.μ

/-- Second moment `μ₂ = ∫₀^∞ z² dF(z)` (A.1). -/
noncomputable def μ₂ : ℝ := ∫ z, z ^ 2 ∂M.μ

/-- The function `A` of (A.5): `A(y) = ∫₀^{1/y} z(1 − F(z)) dz` for `y > 0`, `A(y) = μ₂/2` for `y ≤ 0`. -/
noncomputable def A (y : ℝ) : ℝ :=
  if 0 < y then ∫ z in (0 : ℝ)..(1 / y), z * (1 - M.F z) else M.μ₂ / 2

/-- The function `B` of (A.6): `B(y) = ∫₀^{1/y} (1 − F(z)) dz` for `y > 0`, `B(y) = μ₁` for `y ≤ 0`. -/
noncomputable def B (y : ℝ) : ℝ :=
  if 0 < y then ∫ z in (0 : ℝ)..(1 / y), (1 - M.F z) else M.μ₁

/-- The function `f(y) = −y A(y) + B(y) − γ` of (A.12); `λ` is its unique positive root. -/
noncomputable def fA (y : ℝ) : ℝ := -y * M.A y + M.B y - M.γ

/-- The admissible retained-loss functions `𝓗 = {H : 0 ≤ H(z) ≤ z}` of (3.2), taken measurable. -/
def Hset : Set (ℝ → ℝ) := {H | Measurable H ∧ ∀ z : ℝ, 0 ≤ z → 0 ≤ H z ∧ H z ≤ z}

/-- The operator `𝓛` of (3.2), as a function of the numbers `q = v_xx`, `p = v_x`, `w = v`:
`sup_{H ∈ 𝓗} ((q/2) ∫ H² dF + p ∫ H dF) − γ p − c w`. -/
noncomputable def Lop (q p w : ℝ) : ℝ :=
  sSup ((fun H : ℝ → ℝ => q / 2 * ∫ z, (H z) ^ 2 ∂M.μ + p * ∫ z, H z ∂M.μ) '' Hset)
    - M.γ * p - M.c * w

/-- `v ∈ C^{2,1}(𝒬̄_T ∖ {(0,0)}) ∩ C(𝒬̄_T)` with `𝒬̄_T = [0, ∞) × [0, T]`, and the given functions
`vx`, `vxx`, `vt` are its partial derivatives at interior points and their continuous extensions to
`𝒬̄_T ∖ {(0,0)}`. -/
def IsClassC21 (v vx vxx vt : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (Function.uncurry v) (Set.Ici 0 ×ˢ Set.Icc 0 M.T) ∧
  ContinuousOn (Function.uncurry vx) ((Set.Ici 0 ×ˢ Set.Icc 0 M.T) \ {((0 : ℝ), (0 : ℝ))}) ∧
  ContinuousOn (Function.uncurry vxx) ((Set.Ici 0 ×ˢ Set.Icc 0 M.T) \ {((0 : ℝ), (0 : ℝ))}) ∧
  ContinuousOn (Function.uncurry vt) ((Set.Ici 0 ×ˢ Set.Icc 0 M.T) \ {((0 : ℝ), (0 : ℝ))}) ∧
  ∀ x t : ℝ, 0 < x → 0 < t → t < M.T →
    HasDerivAt (fun y => v y t) (vx x t) x ∧
    HasDerivAt (fun y => vx y t) (vxx x t) x ∧
    HasDerivAt (fun s => v x s) (vt x t) t

/-- `v` solves the variational inequality (3.1) on `𝒬_T = (0, ∞) × (0, T]`:
`min{v_t − 𝓛v, v_x − 1} = 0`, `v(0, t) = 0` for `0 < t ≤ T`, `v(x, 0) = x` for `x > 0`. -/
def SolvesVI (v vx vxx vt : ℝ → ℝ → ℝ) : Prop :=
  (∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T →
    min (vt x t - M.Lop (vxx x t) (vx x t) (v x t)) (vx x t - 1) = 0) ∧
  (∀ t : ℝ, 0 < t → t ≤ M.T → v 0 t = 0) ∧
  (∀ x : ℝ, 0 < x → v x 0 = x)

/-- The properties (3.4)–(3.9) of Theorem 3.1 on `𝒬_T = (0, ∞) × (0, T]`: `v_x ≥ 1`, `v_t ≥ 0`,
`v_xx ≤ 0`, `v_xxx ≥ 0` in the weak sense (`x ↦ v_xx` nondecreasing), `v_xt ≥ 0` (`t ↦ v_x`
nondecreasing), and `λ v_x + v_xx ≥ 0` for every positive root `λ` of `f`. -/
def HJBProps (vx vxx vt : ℝ → ℝ → ℝ) : Prop :=
  (∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T → 1 ≤ vx x t) ∧
  (∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T → 0 ≤ vt x t) ∧
  (∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T → vxx x t ≤ 0) ∧
  (∀ t : ℝ, 0 < t → t ≤ M.T → MonotoneOn (fun y => vxx y t) (Set.Ioi 0)) ∧
  (∀ x : ℝ, 0 < x → MonotoneOn (fun s => vx x s) (Set.Ioc 0 M.T)) ∧
  (∀ lam : ℝ, 0 < lam → M.fA lam = 0 →
    ∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T → 0 ≤ lam * vx x t + vxx x t)

/-- `v` (with derivative functions `vx`, `vxx`, `vt`) is the solution of Theorem 3.1: it lies in
the class `C^{2,1}(𝒬̄_T ∖ {(0,0)}) ∩ C(𝒬̄_T)`, solves (3.1) and satisfies (3.4)–(3.9). Section 4
fixes this `v` ("From now on, we fix v as in Theorem 3.1", p. 10) and writes its second argument as
`τ`. -/
def IsTheorem31Solution (v vx vxx vt : ℝ → ℝ → ℝ) : Prop :=
  M.IsClassC21 v vx vxx vt ∧ M.SolvesVI v vx vxx vt ∧ M.HJBProps vx vxx vt

end Model

end DynReinsDiv.Barriers


