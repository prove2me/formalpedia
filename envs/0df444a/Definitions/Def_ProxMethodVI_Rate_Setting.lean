-- Prove2me | Definitions.Def_ProxMethodVI_Rate_Setting
-- name    : ProxMethodVI_Rate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:16.685093+00:00
-- url     : https://prove2.me/theorems/1727033d-4f8e-496f-80fe-e66b848f6039
-- title:
--   §2.1–§3, pp. 232–237 — Lipschitz monotone F (2.1), strongly convex ω (2.2), prox-mapping P_z, Ω and H_u (2.3), Θ(z₀) (2.13), relaxed CPM (2.11), basic implementation (3.2)–(3.4)
-- statement:
--   This file fixes the objects of §§2–3 of Nemirovski's prox-method paper.
--
--   Let $E$ be a finite-dimensional real vector space with an **arbitrary** norm $\|\cdot\|$, and let $Z\subseteq E$ be a set (convex, compact and nonempty in every theorem that uses these objects). The pairing $\langle\xi,z\rangle$ of a dual vector $\xi$ with $z\in E$ is the value $\xi(z)$ of a linear functional, and the conjugate norm $\|\xi\|_*=\max_{\|z\|\le1}\langle\xi,z\rangle$ is the operator norm of $\xi$.
--
--   1. **Lipschitz continuity and monotonicity (2.1).** A map $F$ from $E$ to linear functionals is $L$-Lipschitz on $Z$ if $\|F(z)-F(z')\|_*\le L\|z-z'\|$ for all $z,z'\in Z$, and monotone on $Z$ if $\langle F(z)-F(z'),z-z'\rangle\ge0$ for all $z,z'\in Z$.
--   2. **Distance-generating function (2.2).** $\omega:Z\to\mathbb R$ is continuously differentiable on $Z$, with derivative $\omega'(z)$ taken within $Z$ and continuous on $Z$, and strongly convex with modulus $\alpha>0$:
--   $$\langle\omega'(z)-\omega'(w),z-w\rangle\ge\alpha\|z-w\|^2\qquad\forall z,w\in Z.$$
--   3. **Prox-mapping.** For $U\subseteq E$, $z\in E$ and a dual vector $\xi$, a point $v$ is a prox point, written $v=P_z(\xi)$ when $U=Z$, if $v\in U$ and $v$ minimizes $\omega(y)+\langle\xi-\omega'(z),y\rangle$ over $y\in U$.
--   4. **Legendre transform and $H_u$ (2.3).** $\Omega(\xi)=\max_{z\in Z}[\langle\xi,z\rangle-\omega(z)]$ and $H_u(z)=\Omega(\omega'(z))-\langle\omega'(z),u\rangle$.
--   5. **The constant $\Theta$ (2.13).** $\Theta(z_0)=\max_{z\in Z}[\omega(z)-\omega(z_0)-\langle\omega'(z_0),z-z_0\rangle]$.
--   6. **Relaxed conceptual prox-method (2.11).** Sequences $(z_t)_{t\ge0}$, $(w_t)_{t\ge1}$, stepsizes $\gamma_t>0$ and tolerances $\epsilon_t$ form a run if $z_0\in Z$ and, for every $t\ge1$, $w_t\in Z$, $z_t=P_{z_{t-1}}(\gamma_tF(w_t))$ and
--   $$\langle\gamma_tF(w_t),w_t-z_t\rangle+\omega(z_{t-1})+\langle\omega'(z_{t-1}),z_t-z_{t-1}\rangle-\omega(z_t)\le\epsilon_t.$$
--   The approximate solution after $N$ steps is $z^N=\big(\sum_{t=1}^N\gamma_t\big)^{-1}\sum_{t=1}^N\gamma_tw_t$, an average of the points $w_t$.
--   7. **Test (3.4).** For a centre $z_{t-1}$, a stepsize $\gamma$ and a pair $(a,b)$, the test is
--   $$\langle\gamma F(a),a-b\rangle+\omega(z_{t-1})+\langle\omega'(z_{t-1}),b-z_{t-1}\rangle-\omega(b)\le0.$$
--   8. **Basic implementation (3.2)–(3.4)** with constant stepsize $\gamma$. A run starts at $z_0\in Z$. Step $t$ computes $w_{t,1}=P_{z_{t-1}}(\gamma F(z_{t-1}))$. If the test holds for $(z_{t-1},w_{t,1})$, then $w_t=z_{t-1}$ and $z_t=w_{t,1}$ ($s_t=1$). Otherwise $w_t=w_{t,1}$ and $z_t=w_{t,2}=P_{z_{t-1}}(\gamma F(w_{t,1}))$ ($s_t=2$).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Dual vectors are continuous linear functionals $E\to\mathbb R$. This is equivalent to the paper's Euclidean space with an inner product and a second norm: every finite-dimensional normed space carries an inner product, and $\xi\mapsto\langle\xi,\cdot\rangle$ is a linear isometry from $(E,\|\cdot\|_*)$ onto the dual with its operator norm. $F$, $\omega$ and $\omega'$ are total functions on $E$, but every condition is imposed on $Z$ only. The prox-mapping is a relation, not a function, so no junk value enters. $\Omega$ and $\Theta$ are suprema over the image of $Z$, which are maxima when $Z$ is compact and nonempty and $\omega$ is continuous on $Z$. Indices follow the paper: in Lean, step $t+1$ goes from `z t` to `w (t+1)` and `z (t+1)`, and `w 0` is unused. The termination test (2.8) is not modelled, so runs never stop. The paper's inner loop "until (3.4) is met" is cut at $s=2$. Theorem 3.2's first claim says this cut loses nothing, and the goal theorem also states that claim.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t), SIAM J. Optim. 15(1) (2004), pp. 232–237, §2.1, §2.2, §2.3, §3, (2.1)–(2.3), (2.11), (2.13), (3.2)–(3.4)

import Mathlib

namespace ProxMethodVI.Rate

/-- (2.1.a), p. 232: `F` is Lipschitz on `Z` from `‖·‖` to the conjugate norm `‖·‖_*`,
`‖F(z) − F(z′)‖_* ≤ L‖z − z′‖` for all `z, z′ ∈ Z`. The values of `F` are linear functionals
`E →L[ℝ] ℝ`, whose operator norm is exactly `‖ξ‖_* = max_{‖z‖ ≤ 1} ⟨ξ, z⟩`. -/
def IsLipschitzOnWRT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (F : E → E →L[ℝ] ℝ) (L : ℝ) : Prop :=
  ∀ z ∈ Z, ∀ z' ∈ Z, ‖F z - F z'‖ ≤ L * ‖z - z'‖

/-- (2.1.b), p. 232: `F` is monotone on `Z`, `⟨F(z) − F(z′), z − z′⟩ ≥ 0` for all `z, z′ ∈ Z`. -/
def IsMonotoneOnWRT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (F : E → E →L[ℝ] ℝ) : Prop :=
  ∀ z ∈ Z, ∀ z' ∈ Z, 0 ≤ (F z - F z') (z - z')

/-- §2.2, (2.2), p. 232: `ω : Z → ℝ` is continuously differentiable on `Z` with derivative `ω′`
(a derivative within `Z`, continuous on `Z`) and strongly convex with modulus `α > 0` in the
monotonicity form `⟨ω′(z) − ω′(w), z − w⟩ ≥ α‖z − w‖²` for all `z, w ∈ Z`. -/
def IsStrongDGF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) : Prop :=
  0 < α ∧ (∀ z ∈ Z, HasFDerivWithinAt ω (ω' z) Z z) ∧ ContinuousOn ω' Z ∧
    ∀ z ∈ Z, ∀ w ∈ Z, α * ‖z - w‖ ^ 2 ≤ (ω' z - ω' w) (z - w)

/-- The prox-mapping of p. 232 as a relation: `IsProxPt U ω ω' z ξ v` says that `v` is a
minimizer over `U` of `y ↦ ω(y) + ⟨y, ξ − ω′(z)⟩`. With `U = Z` this is `v = P_z(ξ)`; with
`U ⊆ Z` and `ξ := γ • ξ` it is the point `w` of (3.6), p. 237. -/
def IsProxPt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (z : E) (ξ : E →L[ℝ] ℝ) (v : E) : Prop :=
  v ∈ U ∧ ∀ y ∈ U, ω v + (ξ - ω' z) v ≤ ω y + (ξ - ω' z) y

/-- p. 232: `Ω(ξ) = max_{z ∈ Z} [⟨ξ, z⟩ − ω(z)]`, the Legendre transformation of `ω|_Z`
(a genuine maximum when `Z` is compact and nonempty and `ω` is continuous on `Z`). -/
noncomputable def legendre {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (ω : E → ℝ) (ξ : E →L[ℝ] ℝ) : ℝ :=
  sSup ((fun z => ξ z - ω z) '' Z)

/-- (2.3), p. 232: `H_u(z) = Ω_u(ω′(z)) = Ω(ω′(z)) − ⟨ω′(z), u⟩`. -/
noncomputable def Hfun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (u z : E) : ℝ :=
  legendre Z ω (ω' z) - ω' z u

/-- (2.13), p. 234: `Θ(z₀) = max_{z ∈ Z} [ω(z) − ω(z₀) − ⟨ω′(z₀), z − z₀⟩]`. -/
noncomputable def theta {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (z₀ : E) : ℝ :=
  sSup ((fun z => ω z - ω z₀ - ω' z₀ (z - z₀)) '' Z)

/-- A run of the relaxed conceptual prox-method of Proposition 2.2, (2.11), p. 234, with
stepsizes `γ t > 0` and tolerances `ε t`. Indices follow the paper: `z 0 = z₀ ∈ Z`, and step
`t + 1` (the paper's step `t = 1, 2, …`) goes from `z t` to `w (t + 1) ∈ Z` and
`z (t + 1) = P_{z t}(γ_{t+1} F(w (t + 1)))`, subject to (2.11) with this substitution.
`w 0` is unused. The termination test (2.8) is not modelled: the run never terminates. -/
def IsRelaxedRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (F : E → E →L[ℝ] ℝ) (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ)
    (γ ε : ℕ → ℝ) (z w : ℕ → E) : Prop :=
  z 0 ∈ Z ∧ ∀ t : ℕ, 0 < γ (t + 1) ∧ w (t + 1) ∈ Z ∧
    IsProxPt Z ω ω' (z t) (γ (t + 1) • F (w (t + 1))) (z (t + 1)) ∧
    γ (t + 1) * F (w (t + 1)) (w (t + 1) - z (t + 1)) + ω (z t)
      + ω' (z t) (z (t + 1) - z t) - ω (z (t + 1)) ≤ ε (t + 1)

/-- p. 233: the weighted average `z^N = (∑_{t=1}^N γ_t)⁻¹ ∑_{t=1}^N γ_t w_t` of the points
`w_t` (not of the `z_t`). -/
noncomputable def ergodicAvg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℕ → ℝ) (w : ℕ → E) (N : ℕ) : E :=
  (∑ t ∈ Finset.Icc 1 N, γ t)⁻¹ • ∑ t ∈ Finset.Icc 1 N, γ t • w t

/-- The test (3.4), p. 237, for the centre `zc = z_{t−1}` and the pair
`(a, b) = (w_{t,s−1}, w_{t,s})`:
`⟨γF(a), a − b⟩ + ω(zc) + ⟨ω′(zc), b − zc⟩ − ω(b) ≤ 0`. -/
def test34 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℝ) (F : E → E →L[ℝ] ℝ) (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (zc a b : E) : Prop :=
  γ * F a (a - b) + ω zc + ω' zc (b - zc) - ω b ≤ 0

/-- A run of the basic implementation, pp. 236–237, with constant stepsize `γ` ((3.2) takes
`γ = α/(√2 L)`). Step `t + 1` starts from `w_{t+1,0} = z t`, computes
`w_{t+1,1} = w₁ = P_{z t}(γ F(z t))` (3.3), and then:
* if (3.4) holds at `s = 1`, sets `w (t + 1) = z t`, `z (t + 1) = w₁` (`s_t = 1`);
* otherwise sets `w (t + 1) = w₁`, `z (t + 1) = w_{t+1,2} = P_{z t}(γ F(w₁))` (`s_t = 2`).

The paper's inner loop "until (3.4) is met" is cut at `s = 2`; this cut is licensed by the first
claim of Theorem 3.2 (p. 239), that (3.4) holds within two inner iterations, which the goal
theorem also asserts. The termination test (2.8) is not modelled. -/
def IsBasicRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (F : E → E →L[ℝ] ℝ) (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ)
    (γ : ℝ) (z w : ℕ → E) : Prop :=
  z 0 ∈ Z ∧ ∀ t : ℕ, ∃ w₁ : E, IsProxPt Z ω ω' (z t) (γ • F (z t)) w₁ ∧
    (test34 γ F ω ω' (z t) (z t) w₁ → w (t + 1) = z t ∧ z (t + 1) = w₁) ∧
    (¬ test34 γ F ω ω' (z t) (z t) w₁ →
      w (t + 1) = w₁ ∧ IsProxPt Z ω ω' (z t) (γ • F w₁) (z (t + 1)))

end ProxMethodVI.Rate


