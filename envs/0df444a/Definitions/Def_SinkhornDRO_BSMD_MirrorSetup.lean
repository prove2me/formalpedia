-- Prove2me | Definitions.Def_SinkhornDRO_BSMD_MirrorSetup
-- name    : SinkhornDRO_BSMD_MirrorSetup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:22:38.698693+00:00
-- url     : https://prove2.me/theorems/7679a11f-20e9-4509-9d28-0333ac6f0586
-- title:
--   Mirror-descent setup: norm with Assumption EC.1, dual norm, Bregman divergence, prox-mapping, BSMD iterates
-- statement:
--   Throughout, $\theta$ ranges over $\mathbb R^{d_\theta}$ with its Euclidean norm $\|\cdot\|_2$, and $\Theta\subseteq\mathbb R^{d_\theta}$ is the feasible set.
--
--   1. **Mirror norm (Assumption EC.1).** A norm $\|\cdot\|$ on $\mathbb R^{d_\theta}$ together with constants $\mathfrak c>0$ and $\mathfrak d$ such that
--   $$\mathfrak c\,\|x\|_2\le\|x\|\le\mathfrak d\,\|x\|_2\qquad\text{for all }x.$$
--   Its **dual norm** is $\|y\|_*=\sup_{\|x\|\le1}\langle y,x\rangle$.
--
--   2. **Bregman divergence.** For $\omega:\Theta\to\mathbb R$ with gradient $\nabla\omega$,
--   $$D_\omega(\theta,\theta')=\omega(\theta')-\omega(\theta)-\langle\nabla\omega(\theta),\theta'-\theta\rangle .$$
--
--   3. **Distance generating function.** $\omega$ is continuously differentiable on $\Theta$ and $\kappa$-strongly convex on $\Theta$ with respect to $\|\cdot\|$: $\kappa>0$ and
--   $$\langle\theta'-\theta,\nabla\omega(\theta')-\nabla\omega(\theta)\rangle\ge\kappa\|\theta'-\theta\|^2\qquad(\theta,\theta'\in\Theta).$$
--
--   4. **Prox-mapping.** $\mathrm{Prox}_\theta(y)\in\arg\min_{\theta'\in\Theta}\{\langle y,\theta'-\theta\rangle+D_\omega(\theta,\theta')\}$ for $\theta\in\Theta$ and every $y$.
--
--   5. **BSMD iterates.** Given a subgradient estimator $v(\theta,\xi)$ (a vector computed at the point $\theta$ from a random sample $\xi$), a step size $h$, a start $\theta_0$ and samples $\xi_0,\dots,\xi_{T-1}$,
--   $$\theta_{t+1}=\mathrm{Prox}_{\theta_t}\big(h\,v(\theta_t,\xi_t)\big),\qquad t=0,\dots,T-1,$$
--   and the averaged output is $\hat\theta=\frac1T\sum_{t=0}^{T-1}\theta_t$.
--
--   These are the objects of Algorithm 1 (BSMD) and of its analysis.
--
--   **Formalization Note** The mirror norm is a function `N` with subadditivity, absolute homogeneity and Assumption EC.1 as fields; the decision space is `EuclideanSpace ℝ (Fin d)`. The dual norm is a real supremum over the unit ball of `N`, which is nonempty and on which $\langle y,\cdot\rangle$ is bounded by $\|y\|_2/\mathfrak c$. The gradient of $\omega$ is a map `ω'` with `HasGradientWithinAt ω (ω' θ) Θ θ` on $\Theta$ and `ContinuousOn ω' Θ`. The prox-mapping is a map characterized by the argmin property on $\Theta$ (a minimizer exists and is unique for a strongly convex $\omega$ on a closed convex set). The iterate sequence is frozen after step $T$. The paper prints $\hat\theta=\frac1T\sum_{t=1}^{T}\theta_t$; the average of the query points $\theta_0,\dots,\theta_{T-1}$ is used here, because Lemma EC.7 fails for the printed average (see that item).
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. 5 (κ-strong convexity), p. 14 (D_ω, Prox), p. 15 (Algorithm 1), p. ec18 (Assumption EC.1, dual norm bounds), p. ec19 (Lemma EC.7 iteration)

import Mathlib

open scoped RealInnerProductSpace

namespace SinkhornDRO.BSMD

/-- The decision space `ℝ^{d_θ}` with its Euclidean norm `‖·‖₂` (Wang–Gao–Xie, arXiv:2109.11926v5,
§4, p. 14). -/
abbrev Param (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The norm `‖·‖` of the mirror-descent setup (p. 14), given as a function `N` with the norm axioms
(subadditivity and absolute homogeneity; definiteness follows from the lower bound), together with
Assumption EC.1 (p. ec18): there are constants `𝔠 > 0` and `𝔡` with
`𝔠 ‖x‖₂ ≤ ‖x‖ ≤ 𝔡 ‖x‖₂` for every `x`. -/
structure MirrorNorm (d : ℕ) where
  /-- the norm `‖·‖` -/
  N : Param d → ℝ
  /-- triangle inequality -/
  add_le : ∀ x y, N (x + y) ≤ N x + N y
  /-- absolute homogeneity -/
  smul_eq : ∀ (a : ℝ) (x : Param d), N (a • x) = |a| * N x
  /-- the lower constant `𝔠` of Assumption EC.1 -/
  c : ℝ
  /-- the upper constant `𝔡` of Assumption EC.1 -/
  dd : ℝ
  c_pos : 0 < c
  lower : ∀ x, c * ‖x‖ ≤ N x
  upper : ∀ x, N x ≤ dd * ‖x‖

/-- The dual norm `‖y‖_* = sup_{‖x‖ ≤ 1} ⟨y, x⟩` of the mirror norm (p. ec18). The supremum is over a
nonempty set (it contains `0`) of reals bounded by `‖y‖₂ / 𝔠`. -/
noncomputable def dualNorm {d : ℕ} (𝒩 : MirrorNorm d) (y : Param d) : ℝ :=
  ⨆ x : {x : Param d // 𝒩.N x ≤ 1}, ⟪y, (x : Param d)⟫

/-- The Bregman divergence `D_ω(θ, θ') = ω(θ') − ω(θ) − ⟨∇ω(θ), θ' − θ⟩` (p. 14), with `ω'` the
gradient map of `ω`. -/
noncomputable def bregman {d : ℕ} (ω : Param d → ℝ) (ω' : Param d → Param d)
    (θ θ' : Param d) : ℝ :=
  ω θ' - ω θ - ⟪ω' θ, θ' - θ⟫

/-- `ω` is a distance generating function on `Θ` with gradient map `ω'` (p. 14 and p. 5): `ω` is
continuously differentiable on `Θ` (its gradient within `Θ` at `θ` is `ω' θ`, and `ω'` is continuous
on `Θ`), and `ω` is `κ`-strongly convex on `Θ` with respect to `‖·‖`, i.e. `κ > 0` and
`⟨θ' − θ, ∇ω(θ') − ∇ω(θ)⟩ ≥ κ ‖θ' − θ‖²` for all `θ, θ' ∈ Θ`. -/
def IsDistGen {d : ℕ} (Θ : Set (Param d)) (𝒩 : MirrorNorm d) (κ : ℝ)
    (ω : Param d → ℝ) (ω' : Param d → Param d) : Prop :=
  (∀ θ ∈ Θ, HasGradientWithinAt ω (ω' θ) Θ θ) ∧ ContinuousOn ω' Θ ∧ 0 < κ ∧
    ∀ θ ∈ Θ, ∀ θ' ∈ Θ, κ * 𝒩.N (θ' - θ) ^ 2 ≤ ⟪θ' - θ, ω' θ' - ω' θ⟫

/-- `prox` is the prox-mapping of `ω` on `Θ` (p. 14): for `θ ∈ Θ` and every `y`,
`Prox_θ(y) ∈ argmin_{θ' ∈ Θ} {⟨y, θ' − θ⟩ + D_ω(θ, θ')}`. -/
def IsProxMap {d : ℕ} (Θ : Set (Param d)) (ω : Param d → ℝ) (ω' : Param d → Param d)
    (prox : Param d → Param d → Param d) : Prop :=
  ∀ θ ∈ Θ, ∀ y : Param d, prox θ y ∈ Θ ∧
    ∀ θ' ∈ Θ, ⟪y, prox θ y - θ⟫ + bregman ω ω' θ (prox θ y) ≤ ⟪y, θ' - θ⟫ + bregman ω ω' θ θ'

/-- The iterates of BSMD (Algorithm 1, p. 15; Lemma EC.7, p. ec19) driven by the samples
`ξ 0, …, ξ (T−1)`: `θ_0 = θ0` and `θ_{t+1} = Prox_{θ_t}(h · v(θ_t, ξ_t))` for `t < T`
(the sequence is frozen after step `T`). `v θ s` is the subgradient estimate at `θ` computed
from the sample `s`. -/
noncomputable def bsmdIter {d : ℕ} {Ω : Type*} (prox : Param d → Param d → Param d)
    (v : Param d → Ω → Param d) (h : ℝ) (θ0 : Param d) {T : ℕ} (ξ : Fin T → Ω) :
    ℕ → Param d
  | 0 => θ0
  | t + 1 =>
    if ht : t < T then
      prox (bsmdIter prox v h θ0 ξ t) (h • v (bsmdIter prox v h θ0 ξ t) (ξ ⟨t, ht⟩))
    else bsmdIter prox v h θ0 ξ t

/-- The averaged output `θ̂ = (1/T) Σ_{t=0}^{T−1} θ_t` of `T` BSMD steps. The paper prints the
average of `θ_1, …, θ_T` (p. 15, p. ec19); see the Formalization Note of the items for why the
average of the `T` query points `θ_0, …, θ_{T−1}` is used. -/
noncomputable def bsmdAvg {d : ℕ} {Ω : Type*} (prox : Param d → Param d → Param d)
    (v : Param d → Ω → Param d) (h : ℝ) (θ0 : Param d) {T : ℕ} (ξ : Fin T → Ω) : Param d :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, bsmdIter prox v h θ0 ξ t

end SinkhornDRO.BSMD


