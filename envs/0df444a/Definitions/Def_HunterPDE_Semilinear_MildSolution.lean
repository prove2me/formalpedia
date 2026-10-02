-- Prove2me | Definitions.Def_HunterPDE_Semilinear_MildSolution
-- name    : HunterPDE_Semilinear_MildSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:12:37.253973+00:00
-- url     : https://prove2.me/theorems/29c6e0ee-3897-4cd2-87a9-28a773a619f2
-- title:
--   Mild H^{2α}-valued solutions of u_t = Δu + λu − γu^m (Definition 5.48, Eqs. (5.38)–(5.40))
-- statement:
--   Fix $\lambda, \gamma \in \mathbb{R}$ and $m \in \mathbb{N}$, and consider the initial value problem
--   $$u_t = \Delta u + \lambda u - \gamma u^m, \qquad u(x,0) = g(x) \tag{5.34}$$
--   for $u : \mathbb{R}^n \times [0,T] \to \mathbb{R}$. Let $F(h)(x) = \lambda h(x) - \gamma h(x)^m$ (5.38) and let $e^{-tA}$ be the heat semigroup. For $s \ge 0$, $C([0,T]; H^s)$ is the space of curves $t \mapsto u(t) \in H^s(\mathbb{R}^n)$ continuous on $[0,T]$ in the $H^s$ norm, with norm $\|u\|_{C([0,T];H^s)} = \sup_{0\le t\le T}\|u(t)\|_{H^s}$. The map (5.40) is
--   $$\Phi(u)(t) = e^{-tA}g + \int_0^t e^{-(t-s)A}F(u(s))\, ds.$$
--   A **mild $H^{2\alpha}$-valued solution** of (5.34) on $[0,T]$ (Definition 5.48, where $T > 0$, $\alpha > n/4$ and $g \in H^{2\alpha}$) is a function $u \in C([0,T]; H^{2\alpha}(\mathbb{R}^n))$ such that
--   $$u(t) = e^{-tA}g + \int_0^t e^{-(t-s)A}F(u(s))\, ds \qquad \text{for every } 0 \le t \le T. \tag{5.39}$$
--
--   This is the integral (Duhamel) form of (5.34), in which local existence is proved by a contraction argument.
--
--   **Formalization Note.** Functions are real-valued; $u$ is a map $\mathbb{R} \to (\mathbb{R}^n \to \mathbb{R})$ of which only the times in $[0,T]$ matter. (5.39) holds as an identity in $H^{2\alpha}$, i.e. for almost every $x$ at each $t \in [0,T]$. The time integral is taken pointwise in $x$ (`intervalIntegral`); for $u \in C([0,T];H^{2\alpha})$ with $\alpha > n/4$ the integrand is bounded and continuous in $s \in [0,t)$, and this pointwise integral represents the book's $L^2$-valued integral. The standing assumptions $T > 0$, $\alpha > n/4$, $g \in H^{2\alpha}$ are hypotheses of the theorems that use the definition. The sup norm is valued in $[0,\infty]$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 153–154, Definition 5.48, Eqs. (5.34), (5.35), (5.38)–(5.40)

import Mathlib
import Definitions.Def_HunterPDE_Semilinear_SobolevHs
import Definitions.Def_HunterPDE_Semilinear_HeatSemigroup

open MeasureTheory Filter
open scoped ENNReal Topology

namespace HunterPDE.Semilinear

/-- The nonlinear operator `F` of Hunter, *Notes on PDEs*, (5.38) (p. 153), built from the
reaction term `f(u) = λu − γu^m` of (5.35):
`F(h)(x) = λ h(x) − γ h(x)^m`, for real parameters `λ, γ` and `m ∈ ℕ`. -/
def nemytskii (lam gam : ℝ) (m : ℕ) {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  lam * h x - gam * h x ^ m

/-- `u ∈ C([0,T]; Hˢ(ℝⁿ))`: a curve `t ↦ u(t)` of real-valued functions on `ℝⁿ` such that
`u(t) ∈ Hˢ(ℝⁿ)` for every `0 ≤ t ≤ T`, and `t ↦ u(t)` is continuous on `[0,T]` in the `Hˢ` norm
(`hsNorm`): `‖u(τ) − u(t)‖_{Hˢ} → 0` as `τ → t` within `[0,T]`, for every `t ∈ [0,T]`.
Values of `u` at times outside `[0,T]` are irrelevant. -/
def IsContinuousHs (n : ℕ) (s T : ℝ) (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, hsNormReal n s (u t) < ⊤) ∧
  ∀ t ∈ Set.Icc (0 : ℝ) T,
    Tendsto (fun τ => hsNormReal n s (u τ - u t)) (𝓝[Set.Icc (0 : ℝ) T] t) (𝓝 0)

/-- The norm of `C([0,T]; Hˢ(ℝⁿ))`: `‖u‖_{C([0,T];Hˢ)} = sup_{0 ≤ t ≤ T} ‖u(t)‖_{Hˢ}`, valued in
`[0, ∞]` (it is finite for `u ∈ C([0,T]; Hˢ)`). -/
noncomputable def supHsNorm (n : ℕ) (s T : ℝ) (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc (0 : ℝ) T, hsNormReal n s (u t)

/-- The map `Φ` of Hunter, *Notes on PDEs*, (5.40) (p. 154):
`Φ(u)(t) = e^{−tA} g + ∫₀ᵗ e^{−(t−s)A} F(u(s)) ds`,
with `e^{−tA}` the heat semigroup (5.37) (`heatSemigroup`) and `F` the operator (5.38)
(`nemytskii lam gam m`). The time integral is taken pointwise in `x ∈ ℝⁿ`; for
`u ∈ C([0,T]; H^{2α})` with `α > n/4` the integrand is bounded and continuous in `s ∈ [0, t)`,
and this pointwise integral is a representative of the `L²`-valued integral of the book. -/
noncomputable def duhamelMap (n : ℕ) (lam gam : ℝ) (m : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  heatSemigroup n t g x +
    ∫ s in (0 : ℝ)..t, heatSemigroup n (t - s) (nemytskii lam gam m (u s)) x

/-- Definition 5.48 of Hunter, *Notes on PDEs* (pp. 153–154): a **mild `H^{2α}`-valued solution**
of (5.34), `u_t = Δu + λu − γu^m`, `u(x,0) = g(x)`, on `[0,T]` is a function
`u ∈ C([0,T]; H^{2α}(ℝⁿ))` such that
`u(t) = e^{−tA} g + ∫₀ᵗ e^{−(t−s)A} F(u(s)) ds` for every `0 ≤ t ≤ T`   (5.39),
where `e^{−tA}` is given by (5.37) and `F` by (5.38). The identity (5.39) is an identity in
`H^{2α}(ℝⁿ)`, i.e. it holds for almost every `x ∈ ℝⁿ`.

The book states this definition under the standing assumptions `T > 0`, `α > n/4` and
`g ∈ H^{2α}(ℝⁿ)`; they are hypotheses of every theorem that uses it. -/
def IsMildSolution (n : ℕ) (α lam gam : ℝ) (m : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (T : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsContinuousHs n (2 * α) T u ∧
  ∀ t ∈ Set.Icc (0 : ℝ) T, u t =ᵐ[volume] duhamelMap n lam gam m g u t

end HunterPDE.Semilinear


