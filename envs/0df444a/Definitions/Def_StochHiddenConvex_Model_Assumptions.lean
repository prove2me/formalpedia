-- Prove2me | Definitions.Def_StochHiddenConvex_Model_Assumptions
-- name    : StochHiddenConvex_Model_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:41.300715+00:00
-- url     : https://prove2.me/theorems/68683c4d-f47c-4f74-a64a-e05596d92f7f
-- title:
--   Assumptions 2.1–2.3 and the standing assumptions of problem (1)
-- statement:
--   For the model of problem (1) and constants $D_{\mathcal X},L_f,L_\phi,\mu_g,S_g$, each condition below is a separate predicate; their conjunction (with $d\ge1$) is the hypothesis of Theorem 3.2.
--
--   1. **Regularity** (the paper's tacit conventions): $\underline X_i\le\bar X_i$; each $\phi_i$ is jointly measurable (`RegularData`), and for the run also $\partial\phi_i/\partial x_i$ on $[\underline X_i,\bar X_i]\times\mathbb R$ (`Regular`); $\phi_i(x_i,\xi_i)$ is integrable for $x\in\mathcal X$. A separate predicate asks that $f(\phi(x,\xi))$ be integrable for $x\in\mathcal X$.
--   2. **Assumption 2.1(a).** The coordinates of $\xi$ are independent.
--   3. **Standing assumption (p.1) and 2.1(b).** For almost every $\xi$, $\phi_i(\cdot,\xi_i)$ is non-decreasing on $[\underline X_i,\bar X_i]$.
--   4. **Assumption 2.1(c).** For every $i$, $\{\phi_i(g_i^{-1}(u_i),\xi_i),u_i\in\mathcal U_i\}$ is stochastically linear in midpoint.
--   5. **Assumption 2.2(a).** $\|x\|\le D_{\mathcal X}$ for all $x\in\mathcal X$.
--   6. **Assumption 2.2(b).** $f$ is convex, $L_f$-Lipschitz and continuously differentiable on $\mathbb R^d$.
--   7. **Assumption 2.2(c).** For almost every $\xi$, $\|\phi(x,\xi)-\phi(y,\xi)\|\le L_\phi\|x-y\|$ for $x,y\in\mathcal X$.
--   8. **Assumption 2.2(d).** For every $x\in\mathcal X$, for almost every $\xi$, $\phi(\cdot,\xi)$ is differentiable at $x$.
--   9. **Assumption 2.3(a).** Each $g_i$ is differentiable within $[\underline X_i,\bar X_i]$ with continuous derivative $g_i'$.
--   10. **Assumption 2.3(b).** $\mu_g>0$ and $g_i'(y)\ge\mu_g$ on $[\underline X_i,\bar X_i]$, i.e. $\nabla g(x)-\mu_gI\succeq0$ on $\mathcal X$.
--   11. **Assumption 2.3(c).** $|g_i'(x_i)-g_i'(y_i)|\le S_g\|x-y\|$ for $x,y\in\mathcal X$ and every $i$, i.e. $\|\nabla g(x)-\nabla g(y)\|\le S_g\|x-y\|$ for the spectral norm of the diagonal matrix.
--
--   **Formalization Note** "For any $\xi\in\Xi$" is read as "for $\mathbb P$-almost every $\xi$". Assumptions 2.1(b), 2.2(c) and 2.3 are imposed on $\mathcal X$ only; the variants on all of $\mathbb R^d$ are in `Model.GlobalModel`.
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, p.1; Assumptions 2.1, 2.2, 2.3, pp.8–10; Theorem 3.2, p.16

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_gradG
import Definitions.Def_StochHiddenConvex_StochLinMidpoint

open MeasureTheory ProbabilityTheory

namespace StochHiddenConvex

namespace Model

variable {d : ℕ} (M : Model d)

/-- Regularity of the data that the paper takes for granted (Chen, He, Hu & Ye,
arXiv:2205.01774v3, p.1 "ϕ(x, ξ) … random vector", (3) p.8, where `g = 𝔼ϕ` and `𝒰` are finite):
the box is a box (`X̲ᵢ ≤ X̄ᵢ`), each `ϕᵢ` is jointly measurable, and `ϕᵢ(xᵢ, ξᵢ)` is integrable
for every `x ∈ 𝒳`.

**Formalization Note.** The field's standing measurability and integrability conventions for a
random function whose expectation `g = 𝔼ϕ` is finite on `𝒳`. -/
def RegularData : Prop :=
  (∀ i, M.lo i ≤ M.hi i) ∧
  (∀ i, Measurable (Function.uncurry (M.phi i))) ∧
  (∀ x ∈ M.box, ∀ i, Integrable (fun s => M.phi i (x i) (s i)) M.P)

/-- Regularity of the random function that the paper takes for granted when it runs MSG
(Chen, He, Hu & Ye, arXiv:2205.01774v3, p.1 "ϕ(x, ξ) … random vector", (3) p.8, Algorithm 2
p.14): `RegularData`, and in addition the derivative `∂ϕᵢ/∂xᵢ` is jointly measurable on
`[X̲ᵢ, X̄ᵢ] × ℝ`.

**Formalization Note.** The paper takes expectations of `∇ϕ(x^t, ξ)` at the random iterates
`x^t ∈ 𝒳` without comment; joint measurability on `𝒳` (and nowhere else) is what makes these
random variables. -/
def Regular : Prop :=
  (∀ i, M.lo i ≤ M.hi i) ∧
  (∀ i, Measurable (Function.uncurry (M.phi i))) ∧
  (∀ i, Measurable (fun p : Set.Icc (M.lo i) (M.hi i) × ℝ => M.dphi i p.1 p.2)) ∧
  (∀ x ∈ M.box, ∀ i, Integrable (fun s => M.phi i (x i) (s i)) M.P)

/-- The objective's expectation exists on `𝒳`: `f(ϕ(x, ·))` is integrable for every `x ∈ 𝒳`
(arXiv:2205.01774v3, (1), p.1: `F(x) = 𝔼[f(ϕ(x, ξ))]` is a finite objective). -/
def IntegrableObjective : Prop :=
  ∀ x ∈ M.box, Integrable (fun s => M.f (M.phiVec x s)) M.P

/-- Assumption 2.1(a) (arXiv:2205.01774v3, p.8): the random vector `ξ` is coordinate-wise
independent. -/
def Assumption21a : Prop := iIndepFun (fun i (s : Fin d → ℝ) => s i) M.P

/-- The standing assumption of p.1 ("ϕ … is component-wise non-decreasing in x") and
Assumption 2.1(b) (arXiv:2205.01774v3, p.8): `ϕᵢ(xᵢ, ξᵢ)` is non-decreasing in `xᵢ` for any
`ξᵢ ∈ Ξᵢ` — here for `xᵢ ∈ [X̲ᵢ, X̄ᵢ]`.

**Formalization Note.** "For any `ξ ∈ Ξ`" is "for `ℙ`-almost every `ξ`" (`Ξ` a set of probability
one), and the domain is the box (the paper states none; see `MonotoneGlobal` for all of `ℝ`). -/
def MonotoneOnBox : Prop :=
  ∀ᵐ s ∂M.P, ∀ i, MonotoneOn (fun y => M.phi i y (s i)) (Set.Icc (M.lo i) (M.hi i))

/-- Assumption 2.1(c) (arXiv:2205.01774v3, p.9): for every `i`, the family
`{ϕᵢ(gᵢ⁻¹(uᵢ), ξᵢ), uᵢ ∈ 𝒰ᵢ}` is stochastically linear in midpoint; `Y(uᵢ)` is the law of
`ϕᵢ(gᵢ⁻¹(uᵢ), ξᵢ)`. -/
def Assumption21c : Prop :=
  ∀ i, StochLinMidpoint (Set.Icc (M.gc i (M.lo i)) (M.gc i (M.hi i)))
    (fun u => M.P.map (fun s => M.phi i (M.ginvC i u) (s i)))

/-- Assumption 2.2(a) (arXiv:2205.01774v3, p.9): `∀ x ∈ 𝒳, ‖x‖ ≤ D_𝒳`. -/
def Assumption22a (D : ℝ) : Prop := ∀ x ∈ M.box, ‖x‖ ≤ D

/-- Assumption 2.2(b) (arXiv:2205.01774v3, p.9): `f` is convex, `L_f`-Lipschitz continuous and
continuously differentiable.

**Formalization Note.** On all of `ℝ^d`. -/
def Assumption22b (Lf : ℝ) : Prop :=
  ConvexOn ℝ Set.univ M.f ∧ (∀ y z : Vec d, |M.f y - M.f z| ≤ Lf * ‖y - z‖) ∧
    ContDiff ℝ 1 M.f

/-- Assumption 2.2(c) (arXiv:2205.01774v3, p.9): `ϕ(x, ξ)` is `L_ϕ`-Lipschitz continuous in `x`
for any `ξ ∈ Ξ` — here for `x ∈ 𝒳` and `ℙ`-almost every `ξ`.

**Formalization Note.** See `LipschitzGlobal` for all of `ℝ^d`. -/
def Assumption22c (Lphi : ℝ) : Prop :=
  ∀ᵐ s ∂M.P, ∀ x ∈ M.box, ∀ y ∈ M.box,
    ‖M.phiVec x s - M.phiVec y s‖ ≤ Lphi * ‖x - y‖

/-- Assumption 2.2(d) (arXiv:2205.01774v3, p.9): "For any `ξ ∈ Ξ`, random function `ϕ(x, ξ)` is
differentiable in `x` almost surely", read as: for every `x ∈ 𝒳`, for `ℙ`-almost every `ξ`,
`ϕ(·, ξ)` is differentiable at `x` (the use on p.30 and p.44). -/
def Assumption22d : Prop :=
  ∀ x ∈ M.box, ∀ᵐ s ∂M.P, ∀ i, DifferentiableAt ℝ (fun y => M.phi i y (s i)) (x i)

/-- Assumption 2.3(a) (arXiv:2205.01774v3, p.10): `g : 𝒳 → 𝒰` is continuously differentiable on
`𝒳`. Since `g` is separable, this says each `gᵢ` is differentiable within `[X̲ᵢ, X̄ᵢ]` with a
continuous derivative `gᵢ′ = dg i`. -/
def Assumption23a : Prop :=
  ∀ i, (∀ y ∈ Set.Icc (M.lo i) (M.hi i),
      HasDerivWithinAt (M.gc i) (M.dg i y) (Set.Icc (M.lo i) (M.hi i)) y) ∧
    ContinuousOn (M.dg i) (Set.Icc (M.lo i) (M.hi i))

/-- Assumption 2.3(b) (arXiv:2205.01774v3, p.10): `∇g(x) − µ_g I` is positive semi-definite for
any `x ∈ 𝒳` and some constant `µ_g > 0`; with `∇g` diagonal, `gᵢ′(xᵢ) ≥ µ_g`. -/
def Assumption23b (μg : ℝ) : Prop :=
  0 < μg ∧ ∀ i, ∀ y ∈ Set.Icc (M.lo i) (M.hi i), μg ≤ M.dg i y

/-- Assumption 2.3(c) (arXiv:2205.01774v3, p.10): `‖∇g(x) − ∇g(y)‖ ≤ S_g ‖x − y‖` for any
`x, y ∈ 𝒳`. The spectral norm of the diagonal matrix `∇g(x) − ∇g(y)` is
`maxᵢ |gᵢ′(xᵢ) − gᵢ′(yᵢ)|`, so this is a bound on every diagonal entry. -/
def Assumption23c (Sg : ℝ) : Prop :=
  ∀ x ∈ M.box, ∀ y ∈ M.box, ∀ i, |M.dg i (x i) - M.dg i (y i)| ≤ Sg * ‖x - y‖

/-- The hypotheses of Theorem 3.2 (arXiv:2205.01774v3, p.16): the standing assumptions of p.1
and Assumptions 2.1, 2.2 and 2.3, all on `𝒳`, with the constants `D_𝒳, L_f, L_ϕ, µ_g, S_g`.

**Formalization Note.** The dimension is positive (`d ∈ ℕ⁺`, Preliminaries, p.8: `[N]` for
`N ∈ ℕ⁺`). The integrability of `f(ϕ(x, ·))` is not listed: it follows from `Regular` and the
Lipschitz continuity of `f` in Assumption 2.2(b). -/
structure Assumptions (D Lf Lphi μg Sg : ℝ) : Prop where
  dim_pos : 0 < d
  regular : M.Regular
  a21a : M.Assumption21a
  a21b : M.MonotoneOnBox
  a21c : M.Assumption21c
  a22a : M.Assumption22a D
  a22b : M.Assumption22b Lf
  a22c : M.Assumption22c Lphi
  a22d : M.Assumption22d
  a23a : M.Assumption23a
  a23b : M.Assumption23b μg
  a23c : M.Assumption23c Sg

end Model

end StochHiddenConvex


