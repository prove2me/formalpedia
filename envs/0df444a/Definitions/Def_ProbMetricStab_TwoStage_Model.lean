-- Prove2me | Definitions.Def_ProbMetricStab_TwoStage_Model
-- name    : ProbMetricStab_TwoStage_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:47.417464+00:00
-- url     : https://prove2.me/theorems/a3074329-111f-4ed8-bf34-e55e761397b2
-- title:
--   §3.1, pp. 10–11 — linear two-stage program (7)–(8): pos W, D, Φ, f₀, (A1), (A2)
-- statement:
--   This module fixes the linear two-stage stochastic program with fixed recourse of Section 3.1,
--
--   $$\min\Big\{cx+\int_\Xi q(\xi)y(\xi)\,\mu(d\xi):\ Wy(\xi)=h(\xi)-T(\xi)x,\ y(\xi)\ge0,\ x\in X\Big\}. \tag{7}$$
--
--   The data are $c\in\mathbb R^m$, a polyhedron $X\subseteq\mathbb R^m$, a polyhedron $\Xi\subseteq\mathbb R^s$, an $(r,\overline m)$-matrix $W$, and the vectors $q(\xi)\in\mathbb R^{\overline m}$, $h(\xi)\in\mathbb R^r$ and the $(r,m)$-matrix $T(\xi)$, which depend affine linearly on $\xi$. The module defines:
--
--   1. $\operatorname{pos}W=\{Wy:y\in\mathbb R^{\overline m}_+\}$ and $D=\{u\in\mathbb R^{\overline m}:\{z\in\mathbb R^r:W'z\le u\}\ne\emptyset\}$;
--   2. the second-stage value $\Phi(u,t)=\inf\{uy:Wy=t,\ y\ge0\}$ for $(u,t)\in\mathbb R^{\overline m}\times\mathbb R^r$, which is $+\infty$ for $t\notin\operatorname{pos}W$;
--   3. polyhedral cones in $\mathbb R^{\overline m}\times\mathbb R^r$: finite intersections of half-spaces $\{(u,t):\langle a_i,u\rangle+\langle b_i,t\rangle\le0\}$;
--   4. the integrand $f_0:\Xi\times\mathbb R^m\to\overline{\mathbb R}$,
--   $$f_0(\xi,x)=\begin{cases}cx+\Phi\big(q(\xi),h(\xi)-T(\xi)x\big), & h(\xi)-T(\xi)x\in\operatorname{pos}W,\ q(\xi)\in D,\\ +\infty, & \text{otherwise,}\end{cases}$$
--   so that (7) becomes problem (8), $\min\{\int_\Xi f_0(\xi,x)\,\mu(d\xi):x\in X\}$;
--   5. the standing assumptions: $X$ is a nonempty polyhedron and $\Xi$ is a polyhedron;
--   6. **(A1)** for each pair $(\xi,x)\in\Xi\times X$, $h(\xi)-T(\xi)x\in\operatorname{pos}W$ and $q(\xi)\in D$ (relatively complete recourse and dual feasibility);
--   7. **(A2)** $\mu\in\mathcal P(\Xi)$ has a finite second order moment, i.e. $\mu\in\mathcal P_2(\Xi)$.
--
--   The optimal value $v(\nu)$ and solution set $S(\nu)$ of (8) under a measure $\nu$ are the general ones of the Setting module applied to $f_0$.
--
--   **Formalization Note** $c x$ is the Euclidean inner product $\langle c,x\rangle$; the second-stage vectors $u$, $t$, $y$, $z$ are plain coordinate vectors `Fin k → ℝ`, and $T(\xi)x$ multiplies $T(\xi)$ with the coordinate vector of $x$. Affine dependence is encoded by affine maps $q,h,T$ defined on all of $\mathbb R^s$ (an affine map on the polyhedron $\Xi$ extends to one). $\Phi$ is an infimum in $\overline{\mathbb R}$ with the same body as the published `NumStochOpt.Bounds.recourseCost`, which could not be imported here (see the mission notes); its arguments are in the paper's order $\Phi(u,t)$. Index sets $\{1,\dots,k\}$ are `Fin k`, 0-based.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), pp. 10–11, (7), (8), (A1), (A2)

import Mathlib
import Definitions.Def_ProbMetricStab_TwoStage_Setting

open MeasureTheory Matrix
open scoped ENNReal

namespace ProbMetricStab.TwoStage

/-- `pos W = {W y : y ∈ ℝ^{m̄}₊}` (p. 11) for an `(r, m̄)`-matrix `W`. -/
def posW {r mbar : ℕ} (W : Matrix (Fin r) (Fin mbar) ℝ) : Set (Fin r → ℝ) :=
  {t | ∃ y : Fin mbar → ℝ, 0 ≤ y ∧ W *ᵥ y = t}

/-- `D = {u ∈ ℝ^{m̄} : {z ∈ ℝ^r : W′z ≤ u} ≠ ∅}` (p. 11). -/
def D {r mbar : ℕ} (W : Matrix (Fin r) (Fin mbar) ℝ) : Set (Fin mbar → ℝ) :=
  {u | ∃ z : Fin r → ℝ, W.transpose *ᵥ z ≤ u}

/-- `Φ(u, t) = inf {u y : W y = t, y ≥ 0}` for `(u, t) ∈ ℝ^{m̄} × ℝ^r` (p. 11), an extended real:
`+∞` when `t ∉ pos W`, possibly `−∞`. -/
noncomputable def Phi {r mbar : ℕ} (W : Matrix (Fin r) (Fin mbar) ℝ) (u : Fin mbar → ℝ)
    (t : Fin r → ℝ) : EReal :=
  ⨅ y ∈ {y : Fin mbar → ℝ | 0 ≤ y ∧ W *ᵥ y = t}, ((u ⬝ᵥ y : ℝ) : EReal)

/-- A polyhedral cone in `ℝ^{m̄} × ℝ^r`: a finite intersection of closed half-spaces through the
origin, `{(u, t) : ⟨a_i, u⟩ + ⟨b_i, t⟩ ≤ 0}`, `i ∈ Fin k`. -/
def IsPolyhedralCone {r mbar : ℕ} (K : Set ((Fin mbar → ℝ) × (Fin r → ℝ))) : Prop :=
  ∃ (k : ℕ) (a : Fin k → Fin mbar → ℝ) (b : Fin k → Fin r → ℝ),
    K = {p | ∀ i, a i ⬝ᵥ p.1 + b i ⬝ᵥ p.2 ≤ 0}

/-- The data of the linear two-stage program with fixed recourse (7), pp. 10–11:
`c ∈ ℝ^m`, `X ⊆ ℝ^m`, `Ξ ⊆ ℝ^s`, the `(r, m̄)`-matrix `W`, and `q(ξ) ∈ ℝ^{m̄}`, `h(ξ) ∈ ℝ^r`
and the `(r, m)`-matrix `T(ξ)`, which depend affine linearly on `ξ`. -/
structure Data (m s r mbar : ℕ) where
  c : EuclideanSpace ℝ (Fin m)
  X : Set (EuclideanSpace ℝ (Fin m))
  Ξ : Set (EuclideanSpace ℝ (Fin s))
  W : Matrix (Fin r) (Fin mbar) ℝ
  q : EuclideanSpace ℝ (Fin s) →ᵃ[ℝ] (Fin mbar → ℝ)
  h : EuclideanSpace ℝ (Fin s) →ᵃ[ℝ] (Fin r → ℝ)
  T : EuclideanSpace ℝ (Fin s) →ᵃ[ℝ] Matrix (Fin r) (Fin m) ℝ

namespace Data

variable {m s r mbar : ℕ} (P : Data m s r mbar)

/-- The standing assumptions of §3.1 (p. 11) together with those of §1 (p. 2): `X` is a nonempty
polyhedron and `Ξ` is a polyhedron (hence both are closed). -/
def Standing : Prop :=
  IsPolyhedron P.X ∧ P.X.Nonempty ∧ IsPolyhedron P.Ξ

/-- The second-stage right-hand side `h(ξ) − T(ξ) x`. -/
noncomputable def rhs (ξ : EuclideanSpace ℝ (Fin s)) (x : EuclideanSpace ℝ (Fin m)) : Fin r → ℝ :=
  P.h ξ - P.T ξ *ᵥ x.ofLp

open Classical in
/-- The integrand `f₀ : Ξ × ℝ^m → ℝ̄` (p. 11):
`f₀(ξ, x) = c x + Φ(q(ξ), h(ξ) − T(ξ) x)` if `h(ξ) − T(ξ) x ∈ pos W` and `q(ξ) ∈ D`,
and `f₀(ξ, x) = +∞` otherwise. -/
noncomputable def f0 (ξ : EuclideanSpace ℝ (Fin s)) (x : EuclideanSpace ℝ (Fin m)) : EReal :=
  if P.rhs ξ x ∈ posW P.W ∧ P.q ξ ∈ D P.W then
    ((inner ℝ P.c x : ℝ) : EReal) + Phi P.W (P.q ξ) (P.rhs ξ x)
  else ⊤

/-- Assumption (A1) (p. 11): for each `(ξ, x) ∈ Ξ × X`, `h(ξ) − T(ξ) x ∈ pos W` and `q(ξ) ∈ D`. -/
def A1 : Prop :=
  ∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, P.rhs ξ x ∈ posW P.W ∧ P.q ξ ∈ D P.W

/-- Assumption (A2) (p. 11): `μ ∈ 𝒫(Ξ)` has a finite second order moment, i.e. `μ ∈ 𝒫₂(Ξ)`. -/
def A2 (μ : Measure (EuclideanSpace ℝ (Fin s))) : Prop :=
  μ ∈ Pp P.Ξ 2

end Data

end ProbMetricStab.TwoStage


