-- Prove2me | Definitions.Def_TwoStageSRO_AsymOpt_Model
-- name    : TwoStageSRO_AsymOpt_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:03.316164+00:00
-- url     : https://prove2.me/theorems/5105e5bc-5844-4782-ad61-658cf77c2266
-- title:
--   §2, pp. 5–6 — two-stage stochastic LP (OPT): data, Ξ, ℓp balls, dual norm, extended-valued recourse Q, V*, v*, optimal set
-- statement:
--   A **two-stage stochastic linear optimization problem** is given by the data
--   $c\in\mathbb R^n$, $q\in\mathbb R^r$, $T\in\mathbb R^{m\times n}$, $W\in\mathbb R^{m\times r}$, $h^0\in\mathbb R^m$, $H\in\mathbb R^{m\times d}$, $G\in\mathbb R^{\tilde m\times d}$ and $g^0\in\mathbb R^{\tilde m}$. The right-hand side is the affine function $h(\zeta)=h^0+H\zeta$, and the polyhedron
--   $$\Xi=\{\zeta\in\mathbb R^d : G\zeta\ge g^0\}$$
--   (componentwise inequality) is a conservative superset of the support of the random vector $\xi$.
--
--   Norms are $\ell_p$-norms, $p\in[1,\infty]$: the closed ball is $B(\hat z,\epsilon)=\{z:\|z-\hat z\|\le\epsilon\}$ and the dual norm is $\|v\|_*=\sup\{u^\top v : \|u\|\le 1\}$.
--
--   Given a first-stage decision $x\in\mathbb R^n$ and a realization $\zeta\in\mathbb R^d$, the **second-stage cost** is the optimal value of a linear program,
--   $$Q(x,\zeta)=\inf_{y\in\mathbb R^r}\{q^\top y : Tx+Wy\ge h(\zeta)\}\in[-\infty,+\infty],$$
--   equal to $+\infty$ when no recourse decision $y$ is feasible. If $\mu$ is the law of $\xi$, the stochastic problem (OPT) has objective and optimal value
--   $$V^*(x)=c^\top x+\mathbb E_\mu[Q(x,\xi)],\qquad v^*=\inf_{x\in\mathbb R^n}V^*(x),$$
--   and its set of optimal first-stage decisions is the set of minimizers of $V^*$ over $\mathbb R^n$.
--
--   These are the objects every statement of the mission is about: the problem (OPT) whose optimal value and optimal decisions the data-driven problems are shown to recover.
--
--   **Formalization Note** Vectors are functions `Fin k → ℝ` and the $\ell_p$-norm is the norm of `PiLp p`, for a parameter `p : ℝ≥0∞` with `1 ≤ p`. Every optimal value is an infimum in `EReal`, so $Q=+\infty$ for an infeasible and $-\infty$ for an unbounded recourse problem; no attainment is assumed. The expectation is the referenced definition `DupacovaWets.Consistency.expect`: $+\infty$ if $\int Q(x,\cdot)^+\,d\mu=\infty$, and $\int Q^+\,d\mu-\int Q^-\,d\mu$ otherwise. When $v^*$ is finite (condition [A2]) this is the usual expectation of $Q(x,\xi)$: then the dual polyhedron $D$ is nonempty, $Q(x,\cdot)$ is bounded below by an affine function of $\xi$, and $\mathbb E\|\xi\|<\infty$ makes $Q^-$ integrable.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, pp. 5–6, Notation and §2, (OPT)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 6, §2.
The data of a two-stage stochastic linear optimization problem:
the first-stage cost `c ∈ ℝⁿ`, the second-stage cost `q ∈ ℝʳ`, the technology matrix
`T ∈ ℝ^{m×n}`, the recourse matrix `W ∈ ℝ^{m×r}`, the affine right-hand side
`h(ξ) = h⁰ + Hξ` (`h0 ∈ ℝᵐ`, `H ∈ ℝ^{m×d}`), and the polyhedron
`Ξ = {ζ ∈ ℝᵈ : Gζ ≥ g⁰}` (`G ∈ ℝ^{m̃×d}`, `g0 ∈ ℝ^{m̃}`; the paper's `m̃` is `mt`). -/
structure Model (n d r m mt : ℕ) where
  c : Fin n → ℝ
  q : Fin r → ℝ
  T : Matrix (Fin m) (Fin n) ℝ
  W : Matrix (Fin m) (Fin r) ℝ
  h0 : Fin m → ℝ
  H : Matrix (Fin m) (Fin d) ℝ
  G : Matrix (Fin mt) (Fin d) ℝ
  g0 : Fin mt → ℝ

variable {n d r m mt : ℕ}

/-- arXiv:1907.07142v4, p. 6: the affine right-hand side `h(ζ) = h⁰ + Hζ`. -/
def Model.h (M : Model n d r m mt) (ζ : Fin d → ℝ) : Fin m → ℝ := M.h0 + M.H *ᵥ ζ

/-- arXiv:1907.07142v4, p. 6: the polyhedron `Ξ = {ζ ∈ ℝᵈ : Gζ ≥ g⁰}` (componentwise order). -/
def Xi (M : Model n d r m mt) : Set (Fin d → ℝ) := {ζ | M.g0 ≤ M.G *ᵥ ζ}

/-- arXiv:1907.07142v4, p. 5, Notation: the closed ball `B(ẑ, ε) = {z : ‖z − ẑ‖ ≤ ε}` for the
`ℓp`-norm `‖·‖`, `p ∈ [1, ∞]`.

**Formalization Note** The paper allows "any ℓp-norm"; the exponent `p` is a parameter, and the norm
is that of `PiLp p`, applied through `WithLp.toLp p`. -/
def ball (p : ℝ≥0∞) [Fact (1 ≤ p)] {k : ℕ} (zhat : Fin k → ℝ) (ε : ℝ) : Set (Fin k → ℝ) :=
  {z | ‖WithLp.toLp p (z - zhat)‖ ≤ ε}

/-- arXiv:1907.07142v4, p. 5, Notation: the dual norm `‖v‖_* = sup {uᵀv : ‖u‖ ≤ 1}` of the
`ℓp`-norm. -/
noncomputable def dualNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  sSup ((fun u => u ⬝ᵥ v) '' {u : Fin k → ℝ | ‖WithLp.toLp p u‖ ≤ 1})

/-- arXiv:1907.07142v4, p. 6: the second-stage cost
`Q(x, ζ) = min_{y ∈ ℝʳ} {qᵀy : Tx + Wy ≥ h(ζ)}`.

**Formalization Note** "minimize" is an infimum in `EReal`: `Q = +∞` when no recourse decision is
feasible (the paper's "standard convention", p. 6), and `Q = −∞` when the recourse problem is
unbounded below. -/
noncomputable def Q (M : Model n d r m mt) (x : Fin n → ℝ) (ζ : Fin d → ℝ) : EReal :=
  sInf {v : EReal | ∃ y : Fin r → ℝ, M.h ζ ≤ M.T *ᵥ x + M.W *ᵥ y ∧ v = ((M.q ⬝ᵥ y : ℝ) : EReal)}

/-- arXiv:1907.07142v4, p. 6, (OPT): the objective `V*(x) = cᵀx + E[Q(x, ξ)]`, where `μ` is the law of
`ξ` on `ℝᵈ`.

**Formalization Note** `E[Q(x, ξ)]` is the extended expectation `DupacovaWets.Consistency.expect`:
`+∞` if `∫ Q(x,·)⁺ dμ = ∞`, and `∫ Q⁺ dμ − ∫ Q⁻ dμ` in `EReal` otherwise (lower Lebesgue integrals). -/
noncomputable def Vstar (M : Model n d r m mt) (μ : Measure (Fin d → ℝ)) (x : Fin n → ℝ) : EReal :=
  ((M.c ⬝ᵥ x : ℝ) : EReal) + DupacovaWets.Consistency.expect μ (Q M x)

/-- arXiv:1907.07142v4, p. 6, (OPT): the optimal value `v* = inf_{x ∈ ℝⁿ} V*(x)` in `EReal`. -/
noncomputable def vStar (M : Model n d r m mt) (μ : Measure (Fin d → ℝ)) : EReal :=
  ⨅ x, Vstar M μ x

/-- arXiv:1907.07142v4, p. 12, [A3]: the set of optimal first-stage decisions of (OPT), i.e. the
minimizers of `V*` over `ℝⁿ`. -/
def optSet (M : Model n d r m mt) (μ : Measure (Fin d → ℝ)) : Set (Fin n → ℝ) :=
  {x | IsMinOn (Vstar M μ) Set.univ x}

end TwoStageSRO.AsymOpt


