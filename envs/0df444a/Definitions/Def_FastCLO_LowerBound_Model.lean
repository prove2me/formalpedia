-- Prove2me | Definitions.Def_FastCLO_LowerBound_Model
-- name    : FastCLO_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:25.698194+00:00
-- url     : https://prove2.me/theorems/312c8e00-57ac-4746-8b36-5d37a33448cf
-- title:
--   The CLO instance: polytope Z = {Az ≤ b}, extreme points Z∠, f*(x) = E[Y | X = x], optimal set Z*, gap Δ, noise condition (7), policies and regret (2)
-- statement:
--   This file sets up the contextual linear optimization (CLO) model of Hu, Kallus and Mao.
--
--   A **polytope** $\mathcal Z = \{z \in \mathbb R^d : Az \le b\}$ is given by finitely many rows $a_i \in \mathbb R^d$ and right-hand sides $b_i$, together with a radius $B > 0$ such that $\mathcal Z$ is nonempty and $\sup_{z\in\mathcal Z}\|z\| \le B$. Its set of extreme points is written $\mathcal Z^\angle$.
--
--   An **instance** is a pair $(\mu, \kappa)$: the law $\mu = \mathbb P_X$ of a covariate $X \in \mathbb R^p$ (a probability measure) and the conditional law $\kappa(x)$ of the cost vector $Y \in \mathbb R^d$ given $X = x$ (a Markov kernel), with $\|Y\| \le 1$ almost surely under every $\kappa(x)$. From it one defines
--   1. the regression function $f^*(x) = \mathbb E[Y \mid X = x] = \int y \, \kappa(x)(dy)$;
--   2. the law $\mu \otimes \kappa$ of $(X, Y)$ and the law $(\mu\otimes\kappa)^n$ of a sample $\mathcal D = ((X_1,Y_1),\dots,(X_n,Y_n))$ of $n$ i.i.d. draws;
--   3. the optimal value $\inf_{z\in\mathcal Z} f^*(x)^\top z$ and the optimal set $\mathcal Z^*(x) = \arg\min_{z\in\mathcal Z} f^*(x)^\top z$;
--   4. the gap of Assumption 2,
--   $$\Delta(x) = \inf_{z\in\mathcal Z^\angle\setminus\mathcal Z^*(x)} f^*(x)^\top z - \inf_{z\in\mathcal Z} f^*(x)^\top z \quad\text{if } \mathcal Z^*(x) \ne \mathcal Z, \qquad \Delta(x) = 0 \text{ otherwise};$$
--   5. the noise condition (7) with parameters $\alpha, \gamma$:
--   $$\mathbb P_X\big(0 < \Delta(X) \le \delta\big) \le (\gamma\delta/B)^\alpha \qquad \forall \delta > 0;$$
--   6. policies, i.e. maps $\pi : \mathbb R^p \to \mathcal Z^\angle$;
--   7. the regret of a data-driven policy $\mathcal D \mapsto \hat\pi_{\mathcal D}$,
--   $$\mathrm{Regret}(\hat\pi) = \mathbb E_{\mathcal D}\,\mathbb E_X\Big[f^*(X)^\top\hat\pi_{\mathcal D}(X) - \min_{z\in\mathcal Z} f^*(X)^\top z\Big].$$
--
--   These objects are the common vocabulary of every statement in the mission.
--
--   **Formalization Note** The instance is given as $(\mu,\kappa)$ rather than as a joint law; every joint law on $\mathbb R^p\times\mathbb R^d$ disintegrates this way. The regret is measured against the optimal value, which equals the paper's $\mathbb E_{\mathcal D}\mathbb E_X[f^*(X)^\top(\hat\pi(X)-\pi^*(X))]$ because $\pi^*(x)\in\mathcal Z^*(x)$. Infima are real `sInf`s over nonempty bounded sets: $\mathcal Z$ is nonempty and bounded, and $\mathcal Z^\angle\setminus\mathcal Z^*(x)$ is nonempty whenever $\mathcal Z^*(x)\ne\mathcal Z$ (if every extreme point were optimal, every point of $\mathcal Z = \mathrm{conv}\,\mathcal Z^\angle$ would be). The power $(\gamma\delta/B)^\alpha$ is the real power of a nonnegative base, with $0^0 = 1$.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Eq. (1)–(3), p. 1–2 (standing assumptions on Z and Y, p. 2), Assumption 2 and Eq. (7), p. 8

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FastCLO.LowerBound

/-- Euclidean space `ℝ^k` with its inner product and norm. Covariates live in `Vec p`,
cost vectors and decisions in `Vec d` (Hu, Kallus, Mao, arXiv:2011.03030v3, §1, p. 1). -/
abbrev Vec (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The decision polytope `Z = {z : Az ≤ b}` of eq. (1) (arXiv:2011.03030v3, p. 1), bundled with the
standing assumptions of p. 2: `Z` is a nonempty polytope with `sup_{z∈Z} ‖z‖ ≤ B`.

Formalization Note: `A` is given by its rows `a_i`; `B > 0` is implicit on the page
(Assumption 2 divides by `B`). -/
structure Polytope (d : ℕ) where
  /-- number of linear constraints -/
  m : ℕ
  /-- the rows `a_i` of the constraint matrix `A` -/
  A : Fin m → Vec d
  /-- the right-hand side `b` -/
  b : Fin m → ℝ
  /-- the bound `B` on the norm of feasible decisions -/
  B : ℝ
  hB : 0 < B
  nonempty : {z : Vec d | ∀ i, ⟪A i, z⟫_ℝ ≤ b i}.Nonempty
  bounded : ∀ z ∈ {z : Vec d | ∀ i, ⟪A i, z⟫_ℝ ≤ b i}, ‖z‖ ≤ B

variable {p d : ℕ}

/-- The feasible set `Z = {z : Az ≤ b}` (eq. (1), p. 1). -/
def Polytope.Z (P : Polytope d) : Set (Vec d) := {z | ∀ i, ⟪P.A i, z⟫_ℝ ≤ P.b i}

/-- The set `Z∠` of extreme points of `Z` (p. 2). -/
def Polytope.ext (P : Polytope d) : Set (Vec d) := Set.extremePoints ℝ P.Z

/-- A CLO instance (p. 1–2): the law `μ` of the covariate `X` and the conditional law `κ x` of the
cost vector `Y` given `X = x`, with `‖Y‖ ≤ 1` almost surely (the standing assumption
`Y ∈ 𝒴 = {y : ‖y‖ ≤ 1}` of p. 2).

Formalization Note: the paper speaks of a joint law of `(X, Y)`; every such law on `ℝ^p × ℝ^d`
disintegrates as `μ ⊗ κ`, so giving `(μ, κ)` is no restriction. -/
structure Instance (p d : ℕ) where
  /-- the law `P_X` of `X` -/
  μ : Measure (Vec p)
  /-- the conditional law of `Y` given `X = x` -/
  κ : Kernel (Vec p) (Vec d)
  [isProb : IsProbabilityMeasure μ]
  [isMarkov : IsMarkovKernel κ]
  boundedY : ∀ x, κ x {y | 1 < ‖y‖} = 0

attribute [instance] Instance.isProb Instance.isMarkov

/-- `f*(x) = E[Y | X = x]`, the mean of the conditional law (p. 1). -/
noncomputable def Instance.fstar (I : Instance p d) (x : Vec p) : Vec d := ∫ y, y ∂(I.κ x)

/-- The joint law of `(X, Y)`. -/
noncomputable def Instance.joint (I : Instance p d) : Measure (Vec p × Vec d) := I.μ ⊗ₘ I.κ

/-- The law of the data `D = ((X_1, Y_1), …, (X_n, Y_n))`: `n` i.i.d. draws from the joint law (p. 2). -/
noncomputable def Instance.sample (I : Instance p d) (n : ℕ) : Measure (Fin n → Vec p × Vec d) :=
  Measure.pi fun _ => I.joint

/-- The optimal value `inf_{z∈Z} f*(x)ᵀz`.

Formalization Note: a real `sInf`; the set is nonempty (`P.nonempty`) and bounded (`‖z‖ ≤ B`,
`‖f*(x)‖ ≤ 1`), so this is the true infimum (in fact a minimum). -/
noncomputable def optVal (P : Polytope d) (I : Instance p d) (x : Vec p) : ℝ :=
  sInf ((fun z => ⟪I.fstar x, z⟫_ℝ) '' P.Z)

/-- The optimal set `Z*(x) = argmin_{z∈Z} f*(x)ᵀz` (p. 2). -/
def Zstar (P : Polytope d) (I : Instance p d) (x : Vec p) : Set (Vec d) :=
  {z ∈ P.Z | ∀ z' ∈ P.Z, ⟪I.fstar x, z⟫_ℝ ≤ ⟪I.fstar x, z'⟫_ℝ}

/-- The suboptimality gap `Δ(x)` of Assumption 2 (p. 8):
`Δ(x) = inf_{z∈Z∠∖Z*(x)} f*(x)ᵀz − inf_{z∈Z} f*(x)ᵀz` if `Z*(x) ≠ Z`, and `Δ(x) = 0` otherwise.

Formalization Note: real `sInf`. The set `Z∠ ∖ Z*(x)` is bounded, and it is nonempty whenever
`Z*(x) ≠ Z` (if every extreme point were optimal, every point of `Z = conv Z∠` would be). -/
noncomputable def gap (P : Polytope d) (I : Instance p d) (x : Vec p) : ℝ :=
  if Zstar P I x = P.Z then 0
  else sInf ((fun z => ⟪I.fstar x, z⟫_ℝ) '' (P.ext \ Zstar P I x)) - optVal P I x

/-- The noise condition (7) of Assumption 2 (p. 8): `P_X(0 < Δ(X) ≤ δ) ≤ (γδ/B)^α` for all `δ > 0`.

Formalization Note: `(γδ/B)^α` is `Real.rpow`; with `0 ^ 0 = 1` at `α = 0`, as on the page.
The page's `α, γ ≥ 0` are hypotheses of the theorems that use this predicate. -/
def NoiseCond (P : Polytope d) (I : Instance p d) (α γ : ℝ) : Prop :=
  ∀ δ > 0, I.μ {x | 0 < gap P I x ∧ gap P I x ≤ δ} ≤ ENNReal.ofReal ((γ * δ / P.B) ^ α)

/-- A policy `π : ℝ^p → Z∠` (p. 2: policies take values in the extreme points). -/
def IsPolicy (P : Polytope d) (π : Vec p → Vec d) : Prop := ∀ x, π x ∈ P.ext

/-- The regret (2) (p. 2) of a data-driven policy `D ↦ π̂_D`:
`E_D E_X[f*(X)ᵀ π̂_D(X) − min_{z∈Z} f*(X)ᵀz]`, with `D ∼ (P_{X,Y})^n`.

Formalization Note: measured against the optimal value; this equals the paper's
`E_D E_X[f*(X)ᵀ(π̂(X) − π*(X))]` because `π*(x) ∈ Z*(x)`. -/
noncomputable def regret (P : Polytope d) (I : Instance p d) (n : ℕ)
    (alg : (Fin n → Vec p × Vec d) → Vec p → Vec d) : ℝ :=
  ∫ D, ∫ x, (⟪I.fstar x, alg D x⟫_ℝ - optVal P I x) ∂I.μ ∂(I.sample n)

end FastCLO.LowerBound


