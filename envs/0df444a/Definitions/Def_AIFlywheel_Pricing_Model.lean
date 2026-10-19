-- Prove2me | Definitions.Def_AIFlywheel_Pricing_Model
-- name    : AIFlywheel_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:05.188567+00:00
-- url     : https://prove2.me/theorems/b56a5764-9db7-49b4-8bfd-fb8471c67748
-- title:
--   §3–§4.1: the two-period AI-flywheel contracting and pricing model
-- statement:
--   The model describes a firm that sells a product in two periods while hiring a provider to develop its algorithm. Effort costs the provider $\kappa>0$. At data size $d$, effort and shirking give high accuracy with probabilities $\pi_w(d)$ and $\pi_s(d)$. Accuracy is either $\alpha_h$ or $\alpha_\ell$, with $0<\alpha_\ell<\alpha_h$.
--
--   A unit-mass market has uniformly distributed buyer sensitivity. If the product collects $\delta\in[0,\nu]$ units of data from buyers at acquisition capacity $\nu$, its revenue is
--   $$
--   R_\nu(\delta,\alpha)=\alpha\frac{\delta}{\nu}\left(1-\frac{\delta}{\nu}\right).
--   $$
--   The data impact is $\rho(d)=(\pi_w(d)-\pi_s(d))/\pi_w(d)$. The second-period myopic value $J_{2b}$ is the supremum of this revenue over $[0,\nu]$.
--
--   A plan chooses nonnegative accuracy-contingent payments $x_{1h},x_{1\ell},x_{2h},x_{2\ell}$ and first-period data quantities $\delta_{1h},\delta_{1\ell}\in[0,\nu]$. Feasibility consists of the two incentive constraints (7) and (9), with the provider's continuation payoff defined by (8). The firm's objective is (6), using the high- and low-accuracy branches of (3)–(5). An optimum maximizes that objective over every feasible plan. The first-best problem fixes all four payments at $\kappa$, drops both incentive constraints, and maximizes over the two data quantities.
--
--   The model supplies the shared definitions for the paper's contract, first-best benchmark, and comparison results.
--
--   **Formalization Note.** Learning curves are functions on $\mathbb R$ whose assumptions apply on $[d_{\min},d_{\max}]$. The standing assumptions require $d_{\min}>0$, $d_{\min}\le d_0$, $\nu>0$, $d_0+\nu\le d_{\max}$, $\kappa>0$, $0<\alpha_\ell<\alpha_h$, $0\le\pi_s<\pi_w<1$, strictly increasing concave $\pi_w$ and $\pi_s$ (both learning curves are increasing concave mappings, pp. 5 and 7–8), differentiable learning curves, and convex $1/\rho$. The positive low accuracy and strict upper probability bound make the stated uniqueness claims well posed. The paper's effort preference motivates Problem (6) and is not a separate constraint.
-- source:
--   Gurkan & de Véricourt, Contracting, Pricing and Data Collection under the AI Flywheel Effect, ESMT Working Paper 20-01 (R3), August 17, 2021, pp. 7–13 (PDF 8–14), §3, equations (1)–(9), §4.1.

import Mathlib

namespace AIFlywheel.Pricing

/-- The learning curves and parameters of the two-period contracting model, §3. -/
structure Params where
  pw : ℝ → ℝ
  ps : ℝ → ℝ
  αh : ℝ
  αl : ℝ
  κ : ℝ
  ν : ℝ
  d0 : ℝ
  dmin : ℝ
  dmax : ℝ

/-- Equation (1): the relative effect of effort on high accuracy. -/
noncomputable def dataImpact (P : Params) (d : ℝ) : ℝ :=
  (P.pw d - P.ps d) / P.pw d

/-- The domain, probability, learning-curve, and convexity conditions of §3. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.dmin ∧ P.dmin ≤ P.d0 ∧ 0 < P.ν ∧ P.d0 + P.ν ≤ P.dmax ∧
  0 < P.κ ∧ 0 < P.αl ∧ P.αl < P.αh ∧
  (∀ d ∈ Set.Icc P.dmin P.dmax, 0 ≤ P.ps d ∧ P.ps d < P.pw d ∧ P.pw d < 1) ∧
  StrictMonoOn P.pw (Set.Icc P.dmin P.dmax) ∧
  ConcaveOn ℝ (Set.Icc P.dmin P.dmax) P.pw ∧
  StrictMonoOn P.ps (Set.Icc P.dmin P.dmax) ∧
  ConcaveOn ℝ (Set.Icc P.dmin P.dmax) P.ps ∧
  DifferentiableOn ℝ P.pw (Set.Icc P.dmin P.dmax) ∧
  DifferentiableOn ℝ P.ps (Set.Icc P.dmin P.dmax) ∧
  ConvexOn ℝ (Set.Icc P.dmin P.dmax) (fun d => 1 / dataImpact P d)

/-- The standard-uniform quantile on its support. -/
def uniformQuantile (u : ℝ) : ℝ := u

/-- The uniform-demand revenue Rν(δ,α) from §3.1. -/
noncomputable def revenue (ν δ α : ℝ) : ℝ :=
  α * (δ / ν) * uniformQuantile (1 - δ / ν)

/-- The standard-uniform virtual value φ(v). -/
noncomputable def virtualValue (v : ℝ) : ℝ := v - (1 - v) / 1

/-- The zero of φ, written φ⁻¹(0) in Lemma 1. -/
noncomputable def phiInvZero : ℝ := 1 / 2

/-- The normalized myopic revenue τ from Lemma 1. -/
noncomputable def tau : ℝ := phiInvZero * (1 - phiInvZero)

/-- The myopic data quantity δᴹ from Lemma 1. -/
noncomputable def deltaM (ν : ℝ) : ℝ := ν * (1 - phiInvZero)

/-- The second-period value J₂ᵦ of equation (2). -/
noncomputable def J2b (ν α : ℝ) : ℝ :=
  sSup ((fun δ => revenue ν δ α) '' Set.Icc 0 ν)

/-- Payments and first-period data choices of Problem (6). -/
structure Plan where
  x1h : ℝ
  x1l : ℝ
  x2h : ℝ
  x2l : ℝ
  δ1h : ℝ
  δ1l : ℝ

/-- The provider's continuation profit Jₚ(d₀), equation (8). -/
noncomputable def providerCont (P : Params) (s : Plan) : ℝ :=
  P.pw (P.d0 + s.δ1l) * s.x2h +
    (1 - P.pw (P.d0 + s.δ1l)) * s.x2l - P.κ

/-- Limited liability, data bounds, and incentive constraints (7) and (9). -/
def Plan.Feasible (P : Params) (s : Plan) : Prop :=
  0 ≤ s.x1h ∧ 0 ≤ s.x1l ∧ 0 ≤ s.x2h ∧ 0 ≤ s.x2l ∧
  s.δ1h ∈ Set.Icc 0 P.ν ∧ s.δ1l ∈ Set.Icc 0 P.ν ∧
  P.pw P.d0 * s.x1h + (1 - P.pw P.d0) * (s.x1l + providerCont P s) - P.κ ≥
    P.ps P.d0 * s.x1h + (1 - P.ps P.d0) * (s.x1l + providerCont P s) ∧
  providerCont P s ≥
    P.ps (P.d0 + s.δ1l) * s.x2h +
      (1 - P.ps (P.d0 + s.δ1l)) * s.x2l

/-- Low-accuracy branch of J₂ₐ, equation (3). -/
noncomputable def J2aLow (P : Params) (d1 x2h x2l : ℝ) : ℝ :=
  P.pw d1 * (J2b P.ν P.αh - x2h) +
    (1 - P.pw d1) * (J2b P.ν P.αl - x2l)

/-- Problem (6)'s objective, using the two branches of (3)–(5). -/
noncomputable def objective (P : Params) (s : Plan) : ℝ :=
  P.pw P.d0 * (revenue P.ν s.δ1h P.αh + J2b P.ν P.αh - s.x1h) +
    (1 - P.pw P.d0) *
      (revenue P.ν s.δ1l P.αl +
        J2aLow P (P.d0 + s.δ1l) s.x2h s.x2l - s.x1l)

/-- A global optimum of Problem (6)–(9). -/
def IsOptimal (P : Params) (s : Plan) : Prop :=
  s.Feasible P ∧ ∀ s' : Plan, s'.Feasible P → objective P s' ≤ objective P s

/-- First-best objective: all payments are κ and incentive constraints are dropped. -/
noncomputable def fbObjective (P : Params) (δ1h δ1l : ℝ) : ℝ :=
  objective P ⟨P.κ, P.κ, P.κ, P.κ, δ1h, δ1l⟩

/-- The one-variable objective in Proposition 1 after optimizing the payments. -/
noncomputable def reducedMoralObjective (P : Params) (δ : ℝ) : ℝ :=
  (1 - P.pw P.d0) *
    (revenue P.ν δ P.αl + P.pw (P.d0 + δ) * (P.αh - P.αl) * tau) -
    P.κ / dataImpact P (P.d0 + δ)

/-- The one-variable objective in Proposition 2. -/
noncomputable def reducedFBObjective (P : Params) (δ : ℝ) : ℝ :=
  revenue P.ν δ P.αl + P.pw (P.d0 + δ) * (P.αh - P.αl) * tau

/-- A global optimum of the first-best problem of §4.1. -/
def IsFBOptimal (P : Params) (δ1h δ1l : ℝ) : Prop :=
  δ1h ∈ Set.Icc 0 P.ν ∧ δ1l ∈ Set.Icc 0 P.ν ∧
  ∀ e1 ∈ Set.Icc 0 P.ν, ∀ e2 ∈ Set.Icc 0 P.ν,
    fbObjective P e1 e2 ≤ fbObjective P δ1h δ1l

end AIFlywheel.Pricing


