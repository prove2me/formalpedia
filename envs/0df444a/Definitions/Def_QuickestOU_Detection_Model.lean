-- Prove2me | Definitions.Def_QuickestOU_Detection_Model
-- name    : QuickestOU_Detection_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:42.616692+00:00
-- url     : https://prove2.me/theorems/a063975a-9f4d-4b5a-8b5c-0adaf47af1c9
-- title:
--   §3–§9 — no-change OU flow, odds, optimal stopping boundary, and integral equation
-- statement:
--   Fix coefficients $\beta_0,\beta_1\in\mathbb R$, $\lambda>0$, and $c>0$, with $\beta_0\ne\beta_1$. A Brownian driver $B$ under a no-change probability law defines an Ornstein–Uhlenbeck flow $X^x$ with initial state $x$ and drift $-\beta_0X$. The posterior-odds path functional is
--
--   $$\Phi_t^{\varphi,x}=e^{E_t^x}\left(\varphi+\lambda\int_0^t e^{-E_s^x}\,ds\right),\quad E_t^x=(\lambda-\delta/2)t+(\delta/2)\left((X_t^x)^2-x^2+\kappa\int_0^t(X_s^x)^2\,ds\right),$$
--
--   where $\delta=\beta_0-\beta_1$ and $\kappa=\beta_0+\beta_1$. The value $\widehat V(\varphi,x)$ is the infimum, over stopping times of the observation, of the expected discounted running cost $e^{-\lambda t}(\Phi_t-\lambda/c)$. Its zero set $D$ determines $b(x)=\inf\{\varphi\ge0:\widehat V(\varphi,x)=0\}$. The first-entry rules $\tau_D$ and $\tau_b$ and the expectation form of the integral equation (9.5) are also defined here.
--
--   These definitions provide the shared no-change model for the boundary and value theorems.
--
--   **Formalization Note** Brownian paths are represented by a continuous, pointwise measurable version. The OU flow uses the integration-by-parts form of (5.15). Signed expectations use separate nonnegative extended integrals; an empty fibre in $b$ has Lean's real-infimum value zero.
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; pp. 10–26, (4.8), (5.15), (7.2)–(7.7), (9.4)–(9.7), (9.12)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- The coefficients in the OU quickest-detection problem, with levels zero and diffusion one. -/
structure Params where
  beta0 : ℝ
  beta1 : ℝ
  lam : ℝ
  c : ℝ

/-- The parameter conditions used throughout the nontrivial cases of the paper. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.lam ∧ 0 < P.c ∧ P.beta0 ≠ P.beta1

def Params.delta (P : Params) : ℝ := P.beta0 - P.beta1
def Params.kappa (P : Params) : ℝ := P.beta0 + P.beta1

/-- A standard real Brownian process with a pathwise continuous, pointwise measurable version. -/
structure Driver {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) : Prop where
  prob : IsProbabilityMeasure μ
  brownian : IsBrownianReal B μ
  cont : ∀ ω, Continuous (fun t => B t ω)
  meas : ∀ t, Measurable (B t)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The no-change OU flow, using the integration-by-parts form of (5.15). -/
noncomputable def ouFlow (P : Params) (B : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-P.beta0 * (t : ℝ)) * x + B t ω -
    P.beta0 * ∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp (-P.beta0 * ((t : ℝ) - s)) * B s.toNNReal ω

/-- The exponent in the pathwise odds formula (9.12). -/
noncomputable def oddsExp (P : Params) (X : ℝ≥0 → ℝ) (x : ℝ)
    (t : ℝ≥0) : ℝ :=
  (P.lam - P.delta / 2) * (t : ℝ) + P.delta / 2 *
    (X t ^ 2 - x ^ 2 + P.kappa * ∫ s in (0 : ℝ)..(t : ℝ), X s.toNNReal ^ 2)

/-- Posterior odds as a functional of the observed path, formula (9.12). -/
noncomputable def odds (P : Params) (X : ℝ≥0 → ℝ) (x phi : ℝ)
    (t : ℝ≥0) : ℝ :=
  Real.exp (oddsExp P X x t) *
    (phi + P.lam * ∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp (-(oddsExp P X x s.toNNReal)))

noncomputable def phiPath (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (phi x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  odds P (fun s => ouFlow P B x s ω) x phi t

/-- The natural filtration of the Brownian observation under the no-change law. -/
noncomputable def natB (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ t, Measurable (B t)) : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural B (fun t => (hB t).stronglyMeasurable)

/-- Times before a possibly infinite stopping time. -/
def beforeStop (τ : Ω → WithTop ℝ≥0) (ω : Ω) : Set ℝ :=
  {t | 0 ≤ t ∧ ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) < τ ω}

/-- Nonnegative part of the discounted running cost in (4.8). -/
noncomputable def payoffPos (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (phi x : ℝ) (τ : Ω → WithTop ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in beforeStop τ ω,
    ENNReal.ofReal (Real.exp (-P.lam * t) * phiPath P B phi x t.toNNReal ω)
      ∂volume ∂μ

/-- The bounded negative part of the discounted running cost in (4.8). -/
noncomputable def payoffNeg (P : Params) (μ : Measure Ω)
    (τ : Ω → WithTop ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in beforeStop τ ω,
    ENNReal.ofReal (Real.exp (-P.lam * t) * (P.lam / P.c))
      ∂volume ∂μ

/-- Expected discounted running cost, with its two parts kept separate. -/
noncomputable def payoff (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (phi x : ℝ) (τ : Ω → WithTop ℝ≥0) : EReal :=
  (payoffPos P B μ phi x τ : EReal) - (payoffNeg P μ τ : EReal)

/-- The optimal stopping value (4.8), over stopping times of the observation. -/
noncomputable def Vhat (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (hB : ∀ t, Measurable (B t)) (phi x : ℝ) : EReal :=
  sInf {v | ∃ τ : Ω → WithTop ℝ≥0,
    IsStoppingTime (natB B hB) τ ∧ v = payoff P B μ phi x τ}

noncomputable def VhatR (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (hB : ∀ t, Measurable (B t)) (phi x : ℝ) : ℝ :=
  (Vhat P B μ hB phi x).toReal

/-- The stopping region D of (7.2). -/
def stopSet (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (hB : ∀ t, Measurable (B t)) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ Vhat P B μ hB q.1 q.2 = 0}

/-- The stopping boundary (7.7). Its real infimum is zero if the fibre is empty. -/
noncomputable def bnd (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (hB : ∀ t, Measurable (B t)) (x : ℝ) : ℝ :=
  sInf {phi : ℝ | 0 ≤ phi ∧ Vhat P B μ hB phi x = 0}

/-- First entry into D, as in (7.3). -/
noncomputable def entryD (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (hB : ∀ t, Measurable (B t)) (phi x : ℝ) :
    Ω → WithTop ℝ≥0 :=
  hittingAfter (fun t ω => (phiPath P B phi x t ω, ouFlow P B x t ω))
    (stopSet P B μ hB) 0

/-- First crossing of a proposed boundary, as in (9.7). -/
noncomputable def tauB (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (a : ℝ → ℝ) (phi x : ℝ) : Ω → WithTop ℝ≥0 :=
  hittingAfter (fun t ω => (phiPath P B phi x t ω, ouFlow P B x t ω))
    {q | a q.2 ≤ q.1} 0

/-- The admissible boundary class of Theorem 11. -/
def BoundaryClass (P : Params) (a : ℝ → ℝ) : Prop :=
  Continuous a ∧ AntitoneOn a (Set.Iic 0) ∧ MonotoneOn a (Set.Ici 0) ∧
    ∀ x, P.lam / P.c ≤ a x

/-- Positive part of the expectation form of (9.4). -/
noncomputable def iePos (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (a : ℝ → ℝ) (phi x : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ici (0 : ℝ), ∫⁻ ω,
    if phiPath P B phi x t.toNNReal ω < a (ouFlow P B x t.toNNReal ω) then
      ENNReal.ofReal (Real.exp (-P.lam * t) * phiPath P B phi x t.toNNReal ω)
    else 0 ∂μ ∂volume

/-- Negative part of the expectation form of (9.4). -/
noncomputable def ieNeg (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (a : ℝ → ℝ) (phi x : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ici (0 : ℝ), ∫⁻ ω,
    if phiPath P B phi x t.toNNReal ω < a (ouFlow P B x t.toNNReal ω) then
      ENNReal.ofReal (Real.exp (-P.lam * t) * (P.lam / P.c))
    else 0 ∂μ ∂volume

/-- Equation (9.5), in the expectation form of (9.4). -/
def SolvesIE (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (a : ℝ → ℝ) : Prop :=
  ∀ x, iePos P B μ a (a x) x = ieNeg P B μ a (a x) x

/-- The finite real representation on the right side of (9.6). -/
noncomputable def Vrep (P : Params) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (a : ℝ → ℝ) (phi x : ℝ) : ℝ :=
  (iePos P B μ a phi x).toReal - (ieNeg P B μ a phi x).toReal

end QuickestOU.Detection


