-- Prove2me | Definitions.Def_RegMT_Classif_Supplement_Transport
-- name    : RegMT_Classif_Supplement_Transport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:23:47.4138+00:00
-- url     : https://prove2.me/theorems/a8e059e6-4cce-4dd7-a970-f2a6e715db83
-- title:
--   Support-restricted risk and infinite label cost
-- statement:
--   The nonnegative expected loss is the extended Lebesgue integral. Norm transport, empirical distributions, and finite-label-price transport are reused from the published definitions. The additional cost-form transport is
--   $$W_c(Q,P)=\inf_{\pi:\,\pi_1=Q,\pi_2=P}\int c(z,z')\,d\pi.$$
--   The ball consists of probability measures supported on the specified support with cost at most $\rho$. For infinite label price, $c((x,y),(x',y'))=\|x-x'\|$ when $y=y'$ and $+\infty$ otherwise. The generic norm risk and classification risk restrict the published balls to the source support; neither transports an arbitrary map without checking its marginals. This layer supports (5), (17), (28), (30) and (33).
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p.7, Definition 2.2 and (3); p.9 (11); p.11 (16); p.14 Theorem 3.20; p.15 (30)

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_WassersteinDRO_Duality_ambiguitySet
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution

open scoped ENNReal

open MeasureTheory
noncomputable section

namespace RegMT.Classif.Supplement

/-- Cost form of Definition 2.2, needed for an infinite label price and metric (11). -/
def costTransport {A : Type*} [MeasurableSpace A] (c : A → A → ℝ≥0∞)
    (Q P : Measure A) : ℝ≥0∞ :=
  ⨅ π : Measure (A × A), ⨅ (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
    ∫⁻ z, c z.1 z.2 ∂π

def costBall {A : Type*} [MeasurableSpace A] (c : A → A → ℝ≥0∞)
    (S : Set A) (P : Measure A) (ρ : ℝ) : Set (Measure A) :=
  {Q | IsProbabilityMeasure Q ∧ Q Sᶜ = 0 ∧ costTransport c Q P ≤ ENNReal.ofReal ρ}

def expected {A : Type*} [MeasurableSpace A] (Q : Measure A) (f : A → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (f z) ∂Q

def normRisk {A : Type*} [MeasurableSpace A] [NormedAddCommGroup A]
    {N : ℕ} (S : Set A) (z : Fin N → A) (ρ : ℝ) (f : A → ℝ) : ℝ≥0∞ :=
  ⨆ Q ∈ WassersteinDRO.Duality.ambiguitySet ρ 1 S
    (WassersteinDRO.Duality.empiricalDistribution z), expected Q f

def costRisk {A : Type*} [MeasurableSpace A] {N : ℕ} (c : A → A → ℝ≥0∞)
    (S : Set A) (z : Fin N → A) (ρ : ℝ) (f : A → ℝ) : ℝ≥0∞ :=
  ⨆ Q ∈ costBall c S (WassersteinDRO.Duality.empiricalDistribution z) ρ, expected Q f

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]

/-- Restrict the published finite-label-price ball to the feature support. -/
def classRisk {N : ℕ} (X : Set V) (x : Fin N → V) (y : Fin N → Bool)
    (κ ρ : ℝ) (f : V × Bool → ℝ) : ℝ≥0∞ :=
  ⨆ Q ∈ DRLogReg.Reformulation.wassersteinBall κ ρ
      (DRLogReg.Reformulation.empirical x y),
    ⨆ (_ : Q (X ×ˢ Set.univ)ᶜ = 0), expected Q f

/-- κ=∞: a mismatched pair has infinite cost, including at zero feature distance. -/
def labelPreservingCost (z z' : V × Bool) : ℝ≥0∞ :=
  if z.2 = z'.2 then ENNReal.ofReal ‖z.1 - z'.1‖ else ⊤

/-- Regression metric (11), not the joint norm metric of §3.1. -/
def weightedCost (κ : ℝ) (z z' : V × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖z.1 - z'.1‖ + κ * |z.2 - z'.2|)

end RegMT.Classif.Supplement


