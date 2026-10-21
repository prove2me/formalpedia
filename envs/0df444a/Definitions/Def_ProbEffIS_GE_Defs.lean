-- Prove2me | Definitions.Def_ProbEffIS_GE_Defs
-- name    : ProbEffIS_GE_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:49.916433+00:00
-- url     : https://prove2.me/theorems/5abc79cb-12ac-4ec7-a4c4-d9690fdd3c60
-- title:
--   §§ 2–5 — scaled log-MGF, dominating sets and probabilistic efficiency
-- statement:
--   Let $X_\gamma$ have law $\nu_\gamma$ on $\mathbb R^d$. This module defines the scaled logarithmic moment generating function $\mu_\gamma$, its limit $\mu$, the rate function $I$, a minimal finite dominating set $A$ with its exponential tilts, and the estimator of $p_\gamma=\Pr(\gamma^{-1}X_\gamma\in\mathcal E)$. It also defines the paper’s relative discrepancy and strong probabilistic efficiency:
--
--   $$
--   \delta_\varepsilon(\hat p,p)=\inf\{\delta>0:\widetilde P(|\hat p-p|>\delta p)\le\varepsilon\},\qquad
--   \exists n(\gamma)\ge1:\ \frac{\log n(\gamma)}{-\log p_\gamma}\to0,\quad\delta_\varepsilon(\hat p,p)\to0\ (\forall\varepsilon>0).
--   $$
--
--   The strong criterion includes the standing rare-event premise $p_\gamma\to0$. These shared definitions give the numbered results a common mathematical model. The laws are carried directly on Euclidean space, with extended-real rates and explicit likelihood ratios. Second moments in asymptotic efficiency are required to be genuine finite $L^2$ moments eventually.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, pp. 6–20, Definitions 1–4, Assumptions 1–2, equations (3), (4), (7), (11)

import Mathlib

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE

/-- The Euclidean space in which the rare event is specified. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- The scaled log moment generating function of the law of `X γ`. -/
noncomputable def scaledLogMGF (ν : ℝ → Measure (Rd d)) (γ : ℝ) (x : Rd d) : EReal :=
  ((γ⁻¹ : ℝ) : EReal) *
    ENNReal.log (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ x y)) ∂(ν γ))

/-- The effective domain of an extended-real function. -/
def dom (f : Rd d → EReal) : Set (Rd d) := {x | f x < ⊤}

/-- Gradient on the interior of the effective domain, where the function is finite. -/
noncomputable def gradE (f : Rd d → EReal) (x : Rd d) : Rd d :=
  gradient (fun y => (f y).toReal) x

/-- Steepness of the limiting log moment generating function. -/
def IsSteep (f : Rd d → EReal) : Prop :=
  ∀ θ₀ ∈ frontier (interior (dom f)),
    Tendsto (fun θ => ‖gradE f θ‖) (𝓝[interior (dom f)] θ₀) atTop

/-- Assumption 1 of Bai, Huang, Lam and Zhao. -/
structure Assumption1 (ν : ℝ → Measure (Rd d)) (μ : Rd d → EReal) : Prop where
  tendsto : ∀ x, Tendsto (fun γ => scaledLogMGF ν γ x) atTop (𝓝 (μ x))
  zero_mem : (0 : Rd d) ∈ interior (dom μ)
  interior_nonempty : (interior (dom μ)).Nonempty
  differentiableOn : DifferentiableOn ℝ (fun x => (μ x).toReal) (interior (dom μ))
  steep : IsSteep μ

/-- The Legendre transform of `μ`. -/
noncomputable def rate (μ : Rd d → EReal) (y : Rd d) : EReal :=
  ⨆ x, ((inner ℝ x y : ℝ) : EReal) - μ x

/-- The infimum of the rate function over a set. -/
noncomputable def rateOn (μ : Rd d → EReal) (S : Set (Rd d)) : EReal :=
  ⨅ y ∈ S, rate μ y

/-- Assumption 2 on the rare-event set. -/
structure Assumption2 (μ : Rd d → EReal) (R : Set (Rd d)) : Prop where
  measurable : MeasurableSet R
  closure_eq : closure R = closure (interior R)
  meets : (interior R ∩ interior (dom (rate μ))).Nonempty
  pos : 0 < rateOn μ R

/-- The half-space associated with a dominating point and tilt. -/
def halfspace (s a : Rd d) : Set (Rd d) := {x | 0 ≤ inner ℝ s (x - a)}

/-- Definition 2: a finite minimal dominating set, enumerated without repetitions. -/
structure IsDominatingSet (μ : Rd d → EReal) (R : Set (Rd d)) {r : ℕ}
    (a s : Fin r → Rd d) : Prop where
  injective : Function.Injective a
  mem_frontier : ∀ i, a i ∈ frontier R
  mem_interior_dom_rate : ∀ i, a i ∈ interior (dom (rate μ))
  tilt_mem : ∀ i, s i ∈ interior (dom μ)
  grad_eq : ∀ i, gradE μ (s i) = a i
  tilt_unique : ∀ i, ∀ t ∈ interior (dom μ), gradE μ t = a i → t = s i
  cover : R ⊆ ⋃ i, halfspace (s i) (a i)
  minimal : ∀ i, ¬ R ⊆ ⋃ j ∈ ({i}ᶜ : Set (Fin r)), halfspace (s j) (a j)

/-- The indices of exactly the lowest-rate dominating points. -/
def IsMostSignificant (μ : Rd d → EReal) {r : ℕ}
    (a : Fin r → Rd d) (S : Finset (Fin r)) : Prop :=
  S.Nonempty ∧ (∀ i ∈ S, ∀ j ∈ S, rate μ (a i) = rate μ (a j)) ∧
    (∀ i ∈ S, ∀ j ∉ S, rate μ (a i) < rate μ (a j))

/-- The mixture of exponential tilts in equations (3) and (11). -/
noncomputable def mixtureIS (ν : ℝ → Measure (Rd d)) (γ : ℝ) {r : ℕ}
    (S : Finset (Fin r)) (α : Fin r → ℝ) (s : Fin r → Rd d) : Measure (Rd d) :=
  ∑ i ∈ S, ENNReal.ofReal (α i) • (ν γ).tilted (fun x => inner ℝ (s i) x)

/-- The explicit likelihood ratio of the mixture, equation (4). -/
noncomputable def likelihoodRatio (ν : ℝ → Measure (Rd d)) (γ : ℝ) {r : ℕ}
    (S : Finset (Fin r)) (α : Fin r → ℝ) (s : Fin r → Rd d) (x : Rd d) : ℝ :=
  (∑ i ∈ S, α i *
    (Real.exp (inner ℝ (s i) x) /
      ∫ y, Real.exp (inner ℝ (s i) y) ∂(ν γ)))⁻¹

/-- The importance-sampling output for a set of scaled observations. -/
noncomputable def isOutput (ν : ℝ → Measure (Rd d)) (γ : ℝ) (B : Set (Rd d))
    {r : ℕ} (S : Finset (Fin r)) (α : Fin r → ℝ) (s : Fin r → Rd d) : Rd d → ℝ :=
  {x | γ⁻¹ • x ∈ B}.indicator (likelihoodRatio ν γ S α s)

/-- Probability of the scaled rare event under the original law. -/
noncomputable def rareProb (ν : ℝ → Measure (Rd d)) (γ : ℝ) (B : Set (Rd d)) : ℝ :=
  (ν γ {x | γ⁻¹ • x ∈ B}).toReal

/-- The portion of the rare set covered by the selected dominating points. -/
def splitIn (R : Set (Rd d)) {r : ℕ} (S : Finset (Fin r))
    (a s : Fin r → Rd d) : Set (Rd d) :=
  R ∩ ⋃ i ∈ S, halfspace (s i) (a i)

/-- The complementary portion of the rare set. -/
def splitOut (R : Set (Rd d)) {r : ℕ} (S : Finset (Fin r))
    (a s : Fin r → Rd d) : Set (Rd d) :=
  R \ splitIn R S a s

/-- An IS output expressed through a Radon–Nikodym derivative. -/
noncomputable def lrOutput {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) (A : Set Ω) : Ω → ℝ :=
  A.indicator (fun ω => (P.rnDeriv Q ω).toReal)

/-- The probability of a parameter-indexed event. -/
noncomputable def eventProb {Ω : Type*} [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) (A : ℝ → Set Ω) (γ : ℝ) : ℝ :=
  (P γ (A γ)).toReal

/-- An IS output for a parameter-indexed event and pair of laws. -/
noncomputable def eventOutput {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℝ → Measure Ω) (A : ℝ → Set Ω) (γ : ℝ) : Ω → ℝ :=
  lrOutput (P γ) (Q γ) (A γ)

/-- The mean of `n` independently sampled outputs. -/
noncomputable def sampleMean {Ω : Type*} (n : ℕ) (Z : Ω → ℝ) (ω : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, Z (ω i)

/-- Definition 3: minimal relative discrepancy at tolerance `ε`. -/
noncomputable def minRelDisc {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (n : ℕ) (Z : Ω → ℝ) (p ε : ℝ) : ℝ :=
  sInf {δ : ℝ | 0 < δ ∧
    Measure.pi (fun _ : Fin n => Q)
      {ω | δ * p < |sampleMean n Z ω - p|} ≤ ENNReal.ofReal ε}

/-- Subexponential growth of `g` on the scale `f`. -/
def IsSubexpIn (g f : ℝ → ℝ) : Prop :=
  Tendsto (fun γ => Real.log (g γ) / f γ) atTop (𝓝 0)

/-- Definition 1, with genuine finite second moments eventually. -/
def AsymptoticallyEfficient {Ω : Type*} [MeasurableSpace Ω]
    (Q : ℝ → Measure Ω) (Z : ℝ → Ω → ℝ) (p : ℝ → ℝ) : Prop :=
  (∀ᶠ γ in atTop, MemLp (Z γ) 2 (Q γ)) ∧
    Tendsto (fun γ => Real.log (∫ ω, Z γ ω ^ 2 ∂(Q γ)) / Real.log (p γ))
      atTop (𝓝 2)

/-- Definition 4.1: one sample-size function works for every tolerance. -/
def StronglyProbEfficient {Ω : Type*} [MeasurableSpace Ω]
    (Q : ℝ → Measure Ω) (Z : ℝ → Ω → ℝ) (p : ℝ → ℝ) : Prop :=
  Tendsto p atTop (𝓝 0) ∧
  ∃ n : ℝ → ℕ, (∀ γ, 1 ≤ n γ) ∧
    IsSubexpIn (fun γ => (n γ : ℝ)) (fun γ => -Real.log (p γ)) ∧
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun γ => minRelDisc (Q γ) (n γ) (Z γ) (p γ) ε) atTop (𝓝 0)

end ProbEffIS.GE


