-- Prove2me | Definitions.Def_OptStopC1_SpaceDeriv_MarkovFlow
-- name    : OptStopC1_SpaceDeriv_MarkovFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:16.558815+00:00
-- url     : https://prove2.me/theorems/bfaba915-a7bc-49b6-a6bb-31e82b224491
-- title:
--   Standard Markov flow, strong Feller property, and C¹ spatial flow
-- statement:
--   A **standard Markov flow** $X^x_t$ starts at $x$, has right-continuous paths with left limits, and is adapted for every initial state to one right-continuous filtration. It obeys the strong Markov conditional-expectation identity at every finite stopping time; first entry times, strictly positive hitting times, and hitting times after any fixed time $s$ of open or closed sets are stopping times, and the corresponding state-to-hitting-probability maps are measurable.
--
--   The **strong Feller property** says that for every $t>0$ and every bounded measurable real $F$, the function $x\mapsto E[F(X^x_t)]$ is continuous. A **C¹ spatial flow** has a universal null set outside which $x\mapsto X_t^x$ is continuously differentiable at every time and each derivative path has right continuity and left limits. Equation (3.5) only requires spatial continuity almost surely at each fixed time.
--
--   These process properties provide the common model for the two routes from probabilistic to Green regularity.
--
--   **Formalization Note** The Markov identity is stated for bounded path functionals whose sampled variables and statewise expectation are measurable. This covers the hitting events used in Section 3 while making the conditional expectation well-defined.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 3, §2.1; p. 4, equation (2.6); p. 6, §2.4; p. 9, §3; p. 10, equation (3.5)

import Definitions.Def_OptStopC1_SpaceDeriv_FlowBasics

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace OptStopC1.SpaceDeriv

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The strong Markov identity for bounded path functionals whose sampled random
variables and statewise expected value are measurable. -/
noncomputable def IsStrongMarkov (X : Flow d Ω) (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 mΩ) : Prop :=
  ∀ (x : State d) (ρ : Ω → ℝ≥0)
    (hρ : IsStoppingTime 𝔽 (fun ω => (ρ ω : ℝ≥0∞)))
    (Φ : (ℝ≥0 → State d) → ℝ),
    Bornology.IsBounded (Set.range Φ) →
    (∀ y, Measurable (fun ω => Φ (fun t => X y t ω))) →
    Measurable (fun y => ∫ ω, Φ (fun t => X y t ω) ∂P) →
    Measurable (fun ω => Φ (fun t => X x (ρ ω + t) ω)) →
    P[fun ω => Φ (fun t => X x (ρ ω + t) ω) | hρ.measurableSpace] =ᵐ[P]
      fun ω => ∫ ω', Φ (fun t => X (X x (ρ ω) ω) t ω') ∂P

/-- Left continuity over stopping times (p. 3): along finite stopping times
increasing strictly to a finite stopping time, the flow converges almost surely. -/
def IsLeftContinuousOverStoppingTimes (X : Flow d Ω) (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 mΩ) : Prop :=
  ∀ (x : State d) (τ : Ω → ℝ≥0) (τn : ℕ → Ω → ℝ≥0),
    IsStoppingTime 𝔽 (fun ω => (τ ω : ℝ≥0∞)) →
    (∀ n, IsStoppingTime 𝔽 (fun ω => (τn n ω : ℝ≥0∞))) →
    (∀ᵐ ω ∂P, (∀ n, τn n ω < τ ω) ∧
      Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) →
    ∀ᵐ ω ∂P,
      Tendsto (fun n => X x (τn n ω) ω) atTop (𝓝 (X x (τ ω) ω))

/-- The standard process hypotheses of Section 2.1, with one shared filtration.
First entry and hitting times of open and closed sets, including hitting times
after a fixed time `s` (the shifted times `s + σ_A ∘ θ_s` of (3.2)), are
stopping times, as recalled on p. 9. -/
def IsStandardMarkovFlow (X : Flow d Ω) (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 mΩ) : Prop :=
  (∀ x ω, X x 0 ω = x) ∧
  (∀ x ω, IsRightContinuousPath (fun t => X x t ω) ∧
    HasLeftLimits (fun t => X x t ω)) ∧
  (∀ x, Adapted 𝔽 (X x)) ∧
  Filtration.IsRightContinuous 𝔽 ∧
  IsStrongMarkov X P 𝔽 ∧
  IsLeftContinuousOverStoppingTimes X P 𝔽 ∧
  (∀ (A : Set (State d)), (IsOpen A ∨ IsClosed A) → ∀ x,
    IsStoppingTime 𝔽 (entryTime X x A) ∧
    IsStoppingTime 𝔽 (hittingTime X x A) ∧
    ∀ s : ℝ≥0, IsStoppingTime 𝔽 (fun ω =>
      sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | s < t ∧ X x t ω ∈ A}))) ∧
  (∀ (A : Set (State d)), (IsOpen A ∨ IsClosed A) →
    ∀ (ε : ℝ≥0), 0 < ε →
      Measurable (fun x : State d =>
        P {ω | (ε : ℝ≥0∞) ≤ hittingTime X x A ω}))

/-- Spatial differentiability of the flow outside one universal null set. -/
def IsC1Flow (X : Flow d Ω) (P : Measure Ω) : Prop :=
  ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
    (∀ ω ∉ N, ∀ t, ContDiff ℝ 1 (fun x : State d => X x t ω)) ∧
    (∀ ω ∉ N, ∀ x i j,
      IsRightContinuousPath (fun t => flowPartial X i j x t ω) ∧
      HasLeftLimits (fun t => flowPartial X i j x t ω))

/-- Pointwise-in-time spatial continuity, equation (3.5). -/
def FlowContinuousAE (X : Flow d Ω) (P : Measure Ω) : Prop :=
  ∀ t : ℝ≥0, ∀ᵐ ω ∂P, Continuous (fun x : State d => X x t ω)

/-- Strong Feller property, equation (2.6). -/
noncomputable def IsStrongFeller (X : Flow d Ω) (P : Measure Ω) : Prop :=
  ∀ t : ℝ≥0, 0 < t → ∀ F : State d → ℝ,
    Measurable F → Bornology.IsBounded (Set.range F) →
    Continuous (fun x => ∫ ω, F (X x t ω) ∂P)

end OptStopC1.SpaceDeriv


