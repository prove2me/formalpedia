-- Prove2me | Definitions.Def_Kyprianou_Ch09_SourceCore
-- name    : Kyprianou_Ch09_SourceCore
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:17:22.170622+00:00
-- url     : https://prove2.me/theorems/7a3f20d0-1f95-4b35-9f0e-3d4916a5bdc0
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner SourceCore
-- statement:
--   Completed natural-filtration model, admissible stopping times, first passages, extremum functions, stopped rewards, scale functions and game gain. This source Definition module provides the actual declarations: SourceModel, AdmissibleStop, AdmissibleFiniteStop, firstStrictBelow, firstWeakAbove, firstStrictReflectedAbove, pathInfAt, pathSupAt, stoppedGain, optionValue, ExponentialHorizon, HasNoPositiveJumps (and 6 further declarations). The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09.B1

/-- The actual source filtration uses the published completed-natural-filtration
predicate and is additionally assumed right continuous, as in Chapter 9. -/
def SourceModel {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) : Prop :=
  LevyFoundations.IsLevyProcess X P ∧
  Kyprianou.Ch03.IsCompletedNaturalFiltration P X F ∧
  ∀ t : ℝ≥0, F t = ⨅ s ∈ Set.Ioi t, F s

/-- All finite/infinite stopping-time choices with their genuine filtration. -/
def AdmissibleStop {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → WithTop ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, @MeasurableSet Ω (F t) {ω | τ ω ≤ (t : WithTop ℝ≥0)}

/-- Finite a.s. admissibility is a genuine smaller class for Theorem 9.11. -/
def AdmissibleFiniteStop {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → WithTop ℝ≥0) : Prop :=
  AdmissibleStop F τ ∧ ∀ᵐ ω ∂P, τ ω ≠ ⊤

/-- Source first strict downcrossing, infinity when never attained. -/
noncomputable def firstStrictBelow {Ω : Type} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf { t : WithTop ℝ≥0 | ∃ s : ℝ≥0,
    0 < s ∧ X s ω < a ∧ t = (s : WithTop ℝ≥0) }

/-- Source first weak upcrossing, including an immediate t=0 hit. -/
noncomputable def firstWeakAbove {Ω : Type} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf { t : WithTop ℝ≥0 | ∃ s : ℝ≥0,
    a ≤ X s ω ∧ t = (s : WithTop ℝ≥0) }

/-- Strict reflected first upcrossing, distinguished at the zero barrier. -/
noncomputable def firstStrictReflectedAbove {Ω : Type}
    (X : ℝ≥0 → Ω → ℝ) (x a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf { t : WithTop ℝ≥0 | ∃ s : ℝ≥0,
    0 < s ∧ a < max x (sSup ((fun u : ℝ≥0 => X u ω) '' Set.Icc 0 s)) -
      X s ω ∧ t = (s : WithTop ℝ≥0) }

/-- All physical-time observations up to an independent, possibly infinite
exponential horizon. In the q=0 case the horizon is infinity. -/
noncomputable def pathInfAt {Ω : Type} (X : ℝ≥0 → Ω → ℝ)
    (T : WithTop ℝ≥0) (ω : Ω) : ℝ :=
  sInf ((fun s : ℝ≥0 => X s ω) '' {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ T})

noncomputable def pathSupAt {Ω : Type} (X : ℝ≥0 → Ω → ℝ)
    (T : WithTop ℝ≥0) (ω : Ω) : ℝ :=
  sSup ((fun s : ℝ≥0 => X s ω) '' {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ T})

/-- Real finite stopped reward; the supplied infinity payoff must equal the
actual terminal limit, a separate source hypothesis. -/
noncomputable def stoppedGain {Ω : Type}
    (X : ℝ≥0 → Ω → ℝ) (G : ℝ → ℝ)
    (q x : ℝ) (terminal : Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  match τ ω with
  | ⊤ => terminal ω
  | (t : ℝ≥0) => Real.exp (-q * (t : ℝ)) * G (x + X t ω)

/-- The actual option value is a supremum over all admissible stopping
times, including infinity, with no candidate-optimality premise. -/
noncomputable def optionValue {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (G : ℝ → ℝ)
    (q x : ℝ) (terminal : Ω → ℝ) : ℝ :=
  sSup {z : ℝ | ∃ τ : Ω → WithTop ℝ≥0,
    AdmissibleStop F τ ∧ z = ∫ ω, stoppedGain X G q x terminal τ ω ∂P}

/-- The exponential clock has its genuine survival law, and q=0 means
infinite clock, without using a fictitious deterministic finite horizon. -/
def ExponentialHorizon {E : Type} [MeasurableSpace E]
    (ν : Measure E) (q : ℝ) (e : E → WithTop ℝ≥0) : Prop :=
  (q = 0 ∧ ∀ᵐ η ∂ν, e η = ⊤) ∨
  (0 < q ∧ ∀ t : ℝ≥0,
      ν {η | (t : WithTop ℝ≥0) < e η} =
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))))

/-- A spectral-negative process has no positive jumps on a common
full-measure event. This does not impose atomlessness on negative jumps. -/
def HasNoPositiveJumps {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
    ∀ v : ℝ, Tendsto (fun s : ℝ≥0 => X s ω)
      (nhdsWithin t (Set.Iio t)) (nhds v) → X t ω ≤ v

/-- The real Laplace exponent is tied to the given process at every
nonnegative time and parameter through its actual exponential moments. -/
def HasLaplaceExponent {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ) : Prop :=
  ∀ θ : ℝ, 0 ≤ θ → ∀ t : ℝ≥0,
    Integrable (fun ω => Real.exp (θ * X t ω)) P ∧
    (∫ ω, Real.exp (θ * X t ω) ∂P) =
      Real.exp ((t : ℝ) * ψ θ)

/-- Bounded-variation spectrally negative law linked to the actual
subordinator and Laplace exponent; jumpMeasure is allowed to have atoms. -/
def IsBVNegativeLevy {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (ψ : ℝ → ℝ) (d : ℝ) (S : ℝ≥0 → Ω → ℝ)
    (jumpMeasure : Measure ℝ) : Prop :=
  0 < d ∧ HasNoPositiveJumps P X ∧ HasLaplaceExponent P X ψ ∧
  (∀ᵐ ω ∂P, ∀ t, X t ω = d * (t : ℝ) - S t ω) ∧
  (∀ᵐ ω ∂P, S 0 ω = 0 ∧ ∀ s t, s ≤ t → S s ω ≤ S t ω) ∧
  (∀ θ : ℝ, 0 ≤ θ →
    ψ θ = d * θ - ∫ y in Set.Ioi (0 : ℝ),
      (1 - Real.exp (-θ * y)) ∂jumpMeasure)

/-- An explicit source-level diffuse jump-measure hypothesis is required
for Theorem 9.11 only; Exercise 9.2 does not inherit it. -/
def IsAtomlessPositiveJumpMeasure (jumpMeasure : Measure ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → jumpMeasure {y} = 0

/-- q-scale function uses the nonnegative Laplace-transform domain,
rather than an arbitrary witness satisfying an optimal-stopping result. -/
def IsScale (ψ : ℝ → ℝ) (q : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, x < 0 → W x = 0) ∧
  (∀ x : ℝ, 0 ≤ x → 0 ≤ W x) ∧
  ContinuousOn W (Set.Ici 0) ∧
  ∀ θ : ℝ, 0 ≤ θ → 0 < ψ θ - q →
    IntegrableOn (fun x => Real.exp (-θ * x) * W x) (Set.Ici 0) ∧
    (∫ x in Set.Ici (0 : ℝ), Real.exp (-θ * x) * W x) =
      (ψ θ - q)⁻¹

/-- Z^(q) is defined from W^(q), including negative arguments as in the
standard scale-function extension. -/
noncomputable def scaleZ (q : ℝ) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + q * ∫ y in (0 : ℝ)..(max x 0), W y

/-- Source game payoff; lower τ wins ties exactly as in Section 9.6. -/
noncomputable def gameGain {Ω : Type}
    (X : ℝ≥0 → Ω → ℝ) (G H : ℝ → ℝ) (q x : ℝ)
    (terminalG terminalH : Ω → ℝ)
    (τ σ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  if τ ω ≤ σ ω then stoppedGain X G q x terminalG τ ω
  else stoppedGain X H q x terminalH σ ω

end Kyprianou.Ch09.B1


