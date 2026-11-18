-- Prove2me | Definitions.Def_Kyprianou_Ch09_SourceMcKean
-- name    : Kyprianou_Ch09_SourceMcKean
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:19:16.893051+00:00
-- url     : https://prove2.me/theorems/c94188a7-67d1-484b-bed6-deedd1232ea2
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner SourceMcKean
-- statement:
--   McKean put identities, first-passage functions, scale transforms and the Exercise 9.1 source propositions. This source Definition module provides the actual declarations: killedInfimumMoment, McKeanDomain, Exercise91Domain, mckeanPutFormula, exercise91Gain, mckeanValueAndThreshold, spectrallyNegativeMckeanScale, mckeanContinuousSmoothFit, exercise9_1_i, exercise9_1_ii, exercise9_1_iii, exercise9_1. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceCore
import Definitions.Def_Kyprianou_Ch09_SourceValues
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09.B1

/-- The actual independent exponential-horizon running infimum moment. -/
noncomputable def killedInfimumMoment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E)
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0) : ℝ :=
  ∫ pair : Ω × E,
    Real.exp (pathInfAt X (e pair.2) pair.1) ∂(P.prod ν)

/-- The q=0 McKean put drifts positive. Exercise 9.1 drifts negative. -/
def McKeanDomain {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E)
    (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (e : E → WithTop ℝ≥0) : Prop :=
  ExponentialHorizon ν q e ∧
    (0 < q ∨ (q = 0 ∧
      ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => X t ω) atTop atTop))

def Exercise91Domain {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E)
    (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (e : E → WithTop ℝ≥0) : Prop :=
  ExponentialHorizon ν q e ∧
    (0 < q ∨ (q = 0 ∧
      ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => X t ω) atTop atBot))

/-- Normalised exponential-horizon put formula, mathematically distinct
from an arbitrary candidate value witness. -/
noncomputable def mckeanPutFormula
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E)
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (K x : ℝ) : ℝ :=
  let m := killedInfimumMoment P ν X e
  (∫ pair : Ω × E, max
     (K * m - Real.exp (x + pathInfAt X (e pair.2) pair.1)) 0
      ∂(P.prod ν)) / m

/-- The source exponential reward in Exercise 9.1, eq. (9.47). -/
noncomputable def exercise91Gain (z : ℝ) : ℝ :=
  1 - Real.exp (-max z 0)

end Kyprianou.Ch09.B1

namespace Kyprianou.Ch09

/-- Theorem 9.2, both the q=0 positive-drift domain and original strict
downcrossing, with actual optimality and the entire running-infimum formula. -/
noncomputable def mckeanValueAndThreshold : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q K : ℝ)
    (hX : B1.SourceModel P X F)
    (hK : 0 < K) (hDomain : B1.McKeanDomain P ν X q e),
    let m := B1.killedInfimumMoment P ν X e
    0 < m ∧ m ≤ 1 ∧
    ∀ x : ℝ,
      let z := Real.log (K * m)
      let τ := fun ω => B1.firstStrictBelow
        (fun t ξ => x + X t ξ) z ω
      B1.AdmissibleStop F τ ∧
      B1.optionValue P F X (B1.putGain K) q x (fun _ => 0) =
        B1.mckeanPutFormula P ν X e K x ∧
      B1.optionValue P F X (B1.putGain K) q x (fun _ => 0) =
        (∫ ω, B1.stoppedGain X (B1.putGain K) q x
          (fun _ => 0) τ ω ∂P)

/-- Corollary 9.3, including signed Esscher p=q-ψ(1). The McKean
threshold remains defined through the true infimum moment at every
source-allowed endpoint. The explicit quotient is demanded only away from
its zero denominator; the q=ψ(1)>0 removable limit is separately required. -/
noncomputable def spectrallyNegativeMckeanScale : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q K : ℝ) (ψ : ℝ → ℝ) (W : ℝ → ℝ)
    (φ : ℝ)
    (hX : B1.SourceModel P X F)
    (hK : 0 < K) (hDomain : B1.McKeanDomain P ν X q e)
    (hSN : B1.HasNoPositiveJumps P X)
    (hψ : B1.HasLaplaceExponent P X ψ)
    (hφ : 0 ≤ φ ∧ ψ φ = q ∧
      ∀ θ : ℝ, 0 ≤ θ → ψ θ = q → θ ≤ φ)
    (hW : B1.IsScale ψ q W),
    let W1 := fun y : ℝ => Real.exp (-y) * W y
    let m := B1.killedInfimumMoment P ν X e
    let z := Real.log (K * m)
    (0 < m ∧
      ∀ x : ℝ,
        B1.optionValue P F X (B1.putGain K) q x (fun _ => 0) =
        K * B1.scaleZ q W (x - z) -
        Real.exp x * B1.scaleZ (q - ψ 1) W1 (x - z)) ∧
    (φ ≠ 0 → q ≠ ψ 1 →
       z = Real.log (K * (q * (φ - 1)) / (φ * (q - ψ 1)))) ∧
    (q = ψ 1 → 0 < q → 0 < deriv ψ 1 →
       Real.exp z = K * q / deriv ψ 1)

/-- Theorem 9.4: convexity in price, continuous fit, explicit right
derivative jump and downward-regularity criterion under Theorem 9.2's domain. -/
noncomputable def mckeanContinuousSmoothFit : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q K : ℝ)
    (hX : B1.SourceModel P X F)
    (hK : 0 < K) (hDomain : B1.McKeanDomain P ν X q e),
    let m := B1.killedInfimumMoment P ν X e
    let z := Real.log (K * m)
    let v := fun x : ℝ =>
      B1.optionValue P F X (B1.putGain K) q x (fun _ => 0)
    0 < m ∧ ConvexOn ℝ (Set.Ioi 0) (fun y => v (Real.log y)) ∧
      ContinuousAt v z ∧
      DifferentiableWithinAt ℝ v (Set.Ici z) z ∧
      derivWithin v (Set.Ici z) z =
        -Real.exp z +
          K * ((P.prod ν)
            {pair : Ω × E | B1.pathInfAt X (e pair.2) pair.1 = 0}).toReal ∧
      (B1.SmoothFitAt v z ↔ B1.RegularBelow P X)

/-- Exercise 9.1(i): actual weak upcrossing/exponential supremum
identity, with the distinct negative-drift q=0 domain. -/
noncomputable def exercise9_1_i : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q : ℝ)
    (hX : B1.SourceModel P X F)
    (hDomain : B1.Exercise91Domain P ν X q e),
    let m := ∫ pair : Ω × E,
      Real.exp (-B1.pathSupAt X (e pair.2) pair.1) ∂(P.prod ν)
    ∀ a x : ℝ, 0 < a →
      (∫ ω, match B1.firstWeakAbove
         (fun t ξ => x + X t ξ) a ω with
        | ⊤ => (0 : ℝ)
        | (t : ℝ≥0) =>
          Real.exp (-q * (t : ℝ)) *
            (1 - Real.exp (-(x + X t ω))) ∂P) =
      (∫ pair : Ω × E,
        if a ≤ x + B1.pathSupAt X (e pair.2) pair.1 then
          1 - Real.exp
            (-(x + B1.pathSupAt X (e pair.2) pair.1)) / m
        else 0 ∂(P.prod ν))

/-- Exercise 9.1(ii): the actual exponential payoff (9.47) and its
McKean-like optimum at e^{-z}=E[e^{-sup at exponential horizon}]. -/
noncomputable def exercise9_1_ii : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q : ℝ)
    (hX : B1.SourceModel P X F)
    (hDomain : B1.Exercise91Domain P ν X q e),
    let m := ∫ pair : Ω × E,
      Real.exp (-B1.pathSupAt X (e pair.2) pair.1) ∂(P.prod ν)
    0 < m ∧ m ≤ 1 ∧
      ∀ x : ℝ,
        let z := -Real.log m
        let τ := fun ω => B1.firstWeakAbove
          (fun t ξ => x + X t ξ) z ω
        B1.AdmissibleStop F τ ∧
        B1.optionValue P F X B1.exercise91Gain q x (fun _ => 0) =
          (∫ ω, B1.stoppedGain X B1.exercise91Gain q x
            (fun _ => 0) τ ω ∂P)

/-- Exercise 9.1(iii): original smooth-fit iff upward-regularity remains
unchanged despite the erroneous final word in the printed author solution. -/
noncomputable def exercise9_1_iii : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q : ℝ)
    (hX : B1.SourceModel P X F)
    (hDomain : B1.Exercise91Domain P ν X q e),
    let m := ∫ pair : Ω × E,
      Real.exp (-B1.pathSupAt X (e pair.2) pair.1) ∂(P.prod ν)
    let z := -Real.log m
    let v := fun x : ℝ =>
      B1.optionValue P F X B1.exercise91Gain q x (fun _ => 0)
    0 < m ∧ ContinuousAt v z ∧
      (B1.SmoothFitAt v z ↔ B1.RegularAbove P X)

/-- The whole source exercise retains each independently named part. -/
noncomputable def exercise9_1 : Prop :=
  exercise9_1_i ∧ exercise9_1_ii ∧ exercise9_1_iii

end Kyprianou.Ch09


