-- Prove2me | Definitions.Def_Kyprianou_Ch09_SourceAppell
-- name    : Kyprianou_Ch09_SourceAppell
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:19:53.203539+00:00
-- url     : https://prove2.me/theorems/b8caa50b-3b86-4af9-875e-e8beb5013d2a
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner SourceAppell
-- statement:
--   Appell-polynomial and Novikov–Shiryaev source propositions, including root and fit conditions. This source Definition module provides the actual declarations: IsJumpMeasureFor, PositiveJumpMoment, powerGain, expMaximum, appellCandidateValue, Definition95Construction, appellPolynomialDefinition, novikovShiryaevOptimalStopping, novikovShiryaevFit, appellFirstPassageFluctuation, appellLargestRootAndSign. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceCore
import Definitions.Def_Kyprianou_Ch09_SourceValues
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09.B1

/-- Lévy's characteristic triplet binds the supplied jump measure to the
actual characteristic law of X, rather than a free Π. Integrability of the
truncated Lévy–Khintchine integrand is explicitly recorded. -/
def IsJumpMeasureFor {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (jumpMeasure : Measure ℝ) : Prop :=
  jumpMeasure {0} = 0 ∧
  IntegrableOn (fun y : ℝ => min 1 (y ^ 2))
    (Set.univ : Set ℝ) jumpMeasure ∧
  ∃ b variance : ℝ, 0 ≤ variance ∧
    ∀ θ : ℝ,
      let integrand := fun y : ℝ =>
        Complex.exp (Complex.I * (θ : ℂ) * (y : ℂ)) -
        1 - Complex.I * (θ : ℂ) * (y : ℂ) *
          (if |y| < 1 then (1 : ℂ) else 0)
      Integrable integrand jumpMeasure ∧
      ∀ t : ℝ≥0,
        (∫ ω, Complex.exp
          (Complex.I * (θ : ℂ) * (X t ω : ℂ)) ∂P) =
        Complex.exp ((t : ℝ) * (
          Complex.I * (b : ℂ) * (θ : ℂ) -
          (variance : ℂ) * (θ : ℂ) ^ 2 / 2 +
          ∫ y, integrand y ∂jumpMeasure))

/-- Full source large-positive-jump moment criterion. -/
def PositiveJumpMoment (jumpMeasure : Measure ℝ) (n : ℕ) : Prop :=
  IntegrableOn (fun y : ℝ => y ^ n) (Set.Ioi 1) jumpMeasure

/-- The real optimal stopping reward in Novikov–Shiryaev, for all x. -/
noncomputable def powerGain (n : ℕ) (x : ℝ) : ℝ :=
  (max x 0) ^ n

/-- The exponential-horizon running maximum on the product sample space. -/
noncomputable def expMaximum
    {Ω E : Type} (X : ℝ≥0 → Ω → ℝ)
    (e : E → WithTop ℝ≥0) (pair : Ω × E) : ℝ :=
  pathSupAt X (e pair.2) pair.1

/-- Actual candidate value via an Appell polynomial and a strict threshold. -/
noncomputable def appellCandidateValue
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E)
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (Q : Polynomial ℝ) (z x : ℝ) : ℝ :=
  ∫ pair : Ω × E,
    if z ≤ x + expMaximum X e pair then
      Q.eval (x + expMaximum X e pair) else 0 ∂(P.prod ν)

/-- The source Definition 9.5 is a non-vacuous construction obligation.
The conditional identity of Lemma 9.8 does not discharge this. -/
noncomputable def Definition95Construction : Prop := AppellExistenceUniqueness

end Kyprianou.Ch09.B1

namespace Kyprianou.Ch09

/-- Definition 9.5's complete existence, uniqueness and polynomiality
obligation, independent of the conditional mean-value property. -/
noncomputable def appellPolynomialDefinition : Prop :=
  B1.Definition95Construction

/-- Theorem 9.6: actual finite-order Appell polynomial family from the
positive-jump moment law; largest nonnegative root, weak upcrossing, value
and attainment for every initial reserve. No free optimality witness. -/
noncomputable def novikovShiryaevOptimalStopping : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (jumpMeasure : Measure ℝ) (q : ℝ) (n : ℕ)
    (hX : B1.SourceModel P X F)
    (hJump : B1.IsJumpMeasureFor P X jumpMeasure)
    (hn : 1 ≤ n) (hq : 0 < q)
    (hmoment : B1.PositiveJumpMoment jumpMeasure n)
    (hExp : B1.ExponentialHorizon ν q e),
    ∃ Q : ℕ → Polynomial ℝ,
      B1.AppellPolynomialFamily (P.prod ν)
        (B1.expMaximum X e) n Q ∧
      ∃ z : ℝ, 0 ≤ z ∧ (Q n).eval z = 0 ∧
        (∀ y : ℝ, 0 ≤ y → (Q n).eval y = 0 → y ≤ z) ∧
        ∀ x : ℝ,
          let τ := fun ω => B1.firstWeakAbove
            (fun t ξ => x + X t ξ) z ω
          B1.AdmissibleStop F τ ∧
          B1.optionValue P F X (B1.powerGain n) q x (fun _ => 0) =
            B1.appellCandidateValue P ν X e (Q n) z x ∧
          B1.optionValue P F X (B1.powerGain n) q x (fun _ => 0) =
            (∫ ω, B1.stoppedGain X (B1.powerGain n) q x
              (fun _ => 0) τ ω ∂P)

/-- Theorem 9.7, corrected I-02 smooth fit. The derivative factor,
not unqualified upward regularity, exactly controls smooth fit. -/
noncomputable def novikovShiryaevFit : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (jumpMeasure : Measure ℝ) (q : ℝ) (n : ℕ)
    (Q : ℕ → Polynomial ℝ) (z : ℝ)
    (hX : B1.SourceModel P X F)
    (hJump : B1.IsJumpMeasureFor P X jumpMeasure)
    (hn : 1 ≤ n) (hq : 0 < q)
    (hmoment : B1.PositiveJumpMoment jumpMeasure n)
    (hExp : B1.ExponentialHorizon ν q e)
    (hQ : B1.AppellPolynomialFamily (P.prod ν)
      (B1.expMaximum X e) n Q)
    (hRoot : 0 ≤ z ∧ (Q n).eval z = 0 ∧
      ∀ y : ℝ, 0 ≤ y → (Q n).eval y = 0 → y ≤ z),
    let v := fun x : ℝ =>
      B1.optionValue P F X (B1.powerGain n) q x (fun _ => 0)
    let atom := ((P.prod ν)
      {pair : Ω × E | B1.expMaximum X e pair = 0}).toReal
    ConvexOn ℝ (Set.univ : Set ℝ) v ∧ ContinuousAt v z ∧
      DifferentiableWithinAt ℝ v (Set.Iic z) z ∧
      DifferentiableWithinAt ℝ v (Set.Ici z) z ∧
      derivWithin v (Set.Iic z) z =
        derivWithin v (Set.Ici z) z -
        (Q n).derivative.eval z * atom ∧
      (B1.SmoothFitAt v z ↔ (Q n).derivative.eval z * atom = 0) ∧
      ((Q n).derivative.eval z ≠ 0 →
        (B1.SmoothFitAt v z ↔ B1.RegularAbove P X))

/-- Lemma 9.9: actual discounted weak upward passage identity, with
overshoots and the event at the independent exponential clock. -/
noncomputable def appellFirstPassageFluctuation : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (jumpMeasure : Measure ℝ) (q : ℝ) (n : ℕ)
    (Q : ℕ → Polynomial ℝ)
    (hX : B1.SourceModel P X F)
    (hJump : B1.IsJumpMeasureFor P X jumpMeasure)
    (hn : 1 ≤ n) (hq : 0 < q)
    (hmoment : B1.PositiveJumpMoment jumpMeasure n)
    (hExp : B1.ExponentialHorizon ν q e)
    (hQ : B1.AppellPolynomialFamily (P.prod ν)
      (B1.expMaximum X e) n Q),
    ∀ a x : ℝ, 0 < a →
      (∫ ω, match B1.firstWeakAbove
        (fun t ξ => x + X t ξ) a ω with
        | ⊤ => (0 : ℝ)
        | (t : ℝ≥0) =>
          Real.exp (-q * (t : ℝ)) * (x + X t ω) ^ n ∂P) =
      B1.appellCandidateValue P ν X e (Q n) a x

/-- Lemma 9.10: repaired largest nonnegative root and weak-sign endpoint,
including deterministic negative drift X_t=-t and degenerate Y=0. The
Bernstein/Wiener-Hopf proof Q_n(0)≤0 is a real Open obligation. -/
noncomputable def appellLargestRootAndSign : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (jumpMeasure : Measure ℝ) (q : ℝ) (n : ℕ)
    (Q : ℕ → Polynomial ℝ)
    (hX : B1.SourceModel P X F)
    (hJump : B1.IsJumpMeasureFor P X jumpMeasure)
    (hn : 1 ≤ n) (hq : 0 < q)
    (hmoment : B1.PositiveJumpMoment jumpMeasure n)
    (hExp : B1.ExponentialHorizon ν q e)
    (hQ : B1.AppellPolynomialFamily (P.prod ν)
      (B1.expMaximum X e) n Q),
    ∃ z : ℝ, 0 ≤ z ∧ (Q n).eval z = 0 ∧
      (∀ x : ℝ, 0 ≤ x → (Q n).eval x = 0 → x ≤ z) ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ z → (Q n).eval x ≤ 0) ∧
      (∀ x : ℝ, z < x → 0 < (Q n).eval x) ∧
      MonotoneOn (fun x : ℝ => (Q n).eval x) (Set.Ici z)

end Kyprianou.Ch09


