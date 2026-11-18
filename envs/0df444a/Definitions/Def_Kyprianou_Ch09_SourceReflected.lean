-- Prove2me | Definitions.Def_Kyprianou_Ch09_SourceReflected
-- name    : Kyprianou_Ch09_SourceReflected
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:20:28.078745+00:00
-- url     : https://prove2.me/theorems/782c2f30-1c9a-4e5c-a599-fe87bbe45f51
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner SourceReflected
-- statement:
--   Russian-option and reflected-process source propositions and Exercise 9.2. This source Definition module provides the actual declarations: russianThreshold, russianOptimalStop, RussianGameSaddle, sheppShiryaevValueAndStrategy, reflectedProcessFit, exercise9_2_i, exercise9_2_ii, exercise9_2_iii, exercise9_2. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceCore
import Definitions.Def_Kyprianou_Ch09_SourceValues
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09.B1

/-- First zero of the source q-reflected scale drift, with no tacit
strictly-positive assumption on the threshold. -/
noncomputable def russianThreshold (q : ℝ) (W : ℝ → ℝ) : ℝ :=
  sInf {u : ℝ | 0 ≤ u ∧ scaleZ q W u ≤ q * W u}

/-- The printed strict reflected upcrossing, kept separate from the corrected
immediate-stopping optimiser at the zero-barrier endpoint. -/
noncomputable def russianOptimalStop {Ω : Type}
    (X : ℝ≥0 → Ω → ℝ) (q d x : ℝ)
    (W : ℝ → ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  if d ≤ q then 0 else
    firstStrictReflectedAbove X x (russianThreshold q W) ω

/-- Full saddle inequalities for a game. An arbitrary payoff or a
candidate's optimality is never stipulated as an input hypothesis. -/
def RussianGameSaddle {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (q x δ : ℝ)
    (τstar σstar : Ω → WithTop ℝ≥0) : Prop :=
  AdmissibleStop F τstar ∧ AdmissibleStop F σstar ∧
    (∀ τ : Ω → WithTop ℝ≥0, AdmissibleStop F τ →
      (∫ ω, russianGameGain X q x δ τ σstar ω ∂P) ≤
      (∫ ω, russianGameGain X q x δ τstar σstar ω ∂P)) ∧
    (∀ σ : Ω → WithTop ℝ≥0, AdmissibleStop F σ →
      (∫ ω, russianGameGain X q x δ τstar σstar ω ∂P) ≤
      (∫ ω, russianGameGain X q x δ τstar σ ω ∂P))

end Kyprianou.Ch09.B1

namespace Kyprianou.Ch09

/-- Theorem 9.11: spectrally negative bounded-variation Russian option,
including q≥d immediate stopping and q<d finite strict upcrossing.
Only this theorem, not Exercise 9.2, assumes an atomless jump measure. -/
noncomputable def sheppShiryaevValueAndStrategy : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (q : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hDiffuse : B1.IsAtomlessPositiveJumpMeasure jumpMeasure)
    (hq : ψ 1 < q) (hq0 : 0 < q)
    (hScale : B1.IsScale ψ q W),
    0 ≤ B1.russianThreshold q W ∧
    ∀ x : ℝ, 0 ≤ x →
      B1.russianValue P F X q x =
        Real.exp x * B1.scaleZ q W (B1.russianThreshold q W - x) ∧
      (d ≤ q →
        B1.russianValue P F X q x = Real.exp x ∧
        (∫ ω, B1.russianGain X q x (fun _ => 0) ω ∂P) = Real.exp x) ∧
      (q < d →
        B1.AdmissibleFiniteStop P F
          (B1.russianOptimalStop X q d x W) ∧
        (∫ ω, B1.russianGain X q x
            (B1.russianOptimalStop X q d x W) ω ∂P) =
          B1.russianValue P F X q x)

/-- Corollary 9.12: positive reflected threshold, convexity, continuous fit,
the explicit derivative jump and the resulting failure of smooth fit. -/
noncomputable def reflectedProcessFit : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (q : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hDiffuse : B1.IsAtomlessPositiveJumpMeasure jumpMeasure)
    (hq : ψ 1 < q) (hq0 : 0 < q)
    (hsmall : q < d) (hScale : B1.IsScale ψ q W),
    let z := B1.russianThreshold q W
    let v := fun x : ℝ => Real.exp x * B1.scaleZ q W (z - x)
    0 < z ∧ ConvexOn ℝ (Set.Ici 0) v ∧
      ContinuousAt v z ∧
      DifferentiableWithinAt ℝ v (Set.Iic z) z ∧
      DifferentiableWithinAt ℝ v (Set.Ici z) z ∧
      derivWithin v (Set.Iic z) z =
        derivWithin v (Set.Ici z) z - q / d * Real.exp z ∧
      ¬ B1.SmoothFitAt v z

/-- Exercise 9.2(i), retaining atomic-jump compound Poisson laws. -/
noncomputable def exercise9_2_i : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (q δ : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hψ : 0 < ψ 1) (hq : ψ 1 < q) (hqd : q < d)
    (hδ : 0 < δ) (hScale : B1.IsScale ψ q W),
    1 + δ ≥ B1.scaleZ q W (B1.russianThreshold q W) →
    ∀ x : ℝ, 0 ≤ x →
      B1.russianGameValue P F X q x δ =
        Real.exp x * B1.scaleZ q W (B1.russianThreshold q W - x)

/-- Exercise 9.2(ii): unique smaller threshold and convex/derivative
properties under general, possibly atomic jump measures. -/
noncomputable def exercise9_2_ii : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (q δ : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hψ : 0 < ψ 1) (hq : ψ 1 < q) (hqd : q < d)
    (hδ : 0 < δ) (hScale : B1.IsScale ψ q W),
    1 + δ < B1.scaleZ q W (B1.russianThreshold q W) →
    (∃! z : ℝ, 0 < z ∧ z < B1.russianThreshold q W ∧
      B1.scaleZ q W z = 1 + δ) ∧
    (∀ z : ℝ, 0 < z → z < B1.russianThreshold q W →
      B1.scaleZ q W z = 1 + δ →
      let v := fun x : ℝ => Real.exp x * B1.scaleZ q W (z - x)
      ConvexOn ℝ (Set.Ici 0) v ∧ ContinuousAt v z ∧
        DifferentiableWithinAt ℝ v (Set.Ici 0) 0 ∧
        0 < derivWithin v (Set.Ici 0) 0 ∧
        DifferentiableWithinAt ℝ v (Set.Iic z) z ∧
        derivWithin v (Set.Iic z) z = Real.exp z * (1 - q / d))

/-- Exercise 9.2(iii): full low-penalty reflected-game value, correct
strict upper barrier and exact zero-reflection cancelling boundary. -/
noncomputable def exercise9_2_iii : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (q δ : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hψ : 0 < ψ 1) (hq : ψ 1 < q) (hqd : q < d)
    (hδ : 0 < δ) (hScale : B1.IsScale ψ q W),
    ∀ z : ℝ, 0 < z → z < B1.russianThreshold q W →
      B1.scaleZ q W z = 1 + δ →
      ∀ x : ℝ, 0 ≤ x →
        B1.russianGameValue P F X q x δ =
          Real.exp x * B1.scaleZ q W (z - x) ∧
        B1.RussianGameSaddle P F X q x δ
          (fun ω => B1.firstStrictReflectedAbove X x z ω)
          (fun ω => sInf {t : WithTop ℝ≥0 |
            ∃ s : ℝ≥0,
              0 < s ∧ max x
                (B1.pathSupAt X s ω) - X s ω = 0 ∧
                t = (s : WithTop ℝ≥0)}) ∧
        ContinuousAt
          (fun y : ℝ => Real.exp y * B1.scaleZ q W (z - y)) z ∧
        ¬ B1.SmoothFitAt
          (fun y : ℝ => Real.exp y * B1.scaleZ q W (z - y)) z

/-- Source Exercise 9.2 is the conjunction of all its three complete
independently accessible, original-scope parts. -/
noncomputable def exercise9_2 : Prop :=
  exercise9_2_i ∧ exercise9_2_ii ∧ exercise9_2_iii

end Kyprianou.Ch09


