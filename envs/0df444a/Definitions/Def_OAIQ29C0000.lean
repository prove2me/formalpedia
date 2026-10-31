-- Prove2me | Definitions.Def_OAIQ29C0000
-- name    : OAIQ29C0000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:43:05.15897+00:00
-- url     : https://prove2.me/theorems/abba5973-9b23-4dee-881f-8964dff94e17
-- title:
--   Definitions bundle OAIQ29C0000 of the split of OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 489 declarations of OpenAI's Lean: 105 definitions, 1 inductive type or structure, 5 instances and 378 theorems. The definitions and types are `OAI.CAT0Fillings.AnalyticMinimizer.criticalMass`, `OAI.CAT0Fillings.AnalyticMinimizer.criticalNorm`, `OAI.CAT0Fillings.AnalyticMinimizer.energy`, `OAI.CAT0Fillings.BorelCoefficients.ActionIntegralAgreement`, `OAI.CAT0Fillings.BorelCoefficients.CoefficientList`, `OAI.CAT0Fillings.BorelCoefficients.borelAction`, `OAI.CAT0Fillings.BorelCoefficients.coefficientLinear`, `OAI.CAT0Fillings.BorelCoefficients.coefficientScale`, `OAI.CAT0Fillings.BorelCoefficients.currentBorelAction`, `OAI.CAT0Fillings.BorelCoefficients.l1Action`, `OAI.CAT0Fillings.BorelCoefficients.l2ToL1`, `OAI.CAT0Fillings.BorelCoefficients.l2ToL1Linear`, `OAI.CAT0Fillings.BorelCoefficients.levelClamp`, `OAI.CAT0Fillings.BorelCoefficients.lipAlgebra`, `OAI.CAT0Fillings.BorelCoefficients.lipToL1`, `OAI.CAT0Fillings.BorelCoefficients.lipToL2`, `OAI.CAT0Fillings.BorelCoefficients.normalizeCoefficients`, `OAI.CAT0Fillings.BorelCoefficients.weightedCurrent`, `OAI.CAT0Fillings.BorelRestriction.restrictCurrent`, `OAI.CAT0Fillings.BoundedLip.toBoundedContinuous`, `OAI.CAT0Fillings.ChartGeometry`, `OAI.CAT0Fillings.ChartGeometry.GraphAmbient`, `OAI.CAT0Fillings.ChartGeometry.Sobolev`, `OAI.CAT0Fillings.ChartGeometry.atlasDomain`, `OAI.CAT0Fillings.ChartGeometry.atlasMeasure`, `OAI.CAT0Fillings.ChartGeometry.atlasParam`, `OAI.CAT0Fillings.ChartGeometry.bivariateValue`, `OAI.CAT0Fillings.ChartGeometry.chordXi`, `OAI.CAT0Fillings.ChartGeometry.closedGradient`, `OAI.CAT0Fillings.ChartGeometry.closedGraph`, `OAI.CAT0Fillings.ChartGeometry.completedExpression`, `OAI.CAT0Fillings.ChartGeometry.composeValue`, `OAI.CAT0Fillings.ChartGeometry.constant`, `OAI.CAT0Fillings.ChartGeometry.coordinateL1`, `OAI.CAT0Fillings.ChartGeometry.coordinateMeasure`, `OAI.CAT0Fillings.ChartGeometry.covector`, `OAI.CAT0Fillings.ChartGeometry.density`, `OAI.CAT0Fillings.ChartGeometry.duNorm`, `OAI.CAT0Fillings.ChartGeometry.energyMeasure`, `OAI.CAT0Fillings.ChartGeometry.gradient` and 66 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `CAT0Fillings_Calculus_Atlas`, `CAT0Fillings_Calculus_Bivariate`, `CAT0Fillings_Calculus_ClosedChain`, `CAT0Fillings_Charts_Atoms`, `CAT0Fillings_Charts_ChangeVariables`, `CAT0Fillings_Charts_ContainingCharts`, `CAT0Fillings_Charts_Control`, `CAT0Fillings_Charts_DensityPush`, `CAT0Fillings_Charts_Differentiability`, `CAT0Fillings_Charts_DomainRestriction`, `CAT0Fillings_Charts_Extensions`, `CAT0Fillings_Charts_ImageRestriction`, `CAT0Fillings_Charts_IntegerSeries`, `CAT0Fillings_Charts_Jacobian`, `CAT0Fillings_Charts_LinearMass`, `CAT0Fillings_Charts_MultiplicityMass`, `CAT0Fillings_Charts_MultiplicityRestriction`, `CAT0Fillings_Charts_Orientation`, `CAT0Fillings_Charts_OverlapSum`, `CAT0Fillings_Charts_RectifiableMass`, `CAT0Fillings_Charts_Reparametrization`, `CAT0Fillings_Charts_Scalar`, `CAT0Fillings_Charts_Straightening`, `CAT0Fillings_Charts_Transitions`, `CAT0Fillings_Chord_GroundProducts`, `CAT0Fillings_Chord_NonnegativeMeasure`, `CAT0Fillings_Chord_RadialIntegral`, `CAT0Fillings_Compactness_ChartDensity`, `CAT0Fillings_Compactness_Coordinates`, `CAT0Fillings_Compactness_IntrinsicBV`, `CAT0Fillings_Currents_ActionLimits`, `CAT0Fillings_Currents_ActionSeries`, `CAT0Fillings_Currents_AtomCompactness`, `CAT0Fillings_Currents_Atoms`, `CAT0Fillings_Currents_Basic`, `CAT0Fillings_Currents_BorelAction`, `CAT0Fillings_Currents_BoundaryMass`, `CAT0Fillings_Currents_CanonicalMass`, `CAT0Fillings_Currents_ChartSums`, `CAT0Fillings_Currents_ComponentMass`, `CAT0Fillings_Currents_Contraction`, `CAT0Fillings_Currents_CountableTests`, `CAT0Fillings_Currents_DenseTests`, `CAT0Fillings_Currents_DisjointUnions`, `CAT0Fillings_Currents_FiniteAtoms`, `CAT0Fillings_Currents_MassBounds`, `CAT0Fillings_Currents_Multilinear`, `CAT0Fillings_Currents_Negation`, `CAT0Fillings_Currents_ProductRule`, `CAT0Fillings_Currents_Restriction`, `CAT0Fillings_Currents_Summation`, `CAT0Fillings_Currents_TestBounds`, `CAT0Fillings_Currents_WeakClosure`, `CAT0Fillings_Currents_WeakCompactness`, `CAT0Fillings_Currents_WeakMass`, `CAT0Fillings_Currents_WeightedAction`, `CAT0Fillings_Differentiation_Density`, `CAT0Fillings_Differentiation_HilbertCharts`, `CAT0Fillings_Differentiation_ScalarBound`, `CAT0Fillings_Fillings_WeightedCone`, `CAT0Fillings_Geometry_Determinant`, `CAT0Fillings_Geometry_Polarization`, `CAT0Fillings_Gradient_Chart`, `CAT0Fillings_Gradient_ClosedLinear`, `CAT0Fillings_Gradient_CyclePairing`, `CAT0Fillings_Gradient_HilbertAtlas`, `CAT0Fillings_Mass_Approximation`, `CAT0Fillings_Mass_Convolution`, `CAT0Fillings_Mass_TestDensity`, `CAT0Fillings_Minimizers_CriticalEnergy`, `CAT0Fillings_Radial_TestBound`, `CAT0Fillings_Slices_Approximation`, `CAT0Fillings_Slices_BorelAction`, `CAT0Fillings_Slices_FullCarrier`, `CAT0Fillings_Slices_FullSlices`, `CAT0Fillings_Slices_NormalBudget`, `CAT0Fillings_Slices_WeakApproximation`, `CAT0Fillings_Slicing_BoundaryTests`, `CAT0Fillings_Slicing_CoordinateCoarea`, `CAT0Fillings_Slicing_EuclideanSplit`, `CAT0Fillings_Slicing_GeneralCoarea`, `CAT0Fillings_Slicing_NormalRestriction`, `CAT0Fillings_Slicing_Profiles`, `CAT0Fillings_Slicing_RectifiableCoarea`, `CAT0Fillings_Slicing_SmoothCutoff`, `CAT0Fillings_Slicing_Superlevels`, `CAT0Fillings_Slicing_WeakRestriction`, `CAT0Fillings_Slicing_WeakSlices`, `CAT0Fillings_Sobolev_Completion`, `CAT0Fillings_Sobolev_Constant`, `CAT0Fillings_Sobolev_CriticalNorm`, `CAT0Fillings_Swept_Current`, `CAT0Fillings_Swept_Measure`, `CAT0Fillings_Tangent_Coordinates`.
--
--   **Imports.** It imports the published bundle `Def_SharpCAT0Filling`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ29C0002`; the statements `OAI.CAT0Fillings.ChartGeometry.closed_added_tests`, `OAI.CAT0Fillings.ChartGeometry.closed_chord_product` and `OAI.CAT0Fillings.ChartGeometry.inclusion_compact`.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_SharpCAT0Filling

section
-- module Solutions.OAIQ29_C0.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_DensityPush
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open MeasureTheory

noncomputable def densityPush {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (φ : α → β) (ρ : α → ℝ) : Measure β :=
  Measure.map φ (μ.withDensity (fun x => ENNReal.ofReal (ρ x)))

lemma densityPush_finite {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (φ : α → β) {ρ : α → ℝ} (hρ : Integrable ρ μ) :
    IsFiniteMeasure (densityPush μ φ ρ) := by
  let := isFiniteMeasure_withDensity_ofReal hρ.hasFiniteIntegral
  exact MeasureTheory.Measure.isFiniteMeasure_map _ _

lemma integral_densityPush {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) {ρ : α → ℝ}
    (hρ : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    {b : β → ℝ} (hb : Continuous b) :
    (∫ x, b x ∂densityPush μ φ ρ) = ∫ z, ρ z*b (φ z) ∂μ := by
  rw [densityPush,integral_map hφ.aemeasurable hb.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ0] with z hz
  simp only [ENNReal.toReal_ofReal hz,smul_eq_mul]

lemma integral_densityPush_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) {ρ : α → ℝ}
    (hρ : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    {b : β → ℝ} (hb : Measurable b) :
    (∫ x, b x ∂densityPush μ φ ρ) = ∫ z, ρ z*b (φ z) ∂μ := by
  rw [densityPush,integral_map hφ.aemeasurable hb.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ0] with z hz
  simp only [ENNReal.toReal_ofReal hz,smul_eq_mul]

section BorelChartTests
variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
lemma integrable_weighted_comp (μ : Measure Z) {φ : Z → X} (hφ : Measurable φ)
    {w : Z → ℝ} (hw : Integrable w μ) {b : X → ℝ}
    (hb : Measurable b) (hB : ∃ M : ℝ, ∀ x, |b x| ≤ M) :
    Integrable (fun z => w z * b (φ z)) μ := by
  obtain ⟨M,hM⟩ := hB
  exact hw.mul_bdd (hb.comp hφ).aestronglyMeasurable
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hM (φ z))

end BorelChartTests
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]

namespace BoundedLip
omit [MeasurableSpace X] in
lemma continuous {b : X → ℝ} (hb : BoundedLip b) : Continuous b :=
  hb.1.choose_spec.continuous

omit [MeasurableSpace X] in
lemma const (a : ℝ) : BoundedLip (fun _ : X => a) := by
  exact ⟨⟨0, LipschitzWith.const a⟩, |a|, fun _ => le_rfl⟩

omit [MeasurableSpace X] in
lemma add {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c) :
    BoundedLip (fun x => b x + c x) := by
  obtain ⟨⟨Kb, hKb⟩, Mb, hMb⟩ := hb
  obtain ⟨⟨Kc, hKc⟩, Mc, hMc⟩ := hc
  refine ⟨⟨Kb + Kc, hKb.add hKc⟩, Mb + Mc, ?_⟩
  intro x
  exact (abs_add_le _ _).trans (add_le_add (hMb x) (hMc x))

omit [MeasurableSpace X] in
lemma const_mul (a : ℝ) {b : X → ℝ} (hb : BoundedLip b) :
    BoundedLip (fun x => a * b x) := by
  obtain ⟨⟨K, hK⟩, M, hM⟩ := hb
  refine ⟨⟨⟨|a|, abs_nonneg a⟩ * K, ?_⟩, |a| * M, ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    change dist (a * b x) (a * b y) ≤ (|a| * (K : ℝ)) * dist x y
    rw [Real.dist_eq, ← mul_sub, abs_mul]
    calc |a| * |b x - b y| ≤ |a| * ((K : ℝ) * dist x y) :=
           mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) (abs_nonneg a)
         _ = _ := by ring
  · intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg a)
end BoundedLip

lemma isMetricCurrent_zero (k : ℕ) : IsMetricCurrent (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) where
  offDomain := by intros; rfl
  linearFirst := by intros; simp
  linearCoord := by intros; simp
  sequentialContinuity := by intros; exact tendsto_const_nhds
  locality := by intros; rfl
  finiteMass := by
    refine ⟨0, inferInstance, ?_⟩
    intro b π hb hπ
    simp

lemma mass_nonneg {k : ℕ} (T : Functional X k) : 0 ≤ mass T := by
  apply Real.sInf_nonneg
  rintro r ⟨μ, _, _, rfl⟩
  exact ENNReal.toReal_nonneg

lemma mass_le_measure {k : ℕ} {T : Functional X k} {μ : Measure X}
    (hμ : IsFiniteMeasure μ) (hT : Controls T μ) : mass T ≤ μ.real univ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨ν, _, _, rfl⟩
    exact ENNReal.toReal_nonneg
  · exact ⟨μ, hμ, hT, rfl⟩

@[simp] lemma mass_zero (k : ℕ) : mass (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) = 0 := by
  apply le_antisymm
  · have h : Controls (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) (0 : Measure X) := by
      intro b π hb hπ
      simp
    simpa using mass_le_measure (μ := (0 : Measure X)) inferInstance h
  · exact mass_nonneg _

omit [MeasurableSpace X] in
@[simp] lemma boundarySucc_zero (k : ℕ) :
    boundarySucc (fun (_ : X → ℝ) (_ : Fin (k+1) → X → ℝ) => 0) = fun _ _ => 0 := by
  funext b π
  simp [boundarySucc]

omit [MeasurableSpace X] in
@[simp] lemma boundary_zero (k : ℕ) :
    boundary (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) = fun _ _ => 0 := by
  cases k with
  | zero => rfl
  | succ k => exact boundarySucc_zero k

noncomputable def emptyChart (k : ℕ) : IntegerChart X k where
  domain := ∅
  borel := MeasurableSet.empty
  bounded := Bornology.isBounded_empty
  param := fun z => False.elim z.property
  bilipschitz := by
    refine ⟨0, 0, ?_, ?_⟩
    · apply lipschitzWith_iff_dist_le_mul.mpr
      intro a b
      exact False.elim a.property
    · intro a b
      exact False.elim a.property
  multiplicity := fun _ => 0
  integrable := by simp

omit [MeasurableSpace X] in
@[simp] lemma emptyChart_image (k : ℕ) : (emptyChart (X := X) k).image = ∅ := by
  ext x
  simp [IntegerChart.image, emptyChart]

omit [MeasurableSpace X] in
@[simp] lemma emptyChart_action (k : ℕ) :
    (emptyChart (X := X) k).action = fun _ _ => 0 := by
  funext b π
  simp [IntegerChart.action, emptyChart]

lemma integerRectifiable_zero (k : ℕ) :
    IntegerRectifiable (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) := by
  refine ⟨fun _ => emptyChart k, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp
  · intro i
    rw [emptyChart_action]
    exact isMetricCurrent_zero k
  · simp only [emptyChart_action, mass_zero]
    exact summable_zero
  · intro b π
    simp

lemma isIntegral_zero (k : ℕ) :
    IsIntegral k (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) := by
  cases k with
  | zero => exact ⟨isMetricCurrent_zero 0, integerRectifiable_zero 0⟩
  | succ k =>
    refine ⟨isMetricCurrent_zero _, integerRectifiable_zero _, ?_, ?_⟩
    · rw [boundarySucc_zero]
      exact isMetricCurrent_zero k
    · rw [boundarySucc_zero]
      exact integerRectifiable_zero k

end Foundations
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Multilinear
attribute [-simp] _root_.OAI.CAT0Fillings.boundarySucc_zero _root_.OAI.CAT0Fillings.boundary_zero _root_.OAI.CAT0Fillings.emptyChart_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
omit [MeasurableSpace X] in
lemma lipschitz_mul_real {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (a : ℝ) :
    LipschitzWith (⟨|a|, abs_nonneg a⟩ * K) (fun x => a * f x) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  change dist (a * f x) (a * f y) ≤ (|a| * (K : ℝ)) * dist x y
  rw [Real.dist_eq, ← mul_sub, abs_mul]
  calc |a| * |f x - f y| ≤ |a| * ((K : ℝ) * dist x y) :=
         mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (abs_nonneg a)
       _ = _ := by ring

def lipSubmodule : Submodule ℝ (X → ℝ) where
  carrier := {f | ∃ K : ℝ≥0, LipschitzWith K f}
  zero_mem' := ⟨0, LipschitzWith.const 0⟩
  add_mem' := by
    rintro f g ⟨K, hK⟩ ⟨L, hL⟩
    exact ⟨K + L, hK.add hL⟩
  smul_mem' := by
    intro a f hf
    obtain ⟨K, hK⟩ := hf
    exact ⟨_, lipschitz_mul_real hK a⟩

omit [MeasurableSpace X] in
lemma lip_coe_update {k : ℕ} (π : Fin k → lipSubmodule (X := X))
    (i : Fin k) (f : lipSubmodule (X := X)) :
    (fun j => ((Function.update π i f) j : X → ℝ)) =
      Function.update (fun j => (π j : X → ℝ)) i (f : X → ℝ) := by
  funext j
  by_cases h : j = i <;> simp [h]

noncomputable def IsMetricCurrent.multilinear {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (b : X → ℝ) (hb : BoundedLip b) :
    MultilinearMap ℝ (fun _ : Fin k => lipSubmodule (X := X)) ℝ :=
  MultilinearMap.mk' (fun π => T b (fun i => π i)) (by
    intro π i f g
    have h := hT.linearCoord b
      (fun j => ((Function.update π i f) j : X → ℝ)) i (g : X → ℝ) 1 1
      ⟨hb, fun j => ((Function.update π i f) j).property⟩ g.property
    simpa only [lip_coe_update, Function.update_self, one_mul,
      Function.update_idem, Submodule.coe_add, Pi.add_def] using h) (by
    intro π i a f
    have h := hT.linearCoord b
      (fun j => ((Function.update π i f) j : X → ℝ)) i (f : X → ℝ) a 0
      ⟨hb, fun j => ((Function.update π i f) j).property⟩ f.property
    simpa only [lip_coe_update, Function.update_self, zero_mul, add_zero,
      Function.update_idem, Submodule.coe_smul, Pi.smul_def, smul_eq_mul] using h)

lemma IsMetricCurrent.scale_coordinates {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b : X → ℝ} (hb : BoundedLip b)
    {π : Fin k → X → ℝ} (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (a : Fin k → ℝ) :
    T b (fun i x => a i * π i x) = (∏ i, a i) * T b π := by
  let p : Fin k → lipSubmodule (X := X) := fun i => ⟨π i, hπ i⟩
  exact (hT.multilinear b hb).map_smul_univ a p

lemma IsMetricCurrent.eq_zero_of_const_coord {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (i : Fin k) (c : ℝ) (hc : ∀ x, π i x = c) :
    T b π = 0 := by
  apply hT.locality b π h
  exact ⟨i, univ, c, isOpen_univ, subset_univ _, fun x _ => hc x⟩

lemma IsMetricCurrent.eq_zero_of_zero_lipschitz_coord {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (i : Fin k) (hi : LipschitzWith 0 (π i)) :
    T b π = 0 := by
  cases isEmpty_or_nonempty X with
  | inl hempty =>
    let := hempty
    exact hT.eq_zero_of_const_coord h i 0 (fun x => isEmptyElim x)
  | inr hnonempty =>
    obtain ⟨x₀⟩ := hnonempty
    apply hT.eq_zero_of_const_coord h i (π i x₀)
    intro x
    apply dist_le_zero.mp
    simpa using hi.dist_le_mul x x₀

end Foundations
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_MassBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
lemma IsMetricCurrent.mass_bound {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {μ : Measure X} (hμ : Controls T μ)
    {b : X → ℝ} (hb : BoundedLip b) {π : Fin k → X → ℝ}
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |T b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := by
  by_cases hzero : ∃ i, K i = 0
  · obtain ⟨i, hi⟩ := hzero
    have hTi := hT.eq_zero_of_zero_lipschitz_coord ⟨hb, fun j => ⟨K j, hK j⟩⟩ i
      (hi ▸ hK i)
    rw [hTi, abs_zero]
    exact mul_nonneg (Finset.prod_nonneg fun j _ => (K j).coe_nonneg)
      (integral_nonneg fun x => abs_nonneg (b x))
  · have hpos : ∀ i, 0 < K i := fun i => pos_iff_ne_zero.mpr (fun hi => hzero ⟨i, hi⟩)
    have hposR : ∀ i, (0 : ℝ) < K i := fun i => hpos i
    let π' : Fin k → X → ℝ := fun i x => (K i : ℝ)⁻¹ * π i x
    have hπ' : ∀ i, LipschitzWith 1 (π' i) := by
      intro i
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      change dist ((K i : ℝ)⁻¹ * π i x) ((K i : ℝ)⁻¹ * π i y) ≤ 1 * dist x y
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr (hposR i)), one_mul]
      calc (K i : ℝ)⁻¹ * |π i x - π i y| ≤
          (K i : ℝ)⁻¹ * ((K i : ℝ) * dist x y) :=
            mul_le_mul_of_nonneg_left ((hK i).dist_le_mul x y) (inv_nonneg.mpr (hposR i).le)
        _ = dist x y := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hposR i)), one_mul]
    have heq : (fun i x => (K i : ℝ) * π' i x) = π := by
      funext i x
      dsimp [π']
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hposR i)), one_mul]
    have hscale := hT.scale_coordinates hb (fun i => ⟨1, hπ' i⟩) (fun i => (K i : ℝ))
    rw [heq] at hscale
    rw [hscale, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)]
    exact mul_le_mul_of_nonneg_left (hμ b π' hb hπ')
      (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)

open scoped BoundedContinuousFunction

omit [MeasurableSpace X] in
noncomputable def BoundedLip.toBoundedContinuous {b : X → ℝ} (hb : BoundedLip b) :
    X →ᵇ ℝ where
  toFun := b
  continuous_toFun := hb.continuous
  map_bounded' := by
    obtain ⟨M, hM⟩ := hb.2
    refine ⟨M + M, fun x y => ?_⟩
    calc dist (b x) (b y) ≤ dist (b x) 0 + dist 0 (b y) := dist_triangle _ _ _
         _ ≤ M + M := by simpa using add_le_add (hM x) (hM y)

variable [BorelSpace X]

lemma continuous_integral_abs_boundedLip {b : X → ℝ} (hb : BoundedLip b) :
    Continuous (fun μ : FiniteMeasure X => ∫ x, |b x| ∂(μ : Measure X)) := by
  let f : X →ᵇ ℝ :=
    { toFun := fun x => |b x|
      continuous_toFun := continuous_abs.comp hb.continuous
      map_bounded' := by
        obtain ⟨M, hM⟩ := hb.2
        refine ⟨M + M, fun x y => ?_⟩
        calc dist |b x| |b y| ≤ dist |b x| 0 + dist 0 |b y| := dist_triangle _ _ _
             _ ≤ M + M := by simpa using add_le_add (hM x) (hM y) }
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id f

lemma isClosed_controls {k : ℕ} (T : Functional X k) :
    IsClosed {μ : FiniteMeasure X | Controls T (μ : Measure X)} := by
  simp only [Controls, ofPred_forall]
  apply isClosed_iInter
  intro b
  apply isClosed_iInter
  intro π
  apply isClosed_iInter
  intro hb
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (continuous_integral_abs_boundedLip hb)

lemma IsMetricCurrent.exists_controls_mass_eq [CompactSpace X] {k : ℕ}
    {T : Functional X k} (hT : IsMetricCurrent T) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls T μ ∧ mass T = μ.real univ := by
  obtain ⟨μ₀, hμ₀, hTμ₀⟩ := hT.finiteMass
  let ν₀ : FiniteMeasure X := ⟨μ₀, hμ₀⟩
  let C : Set (FiniteMeasure X) := {ν | ν.mass ≤ ν₀.mass} ∩ {ν | Controls T (ν : Measure X)}
  have hC : IsCompact C :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X ν₀.mass).inter_right (isClosed_controls T)
  have hne : C.Nonempty := by
    refine ⟨ν₀, ?_⟩
    change ν₀.mass ≤ ν₀.mass ∧ Controls T (ν₀ : Measure X)
    exact ⟨le_rfl, hTμ₀⟩
  obtain ⟨ν, hν, hmin⟩ := hC.exists_isMinOn hne
    FiniteMeasure.continuous_mass.continuousOn
  change ν.mass ≤ ν₀.mass ∧ Controls T (ν : Measure X) at hν
  have hmin' (η : FiniteMeasure X) (hη : Controls T (η : Measure X)) : ν.mass ≤ η.mass := by
    by_cases hle : η.mass ≤ ν₀.mass
    · exact hmin ⟨hle, hη⟩
    · exact hν.1.trans (le_of_not_ge hle)
  refine ⟨ν, inferInstance, hν.2, le_antisymm (mass_le_measure inferInstance hν.2) ?_⟩
  apply le_csInf
  · exact ⟨μ₀.real univ, μ₀, hμ₀, hTμ₀, rfl⟩
  · rintro r ⟨η, hη, htη, rfl⟩
    exact hmin' ⟨η, hη⟩ htη

end Foundations
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_WeakMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
open scoped BoundedContinuousFunction

variable [BorelSpace X]
lemma controls_of_weak_limits {ι : Type*} {l : Filter ι} [NeBot l]
    {k : ℕ} {Ts : ι → Functional X k} {T : Functional X k}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (hc : ∀ j, Controls (Ts j) (μs j : Measure X))
    (hT : ∀ b π, Admissible b π →
      Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) : Controls T (μ : Measure X) := by
  intro b π hb hπ
  exact le_of_tendsto_of_tendsto
    (Filter.Tendsto.abs (hT b π ⟨hb, fun i => ⟨1, hπ i⟩⟩))
    ((continuous_integral_abs_boundedLip hb).tendsto μ |>.comp hμ)
    (Eventually.of_forall fun j => hc j b π hb hπ)

lemma exists_controls_of_bounded_weak_limit [CompactSpace X]
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X k} {T : Functional X k} (M : ℝ≥0)
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hbound : ∀ j, mass (Ts j) ≤ (M : ℝ))
    (hlim : ∀ b π, Admissible b π → Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls T μ ∧ μ.real univ ≤ (M : ℝ) := by
  choose μj hfin hcontrol heq using fun j => (hTs j).exists_controls_mass_eq
  let νs : ι → FiniteMeasure X := fun j => ⟨μj j, hfin j⟩
  have hbound' : ∀ j, νs j ∈ {ν : FiniteMeasure X | ν.mass ≤ M} := by
    intro j
    change (νs j).mass ≤ M
    apply NNReal.coe_le_coe.mp
    change (μj j).real univ ≤ (M : ℝ)
    rw [← heq]
    exact hbound j
  obtain ⟨ν, hν, hcluster⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X M).exists_mapClusterPt_of_frequently (l := l)
      (Eventually.of_forall hbound').frequently
  let l' := comap νs (𝓝 ν) ⊓ l
  have hl' : NeBot l' := neBot_inf_comap_iff_map'.mpr hcluster
  let := hl'
  have hνs : Tendsto νs l' (𝓝 ν) := tendsto_iff_comap.mpr inf_le_left
  have hctrl : Controls T (ν : Measure X) :=
    controls_of_weak_limits hνs hcontrol (fun b π h => (hlim b π h).mono_left inf_le_right)
  exact ⟨ν, inferInstance, hctrl, NNReal.coe_le_coe.mpr hν⟩

lemma mass_le_of_bounded_weak_limit [CompactSpace X]
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X k} {T : Functional X k} (M : ℝ≥0)
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hbound : ∀ j, mass (Ts j) ≤ (M : ℝ))
    (hlim : ∀ b π, Admissible b π → Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    mass T ≤ (M : ℝ) := by
  obtain ⟨μ, hfin, hcontrol, hmass⟩ :=
    exists_controls_of_bounded_weak_limit M hTs hbound hlim
  exact (mass_le_measure hfin hcontrol).trans hmass

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedLip.mul {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c) :
    BoundedLip (fun x => b x * c x) := by
  obtain ⟨⟨Kb, hKb⟩, Mb, hMb⟩ := hb
  obtain ⟨⟨Kc, hKc⟩, Mc, hMc⟩ := hc
  let B : ℝ≥0 := ⟨max Mb 0, le_max_right _ _⟩
  let C : ℝ≥0 := ⟨max Mc 0, le_max_right _ _⟩
  have hB (x : X) : |b x| ≤ (B : ℝ) := (hMb x).trans (le_max_left _ _)
  have hC (x : X) : |c x| ≤ (C : ℝ) := (hMc x).trans (le_max_left _ _)
  refine ⟨⟨B * Kc + C * Kb, ?_⟩, (B : ℝ) * (C : ℝ), ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    rw [Real.dist_eq]
    calc |b x * c x - b y * c y| = |b x * (c x - c y) + (b x - b y) * c y| := by
            congr 1; ring
      _ ≤ |b x| * |c x - c y| + |b x - b y| * |c y| := by
            simpa only [abs_mul] using abs_add_le (b x * (c x - c y)) ((b x - b y) * c y)
      _ ≤ (B : ℝ) * ((Kc : ℝ) * dist x y) + ((Kb : ℝ) * dist x y) * (C : ℝ) := by
            apply add_le_add
            · exact mul_le_mul (hB x) (hKc.dist_le_mul x y) (abs_nonneg _) B.coe_nonneg
            · exact mul_le_mul (hKb.dist_le_mul x y) (hC y) (abs_nonneg _)
                (mul_nonneg Kb.coe_nonneg dist_nonneg)
      _ = ((B * Kc + C * Kb : ℝ≥0) : ℝ) * dist x y := by push_cast; ring
  · intro x
    rw [abs_mul]
    exact mul_le_mul (hB x) (hC x) (abs_nonneg _) B.coe_nonneg

lemma IsMetricCurrent.mass_bound_uniform [CompactSpace X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {b : X → ℝ} (hb : BoundedLip b) {π : Fin k → X → ℝ}
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i))
    {M : ℝ} (hM : ∀ x, |b x| ≤ M) :
    |T b π| ≤ ((∏ i, (K i : ℝ)) * M) * mass T := by
  obtain ⟨μ, hfin, hcontrol, heq⟩ := hT.exists_controls_mass_eq
  let := hfin
  have hint : Integrable (fun x => |b x|) μ := (hb.toBoundedContinuous.integrable μ).abs
  have hbound : (∫ x, |b x| ∂μ) ≤ μ.real univ * M := by
    simpa using integral_mono hint (integrable_const M) hM
  calc |T b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := hT.mass_bound hcontrol hb K hK
    _ ≤ (∏ i, (K i : ℝ)) * (μ.real univ * M) :=
      mul_le_mul_of_nonneg_left hbound (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)
    _ = ((∏ i, (K i : ℝ)) * M) * mass T := by rw [heq]; ring

lemma IsMetricCurrent.eq_zero_of_mass_eq_zero [CompactSpace X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) (hm : mass T = 0) :
    T = fun _ _ => 0 := by
  funext b π
  by_cases h : Admissible b π
  · choose K hK using h.2
    obtain ⟨M, hM⟩ := h.1.2
    have hle := hT.mass_bound_uniform h.1 K hK hM
    rw [hm, mul_zero] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · exact hT.offDomain b π h

end Foundations
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_DenseTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
open scoped BoundedContinuousFunction

variable [BorelSpace X]
lemma summable_actions_of_summable_masses [CompactSpace X]
    {k : ℕ} {Ts : ℕ → Functional X k} (hTs : ∀ j, IsMetricCurrent (Ts j))
    (hsum : Summable fun j => mass (Ts j)) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) : Summable fun j => Ts j b π := by
  choose K hK using h.2
  obtain ⟨M, hM⟩ := h.1.2
  apply (hsum.mul_left ((∏ i, (K i : ℝ)) * M)).of_norm_bounded
  intro j
  exact (hTs j).mass_bound_uniform h.1 K hK hM

end Foundations

lemma tendsto_of_lipschitz_dense {A : Type*} [PseudoMetricSpace A]
    {ι : Type*} {l : Filter ι} {f : ι → A → ℝ} {g : A → ℝ}
    {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j)) (hg : LipschitzWith K g)
    {κ : Type*} {D : κ → A} (hD : DenseRange D)
    (hlim : ∀ i, Tendsto (fun j => f j (D i)) l (𝓝 (g (D i))))
    (x : A) : Tendsto (fun j => f j x) l (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨i, hi⟩ := hD.exists_dist_lt x hδ
  have hdr : (K : ℝ) * dist x (D i) < ε / 4 := by
    have hpos : 0 < (K : ℝ) + 1 := by positivity
    have hm := (mul_lt_mul_of_pos_left hi hpos)
    have heq : ((K : ℝ) + 1) * δ = ε / 4 := by
      dsimp [δ]
      field_simp
    rw [heq] at hm
    calc (K : ℝ) * dist x (D i) ≤ ((K : ℝ) + 1) * dist x (D i) := by
          nlinarith [dist_nonneg (x := x) (y := D i)]
      _ < _ := hm
  filter_upwards [(Metric.tendsto_nhds.mp (hlim i)) (ε / 2) (half_pos hε)] with j hj
  calc dist (f j x) (g x) ≤
      dist (f j x) (f j (D i)) + dist (f j (D i)) (g (D i)) + dist (g (D i)) (g x) :=
        (dist_triangle _ (g (D i)) _).trans (add_le_add (dist_triangle _ (f j (D i)) _) le_rfl)
    _ < ε / 4 + ε / 2 + ε / 4 := by
      apply add_lt_add
      · exact add_lt_add ((hf j).dist_le_mul x (D i) |>.trans_lt hdr) hj
      · rw [dist_comm]
        exact (hg.dist_le_mul x (D i)).trans_lt hdr
    _ = ε := by ring

namespace BorelCoefficients

variable {X : Type u} [MetricSpace X] [CompactSpace X]

def lipAlgebra : Subalgebra ℝ C(X, ℝ) where
  carrier := {f | BoundedLip f}
  algebraMap_mem' r := BoundedLip.const r
  add_mem' hf hg := BoundedLip.add hf hg
  mul_mem' hf hg := BoundedLip.mul hf hg

lemma lipAlgebra_separates : (lipAlgebra (X := X)).SeparatesPoints := by
  intro x y hxy
  let f : C(X, ℝ) := ⟨fun z => dist z x, continuous_id.dist continuous_const⟩
  have hf : BoundedLip f := by
    refine ⟨⟨1, LipschitzWith.dist_left x⟩, ‖f‖, ?_⟩
    intro z
    exact (ContinuousMap.norm_coe_le_norm f z)
  refine ⟨f, ⟨f, hf, rfl⟩, ?_⟩
  change dist x x ≠ dist y x
  simpa only [dist_self, ne_eq, eq_comm, dist_eq_zero] using hxy.symm

lemma lipAlgebra_dense : DenseRange (fun f : lipAlgebra (X := X) => (f : C(X, ℝ))) := by
  rw [denseRange_iff_closure_range]
  rw [Subtype.range_coe_subtype]
  change closure (lipAlgebra (X := X) : Set C(X, ℝ)) = univ
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (lipAlgebra (X := X)) lipAlgebra_separates
  exact congrArg (fun A : Subalgebra ℝ C(X, ℝ) => (A : Set C(X, ℝ))) h

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def lipToL1 : lipAlgebra (X := X) →ₗ[ℝ] Lp ℝ 1 μ :=
  (ContinuousMap.toLp 1 μ ℝ).toLinearMap.comp (lipAlgebra (X := X)).val.toLinearMap

lemma lipToL1_dense : DenseRange (lipToL1 μ) := by
  apply (ContinuousMap.toLp_denseRange ℝ μ ℝ (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp
    lipAlgebra_dense (ContinuousMap.toLp 1 μ ℝ).continuous

lemma norm_lipToL1 (f : lipAlgebra (X := X)) :
    ‖lipToL1 μ f‖ = ∫ x, |f.val x| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f.val] with x hx
  change ‖(ContinuousMap.toLp 1 μ ℝ f.val) x‖ = |f.val x|
  rw [hx, Real.norm_eq_abs]

lemma exists_lipschitz_approximation {b : X → ℝ} (hb : Integrable b μ) :
    ∃ f : ℕ → lipAlgebra (X := X),
      Tendsto (fun j => ∫ x, |(f j).val x-b x| ∂μ) atTop (𝓝 0) := by
  obtain ⟨u,hu,hulim⟩ := mem_closure_iff_seq_limit.mp ((lipToL1_dense μ) hb.toL1)
  choose f hf using hu
  have hfun : (fun j => lipToL1 μ (f j)) = u := funext hf
  have hf := hfun ▸ hulim
  refine ⟨f,?_⟩
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero).mp hf
  convert hnorm using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (lipToL1 μ (f j)) hb.toL1,
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ (f j).val,
    hb.coeFn_toL1] with x hx hfx hbx
  change |(f j).val x-b x| = ‖(lipToL1 μ (f j)-hb.toL1) x‖
  rw [hx]
  change _ = ‖(ContinuousMap.toLp 1 μ ℝ (f j).val) x - (hb.toL1) x‖
  rw [hfx,hbx,Real.norm_eq_abs]

end BorelCoefficients
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Control
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open MeasureTheory

section BorelChartTests
variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
theorem signed_chart_control_borel (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : Measurable φ) {w : Z → ℝ} (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν)
    {b : X → ℝ} (hb : Measurable b) (hB : ∃ M : ℝ, ∀ x, |b x| ≤ M) :
    |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν := by
  let τ := densityPush μ φ (fun z => |w z|)
  let : IsFiniteMeasure τ := densityPush_finite μ φ hw.abs
  let η := ν+τ
  have hνη : ν ≤ η := Measure.le_add_right le_rfl
  have hτη : τ ≤ η := Measure.le_add_left le_rfl
  have hbi : Integrable b η := by
    obtain ⟨M,hM⟩ := hB
    exact Integrable.of_bound hb.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x)
  obtain ⟨f,hf⟩ := BorelCoefficients.exists_lipschitz_approximation η hbi
  have hfi (j : ℕ) : Integrable ((f j).val) η :=
    (f j).val.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hwb : Integrable (fun z => w z*b (φ z)) μ :=
    integrable_weighted_comp μ hφ hw hb hB
  have hwf (j : ℕ) : Integrable (fun z => w z*(f j).val (φ z)) μ :=
    integrable_weighted_comp μ hφ hw (f j).val.continuous.measurable (f j).property.2
  have hflim : Tendsto (fun j => ∫ z, w z*(f j).val (φ z) ∂μ) atTop
      (𝓝 (∫ z, w z*b (φ z) ∂μ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq,←integral_sub (hwf j) hwb]
    calc |∫ z, w z*(f j).val (φ z)-w z*b (φ z) ∂μ| ≤
          ∫ z, |w z| * |(f j).val (φ z)-b (φ z)| ∂μ := by
            simpa only [←mul_sub,Real.norm_eq_abs,abs_mul] using
              norm_integral_le_integral_norm
                (fun z => w z*(f j).val (φ z)-w z*b (φ z))
      _ = ∫ x, |(f j).val x-b x| ∂τ :=
          (integral_densityPush_measurable μ hφ hw.abs
            (Eventually.of_forall fun _ => abs_nonneg _)
            ((f j).val.continuous.measurable.sub hb).abs).symm
      _ ≤ ∫ x, |(f j).val x-b x| ∂η :=
          integral_mono_measure hτη (Eventually.of_forall fun _ => abs_nonneg _)
            ((hfi j).sub hbi).abs
  have hib : Integrable b ν := hbi.mono_measure hνη
  have hfint : Tendsto (fun j => ∫ x, |(f j).val x| ∂ν) atTop
      (𝓝 (∫ x, |b x| ∂ν)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq,←integral_sub ((hfi j).mono_measure hνη).abs hib.abs]
    calc |∫ x, |(f j).val x|-|b x| ∂ν| ≤ ∫ x, abs (|(f j).val x|-|b x|) ∂ν := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun x => |(f j).val x|-|b x|)
      _ ≤ ∫ x, |(f j).val x-b x| ∂ν :=
          integral_mono_ae (((hfi j).mono_measure hνη).abs.sub hib.abs).abs
            (((hfi j).mono_measure hνη).sub hib).abs
            (Eventually.of_forall fun x => abs_abs_sub_abs_le _ _)
      _ ≤ ∫ x, |(f j).val x-b x| ∂η :=
          integral_mono_measure hνη (Eventually.of_forall fun _ => abs_nonneg _)
            ((hfi j).sub hbi).abs
  exact le_of_tendsto_of_tendsto hflim.abs hfint
    (Eventually.of_forall fun j => hcontrol _ (f j).property)
end BorelChartTests
end CAT0Fillings

namespace CAT0Fillings
open MeasureTheory Set

variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma signed_chart_control_dominates_on_of_measurable
    (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : Measurable φ) {s₀ : Set Z}
    (hμ : ∀ᵐ z ∂μ, z ∈ s₀)
    (he : MeasurableEmbedding (fun z : s₀ => φ (z : Z))) {w : Z → ℝ}
    (hwm : Measurable w) (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν) :
    densityPush μ φ (fun z => |w z|) ≤ ν := by
  classical
  let τ := densityPush μ φ (fun z => |w z|)
  let : IsFiniteMeasure τ := densityPush_finite μ φ hw.abs
  let σ : Z → ℝ := fun z => if w z < 0 then -1 else 1
  have hσm : Measurable σ :=
    Measurable.piecewise (measurableSet_lt hwm measurable_const) measurable_const measurable_const
  have hσabs (z : Z) : |σ z| = 1 := by simp [σ]; split <;> norm_num
  have hσmul (z : Z) : w z * σ z = |w z| := by
    by_cases hz : w z < 0
    · simp [σ,hz,abs_of_neg hz]
    · simp [σ,hz,abs_of_nonneg (le_of_not_gt hz)]
  let σe : X → ℝ := Function.extend (fun z : s₀ => φ (z : Z)) (fun z : s₀ => σ (z : Z)) (fun _ => 0)
  have hσem : Measurable σe := he.measurable_extend (hσm.comp measurable_subtype_coe) measurable_const
  have hσee (z : Z) (hz : z ∈ s₀) : σe (φ z) = σ z :=
    he.injective.extend_apply (fun z : s₀ => σ (z : Z)) (fun _ => 0) ⟨z,hz⟩
  have hσeb (x : X) : |σe x| ≤ 1 := by
    by_cases hx : ∃ z : s₀, φ (z : Z) = x
    · obtain ⟨z,rfl⟩ := hx
      rw [hσee z z.property,hσabs]
    · rw [show σe x = 0 from Function.extend_apply' (fun z : s₀ => σ (z : Z)) (fun _ => 0) x hx]
      norm_num
  apply Measure.le_iff.mpr
  intro s hs
  let b := s.indicator σe
  have hbm : Measurable b := hσem.indicator hs
  have hbb (x : X) : |b x| ≤ s.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ s
    · simpa only [b,indicator_of_mem hx] using hσeb x
    · simp [b,hx]
  have hB : ∃ M : ℝ, ∀ x, |b x| ≤ M := ⟨1,fun x => (hbb x).trans (by
    by_cases hx : x ∈ s <;> simp [hx])⟩
  have hbi : Integrable b ν := Integrable.of_bound hbm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hbb x).trans (by by_cases hx : x ∈ s <;> simp [hx]))
  have heq : (∫ z, w z*b (φ z) ∂μ) = τ.real s := by
    rw [←integral_indicator_one hs]
    rw [show τ = densityPush μ φ (fun z => |w z|) from rfl,
      integral_densityPush_measurable μ hφ hw.abs
        (Eventually.of_forall fun _ => abs_nonneg _)
        (b := s.indicator (1 : X → ℝ)) ((measurable_one : Measurable (1 : X → ℝ)).indicator hs)]
    apply integral_congr_ae
    filter_upwards [hμ] with z hzs
    by_cases hz : φ z ∈ s
    · simpa only [b,indicator_of_mem hz,Pi.one_apply,mul_one,hσee z hzs] using hσmul z
    · simp [b,hz]
  have hc := signed_chart_control_borel μ ν hφ hw hcontrol hbm hB
  rw [heq,abs_of_nonneg (show 0 ≤ τ.real s from ENNReal.toReal_nonneg)] at hc
  have hupper : (∫ x, |b x| ∂ν) ≤ ν.real s := by
    rw [←integral_indicator_one hs]
    exact integral_mono_ae hbi.abs ((integrable_const (1 : ℝ)).indicator hs)
      (Eventually.of_forall hbb)
  exact (ENNReal.toReal_le_toReal (measure_ne_top τ s) (measure_ne_top ν s)).mp
    (hc.trans hupper)

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Differentiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open MeasureTheory Set

variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
lemma signed_chart_control_dominates_on
    (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : Measurable φ) {s₀ : Set Z}
    (hμ : ∀ᵐ z ∂μ, z ∈ s₀)
    (he : MeasurableEmbedding (fun z : s₀ => φ (z : Z))) {w : Z → ℝ}
    (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν) :
    densityPush μ φ (fun z => |w z|) ≤ ν := by
  let w' := hw.aestronglyMeasurable.mk w
  have heq : w =ᵐ[μ] w' := hw.aestronglyMeasurable.ae_eq_mk
  have hτ : densityPush μ φ (fun z => |w z|) = densityPush μ φ (fun z => |w' z|) := by
    unfold densityPush
    congr 1
    apply withDensity_congr_ae
    exact heq.mono fun z hz => by dsimp only; rw [hz]
  rw [hτ]
  apply signed_chart_control_dominates_on_of_measurable μ ν hφ hμ he
    hw.aestronglyMeasurable.measurable_mk (hw.congr heq)
  intro b hb
  have hi : (∫ z, w' z*b (φ z) ∂μ) = ∫ z, w z*b (φ z) ∂μ :=
    integral_congr_ae (heq.mono fun z hz => by dsimp only; rw [hz])
  rw [hi]
  exact hcontrol b hb
end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

lemma tangentConeAt_eq_univ_of_density_one (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) : tangentConeAt ℝ s x = univ := by
  apply eq_univ_of_forall
  intro z
  rw [tangentConeAt_eq_biInter_closure]
  simp only [mem_iInter]
  intro U hU
  rw [Metric.mem_closure_iff]
  intro ε hε
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z (ε / 2))).Nonempty :=
    Measure.eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z (half_pos hε)).ne'
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r • closedBall z (ε / 2) ⊆ U := by
    apply nhdsWithin_le_nhds
    have h := eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := (0 : E))
      (s := closedBall z (ε / 2)) isBounded_closedBall hU
    filter_upwards [h] with r hr
    simpa using hr
  obtain ⟨r, ⟨y, ys, hy⟩, hrU, hr⟩ :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, ha, hya⟩ : ∃ a, a ∈ closedBall z (ε / 2) ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, ha, h⟩
    exact ⟨a, ha, by simp only [h, add_neg_cancel_left]⟩
  refine ⟨a, ?_, ?_⟩
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hra : r • a ∈ U ∩ (x + ·) ⁻¹' s :=
      ⟨hrU (smul_mem_smul_set ha), by simpa only [mem_preimage, ← hya] using ys⟩
    exact ⟨r⁻¹, mem_univ _, r • a, hra, inv_smul_smul₀ hr0 a⟩
  · exact lt_of_le_of_lt (by simpa [dist_comm] using ha) (half_lt_self hε)

lemma uniqueDiffWithinAt_of_density_one (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) : UniqueDiffWithinAt ℝ s x := by
  have ht := tangentConeAt_eq_univ_of_density_one μ s x hx
  rw [uniqueDiffWithinAt_iff, ht]
  exact ⟨by simp, mem_closure_of_nonempty_tangentConeAt (by rw [ht]; exact univ_nonempty)⟩

lemma ae_uniqueDiffWithinAt (s : Set E) :
    ∀ᵐ x ∂μ.restrict s, UniqueDiffWithinAt ℝ s x := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s] with x hx
  exact uniqueDiffWithinAt_of_density_one μ s x hx

lemma ae_fderivWithin_eq_fderiv_extension {s : Set E} (hs : MeasurableSet s)
    {f F : E → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (heq : EqOn f F s) :
    ∀ᵐ x ∂μ.restrict s, fderivWithin ℝ f s x = fderiv ℝ F x := by
  filter_upwards [ae_uniqueDiffWithinAt μ s, ae_restrict_mem hs,
    (hF.ae_differentiableAt (μ := μ)).filter_mono (ae_mono Measure.restrict_le_self)]
    with x hx hxs hFx
  rw [fderivWithin_congr' heq hxs, fderivWithin_eq_fderiv hx hFx]

lemma ae_norm_fderivWithin_le {s : Set E} (hs : MeasurableSet s)
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f s) :
    ∀ᵐ x ∂μ.restrict s, ‖fderivWithin ℝ f s x‖ ≤ L := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  filter_upwards [ae_fderivWithin_eq_fderiv_extension μ hs hF heq] with x hx
  rw [hx]
  exact norm_fderiv_le_of_lipschitz ℝ hF

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X]
variable {k : ℕ} (C : IntegerChart X k)
lemma scalar_eq {f : X → ℝ} {z : Euc k} (hz : z ∈ C.domain) :
    C.scalar f z = f (C.param ⟨z, hz⟩) := by simp [scalar, hz]

lemma scalar_mul (f g : X → ℝ) :
    C.scalar (fun x => f x * g x) = C.scalar f * C.scalar g := by
  funext z
  by_cases hz : z ∈ C.domain
  · simp [scalar, hz]
  · simp [scalar, hz]

lemma scalar_lipschitzOn {f : X → ℝ} {K L : ℝ≥0}
    (hφ : LipschitzWith L C.param) (hf : LipschitzWith K f) :
    LipschitzOnWith (K * L) (C.scalar f) C.domain := by
  apply lipschitzOnWith_iff_restrict.mpr
  convert hf.comp hφ using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact C.scalar_eq z.property

lemma measurable_scalar {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Measurable (C.scalar f) := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  obtain ⟨F, hF, heq⟩ := (C.scalar_lipschitzOn hφ hf).extend_real
  have hsc : C.scalar f = C.domain.indicator F := by
    funext z
    by_cases hz : z ∈ C.domain
    · simpa [hz] using heq hz
    · simp [scalar, hz]
  rw [hsc]
  exact hF.continuous.measurable.indicator C.borel

lemma ae_differentiableWithinAt_scalar {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ z ∂volume.restrict C.domain, DifferentiableWithinAt ℝ (C.scalar f) C.domain z := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  obtain ⟨F, hF, heq⟩ := (C.scalar_lipschitzOn hφ hf).extend_real
  filter_upwards [ae_restrict_mem C.borel,
    (hF.ae_differentiableAt (μ := volume)).filter_mono (ae_mono Measure.restrict_le_self)]
    with z hz hd
  exact hd.differentiableWithinAt.congr heq (heq hz)

lemma ae_fderivWithin_scalar_mul {f g : X → ℝ} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) :
    ∀ᵐ z ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (fun x => f x * g x)) C.domain z =
        C.scalar f z • fderivWithin ℝ (C.scalar g) C.domain z +
        C.scalar g z • fderivWithin ℝ (C.scalar f) C.domain z := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,
    C.ae_differentiableWithinAt_scalar hf, C.ae_differentiableWithinAt_scalar hg]
    with z hz hdf hdg
  rw [C.scalar_mul]
  exact fderivWithin_mul hz hdf hdg

lemma ae_jacobian_eq_extensions {π : Fin k → X → ℝ} {F : Fin k → Euc k → ℝ}
    {L : Fin k → ℝ≥0} (hF : ∀ i, LipschitzWith (L i) (F i))
    (heq : ∀ i, EqOn (C.scalar (π i)) (F i) C.domain) :
    C.jacobian π =ᵐ[volume.restrict C.domain]
      fun z => Matrix.det (Matrix.of fun i j => fderiv ℝ (F i) z (EuclideanSpace.single j 1)) := by
  have hae : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
      fderivWithin ℝ (C.scalar (π i)) C.domain z = fderiv ℝ (F i) z :=
    ae_all_iff.mpr fun i => ae_fderivWithin_eq_fderiv_extension volume C.borel (hF i) (heq i)
  filter_upwards [hae] with z hz
  simp only [jacobian, hz]
  rfl

lemma jacobian_aestronglyMeasurable {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    AEStronglyMeasurable (C.jacobian π) (volume.restrict C.domain) := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  choose K hK using hπ
  choose F hF heq using fun i => (C.scalar_lipschitzOn hφ (hK i)).extend_real
  have hmeas : Measurable (fun z => Matrix.det
      (Matrix.of fun i j => fderiv ℝ (F i) z (EuclideanSpace.single j 1))) := by
    simp only [Matrix.det_apply']
    fun_prop
  exact hmeas.aestronglyMeasurable.congr (C.ae_jacobian_eq_extensions hF heq).symm

end IntegerChart
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Jacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X]
variable {k : ℕ} (C : IntegerChart X k)
lemma exists_jacobian_bound {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∃ B : ℝ, ∀ᵐ z ∂volume.restrict C.domain, ‖C.jacobian π z‖ ≤ B := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  choose K hK using hπ
  let R : ℝ := ∑ i, (K i * L : ℝ≥0)
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact
    (Icc (fun (_ _ : Fin k) => -R) (fun _ _ => R))).exists_bound_of_continuousOn
      continuous_id.matrix_det.continuousOn
  refine ⟨B, ?_⟩
  have hae : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
      ‖fderivWithin ℝ (C.scalar (π i)) C.domain z‖ ≤ (K i * L : ℝ≥0) :=
    ae_all_iff.mpr fun i => ae_norm_fderivWithin_le volume C.borel
      (C.scalar_lipschitzOn hφ (hK i))
  filter_upwards [hae] with z hz
  apply hB
  have hentry (i j : Fin k) :
      |(fderivWithin ℝ (C.scalar (π i)) C.domain z) (EuclideanSpace.single j 1)| ≤ R := by
    calc |(fderivWithin ℝ (C.scalar (π i)) C.domain z) (EuclideanSpace.single j 1)| ≤
        ‖fderivWithin ℝ (C.scalar (π i)) C.domain z‖ := by
          simpa using (fderivWithin ℝ (C.scalar (π i)) C.domain z).le_opNorm
            (EuclideanSpace.single j 1)
      _ ≤ (K i * L : ℝ≥0) := hz i
      _ ≤ R := Finset.single_le_sum (fun i _ => NNReal.coe_nonneg (K i * L)) (Finset.mem_univ i)
  exact ⟨fun i j => (abs_le.mp (hentry i j)).1,
    fun i j => (abs_le.mp (hentry i j)).2⟩

lemma integrable_action_integrand {b : X → ℝ} {π : Fin k → X → ℝ}
    (hb : BoundedLip b) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Integrable (fun z => (C.multiplicity z : ℝ) * C.scalar b z * C.jacobian π z)
      (volume.restrict C.domain) := by
  obtain ⟨K, hK⟩ := hb.1
  obtain ⟨M, hM⟩ := hb.2
  have hbint : Integrable (fun z => (C.multiplicity z : ℝ) * C.scalar b z)
      (volume.restrict C.domain) := by
    apply C.integrable.mul_bdd (C.measurable_scalar hK).aestronglyMeasurable
    filter_upwards [ae_restrict_mem C.borel] with z hz
    simpa [C.scalar_eq hz, Real.norm_eq_abs] using hM (C.param ⟨z, hz⟩)
  obtain ⟨B, hB⟩ := C.exists_jacobian_bound hπ
  exact hbint.mul_bdd (C.jacobian_aestronglyMeasurable hπ) hB

lemma jacobian_update (π : Fin k → X → ℝ) (i : Fin k) (f : X → ℝ) (z : Euc k) :
    C.jacobian (Function.update π i f) z =
      (Matrix.updateRow
        (Matrix.of fun a j => fderivWithin ℝ (C.scalar (π a)) C.domain z (EuclideanSpace.single j 1)) i
        (fun j => fderivWithin ℝ (C.scalar f) C.domain z (EuclideanSpace.single j 1))).det := by
  unfold jacobian
  congr 1
  funext a j
  by_cases ha : a = i
  · subst a
    simp
  · simp [ha]

lemma ae_jacobian_update_mul (π : Fin k → X → ℝ) (i : Fin k)
    {f g : X → ℝ} {K J : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith J g) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (fun x => f x * g x)) z =
        C.scalar f z * C.jacobian (Function.update π i g) z +
        C.scalar g z * C.jacobian (Function.update π i f) z := by
  filter_upwards [C.ae_fderivWithin_scalar_mul hf hg] with z hz
  rw [C.jacobian_update, C.jacobian_update, C.jacobian_update, hz]
  simp only [add_apply, smul_apply,
    smul_eq_mul]
  have heq : (fun j => C.scalar f z * fderivWithin ℝ (C.scalar g) C.domain z
        (EuclideanSpace.single j 1) + C.scalar g z * fderivWithin ℝ (C.scalar f) C.domain z
        (EuclideanSpace.single j 1)) =
      C.scalar f z • (fun j => fderivWithin ℝ (C.scalar g) C.domain z
        (EuclideanSpace.single j 1)) +
      C.scalar g z • (fun j => fderivWithin ℝ (C.scalar f) C.domain z
        (EuclideanSpace.single j 1)) := rfl
  rw [heq, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]

lemma action_update_mul {b f g : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (hg : BoundedLip g) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (i : Fin k) :
    C.action b (Function.update π i (fun x => f x * g x)) =
      C.action (fun x => b x * f x) (Function.update π i g) +
      C.action (fun x => b x * g x) (Function.update π i f) := by
  have hup {a : X → ℝ} (ha : BoundedLip a) :
      ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i a) j) := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using ha.1
    · simpa [hji] using hπ j
  have hadm₁ : Admissible b (Function.update π i (fun x => f x * g x)) :=
    ⟨hb, hup (BoundedLip.mul hf hg)⟩
  have hadm₂ : Admissible (fun x => b x * f x) (Function.update π i g) :=
    ⟨BoundedLip.mul hb hf, hup hg⟩
  have hadm₃ : Admissible (fun x => b x * g x) (Function.update π i f) :=
    ⟨BoundedLip.mul hb hg, hup hf⟩
  simp only [action, ite_eq_left hadm₁, ite_eq_left hadm₂, ite_eq_left hadm₃]
  rw [← integral_add (C.integrable_action_integrand hadm₂.1 hadm₂.2)
    (C.integrable_action_integrand hadm₃.1 hadm₃.2)]
  apply integral_congr_ae
  filter_upwards [C.ae_jacobian_update_mul π i hf.1.choose_spec hg.1.choose_spec] with z hz
  rw [hz, C.scalar_mul, C.scalar_mul]
  simp only [Pi.mul_apply]
  ring

end IntegerChart
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Extensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)
noncomputable def paramExtended : Euc k → X :=
  by classical exact fun z => if hz : z ∈ C.domain then C.param ⟨z,hz⟩ else Classical.arbitrary X

lemma measurable_paramExtended : Measurable C.paramExtended := by
  classical
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  exact hL.continuous.measurable.dite measurable_const C.borel

omit [MeasurableSpace X] [BorelSpace X] in
lemma scalar_ae_paramExtended (b : X → ℝ) :
    C.scalar b =ᵐ[volume.restrict C.domain] b ∘ C.paramExtended := by
  filter_upwards [ae_restrict_mem C.borel] with z hz
  simp only [scalar,paramExtended,Function.comp_apply,dite_eq_left hz]

variable [CompactSpace X]

omit [Nonempty X] in
lemma measurableEmbedding_param : MeasurableEmbedding C.param := by
  let := C.borel.standardBorel
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  exact hL.continuous.measurable.measurableEmbedding hU.injective

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] [CompactSpace X] in
lemma integrable_weighted_jacobian {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Integrable (fun z => (C.multiplicity z : ℝ)*C.jacobian π z)
      (volume.restrict C.domain) := by
  obtain ⟨B,hB⟩ := C.exists_jacobian_bound hπ
  exact C.integrable.mul_bdd (C.jacobian_aestronglyMeasurable hπ) hB

lemma weighted_jacobian_le_measure
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) :
    densityPush (volume.restrict C.domain) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) ≤ (∏ i, K i) • ν := by
  have he : MeasurableEmbedding (fun z : C.domain => C.paramExtended (z : Euc k)) := by
    convert C.measurableEmbedding_param using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp [paramExtended,z.property]
  apply signed_chart_control_dominates_on (volume.restrict C.domain) ((∏ i,K i) • ν)
    C.measurable_paramExtended (ae_restrict_mem C.borel) he
    (C.integrable_weighted_jacobian (fun i => ⟨K i,hK i⟩))
  intro b hb
  have heq : (∫ z, (C.multiplicity z : ℝ)*C.jacobian π z*b (C.paramExtended z)
      ∂volume.restrict C.domain) = C.action b π := by
    rw [action,ite_eq_left ⟨hb,fun i => ⟨K i,hK i⟩⟩]
    apply integral_congr_ae
    filter_upwards [C.scalar_ae_paramExtended b] with z hz
    dsimp only [Function.comp_apply] at hz
    rw [hz]
    ring
  rw [heq,integral_smul_nnreal_measure]
  simpa only [NNReal.smul_def,NNReal.coe_prod,smul_eq_mul] using hC.mass_bound hν hb K hK

end IntegerChart

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma ae_fderivWithin_scalar_eq_linear {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (ℓ : Euc k →L[ℝ] ℝ)
    (heq : ∀ z ∈ t, C.scalar f z = ℓ z) :
    ∀ᵐ z ∂volume.restrict t, fderivWithin ℝ (C.scalar f) C.domain z = ℓ := by
  have hd := (C.ae_differentiableWithinAt_scalar hf).filter_mono
    (ae_mono (Measure.restrict_mono hts le_rfl))
  filter_upwards [hd,ae_uniqueDiffWithinAt volume t,ae_restrict_mem ht] with z hz hu hzt
  rw [←fderivWithin_subset hts hu hz,fderivWithin_congr' heq hzt,ℓ.fderivWithin hu]

lemma exists_inverse_coordinate_tests {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (ℓ : Fin k → Euc k →L[ℝ] ℝ) (K : ℝ≥0)
    (hrow : ∀ i y (hy : y ∈ t) z (hz : z ∈ t),
      |ℓ i y - ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩)) :
    ∃ π : Fin k → X → ℝ, (∀ i, LipschitzWith K (π i)) ∧
      (∀ i, ∀ z ∈ t, C.scalar (π i) z = ℓ i z) ∧
      ∀ᵐ z ∂volume.restrict t,
        C.jacobian π z = (Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)).det := by
  classical
  by_cases hne : t.Nonempty
  · let := hne.to_subtype
    let φ : t → X := fun z => C.param ⟨z,hts z.property⟩
    have hinj : Function.Injective φ := by
      obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : C.domain => (z : Euc k)) (hU.injective hab)
    let q : Fin k → X → ℝ := fun i x => ℓ i ((Function.invFun φ x : t) : Euc k)
    have hq (i : Fin k) : LipschitzOnWith K (q i) (Set.range φ) := by
      apply lipschitzOnWith_iff_dist_le_mul.mpr
      rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
      simpa only [q,Function.leftInverse_invFun hinj a,
        Function.leftInverse_invFun hinj b,Real.dist_eq] using
        hrow i a a.property b b.property
    choose π hπ heq using fun i => (hq i).extend_real
    have hagree (i : Fin k) (z : Euc k) (hz : z ∈ t) : C.scalar (π i) z = ℓ i z := by
      rw [C.scalar_eq (hts hz)]
      change π i (φ ⟨z,hz⟩) = _
      rw [←heq i (Set.mem_range_self (⟨z,hz⟩ : t))]
      dsimp only [q]
      rw [Function.leftInverse_invFun hinj]
    refine ⟨π,hπ,hagree,?_⟩
    have hae : ∀ᵐ z ∂volume.restrict t, ∀ i,
        fderivWithin ℝ (C.scalar (π i)) C.domain z = ℓ i :=
      ae_all_iff.mpr fun i => C.ae_fderivWithin_scalar_eq_linear ht hts (hπ i) (ℓ i) (hagree i)
    filter_upwards [hae] with z hz
    simp only [jacobian,hz]
    rfl
  · have ht0 : t = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst t
    exact ⟨fun _ _ => 0,fun _ => LipschitzWith.const' (0 : ℝ),by simp,by simp⟩

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit [MeasurableSpace E] [BorelSpace E] in

lemma seminorm_continuous_finiteDimensional (p : Seminorm ℝ E) : Continuous p := by
  classical
  let b := Module.finBasis ℝ E
  have hsum (I : Finset (Fin (Module.finrank ℝ E)))
      (q : Fin (Module.finrank ℝ E) → E) :
      p (∑ i ∈ I, q i) ≤ ∑ i ∈ I, p (q i) := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
  have hb (v : E) : p v ≤ ∑ i, ‖b.repr v i‖ * p (b i) := by
    convert hsum Finset.univ (fun i => b.repr v i • b i) using 1
    · rw [b.sum_repr]
    · simp only [map_smul_eq_mul]
  have hcont : Continuous (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp b.continuous_coe_repr).norm.mul_const _
  apply Seminorm.continuous_of_continuousAt_zero
  have hc : Tendsto (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto 0
  simpa [ContinuousAt] using tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hc (fun v => apply_nonneg p v) hb

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_HilbertCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]

def HasCenteredMetricDifferentialWithin (s : Set E) (f : s → X)
    (p : Seminorm ℝ E) (x : s) : Prop :=
  (fun y : s => dist (f y) (f x) - p ((y : E)-(x : E))) =o[𝓝 x]
    (fun y : s => (y : E)-(x : E))

end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_ScalarBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma scalar_derivative_bound_of_metric_differential
    {s : Set E} {x : E} {F r : E → ℝ} {p : Seminorm ℝ E} {ℓ : E →L[ℝ] ℝ}
    (hx : Tendsto (fun t => μ (s ∩ closedBall x t) / μ (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (hF : HasFDerivWithinAt F ℓ s x)
    (hr : (fun y => r y-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    {K : ℝ} (hbound : ∀ y ∈ s, |F y-F x| ≤ K*r y) (v : E) :
    |ℓ v| ≤ K*p v := by
  have hv : v ∈ tangentConeAt ℝ s x := by
    rw [tangentConeAt_eq_univ_of_density_one μ s x hx]
    exact mem_univ v
  obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hv
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd₀,hd⟩
  have hl : Tendsto (fun j => ‖c j‖ * |F (x+d j)-F x|) atTop (𝓝 |ℓ v|) := by
    simpa only [Real.norm_eq_abs,smul_eq_mul,abs_mul] using (hF.lim hd₀ hd hcd).norm
  have hsmall := (hr.comp_tendsto ht).norm_right.mul_isBigO
    (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => ‖(x+d j)-x‖*‖c j‖) atTop (𝓝 ‖v‖) := by
    simpa only [norm_smul,add_sub_cancel_left,mul_comm] using hcd.norm
  have hzero := hsmall.tendsto_zero_of_tendsto hnorm
  have hp := (seminorm_continuous_finiteDimensional p).tendsto v |>.comp hcd
  have hlim : Tendsto (fun j => ‖c j‖*r (x+d j)) atTop (𝓝 (p v)) := by
    convert hzero.add hp using 1
    · ext j
      simp only [Function.comp_apply,add_sub_cancel_left,map_smul_eq_mul]
      ring
    · simp
  apply le_of_tendsto_of_tendsto hl (hlim.const_mul K)
  filter_upwards [hd] with j hj
  have hh := mul_le_mul_of_nonneg_left (hbound (x+d j) hj) (norm_nonneg (c j))
  simpa only [mul_left_comm] using hh

end CAT0Fillings

namespace CAT0Fillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {X : Type*} [MetricSpace X]

lemma HasCenteredMetricDifferentialWithin.scalar_bound
    {s : Set E} {f : s → X} {p : Seminorm ℝ E} {x : s}
    (h : HasCenteredMetricDifferentialWithin s f p x)
    (hx : Tendsto (fun t => μ (s ∩ closedBall (x : E) t) / μ (closedBall (x : E) t))
      (𝓝[>] 0) (𝓝 1))
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F : E → ℝ} (hF : ∀ y : s, F y = u (f y))
    {ℓ : E →L[ℝ] ℝ} (hD : HasFDerivWithinAt F ℓ s x) (v : E) :
    |ℓ v| ≤ (K : ℝ)*p v := by
  classical
  let r : E → ℝ := fun z => if hz : z ∈ s then dist (f ⟨z,hz⟩) (f x) else 0
  have hr : (fun y => r y-p (y-(x : E))) =o[𝓝[s] (x : E)] (fun y => y-(x : E)) := by
    rw [nhdsWithin_eq_map_subtype_coe x.property, Asymptotics.isLittleO_map]
    change (fun y : s => dist (f y) (f x)-p ((y : E)-(x : E))) =o[𝓝 x]
      (fun y : s => (y : E)-(x : E)) at h
    convert h using 1
    · ext y
      simp only [Function.comp_apply,r,dite_eq_left y.property,Subtype.coe_eta]
    · rfl
  apply scalar_derivative_bound_of_metric_differential μ hx hD hr (v := v)
  intro y hy
  have hh := hu.dist_le_mul (f ⟨y,hy⟩) (f x)
  rw [Real.dist_eq, ←hF ⟨y,hy⟩, ←hF x] at hh
  simpa only [r,dite_eq_left hy] using hh

noncomputable def scalarOn {s : Set E} (f : s → X) (u : X → ℝ) (z : E) : ℝ :=
  by classical exact if hz : z ∈ s then u (f ⟨z,hz⟩) else 0

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma scalarOn_lipschitzOn {s : Set E} {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith J f) {u : X → ℝ} (hu : LipschitzWith K u) :
    LipschitzOnWith (K*J) (scalarOn f u) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  simpa only [scalarOn,dite_eq_left ha,dite_eq_left hb,Function.comp_apply,Subtype.dist_eq] using
    (hu.comp hf).dist_le_mul ⟨a,ha⟩ ⟨b,hb⟩

lemma ae_scalarOn_derivative_bound {s : Set E} (hs : MeasurableSet s) {f : s → X}
    {J : ℝ≥0} (hf : LipschitzWith J f) {p : E → Seminorm ℝ E}
    (hd : ∀ᵐ x ∂μ.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ x ∂μ.restrict s, ∀ v,
      |fderivWithin ℝ (scalarOn f u) s x v| ≤ (K : ℝ)*p x v := by
  obtain ⟨F,hF,heq⟩ := (scalarOn_lipschitzOn hf hu).extend_real
  have haediff := hF.ae_differentiableAt (μ := μ)
  filter_upwards [hd,ae_restrict_mem hs,Besicovitch.ae_tendsto_measure_inter_div μ s,
    haediff.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hxs hxd hFx
  have hD : HasFDerivWithinAt (scalarOn f u) (fderivWithin ℝ (scalarOn f u) s x) s x := by
    apply DifferentiableWithinAt.hasFDerivWithinAt
    exact hFx.differentiableWithinAt.congr heq (heq hxs)
  intro v
  apply (hx hxs).scalar_bound μ hxd hu _ hD v
  intro y
  simp only [scalarOn,dite_eq_left y.property,Subtype.coe_eta]
end CAT0Fillings.MetricDifferentiation

open Set MeasureTheory
open scoped RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_LinearMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory

lemma densityPush_congr_ae {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) (φ : Z → X) {ρ σ : Z → ℝ} (h : ρ =ᵐ[μ] σ) :
    densityPush μ φ ρ = densityPush μ φ σ := by
  unfold densityPush
  congr 1
  exact withDensity_congr_ae (h.fun_comp ENNReal.ofReal)

lemma densityPush_restrict_le_restrict_image {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) {φ : Z → X} (hφ : Measurable φ) (ρ : Z → ℝ)
    {t : Set Z} (ht : MeasurableSet t) (him : MeasurableSet (φ '' t)) :
    densityPush (μ.restrict t) φ ρ ≤ (densityPush μ φ ρ).restrict (φ '' t) := by
  unfold densityPush
  rw [←restrict_withDensity ht,Measure.restrict_map hφ him]
  apply Measure.map_mono _ hφ
  apply Measure.restrict_mono _ le_rfl
  intro x hx
  exact ⟨x,hx,rfl⟩

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma measurableSet_paramExtended_image {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain) :
    MeasurableSet (C.paramExtended '' t) := by
  let := ht.standardBorel
  have hi : Function.Injective (fun z : t => C.paramExtended (z : Euc k)) := by
    intro a b hab
    have hab' : C.param ⟨a,hts a.property⟩ = C.param ⟨b,hts b.property⟩ := by
      simpa only [paramExtended,dite_eq_left (hts a.property),dite_eq_left (hts b.property)] using hab
    obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
    apply Subtype.ext
    exact congrArg (fun z : C.domain => (z : Euc k)) (hU.injective hab')
  have hm := (C.measurable_paramExtended.comp measurable_subtype_coe).measurableEmbedding hi
  have heq : range (fun z : t => C.paramExtended (z : Euc k)) = C.paramExtended '' t := by
    ext x
    simp
  rw [←heq]
  exact hm.measurableSet_range

lemma linear_piece_mass_le
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (ℓ : Fin k → Euc k →L[ℝ] ℝ) (K : ℝ≥0)
    (hrow : ∀ i y (hy : y ∈ t) z (hz : z ∈ t),
      |ℓ i y - ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩)) :
    densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| *
        |(Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)).det|)
      ≤ ((K^k) • ν).restrict (C.paramExtended '' t) := by
  obtain ⟨π,hπ,_,hjac⟩ := C.exists_inverse_coordinate_tests ht hts ℓ K hrow
  have heq : densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| *
        |(Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)).det|) =
      densityPush (volume.restrict t) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) := by
    apply densityPush_congr_ae
    filter_upwards [hjac] with z hz
    rw [hz,abs_mul]
  rw [heq]
  have hrest : (volume.restrict C.domain).restrict t = volume.restrict t := by
    rw [Measure.restrict_restrict ht,inter_eq_left.mpr hts]
  calc
    _ = densityPush ((volume.restrict C.domain).restrict t) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) := by rw [hrest]
    _ ≤ (densityPush (volume.restrict C.domain) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|)).restrict
          (C.paramExtended '' t) :=
      densityPush_restrict_le_restrict_image (volume.restrict C.domain)
        C.measurable_paramExtended _ ht (C.measurableSet_paramExtended_image ht hts)
    _ ≤ ((K^k) • ν).restrict (C.paramExtended '' t) := by
      apply Measure.restrict_mono le_rfl
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        C.weighted_jacobian_le_measure hC hν π (fun _ => K) hπ

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings
open MeasureTheory

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)

noncomputable def majorantMeasure (J : Euc k → ℝ) : Measure X :=
  densityPush (volume.restrict C.domain) C.paramExtended
    (fun z => |(C.multiplicity z : ℝ)| * J z)

end IntegerChart
end CAT0Fillings

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings

lemma dot_mulVec_sqrt {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (v : Fin n → ℝ) :
    v ⬝ᵥ P.mulVec v = (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v := by
  have hsym : (CFC.sqrt P).transpose = CFC.sqrt P :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P).posSemidef.isHermitian).eq
  conv_lhs => rw [← CFC.sq_sqrt P hP.nonneg,pow_two, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_Polarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace CAT0Fillings
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma exists_bilinForm_of_parallelogram (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    ∃ B : LinearMap.BilinForm ℝ E, B.IsSymm ∧ B.toQuadraticMap.PosDef ∧
      (∀ v, B v v = (p v)^2) ∧
      ∀ u v, B u v = ((p (u+v))^2-(p (u-v))^2)/4 := by
  let : Norm E := ⟨p⟩
  let core : NormedSpace.Core ℝ E :=
    { norm_nonneg := fun v => apply_nonneg p v
      norm_smul := fun c v => map_smul_eq_mul p c v
      norm_triangle := fun x y => map_add_le_add p x y
      norm_eq_zero_iff := hp }
  let : NormedAddCommGroup E := NormedAddCommGroup.ofCore core
  let : NormedSpace ℝ E := NormedSpace.ofCore core
  have hparanorm : ∀ u v : E,
      ‖u+v‖*‖u+v‖+‖u-v‖*‖u-v‖ = 2*(‖u‖*‖u‖+‖v‖*‖v‖) := by
    intro u v
    change p (u+v)*p (u+v)+p (u-v)*p (u-v) = 2*(p u*p u+p v*p v)
    nlinarith [hpara u v]
  let : InnerProductSpace ℝ E := InnerProductSpace.ofNorm ℝ hparanorm
  refine ⟨innerₗ E,?_,?_,?_,?_⟩
  · exact ⟨fun u v => (real_inner_comm u v).symm⟩
  · intro v hv
    change 0 < inner ℝ v v
    exact real_inner_self_pos.mpr hv
  · intro v
    change inner ℝ v v = (p v)^2
    exact real_inner_self_eq_norm_sq v
  · intro u v
    change inner ℝ u v = ((p (u+v))^2-(p (u-v))^2)/4
    have H := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℝ) u v
    change inner ℝ u v = (p (u+v)*p (u+v)-p (u-v)*p (u-v))/4 at H
    simpa only [pow_two] using H

noncomputable def polarizationMatrix {ι : Type*} (p : Seminorm ℝ E) (b : ι → E) : Matrix ι ι ℝ :=
  fun i j => ((p (b i+b j))^2-(p (b i-b j))^2)/4

lemma polarizationMatrix_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    (polarizationMatrix p b).PosDef := by
  obtain ⟨B,hB,hpos,_,hpol⟩ := exists_bilinForm_of_parallelogram p hp hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  rw [heq]
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b B hB).1 hpos

lemma polarizationMatrix_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) (v : E) :
    (b.repr v) ⬝ᵥ (polarizationMatrix p b).mulVec (b.repr v) = (p v)^2 := by
  obtain ⟨B,_,_,hdiag,hpol⟩ := exists_bilinForm_of_parallelogram p hp hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  rw [heq]
  rw [←hdiag v]
  exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B v v).symm

lemma measurable_polarizationMatrix {A ι : Type*} [MeasurableSpace A]
    [Fintype ι] (p : A → Seminorm ℝ E) (b : ι → E)
    (hp : ∀ v, Measurable (fun x => p x v)) :
    ∀ i j, Measurable (fun x => polarizationMatrix (p x) b i j) := by
  intro i j
  exact ((hp _).pow_const 2 |>.sub ((hp _).pow_const 2)).div_const 4
end CAT0Fillings

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ProductRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X]
variable {k : ℕ} (C : IntegerChart X k)
lemma jacobian_permute (π : Fin k → X → ℝ) (σ : Equiv.Perm (Fin k)) (z : Euc k) :
    C.jacobian (π ∘ σ) z = (Equiv.Perm.sign σ : ℤ) * C.jacobian π z := by
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j =>
    fderivWithin ℝ (C.scalar (π i)) C.domain z (EuclideanSpace.single j 1)
  change (M.submatrix σ id).det = (Equiv.Perm.sign σ : ℤ) * M.det
  exact Matrix.det_permute σ M

lemma action_permute {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    C.action b (π ∘ σ) = (Equiv.Perm.sign σ : ℤ) * C.action b π := by
  have hσ : Admissible b (π ∘ σ) := ⟨h.1, fun i => h.2 (σ i)⟩
  simp only [action, ite_eq_left h, ite_eq_left hσ, C.jacobian_permute]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end IntegerChart

namespace Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma IntegerRectifiable.apply_update_mul {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b f g : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (hg : BoundedLip g) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (i : Fin k) :
    T b (Function.update π i (fun x => f x * g x)) =
      T (fun x => b x * f x) (Function.update π i g) +
      T (fun x => b x * g x) (Function.update π i f) := by
  obtain ⟨C, _, hC, hsum, hrepr⟩ := hT
  have hup {a : X → ℝ} (ha : BoundedLip a) :
      ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i a) j) := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using ha.1
    · simpa [hji] using hπ j
  rw [hrepr, hrepr, hrepr, ← Summable.tsum_add
    (summable_actions_of_summable_masses hC hsum ⟨BoundedLip.mul hb hf, hup hg⟩)
    (summable_actions_of_summable_masses hC hsum ⟨BoundedLip.mul hb hg, hup hf⟩)]
  apply tsum_congr
  intro j
  exact (C j).action_update_mul hb hf hg π hπ i

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma admissible_vecCons {k : ℕ} {b f : X → ℝ} {π : Fin k → X → ℝ}
    (hb : BoundedLip b) (hf : ∃ K : ℝ≥0, LipschitzWith K f)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Admissible b (Matrix.vecCons f π) := by
  refine ⟨hb, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf
  · exact hπ j

lemma update_vecCons_zero {α : Type*} {k : ℕ} (f g : α) (π : Fin k → α) :
    Function.update (Matrix.vecCons f π) 0 g = Matrix.vecCons g π := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

lemma IntegerRectifiable.product_rule {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) {b f : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    T b (Matrix.vecCons f π) + T f (Matrix.vecCons b π) =
      boundarySucc T (fun x => b x * f x) π := by
  have h := IntegerRectifiable.apply_update_mul hT (BoundedLip.const 1) hb hf (Matrix.vecCons b π)
    (admissible_vecCons (BoundedLip.const 1) hb.1 hπ).2 0
  simp only [update_vecCons_zero, one_mul] at h
  have hadm : Admissible (fun x => b x * f x) π := ⟨BoundedLip.mul hb hf, hπ⟩
  exact h.symm.trans (by rw [boundarySucc, ite_eq_left hadm])

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.apply_permute {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    T b (π ∘ σ) = (Equiv.Perm.sign σ : ℤ) * T b π := by
  obtain ⟨C, _, _, _, hrepr⟩ := hT
  rw [hrepr, hrepr, ← tsum_mul_left]
  exact tsum_congr fun j => (C j).action_permute h σ

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.abs_apply_permute {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    |T b (π ∘ σ)| = |T b π| := by
  rw [IntegerRectifiable.apply_permute hT h σ, abs_mul, abs_unit_intCast, one_mul]

lemma IntegerRectifiable.head_bound {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) (hcur : IsMetricCurrent T)
    (hbd : IsMetricCurrent (boundarySucc T))
    {b f : X → ℝ} {Kb : ℝ≥0} (hb : LipschitzWith Kb b) (hf : BoundedLip f)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ i, LipschitzWith (K i) (π i))
    (B F : ℝ≥0) (hB : ∀ x, |b x| ≤ B) (hF : ∀ x, |f x| ≤ F) :
    |T b (Matrix.vecCons f π)| ≤
      (∏ i, (K i : ℝ)) * ((B : ℝ) * mass (boundarySucc T) + (Kb : ℝ) * mass T) * F := by
  have hb' : BoundedLip b := ⟨⟨Kb, hb⟩, B, hB⟩
  have hπ' : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (π i) := fun i => ⟨K i, hπ i⟩
  have hprod := IntegerRectifiable.product_rule hT hb' hf π hπ'
  have heq : T b (Matrix.vecCons f π) =
      boundarySucc T (fun x => b x * f x) π - T f (Matrix.vecCons b π) := by
    linarith
  have hbf (x : X) : |b x * f x| ≤ (B : ℝ) * F := by
    rw [abs_mul]
    exact mul_le_mul (hB x) (hF x) (abs_nonneg _) B.coe_nonneg
  have h1 := hbd.mass_bound_uniform (BoundedLip.mul hb' hf) K hπ hbf
  have hK : ∀ i, LipschitzWith (Matrix.vecCons Kb K i) (Matrix.vecCons b π i) := by
    intro i
    exact Fin.cases hb (fun j => hπ j) i
  have h2 := hcur.mass_bound_uniform hf (Matrix.vecCons Kb K) hK hF
  have hmult : (∏ i, ((Matrix.vecCons Kb K i : ℝ≥0) : ℝ)) =
      (Kb : ℝ) * ∏ i, (K i : ℝ) := by rw [Fin.prod_univ_succ]; rfl
  rw [hmult] at h2
  rw [heq]
  calc |boundarySucc T (fun x => b x * f x) π - T f (Matrix.vecCons b π)| ≤
      |boundarySucc T (fun x => b x * f x) π| + |T f (Matrix.vecCons b π)| := abs_sub _ _
    _ ≤ ((∏ i, (K i : ℝ)) * ((B : ℝ) * F)) * mass (boundarySucc T) +
        (((Kb : ℝ) * ∏ i, (K i : ℝ)) * F) * mass T := add_le_add h1 h2
    _ = _ := by ring

end Foundations
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_TestBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedLip_of_lipschitz {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    BoundedLip f := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuous.continuousOn
  exact ⟨⟨K, hf⟩, M, fun x => by simpa [Real.norm_eq_abs] using hM x (mem_univ x)⟩

lemma IntegerRectifiable.coord_bound {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) (hcur : IsMetricCurrent T)
    (hbd : IsMetricCurrent (boundarySucc T))
    {b : X → ℝ} {Kb : ℝ≥0} (hb : LipschitzWith Kb b)
    (π : Fin (k + 1) → X → ℝ) (K : ℝ≥0)
    (hπ : ∀ i, LipschitzWith K (π i)) (i : Fin (k + 1))
    (B F : ℝ≥0) (hB : ∀ x, |b x| ≤ B) (hF : ∀ x, |π i x| ≤ F) :
    |T b π| ≤ (K : ℝ) ^ k *
      ((B : ℝ) * mass (boundarySucc T) + (Kb : ℝ) * mass T) * F := by
  let σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 i
  let ρ : Fin k → X → ℝ := fun j => π (σ j.succ)
  have hadm : Admissible b π := ⟨⟨⟨Kb, hb⟩, B, hB⟩, fun j => ⟨K, hπ j⟩⟩
  have heq : π ∘ σ = Matrix.vecCons (π i) ρ := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [σ]
    · rfl
  rw [← IntegerRectifiable.abs_apply_permute hT hadm σ, heq]
  have h := IntegerRectifiable.head_bound hT hcur hbd hb
    (boundedLip_of_lipschitz (hπ i)) ρ (fun _ => K) (fun j => hπ (σ j.succ)) B F hB hF
  simpa using h

lemma IntegerRectifiable.test_difference_bound {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) (hcur : IsMetricCurrent T)
    (hbd : IsMetricCurrent (boundarySucc T))
    {b : X → ℝ} {Kb : ℝ≥0} (hb : LipschitzWith Kb b)
    (π σ : Fin (k + 1) → X → ℝ) (K : ℝ≥0)
    (hπ : ∀ i, LipschitzWith K (π i)) (hσ : ∀ i, LipschitzWith K (σ i))
    (B ε : ℝ≥0) (hB : ∀ x, |b x| ≤ B) (hε : ∀ i x, |π i x - σ i x| ≤ ε) :
    |T b π - T b σ| ≤ (k + 1 : ℝ) * ((K + K : ℝ≥0) : ℝ) ^ k *
      ((B : ℝ) * mass (boundarySucc T) + (Kb : ℝ) * mass T) * ε := by
  let a : Fin (k + 1) → lipSubmodule (X := X) := fun i => ⟨π i, K, hπ i⟩
  let c : Fin (k + 1) → lipSubmodule (X := X) := fun i => ⟨σ i, K, hσ i⟩
  let ρ : Fin (k + 1) → Fin (k + 1) → X → ℝ := fun i j =>
    if j < i then π j else if i = j then fun x => π j x - σ j x else σ j
  have heq : T b π - T b σ = ∑ i, T b (ρ i) := by
    have h := (hcur.multilinear b ⟨⟨Kb, hb⟩, B, hB⟩).map_sub_map_piecewise a c Finset.univ
    simp only [Finset.mem_univ, forall_const, Finset.piecewise_univ] at h
    change T b π - T b σ = _ at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    change T b _ = T b _
    congr 1
    funext j
    dsimp [ρ]
    split_ifs <;> rfl
  have hρ (i j : Fin (k + 1)) : LipschitzWith (K + K) (ρ i j) := by
    dsimp [ρ]
    split_ifs
    · exact (hπ j).weaken (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ K from bot_le))
    · exact (hπ j).sub (hσ j)
    · exact (hσ j).weaken (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ K from bot_le))
  have hρi (i : Fin (k + 1)) (x : X) : |ρ i i x| ≤ ε := by
    simpa [ρ] using hε i x
  rw [heq]
  calc |∑ i, T b (ρ i)| ≤ ∑ i, |T b (ρ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (k + 1), ((K + K : ℝ≥0) : ℝ) ^ k *
        ((B : ℝ) * mass (boundarySucc T) + (Kb : ℝ) * mass T) * ε :=
      Finset.sum_le_sum fun i _ => IntegerRectifiable.coord_bound hT hcur hbd hb
        (ρ i) (K + K) (hρ i) i B ε hB (hρi i)
    _ = _ := by simp; ring

omit [MeasurableSpace X] [BorelSpace X] in
lemma lipschitz_pointwise_uniform {ι : Type*} {l : Filter ι}
    {f : ι → X → ℝ} {g : X → ℝ} {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hg : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    TendstoUniformly f g l := by
  have heq : Equicontinuous f := Metric.equicontinuous_of_continuity_modulus
    (fun r : ℝ => (K : ℝ) * r) (by simpa using (tendsto_const_nhds (x := (K : ℝ))).mul (show Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0) from tendsto_id)) f
    (fun x y i => (hf i).dist_le_mul x y)
  have ht := (heq.tendsto_uniformFun_iff_pi l g).mpr (tendsto_pi_nhds.mpr hg)
  exact UniformFun.tendsto_iff_tendstoUniformly.mp ht

lemma weak_limit_test_difference_bound
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X (k + 1)} {T : Functional X (k + 1)}
    (hTs : ∀ j, IntegerRectifiable (Ts j))
    (hcur : ∀ j, IsMetricCurrent (Ts j))
    (hbd : ∀ j, IsMetricCurrent (boundarySucc (Ts j)))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Admissible b π → Tendsto (fun j => Ts j b π) l (𝓝 (T b π)))
    {b : X → ℝ} {Kb : ℝ≥0} (hb : LipschitzWith Kb b)
    (π σ : Fin (k + 1) → X → ℝ) (K : ℝ≥0)
    (hπ : ∀ i, LipschitzWith K (π i)) (hσ : ∀ i, LipschitzWith K (σ i))
    (B ε : ℝ≥0) (hB : ∀ x, |b x| ≤ B) (hε : ∀ i x, |π i x - σ i x| ≤ ε) :
    |T b π - T b σ| ≤ (k + 1 : ℝ) * ((K + K : ℝ≥0) : ℝ) ^ k *
      ((B : ℝ) * N + (Kb : ℝ) * M) * ε := by
  have hb' : BoundedLip b := ⟨⟨Kb, hb⟩, B, hB⟩
  apply le_of_tendsto ((hlim b π ⟨hb', fun i => ⟨K, hπ i⟩⟩).sub
    (hlim b σ ⟨hb', fun i => ⟨K, hσ i⟩⟩)).abs
  apply Eventually.of_forall
  intro j
  refine (IntegerRectifiable.test_difference_bound (hTs j) (hcur j) (hbd j) hb
    π σ K hπ hσ B ε hB hε).trans ?_
  apply mul_le_mul_of_nonneg_right _ ε.coe_nonneg
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left (hN j) B.coe_nonneg)
    (mul_le_mul_of_nonneg_left (hM j) Kb.coe_nonneg)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma lipschitz_of_pointwise_limit {ι : Type*} {l : Filter ι} [NeBot l]
    {f : ι → X → ℝ} {g : X → ℝ} {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hg : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    LipschitzWith K g := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  exact le_of_tendsto ((hg x).dist (hg y))
    (Eventually.of_forall fun i => (hf i).dist_le_mul x y)

end Foundations
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_WeakClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
omit [MeasurableSpace X] [BorelSpace X] in
lemma eval_tendsto_of_uniform_modulus {d : ℕ}
    (F : (Fin d → X → ℝ) → ℝ) (π : Fin d → X → ℝ)
    (πs : ℕ → Fin d → X → ℝ)
    (hLip : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hpt : ∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x)))
    (hmod : ∀ K : ℝ≥0, ∃ C : ℝ≥0, ∀ (ρ σ : Fin d → X → ℝ),
      (∀ i, LipschitzWith K (ρ i)) → (∀ i, LipschitzWith K (σ i)) →
      ∀ ε : ℝ≥0, (∀ i x, |ρ i x - σ i x| ≤ ε) → |F ρ - F σ| ≤ C * ε) :
    Tendsto (fun j => F (πs j)) atTop (𝓝 (F π)) := by
  choose Ks hKs using hLip
  let K : ℝ≥0 := ∑ i, Ks i
  have hK (i : Fin d) : Ks i ≤ K :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
  have hseq (j : ℕ) (i : Fin d) : LipschitzWith K (πs j i) := (hKs i j).weaken (hK i)
  have hlimit (i : Fin d) : LipschitzWith K (π i) :=
    lipschitz_of_pointwise_limit (fun j => hseq j i) (hpt i)
  obtain ⟨C, hC⟩ := hmod K
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / ((C : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hev (i : Fin d) : ∀ᶠ j in atTop, ∀ x, |πs j i x - π i x| ≤ δ := by
    have hu := lipschitz_pointwise_uniform (fun j => hseq j i) (hpt i)
    filter_upwards [Metric.tendstoUniformly_iff.mp hu δ hδ] with j hj x
    exact le_of_lt (by simpa [Real.dist_eq, abs_sub_comm] using hj x)
  filter_upwards [Filter.eventually_all.mpr hev] with j hj
  rw [Real.dist_eq]
  have h := hC (πs j) π (hseq j) hlimit ⟨δ, hδ.le⟩ hj
  refine h.trans_lt ?_
  change (C : ℝ) * δ < ε
  calc (C : ℝ) * δ < ((C : ℝ) + 1) * δ := by nlinarith
    _ = ε := by dsimp [δ]; exact mul_div_cancel₀ ε (by positivity : (C : ℝ) + 1 ≠ 0)

lemma metricCurrent_of_bounded_weak_limit
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X (k + 1)} {T : Functional X (k + 1)}
    (hTs : ∀ j, IntegerRectifiable (Ts j))
    (hcur : ∀ j, IsMetricCurrent (Ts j))
    (hbd : ∀ j, IsMetricCurrent (boundarySucc (Ts j)))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    IsMetricCurrent T := by
  obtain ⟨μ, hμ, hctrl, _⟩ := exists_controls_of_bounded_weak_limit M hcur hM
    (fun b π _ => hlim b π)
  refine {
    offDomain := ?_
    linearFirst := ?_
    linearCoord := ?_
    sequentialContinuity := ?_
    locality := ?_
    finiteMass := ⟨μ, hμ, hctrl⟩ }
  · intro b π h
    apply tendsto_nhds_unique (hlim b π)
    have heq : (fun j => Ts j b π) = fun _ => 0 :=
      funext fun j => (hcur j).offDomain b π h
    rw [heq]
    exact tendsto_const_nhds
  · intro b₁ b₂ π a c hb₁ hb₂ hπ
    apply tendsto_nhds_unique (hlim (fun x => a * b₁ x + c * b₂ x) π)
    convert ((hlim b₁ π).const_mul a).add ((hlim b₂ π).const_mul c) using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    exact (hcur j).linearFirst b₁ b₂ π a c hb₁ hb₂ hπ
  · intro b π i f a c hadm hf
    apply tendsto_nhds_unique (hlim b (Function.update π i (fun x => a * π i x + c * f x)))
    convert ((hlim b π).const_mul a).add
      ((hlim b (Function.update π i f)).const_mul c) using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    exact (hcur j).linearCoord b π i f a c hadm hf
  · intro b π πs hb hLip hpt
    obtain ⟨Kb, hKb⟩ := hb.1
    obtain ⟨B₀, hB₀⟩ := hb.2
    let B : ℝ≥0 := ⟨max B₀ 0, le_max_right _ _⟩
    have hB (x : X) : |b x| ≤ B := (hB₀ x).trans (le_max_left _ _)
    apply eval_tendsto_of_uniform_modulus (T b) π πs hLip hpt
    intro K
    let C : ℝ≥0 := (k + 1) * (K + K) ^ k * (B * N + Kb * M)
    refine ⟨C, ?_⟩
    intro ρ σ hρ hσ ε hε
    have h := weak_limit_test_difference_bound hTs hcur hbd M N hM hN
      (fun b π _ => hlim b π) hKb ρ σ K hρ hσ B ε hB hε
    simpa [C] using h
  · intro b π hadm hloc
    apply tendsto_nhds_unique (hlim b π)
    have heq : (fun j => Ts j b π) = fun _ => 0 :=
      funext fun j => (hcur j).locality b π hadm hloc
    rw [heq]
    exact tendsto_const_nhds

omit [BorelSpace X] [CompactSpace X] in
lemma boundarySucc_boundarySucc {k : ℕ} {T : Functional X (k + 1 + 1)}
    (hT : IsMetricCurrent T) : boundarySucc (boundarySucc T) = fun _ _ => 0 := by
  funext b π
  by_cases h : Admissible b π
  · rw [boundarySucc, ite_eq_left h]
    have hadm : Admissible (fun _ : X => (1 : ℝ)) (Matrix.vecCons b π) :=
      admissible_vecCons (BoundedLip.const 1) h.1.1 h.2
    rw [boundarySucc, ite_eq_left hadm]
    apply hT.eq_zero_of_const_coord (admissible_vecCons (BoundedLip.const 1)
      ⟨0, LipschitzWith.const 1⟩ hadm.2) 0 1
    intro x
    rfl
  · rw [boundarySucc, ite_eq_right h]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma boundarySucc_weak_limit {ι : Type*} {l : Filter ι} {k : ℕ}
    {Ts : ι → Functional X (k + 1)} {T : Functional X (k + 1)}
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    ∀ b π, Tendsto (fun j => boundarySucc (Ts j) b π) l (𝓝 (boundarySucc T b π)) := by
  intro b π
  by_cases h : Admissible b π
  · simpa only [boundarySucc, ite_eq_left h] using hlim (fun _ => 1) (Matrix.vecCons b π)
  · simp only [boundarySucc, ite_eq_right h]
    exact tendsto_const_nhds

lemma normal_of_bounded_integral_weak_limit
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X (k + 1 + 1)} {T : Functional X (k + 1 + 1)}
    (hTs : ∀ j, IsIntegral (k + 1 + 1) (Ts j))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    IsMetricCurrent T ∧ IsMetricCurrent (boundarySucc T) := by
  have hcur (j : ι) := (hTs j).1
  have hint (j : ι) := (hTs j).2.1
  have hbd (j : ι) := (hTs j).2.2.1
  have hbdi (j : ι) := (hTs j).2.2.2
  refine ⟨metricCurrent_of_bounded_weak_limit hint hcur hbd M N hM hN hlim, ?_⟩
  apply metricCurrent_of_bounded_weak_limit hbdi hbd (fun j => ?_) N 0 hN
    (fun j => ?_) (boundarySucc_weak_limit hlim)
  · rw [boundarySucc_boundarySucc (hcur j)]
    exact isMetricCurrent_zero k
  · rw [boundarySucc_boundarySucc (hcur j), mass_zero]
    rfl

end Foundations
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_WeakCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma IsMetricCurrent.first_difference_bound {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c)
    (π : Fin k → X → ℝ) (K : ℝ≥0) (hπ : ∀ i, LipschitzWith K (π i))
    (ε : ℝ≥0) (hε : ∀ x, |b x - c x| ≤ ε) :
    |T b π - T c π| ≤ (K : ℝ) ^ k * ε * mass T := by
  have hsub : BoundedLip (fun x => b x - c x) := by
    simpa [sub_eq_add_neg] using hb.add (hc.const_mul (-1))
  have heq : T (fun x => b x - c x) π = T b π - T c π := by
    simpa [sub_eq_add_neg] using hT.linearFirst b c π 1 (-1) hb hc (fun i => ⟨K, hπ i⟩)
  rw [← heq]
  simpa using hT.mass_bound_uniform hsub (fun _ => K) hπ hε

abbrev TestClass (d : ℕ) (K : ℕ) :=
  {p : C(X, ℝ) × (Fin d → C(X, ℝ)) //
    LipschitzWith K p.1 ∧ ‖p.1‖ ≤ K ∧ ∀ i, LipschitzWith K (p.2 i)}

instance testClass_nonempty (d K : ℕ) : Nonempty (TestClass (X := X) d K) := by
  refine ⟨⟨(0, fun _ => 0), ?_⟩⟩
  refine ⟨(LipschitzWith.const 0).weaken (by positivity), ?_, ?_⟩
  · simp
  · intro i
    exact (LipschitzWith.const 0).weaken (by positivity)

noncomputable def TestClass.eval {d K : ℕ} (T : Functional X d)
    (p : TestClass (X := X) d K) : ℝ := T p.val.1 (fun i => p.val.2 i)

omit [MeasurableSpace X] [BorelSpace X] in
lemma TestClass.boundedLip {d K : ℕ} (p : TestClass (X := X) d K) :
    BoundedLip (p.val.1 : X → ℝ) :=
  ⟨⟨K, p.property.1⟩, K, fun x => (p.val.1.norm_coe_le_norm x).trans p.property.2.1⟩

lemma IntegerRectifiable.testClass_lipschitz {k : ℕ} {T : Functional X (k+1)}
    (hT : IntegerRectifiable T) (hcur : IsMetricCurrent T)
    (hbd : IsMetricCurrent (boundarySucc T))
    (M N : ℝ≥0) (hM : mass T ≤ M) (hN : mass (boundarySucc T) ≤ N) (K : ℕ) :
    LipschitzWith ((K : ℝ≥0) ^ (k+1) * M +
      (k+1) * ((K : ℝ≥0) + K) ^ k * (K * N + K * M))
      (TestClass.eval (K := K) T) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro p q
  let ε : ℝ≥0 := nndist p q
  have hb : ∀ x, |p.val.1 x - q.val.1 x| ≤ ε := by
    intro x
    exact (ContinuousMap.dist_apply_le_dist x).trans
      (le_max_left (dist p.val.1 q.val.1) (dist p.val.2 q.val.2))
  have hπ : ∀ i x, |p.val.2 i x - q.val.2 i x| ≤ ε := by
    intro i x
    exact ((ContinuousMap.dist_apply_le_dist x).trans
      (dist_le_pi_dist p.val.2 q.val.2 i)).trans (le_max_right _ _)
  have hB (x : X) : |q.val.1 x| ≤ (K : ℝ≥0) :=
    (q.val.1.norm_coe_le_norm x).trans q.property.2.1
  have hfirst := IsMetricCurrent.first_difference_bound hcur p.boundedLip q.boundedLip
    (fun i => p.val.2 i) K p.property.2.2 ε hb
  have hcoord := IntegerRectifiable.test_difference_bound hT hcur hbd q.property.1
    (fun i => p.val.2 i) (fun i => q.val.2 i) K p.property.2.2 q.property.2.2 K ε hB hπ
  have hfirst' : |T p.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => p.val.2 i)| ≤
      (K : ℝ) ^ (k+1) * M * ε := by
    refine hfirst.trans ?_
    calc (K : ℝ) ^ (k+1) * ε * mass T ≤ (K : ℝ) ^ (k+1) * ε * M :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by ring
  have hcoord' : |T q.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => q.val.2 i)| ≤
      (k+1 : ℝ) * (K + K : ℝ) ^ k * ((K : ℝ) * N + K * M) * ε := by
    refine hcoord.trans ?_
    apply mul_le_mul_of_nonneg_right _ ε.coe_nonneg
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left hN (by positivity))
      (mul_le_mul_of_nonneg_left hM (by positivity))
  calc dist (TestClass.eval T p) (TestClass.eval T q) ≤
      |T p.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => p.val.2 i)| +
      |T q.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => q.val.2 i)| :=
        dist_triangle _ (T q.val.1 (fun i => p.val.2 i)) _
    _ ≤ _ := add_le_add hfirst' hcoord'
    _ = _ := by dsimp [ε]; push_cast; ring

omit [MeasurableSpace X] [BorelSpace X] in

lemma admissible_mem_testClass {d : ℕ} {b : X → ℝ} {π : Fin d → X → ℝ}
    (h : Admissible b π) :
    ∃ (K : ℕ) (p : TestClass (X := X) d K),
      (p.val.1 : X → ℝ) = b ∧ (fun i => (p.val.2 i : X → ℝ)) = π := by
  obtain ⟨⟨Kb, hb⟩, B, hB⟩ := h.1
  choose Ks hKs using h.2
  let Bn : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let L : ℝ≥0 := max Kb (max Bn (Finset.univ.sup Ks))
  obtain ⟨K, hK⟩ := exists_nat_gt L
  have hbK : Kb ≤ (K : ℝ≥0) := (le_max_left _ _).trans hK.le
  have hBK : Bn ≤ (K : ℝ≥0) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hK.le
  have hπK (i : Fin d) : Ks i ≤ (K : ℝ≥0) :=
    ((Finset.le_sup (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans (le_max_right _ _))).trans hK.le
  let p : C(X, ℝ) × (Fin d → C(X, ℝ)) :=
    (⟨b, hb.continuous⟩, fun i => ⟨π i, (hKs i).continuous⟩)
  refine ⟨K, ⟨p, ⟨hb.weaken hbK, ?_, fun i => (hKs i).weaken (hπK i)⟩⟩, rfl, rfl⟩
  apply (p.1.norm_le (by positivity)).mpr
  intro x
  exact (hB x).trans ((le_max_left B 0).trans hBK)

end Foundations

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_CountableTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma IsMetricCurrent.testClass_continuous {d : ℕ} {T : Functional X d}
    (hT : IsMetricCurrent T) (K : ℕ) :
    Continuous (TestClass.eval (X := X) (d := d) (K := K) T) := by
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have hcoord : Tendsto (fun n => T p.val.1 (fun i => (ps n).val.2 i)) atTop
      (𝓝 (T p.val.1 (fun i => p.val.2 i))) := by
    apply hT.sequentialContinuity _ _ _ p.boundedLip
    · intro i
      exact ⟨K,fun n => (ps n).property.2.2 i⟩
    · intro i x
      have hc : Continuous (fun q : TestClass (X := X) d K => q.val.2 i x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp
  have hd : Tendsto (fun n => dist (ps n) p) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hp
  have hbnd (n : ℕ) :
      dist (T p.val.1 (fun i => (ps n).val.2 i))
        (T (ps n).val.1 (fun i => (ps n).val.2 i)) ≤
      ((K:ℝ)^d * mass T) * dist (ps n) p := by
    have hh := IsMetricCurrent.first_difference_bound hT p.boundedLip (ps n).boundedLip
      (fun i => (ps n).val.2 i) K (ps n).property.2.2 (nndist (ps n) p) (fun x => ?_)
    · simpa only [Real.dist_eq,NNReal.coe_natCast,coe_nndist,mul_assoc,mul_comm,mul_left_comm]
        using hh
    · have h := (ContinuousMap.dist_apply_le_dist (f := (ps n).val.1) (g := p.val.1) x).trans
        (le_max_left (dist (ps n).val.1 p.val.1) (dist (ps n).val.2 p.val.2))
      change dist ((ps n).val.1 x) (p.val.1 x) ≤ dist (ps n) p at h
      simpa only [coe_nndist,Real.dist_eq,abs_sub_comm] using h
  apply tendsto_of_tendsto_of_dist hcoord
  exact squeeze_zero (fun n => dist_nonneg) hbnd (by simpa using hd.const_mul ((K:ℝ)^d * mass T))

end CAT0Fillings.Foundations

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_EuclideanSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Prism
abbrev Euc (k : ℕ) := EuclideanSpace ℝ (Fin k)

noncomputable def splitLinear (k : ℕ) : Euc (k+1) ≃ₗ[ℝ] ℝ × Euc k where
  toFun z := (z 0, WithLp.toLp 2 (fun i => z i.succ))
  invFun p := WithLp.toLp 2 (Matrix.vecCons p.1 (WithLp.ofLp p.2))
  left_inv z := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by aesop
  map_add' z w := by ext <;> rfl
  map_smul' a z := by ext <;> rfl

noncomputable def split (k : ℕ) : Euc (k+1) ≃L[ℝ] ℝ × Euc k :=
  (splitLinear k).toContinuousLinearEquiv

@[simp] lemma split_apply (k : ℕ) (z : Euc (k+1)) :
    split k z = (z 0, WithLp.toLp 2 (fun i => z i.succ)) := rfl

@[simp] lemma split_symm_apply (k : ℕ) (p : ℝ × Euc k) :
    (split k).symm p = WithLp.toLp 2 (Matrix.vecCons p.1 (WithLp.ofLp p.2)) := rfl

lemma split_measurePreserving (k : ℕ) : MeasurePreserving (split k) := by
  have h := (MeasurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ))
    (PiLp.volume_preserving_toLp (Fin k))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) 0).comp
        (PiLp.volume_preserving_ofLp (Fin (k+1))))
  convert h using 1
  · funext z
    apply Prod.ext
    · rfl
    · ext j
      simp [Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply,Fin.tail]
  · rfl

lemma split_symm_measurePreserving (k : ℕ) : MeasurePreserving (split k).symm := by
  exact MeasurePreserving.symm (split k).toHomeomorph.toMeasurableEquiv
    (split_measurePreserving k)

lemma integral_split (k : ℕ) (f : Euc (k+1) → ℝ) :
    ∫ z, f z = ∫ p : ℝ × Euc k, f ((split k).symm p) := by
  exact ((split_symm_measurePreserving k).integral_comp (split k).symm.toHomeomorph.measurableEmbedding f).symm

end CAT0Fillings.Prism

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_CoordinateCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]
lemma integrable_boundedLip {b : X → ℝ} (hb : BoundedLip b) : Integrable b μ :=
  hb.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end CAT0Fillings.BorelCoefficients
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_BorelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
universe u
attribute [local instance] Classical.propDecidable
namespace BorelCoefficients
variable {X : Type u} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
noncomputable def coefficientLinear (hT : IsMetricCurrent T) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    lipAlgebra (X := X) →ₗ[ℝ] ℝ where
  toFun f := T f.val π
  map_add' f g := by
    change T (fun x => f.val x + g.val x) π = _
    simpa using hT.linearFirst f.val g.val π 1 1 f.property g.property hπ
  map_smul' r f := by
    change T (fun x => r * f.val x) π = _
    simpa using hT.linearFirst f.val f.val π r 0 f.property f.property hπ

lemma coefficientLinear_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) (f : lipAlgebra (X := X)) :
    ‖coefficientLinear hT π (fun i => ⟨K i, hK i⟩) f‖ ≤
      (∏ i, (K i : ℝ)) * ‖lipToL1 μ f‖ := by
  rw [norm_lipToL1]
  exact hT.mass_bound hμ f.property K hK

noncomputable def l1Action (hT : IsMetricCurrent T) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) : Lp ℝ 1 μ →L[ℝ] ℝ :=
  (coefficientLinear hT π hπ).extendOfNorm (lipToL1 μ)

lemma l1Action_eq (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (f : lipAlgebra (X := X)) : l1Action μ hT π hπ (lipToL1 μ f) = T f.val π := by
  have hπcopy := hπ
  choose K hK using hπcopy
  exact LinearMap.extendOfNorm_eq (lipToL1_dense μ)
    ⟨∏ i, (K i : ℝ), coefficientLinear_bound μ hT hμ π K hK⟩ f

lemma l1Action_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) (b : Lp ℝ 1 μ) :
    |l1Action μ hT π (fun i => ⟨K i, hK i⟩) b| ≤ (∏ i, (K i : ℝ)) * ‖b‖ :=
  LinearMap.norm_extendOfNorm_apply_le (lipToL1_dense μ) _
    (coefficientLinear_bound μ hT hμ π K hK) b

noncomputable def borelAction (hT : IsMetricCurrent T) : Functional X k :=
  fun b π => if hb : Integrable b μ then
    if hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i) then
      l1Action μ hT π hπ (hb.toL1 b) else 0 else 0

lemma borelAction_of_integrable (hT : IsMetricCurrent T) {b : X → ℝ}
    (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT b π = l1Action μ hT π hπ (hb.toL1 b) := by
  simp only [borelAction, dite_eq_left hb, dite_eq_left hπ]

lemma borelAction_eq (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hadm : Admissible b π) :
    borelAction μ hT b π = T b π := by
  let f : lipAlgebra (X := X) := ⟨⟨b, hadm.1.continuous⟩, hadm.1⟩
  have hbeq : (integrable_boundedLip μ hadm.1).toL1 b = lipToL1 μ f := by
    apply Lp.ext
    exact (Integrable.coeFn_toL1 _).trans
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f.val).symm
  rw [borelAction_of_integrable μ hT (integrable_boundedLip μ hadm.1) π hadm.2, hbeq]
  exact l1Action_eq μ hT hμ π hadm.2 f

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma norm_toL1_integral_abs {b : X → ℝ} (hb : Integrable b μ) :
    ‖hb.toL1 b‖ = ∫ x, |b x| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toL1] with x hx
  rw [hx, Real.norm_eq_abs]

lemma borelAction_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |borelAction μ hT b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := by
  rw [borelAction_of_integrable μ hT hb π (fun i => ⟨K i, hK i⟩)]
  simpa only [norm_toL1_integral_abs] using l1Action_bound μ hT hμ π K hK (hb.toL1 b)

lemma borelAction_add (hT : IsMetricCurrent T) {b c : X → ℝ}
    (hb : Integrable b μ) (hc : Integrable c μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT (b + c) π = borelAction μ hT b π + borelAction μ hT c π := by
  simp only [borelAction_of_integrable μ hT (hb.add hc) π hπ,
    borelAction_of_integrable μ hT hb π hπ, borelAction_of_integrable μ hT hc π hπ,
    ]
  change l1Action μ hT π hπ (hb.toL1 b + hc.toL1 c) = _
  exact map_add _ _ _

lemma borelAction_smul (hT : IsMetricCurrent T) {b : X → ℝ}
    (hb : Integrable b μ) (π : Fin k → X → ℝ) (r : ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT (r • b) π = r * borelAction μ hT b π := by
  simp only [borelAction_of_integrable μ hT (hb.smul r) π hπ,
    borelAction_of_integrable μ hT hb π hπ]
  change l1Action μ hT π hπ (r • hb.toL1 b) = _
  exact map_smul _ _ _

lemma l1Action_lipschitz (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) :
    LipschitzWith (∏ i, K i) (l1Action μ hT π (fun i => ⟨K i, hK i⟩)) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro b c
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  simpa only [Real.norm_eq_abs, NNReal.coe_prod] using l1Action_bound μ hT hμ π K hK (b-c)

lemma borelAction_sequentialContinuity (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (πs : ℕ → Fin k → X → ℝ)
    (hLip : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hpt : ∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x))) :
    Tendsto (fun j => borelAction μ hT b (πs j)) atTop (𝓝 (borelAction μ hT b π)) := by
  choose K hK using hLip
  have hKlim (i) : LipschitzWith (K i) (π i) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    exact le_of_tendsto ((hpt i x).dist (hpt i y))
      (Eventually.of_forall fun j => (hK i j).dist_le_mul x y)
  have hlim := tendsto_of_lipschitz_dense (l := atTop)
    (fun j => l1Action_lipschitz μ hT hμ (πs j) K (fun i => hK i j))
    (l1Action_lipschitz μ hT hμ π K hKlim) (lipToL1_dense μ)
    (fun f => ?_) (hb.toL1 b)
  · simp only [borelAction_of_integrable μ hT hb _ (fun i => ⟨K i, hK i _⟩),
      borelAction_of_integrable μ hT hb π (fun i => ⟨K i, hKlim i⟩)]
    exact hlim
  · simp only [l1Action_eq μ hT hμ]
    exact hT.sequentialContinuity f.val π πs f.property (fun i => ⟨K i, hK i⟩) hpt

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ActionLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
lemma borelAction_sub (hT : IsMetricCurrent T) {b c : X → ℝ}
    (hb : Integrable b μ) (hc : Integrable c μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT (fun x => b x-c x) π =
      borelAction μ hT b π-borelAction μ hT c π := by
  have he : (fun x => b x-c x) = b+(-1 : ℝ) • c := by ext x; simp [sub_eq_add_neg]
  rw [he,borelAction_add μ hT hb (hc.smul (-1)) π hπ,
    borelAction_smul μ hT hc π (-1) hπ]
  ring

lemma borelAction_difference_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b c : X → ℝ} (hb : Integrable b μ) (hc : Integrable c μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |borelAction μ hT b π-borelAction μ hT c π| ≤
      (∏ i, (K i : ℝ)) * ∫ x, |b x-c x| ∂μ := by
  rw [←borelAction_sub μ hT hb hc π (fun i => ⟨K i,hK i⟩)]
  exact borelAction_bound μ hT hμ (hb.sub hc) π K hK

lemma borelAction_tendsto (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} {f : ℕ → X → ℝ} (hb : Integrable b μ)
    (hf : ∀ j, Integrable (f j) μ)
    (hlim : Tendsto (fun j => ∫ x, |f j x-b x| ∂μ) atTop (𝓝 0))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Tendsto (fun j => borelAction μ hT (f j) π) atTop (𝓝 (borelAction μ hT b π)) := by
  choose K hK using hπ
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun j => (borelAction_difference_bound μ hT hμ (hf j) hb π K hK))
  simpa only [mul_zero] using hlim.const_mul (∏ i, (K i : ℝ))

lemma borelAction_independent (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls T ν)
    {b : X → ℝ} (hbμ : Integrable b μ) (hbν : Integrable b ν)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT b π = borelAction ν hT b π := by
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation (μ+ν) (hbμ.add_measure hbν)
  have hi (j) := integrable_boundedLip (μ+ν) (f j).property
  have hlμ : Tendsto (fun j => ∫ x, |(f j).val x-b x| ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun j => integral_mono_measure (Measure.le_add_right le_rfl)
        (Eventually.of_forall fun _ => abs_nonneg _) ((hi j).sub (hbμ.add_measure hbν)).abs) hf
  have hlν : Tendsto (fun j => ∫ x, |(f j).val x-b x| ∂ν) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun j => integral_mono_measure (Measure.le_add_left le_rfl)
        (Eventually.of_forall fun _ => abs_nonneg _) ((hi j).sub (hbμ.add_measure hbν)).abs) hf
  have hμlim := borelAction_tendsto μ hT hμ hbμ
    (fun j => integrable_boundedLip μ (f j).property) hlμ π hπ
  have hνlim := borelAction_tendsto ν hT hν hbν
    (fun j => integrable_boundedLip ν (f j).property) hlν π hπ
  simp only [borelAction_eq μ hT hμ ⟨(f _).property,hπ⟩] at hμlim
  simp only [borelAction_eq ν hT hν ⟨(f _).property,hπ⟩] at hνlim
  exact tendsto_nhds_unique hμlim hνlim

end BorelCoefficients

attribute [local instance] Classical.propDecidable
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_CanonicalMass
attribute [-instance] _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
universe u
namespace MassMeasure
variable {X : Type u} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
noncomputable def weighted (μ : Measure X) (f : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))

lemma weighted_finite (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Continuous f) : IsFiniteMeasure (weighted μ f) :=
  isFiniteMeasure_withDensity_ofReal
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

omit [CompactSpace X] in
lemma integral_weighted (μ : Measure X) {f : X → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) (g : X → ℝ) :
    (∫ x, g x ∂weighted μ f) = ∫ x, f x * g x ∂μ := by
  rw [weighted, integral_withDensity_eq_integral_toReal_smul
    (hf.measurable.ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]

omit [CompactSpace X] in
lemma weighted_total (μ : Measure X) {f : X → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    (weighted μ f).real univ = ∫ x, f x ∂μ := by
  simpa using integral_weighted μ hf hpos (fun _ => 1)

variable {k : ℕ} {T : Functional X k}

lemma controls_splice (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    {f : X → ℝ} (hf : BoundedLip f) (hpos : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ 1) :
    Controls T (weighted μ (fun x => 1 - f x) + weighted ν f) := by
  have hg : BoundedLip (fun x => 1 - f x) := by
    simpa only [neg_mul, one_mul, sub_eq_add_neg] using
      (BoundedLip.const 1).add (hf.const_mul (-1))
  let := weighted_finite μ hg.continuous
  let := weighted_finite ν hf.continuous
  intro b π hb hπ
  have hlin : T b π = T (fun x => b x * (1 - f x)) π + T (fun x => b x * f x) π := by
    have h := hT.linearFirst (fun x => b x * (1-f x)) (fun x => b x * f x) π 1 1
      (hb.mul hg) (hb.mul hf) (fun i => ⟨1, hπ i⟩)
    have heq : (fun x => 1 * (b x * (1-f x)) + 1 * (b x * f x)) = b := by
      funext x; ring
    rwa [heq, one_mul, one_mul] at h
  rw [hlin]
  calc |T (fun x => b x * (1-f x)) π + T (fun x => b x * f x) π| ≤
        |T (fun x => b x * (1-f x)) π| + |T (fun x => b x * f x) π| := abs_add_le _ _
    _ ≤ (∫ x, |b x * (1-f x)| ∂μ) + ∫ x, |b x * f x| ∂ν :=
      add_le_add (hμ _ _ (hb.mul hg) hπ) (hν _ _ (hb.mul hf) hπ)
    _ = ∫ x, |b x| ∂(weighted μ (fun x => 1-f x) + weighted ν f) := by
      rw [integral_add_measure
        (hb.continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hb.continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
        integral_weighted μ hg.continuous (fun x => sub_nonneg.mpr (hbound x)),
        integral_weighted ν hf.continuous hpos]
      congr 1
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change |b x * (1-f x)| = (1-f x) * |b x|
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hbound x)), mul_comm]
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change |b x * f x| = f x * |b x|
          rw [abs_mul, abs_of_nonneg (hpos x), mul_comm]

lemma integral_cutoff_le (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hm : mass T = μ.real univ)
    {f : X → ℝ} (hf : BoundedLip f) (hpos : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ 1) :
    (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν := by
  have hg : Continuous (fun x => 1-f x) := continuous_const.sub hf.continuous
  let := weighted_finite μ hg
  let := weighted_finite ν hf.continuous
  have h := mass_le_measure (T := T)
    (μ := weighted μ (fun x => 1-f x) + weighted ν f) inferInstance
    (controls_splice hT hμ hν hf hpos hbound)
  rw [hm] at h
  have heq : (weighted μ (fun x => 1-f x) + weighted ν f).real univ =
      μ.real univ - (∫ x, f x ∂μ) + ∫ x, f x ∂ν := by
    rw [measureReal_add_apply (by finiteness) (by finiteness),
      weighted_total μ hg (fun x => sub_nonneg.mpr (hbound x)),
      weighted_total ν hf.continuous hpos]
    rw [integral_sub (integrable_const 1)
      (hf.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_const, smul_eq_mul, mul_one]
  rw [heq] at h
  linarith

lemma measure_closed_le (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hm : mass T = μ.real univ) {K : Set X} (hK : IsClosed K) : μ K ≤ ν K := by
  let fs : ℕ → X → ℝ := fun n x =>
    thickenedIndicator (δ := (1 : ℝ)/(n+1)) (by positivity) K x
  have hlimμ : Tendsto (fun n => ∫ x, fs n x ∂μ) atTop (𝓝 (μ.real K)) :=
    tendsto_integral_thickenedIndicator_of_isClosed μ hK (δs := fun n => (1 : ℝ)/(n+1))
      (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimν : Tendsto (fun n => ∫ x, fs n x ∂ν) atTop (𝓝 (ν.real K)) :=
    tendsto_integral_thickenedIndicator_of_isClosed ν hK (δs := fun n => (1 : ℝ)/(n+1))
      (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have hle : ∀ n, (∫ x, fs n x ∂μ) ≤ ∫ x, fs n x ∂ν := by
    intro n
    have hp x : 0 ≤ fs n x := by simp [fs]
    have hb x : fs n x ≤ 1 :=
      thickenedIndicator_le_one _ _ _
    apply integral_cutoff_le hT hμ hν hm _ hp hb
    refine ⟨⟨_, NNReal.isometry_coe.lipschitz.comp
      (lipschitzWith_thickenedIndicator
        (δ := (1 : ℝ)/(n+1)) (by positivity) K)⟩, 1, ?_⟩
    intro x
    rw [abs_of_nonneg (hp x)]
    exact hb x
  exact (ENNReal.toReal_le_toReal (measure_ne_top μ K) (measure_ne_top ν K)).mp
    (le_of_tendsto_of_tendsto hlimμ hlimν (Eventually.of_forall hle))

lemma measure_le (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hm : mass T = μ.real univ) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKs => iSup_le fun hK => ?_
  exact (measure_closed_le hT hμ hν hm hK.isClosed).trans (measure_mono hKs)

noncomputable def currentMassMeasure (hT : IsMetricCurrent T) : Measure X :=
  hT.exists_controls_mass_eq.choose

instance currentMassMeasure_finite (hT : IsMetricCurrent T) :
    IsFiniteMeasure (currentMassMeasure hT) :=
  hT.exists_controls_mass_eq.choose_spec.1

lemma currentMassMeasure_controls (hT : IsMetricCurrent T) :
    Controls T (currentMassMeasure hT) :=
  hT.exists_controls_mass_eq.choose_spec.2.1

lemma currentMassMeasure_total (hT : IsMetricCurrent T) :
    (currentMassMeasure hT).real univ = mass T :=
  hT.exists_controls_mass_eq.choose_spec.2.2.symm

lemma currentMassMeasure_le (hT : IsMetricCurrent T) {ν : Measure X}
    [IsFiniteMeasure ν] (hν : Controls T ν) : currentMassMeasure hT ≤ ν :=
  measure_le hT (currentMassMeasure_controls hT) hν (currentMassMeasure_total hT).symm

end MassMeasure
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_WeightedAction
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
universe u
attribute [local instance] Classical.propDecidable
namespace BorelCoefficients
variable {X : Type u} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in

lemma toL1_mul_dist_le {f g b : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hb : AEStronglyMeasurable b μ) {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) :
    ‖(hf.mul_bdd hb hM).toL1 (fun x => f x * b x) -
      (hg.mul_bdd hb hM).toL1 (fun x => g x * b x)‖ ≤
      M * ‖hf.toL1 f - hg.toL1 g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub ((hf.mul_bdd hb hM).toL1 (fun x => f x * b x))
      ((hg.mul_bdd hb hM).toL1 (fun x => g x * b x)),
    (hf.mul_bdd hb hM).coeFn_toL1, (hg.mul_bdd hb hM).coeFn_toL1,
    Lp.coeFn_sub (hf.toL1 f) (hg.toL1 g), hf.coeFn_toL1, hg.coeFn_toL1, hM]
    with x hsub hfb hgb hsub' hfx hgx hMx
  simp only [Pi.sub_apply] at hsub hsub'
  rw [hsub, hfb, hgb, hsub', hfx, hgx, ← sub_mul, norm_mul]
  nlinarith [norm_nonneg (f x - g x)]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma tendsto_toL1_mul {ι : Type*} {l : Filter ι} {fs : ι → X → ℝ} {f b : X → ℝ}
    (hfs : ∀ j, Integrable (fs j) μ) (hf : Integrable f μ)
    (hb : AEStronglyMeasurable b μ) {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    (hlim : Tendsto (fun j => (hfs j).toL1 (fs j)) l (𝓝 (hf.toL1 f))) :
    Tendsto (fun j => ((hfs j).mul_bdd hb hM).toL1 (fun x => fs j x * b x)) l
      (𝓝 ((hf.mul_bdd hb hM).toL1 (fun x => f x * b x))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun j => norm_nonneg _)
    (fun j => toL1_mul_dist_le μ (hfs j) hf hb hM)
  simpa only [mul_zero] using
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul M

lemma borelAction_locality_mul (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f b : X → ℝ} (hf : Integrable f μ) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hloc : ∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧
      Function.support b ⊆ U ∧ ∀ x ∈ U, π i x = c) :
    borelAction μ hT (fun x => f x * b x) π = 0 := by
  obtain ⟨M, hM⟩ := hb.2
  have hbM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M := Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hM x
  have hbmeas := hb.continuous.aestronglyMeasurable (μ := μ)
  obtain ⟨as, has, halim⟩ := mem_closure_iff_seq_limit.mp (lipToL1_dense μ (hf.toL1 f))
  choose fs hfs using has
  have hnorm : Tendsto (fun j => lipToL1 μ (fs j)) atTop (𝓝 (hf.toL1 f)) := by
    simpa only [hfs] using halim
  have hLp (j) : (integrable_boundedLip μ (fs j).property).toL1 (fs j).val =
      lipToL1 μ (fs j) := by
    apply Lp.ext
    exact (Integrable.coeFn_toL1 _).trans
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ (fs j).val).symm
  have hnorm' : Tendsto (fun j => (integrable_boundedLip μ (fs j).property).toL1 (fs j).val)
      atTop (𝓝 (hf.toL1 f)) := by simpa only [hLp] using hnorm
  have hprod := tendsto_toL1_mul μ (fun j => integrable_boundedLip μ (fs j).property)
    hf hbmeas hbM hnorm'
  have hact := (l1Action μ hT π hπ).continuous.continuousAt.tendsto.comp hprod
  have hz (j) : l1Action μ hT π hπ
      (((integrable_boundedLip μ (fs j).property).mul_bdd hbmeas hbM).toL1
        (fun x => (fs j).val x * b x)) = 0 := by
    rw [← borelAction_of_integrable μ hT _ π hπ,
      borelAction_eq μ hT hμ ⟨(fs j).property.mul hb, hπ⟩]
    apply hT.locality _ _ ⟨(fs j).property.mul hb, hπ⟩
    obtain ⟨i, U, c, hU, hbU, hc⟩ := hloc
    refine ⟨i, U, c, hU, ?_, hc⟩
    intro x hx
    apply hbU
    change b x ≠ 0
    intro hbx
    exact hx (by simp only [hbx, mul_zero])
  have heq : l1Action μ hT π hπ ((hf.mul_bdd hbmeas hbM).toL1 (fun x => f x * b x)) = 0 :=
    tendsto_nhds_unique hact (by simpa only [Function.comp_def, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  rwa [borelAction_of_integrable μ hT (hf.mul_bdd hbmeas hbM) π hπ]

lemma borelAction_linearCoord (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (i : Fin k)
    (g : X → ℝ) (hg : ∃ K : ℝ≥0, LipschitzWith K g) (a c : ℝ) :
    borelAction μ hT b (Function.update π i (fun x => a * π i x + c * g x)) =
      a * borelAction μ hT b π + c * borelAction μ hT b (Function.update π i g) := by
  have hπg : ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i g) j) := by
    intro j
    by_cases hji : j = i
    · simpa only [hji, Function.update_self] using hg
    · simpa only [Function.update_of_ne hji] using hπ j
  have hac : ∃ K : ℝ≥0, LipschitzWith K (fun x => a * π i x + c * g x) := by
    obtain ⟨K, hK⟩ := hπ i
    obtain ⟨L, hL⟩ := hg
    exact ⟨_, (lipschitz_mul_real hK a).add (lipschitz_mul_real hL c)⟩
  have hπac : ∀ j, ∃ K : ℝ≥0,
      LipschitzWith K ((Function.update π i (fun x => a * π i x + c * g x)) j) := by
    intro j
    by_cases hji : j = i
    · simpa only [hji, Function.update_self] using hac
    · simpa only [Function.update_of_ne hji] using hπ j
  have heq : (fun f : Lp ℝ 1 μ =>
      l1Action μ hT (Function.update π i (fun x => a * π i x + c * g x)) hπac f) =
      (fun f => a * l1Action μ hT π hπ f +
        c * l1Action μ hT (Function.update π i g) hπg f) := by
    apply (lipToL1_dense μ).equalizer
    · exact (l1Action μ hT _ _).continuous
    · exact ((l1Action μ hT π hπ).continuous.const_mul a).add
        ((l1Action μ hT _ _).continuous.const_mul c)
    · funext f
      simp only [Function.comp_apply, l1Action_eq μ hT hμ]
      exact hT.linearCoord _ _ i g a c ⟨f.property, hπ⟩ hg
  simpa only [borelAction_of_integrable μ hT hb _ hπac,
    borelAction_of_integrable μ hT hb _ hπ,
    borelAction_of_integrable μ hT hb _ hπg] using congrFun heq (hb.toL1 b)

noncomputable def weightedCurrent (hT : IsMetricCurrent T) (b : X → ℝ) : Functional X k :=
  fun f π => if Admissible f π then borelAction μ hT (fun x => b x * f x) π else 0

lemma weightedCurrent_isMetricCurrent (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) {M : ℝ≥0} (hM : ∀ᵐ x ∂μ, |b x| ≤ M) :
    IsMetricCurrent (weightedCurrent μ hT b) := by
  have hprod {f : X → ℝ} (hf : BoundedLip f) : Integrable (fun x => b x * f x) μ := by
    obtain ⟨N, hN⟩ := hf.2
    exact hb.mul_bdd hf.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hN x)
  have hap {f : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible f π) :
      weightedCurrent μ hT b f π = borelAction μ hT (fun x => b x * f x) π := ite_eq_left h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f π h
    exact ite_eq_right h
  · intro f g π a c hf hg hπ
    rw [hap ⟨(hf.const_mul a).add (hg.const_mul c), hπ⟩,
      hap ⟨hf, hπ⟩, hap ⟨hg, hπ⟩]
    have heq : (fun x => b x * (a * f x + c * g x)) =
        a • (fun x => b x * f x) + c • (fun x => b x * g x) := by funext x; simp; ring
    rw [heq, borelAction_add μ hT ((hprod hf).smul a) ((hprod hg).smul c) π hπ,
      borelAction_smul μ hT (hprod hf) π a hπ,
      borelAction_smul μ hT (hprod hg) π c hπ]
  · intro f π i g a c h hg
    have hπg : ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i g) j) := by
      intro j
      by_cases hji : j = i
      · simpa only [hji, Function.update_self] using hg
      · simpa only [Function.update_of_ne hji] using h.2 j
    have hac : ∃ K : ℝ≥0, LipschitzWith K (fun x => a * π i x + c * g x) := by
      obtain ⟨K, hK⟩ := h.2 i
      obtain ⟨L, hL⟩ := hg
      exact ⟨_, (lipschitz_mul_real hK a).add (lipschitz_mul_real hL c)⟩
    have hπac : ∀ j, ∃ K : ℝ≥0,
        LipschitzWith K ((Function.update π i (fun x => a * π i x + c * g x)) j) := by
      intro j
      by_cases hji : j = i
      · simpa only [hji, Function.update_self] using hac
      · simpa only [Function.update_of_ne hji] using h.2 j
    rw [hap ⟨h.1, hπac⟩, hap h, hap ⟨h.1, hπg⟩]
    exact borelAction_linearCoord μ hT hμ (hprod h.1) π h.2 i g hg a c
  · intro f π πs hf hLip hpt
    choose K hK using hLip
    have hπ (i) : LipschitzWith (K i) (π i) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      exact le_of_tendsto ((hpt i x).dist (hpt i y))
        (Eventually.of_forall fun j => (hK i j).dist_le_mul x y)
    simp only [hap ⟨hf, fun i => ⟨K i, hK i _⟩⟩, hap ⟨hf, fun i => ⟨K i, hπ i⟩⟩]
    exact borelAction_sequentialContinuity μ hT hμ (hprod hf) π πs
      (fun i => ⟨K i, hK i⟩) hpt
  · intro f π h hloc
    rw [hap h]
    exact borelAction_locality_mul μ hT hμ hb h.1 π h.2 hloc
  · have hfin : IsFiniteMeasure ((M : ℝ≥0∞) • μ) := by
      constructor
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ univ)
    refine ⟨(M : ℝ≥0∞) • μ, hfin, ?_⟩
    intro f π hf hπ
    rw [hap ⟨hf, fun i => ⟨1, hπ i⟩⟩,
      integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
    have hbound := borelAction_bound μ hT hμ (hprod hf) π (fun _ => 1) hπ
    simp only [NNReal.coe_one, Finset.prod_const_one, one_mul] at hbound
    apply hbound.trans
    rw [← integral_const_mul]
    apply integral_mono_ae (hprod hf).abs ((integrable_boundedLip μ hf).abs.const_mul M)
    filter_upwards [hM] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

end BorelCoefficients

attribute [local instance] Classical.propDecidable
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
namespace BorelRestriction
open BorelCoefficients MassMeasure

universe u

variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ} {T : Functional X k}
noncomputable def restrictCurrent (hT : IsMetricCurrent T) (E : Set X) : Functional X k :=
  fun b π => if Admissible b π then
    borelAction (currentMassMeasure hT) hT (E.indicator b) π else 0

lemma restrictCurrent_apply (hT : IsMetricCurrent T) (E : Set X) {b : X → ℝ}
    {π : Fin k → X → ℝ} (h : Admissible b π) :
    restrictCurrent hT E b π = borelAction (currentMassMeasure hT) hT (E.indicator b) π :=
  ite_eq_left h

lemma restrictCurrent_isMetricCurrent (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) : IsMetricCurrent (restrictCurrent hT E) := by
  have he : restrictCurrent hT E =
      weightedCurrent (currentMassMeasure hT) hT (E.indicator (fun _ => 1)) := by
    funext b π
    dsimp only [restrictCurrent, weightedCurrent]
    congr 2
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [he]
  apply weightedCurrent_isMetricCurrent _ hT (currentMassMeasure_controls hT)
    ((integrable_const (1 : ℝ)).indicator hE) (M := 1)
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ E <;> simp [hx]

lemma restrictCurrent_controls (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) : Controls (restrictCurrent hT E) ((currentMassMeasure hT).restrict E) := by
  intro b π hb hπ
  rw [restrictCurrent_apply hT E ⟨hb, fun i => ⟨1, hπ i⟩⟩]
  have h := borelAction_bound (currentMassMeasure hT) hT (currentMassMeasure_controls hT)
    ((integrable_boundedLip _ hb).indicator hE) π (fun _ => 1) hπ
  simp only [NNReal.coe_one, Finset.prod_const_one, one_mul] at h
  apply h.trans_eq
  rw [← integral_indicator hE]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ E <;> simp [hx]

lemma restrictCurrent_complement_sum (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) (b : X → ℝ) (π : Fin k → X → ℝ) :
    restrictCurrent hT E b π + restrictCurrent hT Eᶜ b π = T b π := by
  by_cases h : Admissible b π
  · rw [restrictCurrent_apply hT E h, restrictCurrent_apply hT Eᶜ h,
      ← borelAction_add (currentMassMeasure hT) hT
        ((integrable_boundedLip _ h.1).indicator hE)
        ((integrable_boundedLip _ h.1).indicator hE.compl) π h.2]
    have he : E.indicator b + Eᶜ.indicator b = b := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [he]
    exact borelAction_eq _ hT (currentMassMeasure_controls hT) h
  · simp only [restrictCurrent, ite_eq_right h, hT.offDomain b π h, add_zero]

lemma restrictMass_le (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) ≤
      (currentMassMeasure hT).restrict E :=
  currentMassMeasure_le _ (restrictCurrent_controls hT hE)

lemma controls_restriction_sum (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    Controls T (currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) +
      currentMassMeasure (restrictCurrent_isMetricCurrent hT hE.compl)) := by
  intro b π hb hπ
  rw [← restrictCurrent_complement_sum hT hE b π]
  apply (abs_add_le _ _).trans
  rw [integral_add_measure (integrable_boundedLip _ hb).abs (integrable_boundedLip _ hb).abs]
  exact add_le_add (currentMassMeasure_controls (restrictCurrent_isMetricCurrent hT hE) b π hb hπ)
    (currentMassMeasure_controls (restrictCurrent_isMetricCurrent hT hE.compl) b π hb hπ)

lemma restriction_massMeasure (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) =
      (currentMassMeasure hT).restrict E := by
  apply le_antisymm (restrictMass_le hT hE)
  rw [Measure.le_iff]
  intro B hB
  let μ := currentMassMeasure hT
  let ν := currentMassMeasure (restrictCurrent_isMetricCurrent hT hE)
  let ξ := currentMassMeasure (restrictCurrent_isMetricCurrent hT hE.compl)
  have hle : μ ≤ ν + ξ := currentMassMeasure_le hT (controls_restriction_sum hT hE)
  have hξ : ξ (B ∩ E) = 0 := by
    apply le_antisymm _ bot_le
    apply (restrictMass_le hT hE.compl (B ∩ E)).trans
    rw [Measure.restrict_apply (hB.inter hE)]
    have he : B ∩ E ∩ Eᶜ = ∅ := by aesop
    rw [he, measure_empty]
    exact le_refl _
  rw [Measure.restrict_apply hB]
  calc
    μ (B ∩ E) ≤ (ν + ξ) (B ∩ E) := hle _
    _ = ν (B ∩ E) := by rw [Measure.add_apply, hξ, add_zero]
    _ ≤ ν B := measure_mono inter_subset_left

lemma restriction_mass (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    mass (restrictCurrent hT E) = (currentMassMeasure hT).real E := by
  rw [← currentMassMeasure_total (restrictCurrent_isMetricCurrent hT hE),
    Measure.real, restriction_massMeasure hT hE, Measure.restrict_apply_univ]
  rfl

end BorelRestriction

attribute [local instance] Classical.propDecidable
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_MultiplicityRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
namespace IntegerChart
open BorelCoefficients

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [Nonempty X]
variable {k : ℕ} (C : IntegerChart X k)
lemma borelAction_eq_integral (hC : IsMetricCurrent C.action)
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : Controls C.action μ)
    {b : X → ℝ} (hb : Measurable b) (hB : ∃ M : ℝ, ∀ x, |b x| ≤ M)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hC b π =
      ∫ z, (C.multiplicity z : ℝ)*C.jacobian π z*b (C.paramExtended z)
        ∂volume.restrict C.domain := by
  choose K hK using hπ
  let w : Euc k → ℝ := fun z => (C.multiplicity z : ℝ)*C.jacobian π z
  have hw := C.integrable_weighted_jacobian (fun i => ⟨K i,hK i⟩)
  change Integrable w (volume.restrict C.domain) at hw
  have heq (f : X → ℝ) (hf : BoundedLip f) :
      C.action f π = ∫ z, w z*f (C.paramExtended z) ∂volume.restrict C.domain := by
    rw [action,ite_eq_left ⟨hf,fun i => ⟨K i,hK i⟩⟩]
    apply integral_congr_ae
    filter_upwards [C.scalar_ae_paramExtended f] with z hz
    change C.scalar f z = f (C.paramExtended z) at hz
    rw [hz]
    dsimp [w]
    ring
  have hcontrol (f : X → ℝ) (hf : BoundedLip f) :
      |∫ z, w z*f (C.paramExtended z) ∂volume.restrict C.domain| ≤
        ∫ x, |f x| ∂((∏ i,K i) • μ) := by
    rw [←heq f hf,integral_smul_nnreal_measure]
    simpa only [NNReal.smul_def,NNReal.coe_prod,smul_eq_mul] using hC.mass_bound hμ hf K hK
  have hbi : Integrable b μ := by
    obtain ⟨M,hM⟩ := hB
    exact Integrable.of_bound hb.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x)
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation μ hbi
  have hfi (j) := integrable_boundedLip μ (f j).property
  have hblim := borelAction_tendsto μ hC hμ hbi hfi hf π (fun i => ⟨K i,hK i⟩)
  have hwbi := integrable_weighted_comp (volume.restrict C.domain)
    C.measurable_paramExtended hw hb hB
  have hwfi (j) := integrable_weighted_comp (volume.restrict C.domain)
    C.measurable_paramExtended hw (f j).val.continuous.measurable (f j).property.2
  have hilim : Tendsto (fun j => ∫ z, w z*(f j).val (C.paramExtended z)
      ∂volume.restrict C.domain) atTop
      (𝓝 (∫ z, w z*b (C.paramExtended z) ∂volume.restrict C.domain)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (by simpa only [mul_zero] using hf.const_mul (∏ i, (K i : ℝ)))
    rw [Real.dist_eq,←integral_sub (hwfi j) hwbi]
    have hsub : (fun z => w z*(f j).val (C.paramExtended z)-w z*b (C.paramExtended z)) =
        (fun z => w z*((f j).val (C.paramExtended z)-b (C.paramExtended z))) := by
      ext z; ring
    rw [hsub]
    have hbnd : ∃ M : ℝ, ∀ x, |(f j).val x-b x| ≤ M := by
      obtain ⟨M,hM⟩ := (f j).property.2
      obtain ⟨N,hN⟩ := hB
      exact ⟨M+N,fun x => (abs_sub _ _).trans (add_le_add (hM x) (hN x))⟩
    have hh := signed_chart_control_borel (volume.restrict C.domain) ((∏ i,K i) • μ)
      C.measurable_paramExtended hw hcontrol
      ((f j).val.continuous.measurable.sub hb) hbnd
    rw [integral_smul_nnreal_measure] at hh
    simpa only [NNReal.smul_def,NNReal.coe_prod,smul_eq_mul,Pi.sub_apply] using hh
  have hseq : (fun j => borelAction μ hC (f j).val π) =
      (fun j => ∫ z, w z*(f j).val (C.paramExtended z) ∂volume.restrict C.domain) := by
    ext j
    rw [borelAction_eq μ hC hμ ⟨(f j).property,fun i => ⟨K i,hK i⟩⟩,heq]
    exact (f j).property
  rw [hseq] at hblim
  exact tendsto_nhds_unique hblim hilim

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
namespace IntegerChart
open BorelCoefficients BorelRestriction MassMeasure

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [Nonempty X]
variable {k : ℕ} (C : IntegerChart X k)

noncomputable def restrictMultiplicity (E : Set X) (hE : MeasurableSet E) : IntegerChart X k :=
  { C with
    multiplicity := (C.paramExtended ⁻¹' E).indicator C.multiplicity
    integrable := by
      have heq : (fun z => (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ)) =
          (C.paramExtended ⁻¹' E).indicator (fun z => (C.multiplicity z : ℝ)) := by
        funext z
        by_cases hz : C.paramExtended z ∈ E <;> simp [hz]
      rw [heq]
      exact C.integrable.indicator (hE.preimage C.measurable_paramExtended) }

lemma restrictMultiplicity_action (hC : IsMetricCurrent C.action)
    {E : Set X} (hE : MeasurableSet E) :
    (C.restrictMultiplicity E hE).action = restrictCurrent hC E := by
  funext b π
  by_cases hadm : Admissible b π
  · rw [restrictCurrent_apply hC E hadm,
      C.borelAction_eq_integral hC (currentMassMeasure_controls hC)
        (hadm.1.continuous.measurable.indicator hE) ?_ π hadm.2]
    · rw [action,ite_eq_left hadm]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem C.borel] with z hz
      change (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ) * C.scalar b z *
        C.jacobian π z = (C.multiplicity z : ℝ)*C.jacobian π z*E.indicator b (C.paramExtended z)
      have hz' : z ∈ C.domain := hz
      have hs : C.scalar b z = b (C.paramExtended z) := by
        simp only [scalar,paramExtended,dite_eq_left hz']
      rw [hs]
      by_cases he : C.paramExtended z ∈ E <;> simp [he,mul_comm,mul_left_comm]
    · obtain ⟨M,hM⟩ := hadm.1.2
      refine ⟨max M 0,fun x => ?_⟩
      by_cases hx : x ∈ E
      · simpa only [indicator_of_mem hx] using (hM x).trans (le_max_left M 0)
      · simp only [indicator_of_notMem hx,abs_zero,le_max_iff,le_refl,or_true]
  · rw [action,ite_eq_right hadm]
    exact (restrictCurrent_isMetricCurrent hC hE).offDomain b π hadm |>.symm

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ComponentMass
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma finite_sum_measure_of_summable_total {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (hs : Summable (fun i => (μ i).real univ)) : IsFiniteMeasure (Measure.sum μ) := by
  constructor
  have heq : (Measure.sum μ) univ = ENNReal.ofReal (∑' i, (μ i).real univ) := by
    rw [Measure.sum_apply _ MeasurableSet.univ,
      ENNReal.ofReal_tsum_of_nonneg (fun i => measureReal_nonneg) hs]
    congr 1
    funext i
    exact (ENNReal.ofReal_toReal (measure_ne_top (μ i) univ)).symm
  rw [heq]
  exact ENNReal.ofReal_lt_top

section SumControls
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]

lemma controls_sum (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π) : Controls T (Measure.sum μ) := by
  intro b π hb hπ
  have hbi : Integrable (fun x => |b x|) (Measure.sum μ) :=
    (BorelCoefficients.integrable_boundedLip _ hb).abs
  have hs : Summable (fun i => ∫ x, |b x| ∂μ i) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hbi.summable_integral
  have hsa : Summable (fun i => S i b π) :=
    hs.of_norm_bounded (fun i => by simpa only [Real.norm_eq_abs] using hμ i b π hb hπ)
  rw [hT b π,integral_sum_measure hbi]
  calc
    |∑' i, S i b π| ≤ ∑' i, |S i b π| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => S i b π) hsa.norm)
    _ ≤ ∑' i, ∫ x, |b x| ∂μ i := hsa.abs.tsum_le_tsum (fun i => hμ i b π hb hπ) hs

end SumControls

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ActionSeries
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  (μ : ℕ → Measure X) [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure (Measure.sum μ)]
omit [IsFiniteMeasure (Measure.sum μ)] in
lemma summable_borelAction (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    {b : X → ℝ} (hb : Integrable b (Measure.sum μ))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) :
    Summable (fun i => borelAction (μ i) (hS i) b π) := by
  choose K hK using hπ
  have hs : Summable (fun i => ∫ x, |b x| ∂μ i) := by
    simpa only [Real.norm_eq_abs] using hb.summable_integral
  apply (hs.mul_left (∏ j, (K j : ℝ))).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs] using borelAction_bound (μ i) (hS i) (hμ i)
    (hb.mono_measure (Measure.le_sum μ i)) π K hK

omit [IsFiniteMeasure (Measure.sum μ)] in
lemma borelAction_sum_difference_bound (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    {b c : X → ℝ} (hb : Integrable b (Measure.sum μ))
    (hc : Integrable c (Measure.sum μ))
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ j, LipschitzWith (K j) (π j)) :
    |(∑' i, borelAction (μ i) (hS i) b π)-(∑' i, borelAction (μ i) (hS i) c π)| ≤
      (∏ j, (K j : ℝ)) * ∫ x, |b x-c x| ∂Measure.sum μ := by
  have hsb := summable_borelAction μ hS hμ hb π (fun j => ⟨K j,hK j⟩)
  have hsc := summable_borelAction μ hS hμ hc π (fun j => ⟨K j,hK j⟩)
  have hbc : Integrable (fun x => b x-c x) (Measure.sum μ) := hb.sub hc
  have hs : Summable (fun i => ∫ x, |b x-c x| ∂μ i) := by
    simpa only [Real.norm_eq_abs] using hbc.summable_integral
  rw [←hsb.tsum_sub hsc,integral_sum_measure hbc.abs,←tsum_mul_left]
  calc
    |∑' i, (borelAction (μ i) (hS i) b π-borelAction (μ i) (hS i) c π)| ≤
      ∑' i, |borelAction (μ i) (hS i) b π-borelAction (μ i) (hS i) c π| := by
        simpa only [Real.norm_eq_abs] using
          (norm_tsum_le_tsum_norm
            (f := fun i => borelAction (μ i) (hS i) b π-borelAction (μ i) (hS i) c π)
            (hsb.sub hsc).norm)
    _ ≤ ∑' i, (∏ j, (K j : ℝ)) * ∫ x, |b x-c x| ∂μ i :=
      (hsb.sub hsc).abs.tsum_le_tsum
        (fun i => borelAction_difference_bound (μ i) (hS i) (hμ i)
          (hb.mono_measure (Measure.le_sum μ i)) (hc.mono_measure (Measure.le_sum μ i)) π K hK)
        (hs.mul_left _)

lemma borelAction_sum (hT : IsMetricCurrent T) (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    (heq : ∀ b π, T b π = ∑' i, S i b π)
    {b : X → ℝ} (hb : Integrable b (Measure.sum μ))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) :
    borelAction (Measure.sum μ) hT b π = ∑' i, borelAction (μ i) (hS i) b π := by
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation (Measure.sum μ) hb
  have hfi (j) := integrable_boundedLip (Measure.sum μ) (f j).property
  have hleft := borelAction_tendsto (Measure.sum μ) hT (controls_sum hμ heq)
    hb hfi hf π hπ
  have hright : Tendsto (fun j => ∑' i, borelAction (μ i) (hS i) (f j).val π) atTop
      (𝓝 (∑' i, borelAction (μ i) (hS i) b π)) := by
    choose K hK using hπ
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun j => borelAction_sum_difference_bound μ hS hμ (hfi j) hb π K hK)
    simpa only [mul_zero] using hf.const_mul (∏ i, (K i : ℝ))
  have hseq : (fun j => borelAction (Measure.sum μ) hT (f j).val π) =
      (fun j => ∑' i, borelAction (μ i) (hS i) (f j).val π) := by
    ext j
    rw [borelAction_eq _ hT (controls_sum hμ heq) ⟨(f j).property,hπ⟩,heq]
    apply tsum_congr
    intro i
    exact (borelAction_eq (μ i) (hS i) (hμ i) ⟨(f j).property,hπ⟩).symm
  rw [hseq] at hleft
  exact tendsto_nhds_unique hleft hright

end BorelCoefficients

attribute [local instance] Classical.propDecidable

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_DomainRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma ae_fderivWithin_restrict_domain (μ : Measure E) [μ.IsAddHaarMeasure]
    {s t : Set E} (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s)
    {f g : E → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hgf : EqOn g f t) :
    ∀ᵐ x ∂μ.restrict t, fderivWithin ℝ g t x = fderivWithin ℝ f s x := by
  obtain ⟨F,hF,hfF⟩ := hf.extend_real
  have hgF : EqOn g F t := fun x hx => (hgf hx).trans (hfF (hts hx))
  filter_upwards [ae_fderivWithin_eq_fderiv_extension μ ht hF hgF,
    (ae_fderivWithin_eq_fderiv_extension μ hs hF hfF).filter_mono
      (ae_mono (Measure.restrict_mono hts le_rfl))] with x hx hy
  exact hx.trans hy.symm

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} (C : IntegerChart X k)

noncomputable def restrictDomain {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) : IntegerChart X k where
  domain := t
  borel := ht
  bounded := C.bounded.subset hts
  param := fun z => C.param ⟨z,hts z.property⟩
  bilipschitz := by
    obtain ⟨K,J,hK,hJ⟩ := C.bilipschitz
    refine ⟨K,J,LipschitzWith.of_dist_le_mul (fun a b =>
      hK.dist_le_mul ⟨a,hts a.property⟩ ⟨b,hts b.property⟩),?_⟩
    exact AntilipschitzWith.of_le_mul_dist (fun a b =>
      hJ.le_mul_dist ⟨a,hts a.property⟩ ⟨b,hts b.property⟩)
  multiplicity := C.multiplicity
  integrable := C.integrable.mono_measure (Measure.restrict_mono hts le_rfl)

omit [MeasurableSpace X] [BorelSpace X] in
lemma restrictDomain_scalar {t : Set (Euc k)} (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (b : X → ℝ) : EqOn ((C.restrictDomain ht hts).scalar b) (C.scalar b) t := by
  classical
  intro x hx
  change (if hz : x ∈ t then b (C.param ⟨x,hts hz⟩) else 0) = C.scalar b x
  rw [dite_eq_left hx,scalar,dite_eq_left (hts hx)]

omit [MeasurableSpace X] [BorelSpace X] in
lemma restrictDomain_jacobian_ae {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    (C.restrictDomain ht hts).jacobian π =ᵐ[volume.restrict t] C.jacobian π := by
  have hderiv : ∀ᵐ x ∂volume.restrict t, ∀ i,
      fderivWithin ℝ ((C.restrictDomain ht hts).scalar (π i)) t x =
        fderivWithin ℝ (C.scalar (π i)) C.domain x := by
    rw [eventually_all]
    intro i
    obtain ⟨K,hK⟩ := hπ i
    obtain ⟨L,J,hL,_⟩ := C.bilipschitz
    exact ae_fderivWithin_restrict_domain volume C.borel ht hts
      (C.scalar_lipschitzOn hL hK) (C.restrictDomain_scalar ht hts (π i))
  filter_upwards [hderiv] with x hx
  unfold jacobian
  congr 1
  funext i j
  exact congrArg (fun l => l (EuclideanSpace.single j 1)) (hx i)

variable [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma paramExtended_mem_image_iff {t : Set (Euc k)} (hts : t ⊆ C.domain)
    {x : Euc k} (hx : x ∈ C.domain) :
    C.paramExtended x ∈ C.paramExtended '' t ↔ x ∈ t := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    obtain ⟨K,J,_,hJ⟩ := C.bilipschitz
    have hxy' : C.param ⟨y,hts hy⟩ = C.param ⟨x,hx⟩ := by
      simpa only [paramExtended,dite_eq_left hx,dite_eq_left (hts hy)] using hxy
    have heq : y = x := congrArg Subtype.val (hJ.injective hxy')
    exact heq ▸ hy
  · exact fun h => ⟨x,h,rfl⟩

lemma restrictDomain_action {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) (hC : IsMetricCurrent C.action) :
    (C.restrictDomain ht hts).action =
      BorelRestriction.restrictCurrent hC (C.paramExtended '' t) := by
  classical
  let E := C.paramExtended '' t
  have hE : MeasurableSet E := C.measurableSet_paramExtended_image ht hts
  rw [←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hadm : Admissible b π
  · rw [action,action,ite_eq_left hadm,ite_eq_left hadm]
    change (∫ z in t, (C.multiplicity z : ℝ)*(C.restrictDomain ht hts).scalar b z*
      (C.restrictDomain ht hts).jacobian π z) =
      ∫ z in C.domain, (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ)*
        C.scalar b z*C.jacobian π z
    calc
      _ = ∫ z in t, (C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z := by
        apply integral_congr_ae
        filter_upwards [C.restrictDomain_jacobian_ae ht hts hadm.2,ae_restrict_mem ht] with z hz hzt
        rw [hz,C.restrictDomain_scalar ht hts b hzt]
      _ = ∫ z in C.domain, t.indicator (fun z =>
          (C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z) z := by
        rw [integral_indicator ht,Measure.restrict_restrict ht,inter_eq_left.mpr hts]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem C.borel] with z hz
        have he : z ∈ C.paramExtended ⁻¹' E ↔ z ∈ t := C.paramExtended_mem_image_iff hts hz
        by_cases hzt : z ∈ t
        · simp only [indicator_of_mem hzt,indicator_of_mem (he.mpr hzt)]
        · simp only [indicator_of_notMem hzt,indicator_of_notMem (mt he.mp hzt),Int.cast_zero,zero_mul]
  · simp only [action,ite_eq_right hadm]

end IntegerChart
end CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_ImageRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
noncomputable def restrictImage (E : Set X) (hE : MeasurableSet E) : IntegerChart X k :=
  C.restrictDomain (C.borel.inter (C.measurable_paramExtended hE)) inter_subset_left

omit [CompactSpace X] in
lemma restrictImage_image (E : Set X) (hE : MeasurableSet E) :
    (C.restrictImage E hE).image = C.image ∩ E := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨⟨⟨z,z.property.1⟩,rfl⟩,by
      change C.param ⟨z,z.property.1⟩ ∈ E
      simpa only [mem_preimage,paramExtended,dite_eq_left z.property.1] using z.property.2⟩
  · rintro ⟨⟨z,rfl⟩,hz⟩
    refine ⟨⟨z,⟨z.property,?_⟩⟩,rfl⟩
    simpa only [mem_preimage,paramExtended,dite_eq_left z.property] using hz

lemma restrictImage_action (E : Set X) (hE : MeasurableSet E)
    (hC : IsMetricCurrent C.action) :
    (C.restrictImage E hE).action = BorelRestriction.restrictCurrent hC E := by
  classical
  let t := C.domain ∩ C.paramExtended ⁻¹' E
  have ht : MeasurableSet t := C.borel.inter (C.measurable_paramExtended hE)
  have hts : t ⊆ C.domain := inter_subset_left
  have him : MeasurableSet (C.paramExtended '' t) := C.measurableSet_paramExtended_image ht hts
  change (C.restrictDomain ht hts).action = _
  rw [C.restrictDomain_action ht hts hC,←C.restrictMultiplicity_action hC him,
    ←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem C.borel] with z hz
    have hi : C.paramExtended z ∈ C.paramExtended '' t ↔ C.paramExtended z ∈ E := by
      rw [C.paramExtended_mem_image_iff hts hz]
      exact and_iff_right hz
    change (↑((C.paramExtended ⁻¹' (C.paramExtended '' t)).indicator C.multiplicity z) : ℝ) *
      C.scalar b z * C.jacobian π z =
      ↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) * C.scalar b z * C.jacobian π z
    by_cases he : C.paramExtended z ∈ E
    · rw [indicator_of_mem (show z ∈ C.paramExtended ⁻¹' (C.paramExtended '' t) from hi.mpr he),
        indicator_of_mem (show z ∈ C.paramExtended ⁻¹' E from he)]
    · rw [indicator_of_notMem (show z ∉ C.paramExtended ⁻¹' (C.paramExtended '' t) from mt hi.mp he),
        indicator_of_notMem (show z ∉ C.paramExtended ⁻¹' E from he)]
  · simp only [action,ite_eq_right hab]

lemma restrictImage_isMetricCurrent (E : Set X) (hE : MeasurableSet E)
    (hC : IsMetricCurrent C.action) : IsMetricCurrent (C.restrictImage E hE).action := by
  rw [C.restrictImage_action E hE hC]
  exact BorelRestriction.restrictCurrent_isMetricCurrent hC hE

lemma restrictImage_mass_le (E : Set X) (hE : MeasurableSet E)
    (hC : IsMetricCurrent C.action) : mass (C.restrictImage E hE).action ≤ mass C.action := by
  rw [C.restrictImage_action E hE hC,BorelRestriction.restriction_mass hC hE,
    ←MassMeasure.currentMassMeasure_total hC]
  exact measureReal_mono (subset_univ E)

lemma restrictCurrent_image_eq (hC : IsMetricCurrent C.action) {E : Set X}
    (hE : MeasurableSet E) (hCE : C.image ⊆ E) :
    BorelRestriction.restrictCurrent hC E = C.action := by
  classical
  rw [←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem C.borel] with z hz
    change z ∈ C.domain at hz
    have hi : C.paramExtended z ∈ E := hCE ⟨⟨z,hz⟩,by simp only [paramExtended,dite_eq_left hz]⟩
    change (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ) *
      C.scalar b z * C.jacobian π z = _
    rw [indicator_of_mem (show z ∈ C.paramExtended ⁻¹' E from hi)]
  · simp only [action,ite_eq_right hab]

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_ContainingCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C D : IntegerChart X k)
noncomputable def withMultiplicity (θ : Euc k → ℤ)
    (hθ : Integrable (fun x => (θ x : ℝ)) (volume.restrict C.domain)) : IntegerChart X k :=
  {C with multiplicity := θ, integrable := hθ}

variable (hCD : C.domain ⊆ D.domain)
  (hparam : ∀ z : C.domain, C.param z = D.param ⟨z,hCD z.property⟩)

include hCD hparam in
lemma scalar_eqOn_containing (b : X → ℝ) : EqOn (C.scalar b) (D.scalar b) C.domain := by
  intro x hx
  rw [C.scalar_eq hx,D.scalar_eq (hCD hx),hparam ⟨x,hx⟩]

include hCD hparam in
lemma jacobian_eqOn_containing_ae {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    C.jacobian π =ᵐ[volume.restrict C.domain] D.jacobian π := by
  have hrow : ∀ i, ∀ᵐ x ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (π i)) C.domain x =
      fderivWithin ℝ (D.scalar (π i)) D.domain x := by
    intro i
    obtain ⟨K,hK⟩ := hπ i
    obtain ⟨L,U,hL,_⟩ := D.bilipschitz
    exact ae_fderivWithin_restrict_domain volume D.borel C.borel hCD
      (D.scalar_lipschitzOn hL hK) (C.scalar_eqOn_containing D hCD hparam (π i))
  filter_upwards [ae_all_iff.mpr hrow] with x hx
  unfold jacobian
  congr 1
  funext i j
  exact congrArg (fun A => A (EuclideanSpace.single j 1)) (hx i)

include hCD in
lemma indicatorMultiplicity_integrable :
    Integrable (fun x => ((C.domain.indicator C.multiplicity x : ℤ) : ℝ))
      (volume.restrict D.domain) := by
  have hI : IntegrableOn (fun x => (C.multiplicity x : ℝ)) C.domain
      (volume.restrict D.domain) := by
    simpa only [IntegrableOn,Measure.restrict_restrict C.borel,inter_eq_left.mpr hCD] using C.integrable
  apply ((integrable_indicator_iff C.borel).mpr hI).congr
  filter_upwards with x
  by_cases hx : x ∈ C.domain <;> simp [hx]

noncomputable def extendOn : IntegerChart X k :=
  D.withMultiplicity (C.domain.indicator C.multiplicity) (C.indicatorMultiplicity_integrable D hCD)

include hparam in
lemma extendOn_action : (C.extendOn D hCD).action = C.action := by
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    change (∫ x in D.domain, ((C.domain.indicator C.multiplicity x : ℤ) : ℝ) *
      D.scalar b x * D.jacobian π x) = _
    have heq : (fun x => ((C.domain.indicator C.multiplicity x : ℤ) : ℝ) *
        D.scalar b x * D.jacobian π x) =
        C.domain.indicator (fun x => (C.multiplicity x : ℝ) * D.scalar b x * D.jacobian π x) := by
      funext x
      by_cases hx : x ∈ C.domain <;> simp [hx]
    rw [heq,integral_indicator C.borel,Measure.restrict_restrict C.borel,inter_eq_left.mpr hCD]
    apply integral_congr_ae
    filter_upwards [C.jacobian_eqOn_containing_ae D hCD hparam hab.2,
      ae_restrict_mem C.borel] with x hx hxs
    rw [hx,C.scalar_eqOn_containing D hCD hparam b hxs]
  · simp only [action,ite_eq_right hab]

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Summation
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
lemma tsum_lintegral_norm_ne_top {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ ≠ ⊤ := by
  have h i : ∫⁻ x, ‖f i x‖ₑ ∂μ = ‖∫ x, ‖f i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hf i).norm]
    simp only [ENNReal.coe_nnreal_eq,coe_nnnorm,Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (f i x)))]
  rw [funext h]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hS.abs)

lemma ae_summable_norm_of_integral {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => ‖f i x‖) := by
  have ht := tsum_lintegral_norm_ne_top hf hS
  rw [←lintegral_tsum (fun i => (hf i).aestronglyMeasurable.enorm)] at ht
  filter_upwards [ae_lt_top' (AEMeasurable.tsum
    (fun i => (hf i).aestronglyMeasurable.enorm)) ht] with x hx
  exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne

lemma integrable_series_norm {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, ‖f i x‖) μ := by
  refine ⟨by fun_prop,?_⟩
  have hfin : ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ < ⊤ := by
    rw [lintegral_tsum (fun i => (hf i).aestronglyMeasurable.enorm)]
    exact (tsum_lintegral_norm_ne_top hf hS).lt_top
  change (∫⁻ x, ‖∑' i, ‖f i x‖‖ₑ ∂μ) < ⊤
  convert hfin using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr_ae
  filter_upwards [ae_summable_norm_of_integral hf hS] with x hx
  simp_rw [←coe_nnnorm,←NNReal.coe_tsum,enorm_eq_nnnorm,NNReal.nnnorm_eq]
  exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)

lemma integrable_series {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  apply (integrable_series_norm hf hS).mono' (by fun_prop)
  filter_upwards [ae_summable_norm_of_integral hf hS] with x hx
  exact norm_tsum_le_tsum_norm hx

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}

lemma summable_actions_all {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i)))
    (b : X → ℝ) (π : Fin k → X → ℝ) : Summable (fun i => T i b π) := by
  by_cases hab : Admissible b π
  · exact summable_actions_of_summable_masses hT hS hab
  · simp only [fun i => (hT i).offDomain b π hab,summable_zero]

theorem isMetricCurrent_tsum {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i))) :
    IsMetricCurrent (fun b π => ∑' i, T i b π) := by
  have hs := summable_actions_all hT hS
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [fun i => (hT i).offDomain b π hab,tsum_zero]
  · intro b c π a d hb hc hπ
    simp only [fun i => (hT i).linearFirst b c π a d hb hc hπ]
    rw [((hs b π).mul_left a).tsum_add ((hs c π).mul_left d)]
    simp only [tsum_mul_left]
  · intro b π j f a c hab hf
    simp only [fun i => (hT i).linearCoord b π j f a c hab hf]
    rw [((hs b π).mul_left a).tsum_add ((hs b (Function.update π j f)).mul_left c)]
    simp only [tsum_mul_left]
  · intro b π πs hb hπs hlim
    choose K hK using hπs
    obtain ⟨M,hM⟩ := hb.2
    apply tendsto_tsum_of_dominated_convergence
      (hS.mul_left ((∏ j, (K j : ℝ)) * M))
      (fun i => (hT i).sequentialContinuity b π πs hb (fun j => ⟨K j,hK j⟩) hlim)
    exact Eventually.of_forall (fun j i => (hT i).mass_bound_uniform hb K (fun l => hK l j) hM)
  · intro b π hab hloc
    simp only [fun i => (hT i).locality b π hab hloc,tsum_zero]
  · choose μ hfin hμ heq using fun i => (hT i).exists_controls_mass_eq
    let : ∀ i, IsFiniteMeasure (μ i) := hfin
    have hm : Summable (fun i => (μ i).real univ) := by simpa only [←heq] using hS
    let := finite_sum_measure_of_summable_total μ hm
    exact ⟨Measure.sum μ,inferInstance,controls_sum hμ (fun _ _ => rfl)⟩

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_IntegerSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
lemma intCast_tsum_exists (a : ℕ → ℤ) :
    ∃ z : ℤ, (z : ℝ) = ∑' i, (a i : ℝ) := by
  by_cases h : Summable (fun i => (a i : ℝ))
  · have hm : (∑' i, (a i : ℝ)) ∈ Set.range ((↑) : ℤ → ℝ) := by
      apply Real.isClosed_range_intCast.mem_of_tendsto h.hasSum
      exact Filter.Eventually.of_forall fun s => ⟨∑ i ∈ s, a i,by simp⟩
    exact hm
  · exact ⟨0,by simpa only [Int.cast_zero] using (tsum_eq_zero_of_not_summable h).symm⟩

noncomputable def summedMultiplicity (θ : ℕ → X → ℤ) (x : X) : ℤ :=
  (intCast_tsum_exists (fun i => θ i x)).choose

omit [MeasurableSpace X] in
lemma summedMultiplicity_cast (θ : ℕ → X → ℤ) (x : X) :
    (summedMultiplicity θ x : ℝ) = ∑' i, (θ i x : ℝ) :=
  (intCast_tsum_exists (fun i => θ i x)).choose_spec

lemma summedMultiplicity_integrable {θ : ℕ → X → ℤ}
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) μ)
    (hS : Summable (fun i => ∫ x, |(θ i x : ℝ)| ∂μ)) :
    Integrable (fun x => (summedMultiplicity θ x : ℝ)) μ := by
  simp_rw [summedMultiplicity_cast]
  exact integrable_series hθ (by simpa only [Real.norm_eq_abs] using hS)

lemma summedMultiplicity_integral_weight {θ : ℕ → X → ℤ}
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) μ)
    (hS : Summable (fun i => ∫ x, |(θ i x : ℝ)| ∂μ))
    {g : X → ℝ} (hg : AEStronglyMeasurable g μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖g x‖ ≤ M) :
    (∫ x, (summedMultiplicity θ x : ℝ) * g x ∂μ) =
      ∑' i, ∫ x, (θ i x : ℝ) * g x ∂μ := by
  have hI i := (hθ i).mul_bdd hg hM
  have hsum : Summable (fun i => ∫ x, ‖(θ i x : ℝ) * g x‖ ∂μ) := by
    apply (hS.mul_left M).of_nonneg_of_le
    · intro i
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro i
      rw [←integral_const_mul]
      apply integral_mono_ae (hI i).norm ((hθ i).abs.const_mul M)
      filter_upwards [hM] with x hx
      simpa only [norm_mul,Real.norm_eq_abs,mul_comm] using
        mul_le_mul_of_nonneg_left hx (norm_nonneg (θ i x : ℝ))
  rw [integral_tsum_of_summable_integral_norm hI hsum]
  apply integral_congr_ae
  filter_upwards with x
  rw [summedMultiplicity_cast,tsum_mul_right]

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_MultiplicityMass
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma multiplicity_integral_le_mass (hC : IsMetricCurrent C.action)
    {U : ℝ≥0} (hU : AntilipschitzWith U C.param) :
    (∫ z in C.domain, |(C.multiplicity z : ℝ)|) ≤ (U : ℝ)^k * mass C.action := by
  obtain ⟨ν,hν,hcontrol,hmass⟩ := hC.exists_controls_mass_eq
  let := hν
  have hrow : ∀ (i : Fin k) y (hy : y ∈ C.domain) z (hz : z ∈ C.domain),
      |EuclideanSpace.proj i y - EuclideanSpace.proj i z| ≤
        (U : ℝ) * dist (C.param ⟨y,hy⟩) (C.param ⟨z,hz⟩) := by
    intro i y hy z hz
    calc
      _ = ‖(y-z).ofLp i‖ := by
        change |y.ofLp i-z.ofLp i| = ‖(y-z).ofLp i‖
        simp [Real.norm_eq_abs]
      _ ≤ ‖y-z‖ := PiLp.norm_apply_le (y-z) i
      _ ≤ _ := by simpa only [dist_eq_norm,Subtype.dist_eq] using
        hU.le_mul_dist ⟨y,hy⟩ ⟨z,hz⟩
  have hdet : |(Matrix.of fun (i j : Fin k) =>
      EuclideanSpace.proj i (EuclideanSpace.single j (1 : ℝ))).det| = 1 := by
    have he : (Matrix.of fun (i j : Fin k) =>
        EuclideanSpace.proj i (EuclideanSpace.single j (1 : ℝ))) = 1 := by
      ext i j
      change (EuclideanSpace.single j (1 : ℝ)).ofLp i = (1 : Matrix (Fin k) (Fin k) ℝ) i j
      simp [PiLp.single_apply,Matrix.one_apply]
    rw [he,Matrix.det_one,abs_one]
  have hle := C.linear_piece_mass_le hC hcontrol C.borel (Subset.refl _)
    (fun i => EuclideanSpace.proj i) U hrow
  simp only [hdet,mul_one] at hle
  have hle' := hle.trans (Measure.restrict_le_self)
  have hI := integral_mono_measure hle' (Eventually.of_forall (fun _ => (zero_le_one : (0:ℝ) ≤ 1)))
    (integrable_const (1 : ℝ) : Integrable (fun _ : X => (1 : ℝ)) ((U^k) • ν))
  rw [integral_densityPush (volume.restrict C.domain) C.measurable_paramExtended
    C.integrable.abs (Eventually.of_forall (fun _ => abs_nonneg _)) continuous_const] at hI
  rw [integral_smul_nnreal_measure] at hI
  simp only [mul_one,integral_const,smul_eq_mul,NNReal.smul_def,NNReal.coe_pow] at hI
  simpa only [hmass,mul_one] using hI

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_ChangeVariables
attribute [-instance] _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
lemma lipschitzOn_image_null {s : Set E} {f : E → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : μ s = 0) : μ (f '' s) = 0 := by
  let H : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have ha : H ≪ μ := Measure.absolutelyContinuous_isAddHaarMeasure H μ
  have hb : μ ≪ H := Measure.absolutelyContinuous_isAddHaarMeasure μ H
  apply hb
  apply le_antisymm _ zero_le
  have hi := hf.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
  change H (f '' s) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * H s at hi
  simpa only [ha hs,mul_zero] using hi

lemma lipschitzOn_image_ae_congr_subset {s t : Set E} {f : E → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hts : t ⊆ s) (heq : s =ᵐ[μ] t) :
    f '' s =ᵐ[μ] f '' t := by
  apply ae_eq_set.mpr
  constructor
  · have hsub : f '' s \ f '' t ⊆ f '' (s \ t) := by
      rintro y ⟨⟨x,hx,rfl⟩,hy⟩
      exact ⟨x,⟨hx,fun h => hy ⟨x,h,rfl⟩⟩,rfl⟩
    exact measure_mono_null hsub
      (lipschitzOn_image_null μ (hf.mono sdiff_subset) (ae_eq_set.mp heq).1)
  · rw [sdiff_eq_empty.mpr (image_mono hts),measure_empty]

lemma exists_measurable_full_derivative_domain {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ t, t ⊆ s ∧ MeasurableSet t ∧ t =ᵐ[μ] s ∧
      ∀ x ∈ t, HasFDerivWithinAt f (fderivWithin ℝ f s x) t x := by
  let d : Set E := {x | x ∈ s ∧ DifferentiableWithinAt ℝ f s x}
  have hd : d =ᵐ[μ] s := by
    filter_upwards [(ae_restrict_iff' hs).mp (hf.ae_differentiableWithinAt hs (μ := μ))] with x hx
    change (x ∈ s ∧ DifferentiableWithinAt ℝ f s x) = (x ∈ s)
    exact propext ⟨And.left,fun h => ⟨h,hx h⟩⟩
  obtain ⟨t,htd,htm,hteq⟩ := (hs.nullMeasurableSet.congr hd.symm).exists_measurable_subset_ae_eq
  have hts : t ⊆ s := fun x hx => (htd hx).1
  exact ⟨t,hts,htm,hteq.trans hd,fun x hx => (htd hx).2.hasFDerivWithinAt.mono hts⟩

lemma integral_image_eq_integral_abs_det_within {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : E → V) :
    ∫ y in f '' s, g y ∂μ =
      ∫ x in s, |(fderivWithin ℝ f s x).det| • g (f x) ∂μ := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  calc
    _ = ∫ y in f '' t, g y ∂μ :=
      setIntegral_congr_set (lipschitzOn_image_ae_congr_subset μ hf hts hteq.symm)
    _ = ∫ x in t, |(fderivWithin ℝ f s x).det| • g (f x) ∂μ :=
      integral_image_eq_integral_abs_det_fderiv_smul μ htm htd (hinj.mono hts) g
    _ = _ := setIntegral_congr_set hteq

lemma integrableOn_image_iff_integrableOn_abs_det_within {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : E → V) :
    IntegrableOn g (f '' s) μ ↔
      IntegrableOn (fun x => |(fderivWithin ℝ f s x).det| • g (f x)) s μ := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  exact (integrableOn_congr_set_ae (lipschitzOn_image_ae_congr_subset μ hf hts hteq.symm)).trans
    ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ htm htd (hinj.mono hts) g).trans
      (integrableOn_congr_set_ae hteq))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lipschitzOn_invFunOn {s : Set E} {f : E → E} {L : ℝ≥0}
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y)) :
    LipschitzOnWith L (Function.invFunOn f s) (f '' s) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have h := ha _ (Function.invFunOn_mem hx) _ (Function.invFunOn_mem hy)
  simpa only [Function.invFunOn_eq hx,Function.invFunOn_eq hy] using h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma antilipschitzOn_injOn {s : Set E} {f : E → E} {L : ℝ≥0}
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y)) :
    InjOn f s := by
  intro x hx y hy heq
  have h := ha x hx y hy
  rw [heq,dist_self,mul_zero] at h
  exact dist_le_zero.mp h

lemma bilipschitzOn_ae_pullback {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y))
    {p : E → Prop} (hp : ∀ᵐ y ∂μ.restrict (f '' s), p y) :
    ∀ᵐ x ∂μ.restrict s, p (f x) := by
  have hinj := antilipschitzOn_injOn ha
  have him := hs.image_of_continuousOn_injOn hf.continuousOn hinj
  have hnull : μ ({y | ¬ p y} ∩ f '' s) = 0 := by
    rwa [ae_iff,Measure.restrict_apply' him] at hp
  rw [ae_iff,Measure.restrict_apply' hs]
  apply measure_mono_null _
    (lipschitzOn_image_null μ ((lipschitzOn_invFunOn ha).mono inter_subset_right) hnull)
  intro x hx
  refine ⟨f x,⟨hx.1,⟨x,hx.2,rfl⟩⟩,?_⟩
  exact hinj.leftInvOn_invFunOn hx.2

lemma ae_fderivWithin_comp_bilipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {g : E → V} {J : ℝ≥0} (hg : LipschitzOnWith J g (f '' s)) :
    ∀ᵐ x ∂μ.restrict s, fderivWithin ℝ (g ∘ f) s x =
      (fderivWithin ℝ g (f '' s) (f x)).comp (fderivWithin ℝ f s x) := by
  have hinj := antilipschitzOn_injOn ha
  have him := hs.image_of_continuousOn_injOn hf.continuousOn hinj
  filter_upwards [ae_uniqueDiffWithinAt μ s,hf.ae_differentiableWithinAt hs (μ := μ),
    bilipschitzOn_ae_pullback μ hs hf ha (hg.ae_differentiableWithinAt him (μ := μ))]
    with x hx hfx hgx
  exact fderivWithin_comp x hgx hfx (mapsTo_image f s) hx

lemma aemeasurable_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    AEMeasurable (fderivWithin ℝ f s) (μ.restrict s) := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  have h := aemeasurable_fderivWithin μ htm htd
  rwa [Measure.restrict_congr_set hteq] at h

lemma ae_norm_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∀ᵐ x ∂μ.restrict s, ‖fderivWithin ℝ f s x‖ ≤ K := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  have hlin : ApproximatesLinearOn f (0 : E →L[ℝ] E) t K := by
    intro x hx y hy
    simpa only [_root_.zero_apply,sub_zero,←dist_eq_norm] using
      hf.dist_le_mul x (hts hx) y (hts hy)
  have h := hlin.norm_fderiv_sub_le μ htm (fderivWithin ℝ f s) htd
  rw [Measure.restrict_congr_set hteq] at h
  filter_upwards [h] with x hx
  exact_mod_cast (by simpa only [sub_zero] using hx : ‖fderivWithin ℝ f s x‖₊ ≤ K)

lemma ae_bound_det_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ C : ℝ, ∀ᵐ x ∂μ.restrict s, ‖(fderivWithin ℝ f s x).det‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) (K : ℝ)).exists_bound_of_continuousOn
    (ContinuousLinearMap.continuous_det (𝕜 := ℝ) (E := E)).continuousOn
  refine ⟨C,?_⟩
  filter_upwards [ae_norm_fderivWithin_lipschitzOn μ hs hf] with x hx
  exact hC _ (by simpa only [mem_closedBall,dist_zero_right] using hx)

lemma integrable_mul_det_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    {g : E → ℝ} (hg : IntegrableOn g s μ) :
    IntegrableOn (fun x => g x * (fderivWithin ℝ f s x).det) s μ := by
  obtain ⟨C,hC⟩ := ae_bound_det_fderivWithin_lipschitzOn μ hs hf
  exact hg.mul_bdd ((ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
    (aemeasurable_fderivWithin_lipschitzOn μ hs hf)).aestronglyMeasurable) hC

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Orientation
attribute [-instance] _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
noncomputable def differentialOrientation (d : ℝ) : ℤ := if 0 ≤ d then 1 else -1

lemma abs_mul_differentialOrientation (d : ℝ) :
    |d| * (differentialOrientation d : ℝ) = d := by
  by_cases hd : 0 ≤ d
  · simp [differentialOrientation,hd,abs_of_nonneg hd]
  · simp [differentialOrientation,hd,abs_of_neg (lt_of_not_ge hd)]

lemma signed_lipschitzOn_changeVariables {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    (θ : E → ℤ) (g : E → ℝ) :
    ∫ y in f '' s, ((θ (Function.invFunOn f s y) *
      differentialOrientation (fderivWithin ℝ f s (Function.invFunOn f s y)).det : ℤ) : ℝ) * g y ∂μ =
    ∫ x in s, (θ x : ℝ) * (fderivWithin ℝ f s x).det * g (f x) ∂μ := by
  rw [integral_image_eq_integral_abs_det_within μ hs hf hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [hinj.leftInvOn_invFunOn hx,Int.cast_mul,smul_eq_mul]
  have heq := abs_mul_differentialOrientation (fderivWithin ℝ f s x).det
  calc
    _ = (θ x : ℝ) * (|(fderivWithin ℝ f s x).det| *
      (differentialOrientation (fderivWithin ℝ f s x).det : ℝ)) * g (f x) := by ring
    _ = _ := by rw [heq]

lemma integrableOn_oriented_multiplicity_image {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    {θ : E → ℤ} (hθ : IntegrableOn (fun x => (θ x : ℝ)) s μ) :
    IntegrableOn (fun y => ((θ (Function.invFunOn f s y) *
      differentialOrientation (fderivWithin ℝ f s (Function.invFunOn f s y)).det : ℤ) : ℝ))
      (f '' s) μ := by
  rw [integrableOn_image_iff_integrableOn_abs_det_within μ hs hf hinj]
  apply (integrable_mul_det_fderivWithin_lipschitzOn μ hs hf hθ).congr
  filter_upwards [ae_restrict_mem hs] with x hx
  rw [hinj.leftInvOn_invFunOn hx,Int.cast_mul,smul_eq_mul]
  rw [←mul_assoc,mul_comm _ (θ x : ℝ),mul_assoc,abs_mul_differentialOrientation]

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Reparametrization
attribute [-instance] _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
variable (f : Euc k → Euc k) {K L : ℝ≥0}
  (hf : LipschitzOnWith K f C.domain)
  (ha : ∀ x ∈ C.domain, ∀ y ∈ C.domain,
    dist x y ≤ (L : ℝ) * dist (f x) (f y))
noncomputable def reparam : IntegerChart X k where
  domain := f '' C.domain
  borel := C.borel.image_of_continuousOn_injOn hf.continuousOn (antilipschitzOn_injOn ha)
  bounded := by
    apply Metric.isBounded_iff.mpr
    refine ⟨(K : ℝ) * diam C.domain,?_⟩
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (hf.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_left (dist_le_diam_of_mem C.bounded hx hy) K.coe_nonneg)
  param := fun y => C.param ⟨Function.invFunOn f C.domain y,Function.invFunOn_mem y.property⟩
  bilipschitz := by
    obtain ⟨J,U,hJ,hU⟩ := C.bilipschitz
    refine ⟨J * L,K * U,?_,?_⟩
    · rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      have h := (lipschitzOn_invFunOn ha).dist_le_mul x x.property y y.property
      exact (hJ.dist_le_mul _ _).trans (by
        simpa only [mul_assoc,NNReal.coe_mul,Subtype.dist_eq] using
          (mul_le_mul_of_nonneg_left h J.coe_nonneg))
    · apply AntilipschitzWith.of_le_mul_dist
      intro x y
      have hx := Function.invFunOn_mem x.property
      have hy := Function.invFunOn_mem y.property
      have h := hf.dist_le_mul _ hx _ hy
      rw [Function.invFunOn_eq x.property,Function.invFunOn_eq y.property] at h
      exact h.trans (by
        simpa only [mul_assoc,NNReal.coe_mul,Subtype.dist_eq] using
          (mul_le_mul_of_nonneg_left (hU.le_mul_dist ⟨_,hx⟩ ⟨_,hy⟩) K.coe_nonneg))
  multiplicity := fun y => C.multiplicity (Function.invFunOn f C.domain y) *
    differentialOrientation (fderivWithin ℝ f C.domain (Function.invFunOn f C.domain y)).det
  integrable := integrableOn_oriented_multiplicity_image volume C.borel hf
    (antilipschitzOn_injOn ha) C.integrable

lemma reparam_scalar {b : X → ℝ} {x : Euc k} (hx : x ∈ C.domain) :
    (C.reparam f hf ha).scalar b (f x) = C.scalar b x := by
  have hfx : f x ∈ (C.reparam f hf ha).domain := ⟨x,hx,rfl⟩
  rw [(C.reparam f hf ha).scalar_eq hfx,C.scalar_eq hx]
  change b (C.param ⟨Function.invFunOn f C.domain (f x),_⟩) = b (C.param ⟨x,hx⟩)
  congr 2
  apply Subtype.ext
  exact (antilipschitzOn_injOn ha).leftInvOn_invFunOn hx

lemma reparam_image : (C.reparam f hf ha).image = C.image := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨⟨Function.invFunOn f C.domain y,Function.invFunOn_mem y.property⟩,rfl⟩
  · rintro ⟨z,rfl⟩
    refine ⟨⟨f z,⟨z,z.property,rfl⟩⟩,?_⟩
    change C.param ⟨Function.invFunOn f C.domain (f z),_⟩ = C.param z
    congr 1
    apply Subtype.ext
    exact (antilipschitzOn_injOn ha).leftInvOn_invFunOn z.property

end IntegerChart

lemma row_det_comp {k : ℕ} (rows : Fin k → Euc k →L[ℝ] ℝ) (A : Euc k →L[ℝ] Euc k) :
    Matrix.det (fun i j => rows i (A (EuclideanSpace.single j 1))) =
      Matrix.det (fun i j => rows i (EuclideanSpace.single j 1)) * A.det := by
  let B := EuclideanSpace.basisFun (Fin k) ℝ
  have hm : (fun i j => rows i (A (EuclideanSpace.single j 1))) =
      (show Matrix (Fin k) (Fin k) ℝ from fun i j => rows i (EuclideanSpace.single j 1)) * LinearMap.toMatrix B.toBasis B.toBasis A.toLinearMap := by
    ext i j
    rw [Matrix.mul_apply]
    have h := congrArg (rows i) (B.sum_repr (A (EuclideanSpace.single j 1)))
    simp only [_root_.map_sum,map_smul,smul_eq_mul] at h
    simpa only [B,LinearMap.toMatrix_apply,EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr,OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis,ContinuousLinearMap.coe_coe,mul_comm] using h.symm
  rw [hm,Matrix.det_mul,LinearMap.det_toMatrix]

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
variable (f : Euc k → Euc k) {K L : ℝ≥0}
  (hf : LipschitzOnWith K f C.domain)
  (ha : ∀ x ∈ C.domain, ∀ y ∈ C.domain,
    dist x y ≤ (L : ℝ) * dist (f x) (f y))

lemma reparam_jacobian_ae {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ J : ℝ≥0, LipschitzWith J (π i)) :
    ∀ᵐ x ∂volume.restrict C.domain, C.jacobian π x =
      (C.reparam f hf ha).jacobian π (f x) * (fderivWithin ℝ f C.domain x).det := by
  have hr : ∀ i, ∀ᵐ x ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (π i)) C.domain x =
        (fderivWithin ℝ ((C.reparam f hf ha).scalar (π i)) (f '' C.domain) (f x)).comp
          (fderivWithin ℝ f C.domain x) := by
    intro i
    obtain ⟨J,hJ⟩ := hπ i
    obtain ⟨U,V,hU,_⟩ := (C.reparam f hf ha).bilipschitz
    have hc := ae_fderivWithin_comp_bilipschitzOn volume C.borel hf ha
      ((C.reparam f hf ha).scalar_lipschitzOn hU hJ)
    filter_upwards [hc,ae_restrict_mem C.borel] with x hx hxs
    have heq : EqOn ((C.reparam f hf ha).scalar (π i) ∘ f) (C.scalar (π i)) C.domain :=
      fun z hz => C.reparam_scalar f hf ha hz
    rwa [fderivWithin_congr' heq hxs] at hx
  filter_upwards [ae_all_iff.mpr hr] with x hx
  unfold jacobian
  simp_rw [hx,ContinuousLinearMap.comp_apply]
  exact row_det_comp _ _

variable [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in

lemma reparam_action : (C.reparam f hf ha).action = C.action := by
  funext b π
  by_cases hbπ : Admissible b π
  · simp only [action,ite_eq_left hbπ]
    change (∫ y in f '' C.domain,
      ((C.multiplicity (Function.invFunOn f C.domain y) * differentialOrientation
        (fderivWithin ℝ f C.domain (Function.invFunOn f C.domain y)).det : ℤ) : ℝ) *
        (C.reparam f hf ha).scalar b y * (C.reparam f hf ha).jacobian π y) = _
    simp_rw [mul_assoc]
    rw [signed_lipschitzOn_changeVariables volume C.borel hf (antilipschitzOn_injOn ha)]
    apply integral_congr_ae
    filter_upwards [C.reparam_jacobian_ae f hf ha hbπ.2,ae_restrict_mem C.borel] with x hx hxs
    rw [C.reparam_scalar f hf ha hxs,hx]
    ring
  · simp only [action,ite_eq_right hbπ]

end IntegerChart
end CAT0Fillings
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Transitions
attribute [-instance] _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
open Set Metric
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C D : IntegerChart X k)
noncomputable def inverseParam (x : X) : Euc k :=
  if hx : x ∈ C.image then (Classical.choose hx : C.domain).val else 0

lemma inverseParam_mem {x : X} (hx : x ∈ C.image) :
    C.inverseParam x ∈ C.domain := by
  simp only [inverseParam,dite_eq_left hx]
  exact (Classical.choose hx).property

lemma param_inverseParam {x : X} (hx : x ∈ C.image) :
    C.param ⟨C.inverseParam x,C.inverseParam_mem hx⟩ = x := by
  change C.param ⟨if h : x ∈ C.image then (Classical.choose h).val else 0,_⟩ = x
  simpa only [dite_eq_left hx] using (Classical.choose_spec hx)

lemma inverseParam_dist {U : ℝ≥0} (ha : AntilipschitzWith U C.param)
    {x y : X} (hx : x ∈ C.image) (hy : y ∈ C.image) :
    dist (C.inverseParam x) (C.inverseParam y) ≤ (U : ℝ) * dist x y := by
  have h := ha.le_mul_dist ⟨C.inverseParam x,C.inverseParam_mem hx⟩
    ⟨C.inverseParam y,C.inverseParam_mem hy⟩
  simpa only [Subtype.dist_eq,C.param_inverseParam hx,C.param_inverseParam hy] using h

noncomputable def transition (z : Euc k) : Euc k :=
  if hz : z ∈ C.domain then D.inverseParam (C.param ⟨z,hz⟩) else 0

lemma transition_apply {z : Euc k} (hz : z ∈ C.domain) :
    C.transition D z = D.inverseParam (C.param ⟨z,hz⟩) := by
  simp only [transition,dite_eq_left hz]

variable (hCD : C.image ⊆ D.image)
include hCD

lemma transition_mem {z : Euc k} (hz : z ∈ C.domain) :
    C.transition D z ∈ D.domain := by
  rw [C.transition_apply D hz]
  exact D.inverseParam_mem (hCD ⟨⟨z,hz⟩,rfl⟩)

lemma transition_param {z : Euc k} (hz : z ∈ C.domain) :
    D.param ⟨C.transition D z,C.transition_mem D hCD hz⟩ = C.param ⟨z,hz⟩ := by
  convert D.param_inverseParam (hCD (show C.param ⟨z,hz⟩ ∈ C.image from ⟨⟨z,hz⟩,rfl⟩)) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Subtype.ext
  exact C.transition_apply D hz

lemma transition_bilipschitz : ∃ K L : ℝ≥0,
    LipschitzOnWith K (C.transition D) C.domain ∧
    ∀ x ∈ C.domain, ∀ y ∈ C.domain,
      dist x y ≤ (L : ℝ) * dist (C.transition D x) (C.transition D y) := by
  obtain ⟨J,U,hJ,hU⟩ := C.bilipschitz
  obtain ⟨K,V,hK,hV⟩ := D.bilipschitz
  refine ⟨V * J,U * K,?_,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [C.transition_apply D hx,C.transition_apply D hy]
    have h := D.inverseParam_dist hV (hCD ⟨⟨x,hx⟩,rfl⟩) (hCD ⟨⟨y,hy⟩,rfl⟩)
    exact h.trans (by simpa only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq] using
      mul_le_mul_of_nonneg_left (hJ.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩) V.coe_nonneg)
  · intro x hx y hy
    have h := hU.le_mul_dist ⟨x,hx⟩ ⟨y,hy⟩
    have h' := hK.dist_le_mul ⟨C.transition D x,C.transition_mem D hCD hx⟩
      ⟨C.transition D y,C.transition_mem D hCD hy⟩
    rw [C.transition_param D hCD hx,C.transition_param D hCD hy] at h'
    exact h.trans (by simpa only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq] using
      mul_le_mul_of_nonneg_left h' U.coe_nonneg)

theorem exists_inCoordinates :
    ∃ E : IntegerChart X k, ∃ hED : E.domain ⊆ D.domain,
      (∀ z : E.domain, E.param z = D.param ⟨z,hED z.property⟩) ∧
      E.action = C.action ∧ E.image = C.image := by
  obtain ⟨K,L,hf,ha⟩ := C.transition_bilipschitz D hCD
  let E := C.reparam (C.transition D) hf ha
  have hED : E.domain ⊆ D.domain := by
    rintro y ⟨x,hx,rfl⟩
    exact C.transition_mem D hCD hx
  refine ⟨E,hED,?_,C.reparam_action _ hf ha,C.reparam_image _ hf ha⟩
  intro z
  let x := Function.invFunOn (C.transition D) C.domain z
  have hx : x ∈ C.domain := Function.invFunOn_mem z.property
  have he : C.transition D x = z := Function.invFunOn_eq z.property
  change C.param ⟨x,hx⟩ = D.param ⟨z,hED z.property⟩
  rw [←C.transition_param D hCD hx]
  congr 1
  exact Subtype.ext he

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_OverlapSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma actionWeight_bound {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    ∃ M : ℝ, ∀ᵐ x ∂volume.restrict C.domain, ‖C.scalar b x * C.jacobian π x‖ ≤ M := by
  obtain ⟨M,hM⟩ := hab.1.2
  obtain ⟨B,hB⟩ := C.exists_jacobian_bound hab.2
  refine ⟨max M 0 * max B 0,?_⟩
  filter_upwards [hB,ae_restrict_mem C.borel] with x hx hxs
  rw [norm_mul]
  apply mul_le_mul
  · rw [C.scalar_eq hxs,Real.norm_eq_abs]
    exact (hM _).trans (le_max_left _ _)
  · exact hx.trans (le_max_left _ _)
  · exact norm_nonneg _
  · exact le_max_right _ _

noncomputable def sumMultiplicities (θ : ℕ → Euc k → ℤ)
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) (volume.restrict C.domain))
    (hS : Summable (fun i => ∫ x in C.domain, |(θ i x : ℝ)|)) : IntegerChart X k :=
  C.withMultiplicity (summedMultiplicity θ) (summedMultiplicity_integrable hθ hS)

lemma sumMultiplicities_action (θ : ℕ → Euc k → ℤ)
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) (volume.restrict C.domain))
    (hS : Summable (fun i => ∫ x in C.domain, |(θ i x : ℝ)|)) (b : X → ℝ) (π : Fin k → X → ℝ) :
    (C.sumMultiplicities θ hθ hS).action b π =
      ∑' i, (C.withMultiplicity (θ i) (hθ i)).action b π := by
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    change (∫ x in C.domain, (summedMultiplicity θ x : ℝ) * C.scalar b x * C.jacobian π x) =
      ∑' i, ∫ x in C.domain, (θ i x : ℝ) * C.scalar b x * C.jacobian π x
    simp_rw [mul_assoc]
    obtain ⟨M,hM⟩ := C.actionWeight_bound hab
    obtain ⟨K,hK⟩ := hab.1.1
    exact summedMultiplicity_integral_weight hθ hS
      ((C.measurable_scalar hK).aestronglyMeasurable.mul (C.jacobian_aestronglyMeasurable hab.2)) hM
  · simp only [action,ite_eq_right hab,tsum_zero]

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}

theorem exists_overlap_sum (D : IntegerChart X k) (C : ℕ → IntegerChart X k)
    (hCD : ∀ i, (C i).image ⊆ D.image) (hC : ∀ i, IsMetricCurrent (C i).action)
    (hS : Summable (fun i => mass (C i).action)) :
    ∃ E : IntegerChart X k, E.image = D.image ∧
      ∀ b π, E.action b π = ∑' i, (C i).action b π := by
  choose F hFD hparam hact him using fun i => (C i).exists_inCoordinates D (hCD i)
  let G (i : ℕ) : IntegerChart X k := (F i).extendOn D (hFD i)
  have hG i : (G i).action = (C i).action :=
    ((F i).extendOn_action D (hFD i) (hparam i)).trans (hact i)
  have hGcurrent i : IsMetricCurrent (G i).action := by rw [hG]; exact hC i
  obtain ⟨L,U,_,hU⟩ := D.bilipschitz
  let θ (i : ℕ) := (G i).multiplicity
  have hθ i : Integrable (fun x => (θ i x : ℝ)) (volume.restrict D.domain) := (G i).integrable
  have hl1 : Summable (fun i => ∫ x in D.domain, |(θ i x : ℝ)|) := by
    apply (hS.mul_left ((U : ℝ)^k)).of_nonneg_of_le
    · intro i
      exact integral_nonneg (fun _ => abs_nonneg _)
    · intro i
      have hbound := (G i).multiplicity_integral_le_mass (hGcurrent i) hU
      change (∫ x in D.domain, |(θ i x : ℝ)|) ≤ (U : ℝ)^k * mass (G i).action at hbound
      simpa only [hG] using hbound
  refine ⟨D.sumMultiplicities θ hθ hl1,rfl,?_⟩
  intro b π
  rw [D.sumMultiplicities_action θ hθ hl1]
  apply tsum_congr
  intro i
  change (G i).action b π = _
  rw [hG]

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_RectifiableMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma measurableSet_image : MeasurableSet C.image := by
  have heq : C.image = C.paramExtended '' C.domain := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z,z.property,by simp only [paramExtended,dite_eq_left z.property]⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,by simp only [paramExtended,dite_eq_left hz]⟩
  rw [heq]
  exact C.measurableSet_paramExtended_image C.borel (Subset.rfl)

end IntegerChart

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_DisjointUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

lemma sum_disjoint_indicators {X : Type*} (Z : ℕ → Set X)
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) (b : X → ℝ)
    (s : Finset ℕ) (x : X) :
    ∑ i ∈ s, (Z i).indicator b x = (⋃ i ∈ s, Z i).indicator b x := by
  classical
  by_cases h : ∃ i ∈ s, x ∈ Z i
  · obtain ⟨i,hi,hxi⟩ := h
    rw [indicator_of_mem (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hxi⟩⟩)]
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hxi b
    · intro j _ hji
      exact indicator_of_notMem (fun hxj => Set.disjoint_left.mp (hd hji) hxj hxi) b
    · exact fun h => (h hi).elim
  · have hnot : x ∉ ⋃ i ∈ s, Z i := by simpa only [mem_iUnion,exists_prop] using h
    rw [indicator_of_notMem hnot]
    exact Finset.sum_eq_zero fun i hi => indicator_of_notMem (fun hx => h ⟨i,hi,hx⟩) b

namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

lemma borelAction_finset_sum (hT : IsMetricCurrent T) (f : ℕ → X → ℝ)
    (hf : ∀ i, Integrable (f i) μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (s : Finset ℕ) :
    borelAction μ hT (∑ i ∈ s, f i) π = ∑ i ∈ s, borelAction μ hT (f i) π := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [borelAction_of_integrable μ hT (integrable_zero X ℝ μ) π hπ]
      change l1Action μ hT π hπ 0 = 0
      exact map_zero _
  | @insert i s hi ih =>
      have hs : Integrable (∑ j ∈ s, f j) μ := by
        exact integrable_finsetSum' s (fun j _ => hf j)
      rw [Finset.sum_insert hi,Finset.sum_insert hi,borelAction_add μ hT (hf i) hs π hπ,ih]

lemma borelAction_iUnion (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    HasSum (fun i => borelAction μ hT ((Z i).indicator b) π)
      (borelAction μ hT ((⋃ i, Z i).indicator b) π) := by
  classical
  let g := (⋃ i, Z i).indicator b
  let f (j : ℕ) := (⋃ i ∈ Finset.range j, Z i).indicator b
  have hfi j : Integrable (f j) μ := hb.indicator (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hZ i)
  have hg : Integrable g μ := hb.indicator (MeasurableSet.iUnion hZ)
  have heq j : f j = ∑ i ∈ Finset.range j, (Z i).indicator b := by
    ext x
    simpa only [Finset.sum_apply] using (sum_disjoint_indicators Z hd b (Finset.range j) x).symm
  have hlimx (x : X) : ∀ᶠ j : ℕ in atTop, f j x = g x := by
    by_cases hx : x ∈ ⋃ i, Z i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      filter_upwards [eventually_ge_atTop (i+1)] with j hj
      change (⋃ i ∈ Finset.range j, Z i).indicator b x = (⋃ i, Z i).indicator b x
      rw [indicator_of_mem hx,indicator_of_mem
        (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hi⟩⟩)]
    · exact Eventually.of_forall fun j => by
        have hxj : x ∉ ⋃ i ∈ Finset.range j, Z i := by
          intro hj
          obtain ⟨i,hi⟩ := mem_iUnion.mp hj
          obtain ⟨_,hxi⟩ := mem_iUnion.mp hi
          exact hx (mem_iUnion.mpr ⟨i,hxi⟩)
        change (⋃ i ∈ Finset.range j, Z i).indicator b x = (⋃ i, Z i).indicator b x
        rw [indicator_of_notMem hx,indicator_of_notMem hxj]
  have hbound j x : |f j x-g x| ≤ |b x|+|b x| := by
    exact (abs_sub _ _).trans (add_le_add (by simpa only [Real.norm_eq_abs] using norm_indicator_le_norm_self (s := _) b x)
      (by simpa only [Real.norm_eq_abs] using norm_indicator_le_norm_self (s := _) b x))
  have hlim : Tendsto (fun j => ∫ x, |f j x-g x| ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (fun x => |b x|+|b x|)
      (fun j => ((hfi j).sub hg).abs.aestronglyMeasurable) (hb.abs.add hb.abs)
      (fun j => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_abs,Pi.sub_apply] using hbound j x)
      (Eventually.of_forall fun x =>
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
          ((hlimx x).mono fun j hj => by change 0 = |f j x-g x|; rw [hj,sub_self,abs_zero]))
    simpa only [integral_zero,Pi.sub_apply] using ht
  have ht := borelAction_tendsto μ hT hμ hg hfi hlim π hπ
  have htsum : Summable (fun i => borelAction μ hT ((Z i).indicator b) π) := by
    choose K hK using hπ
    have hsum : Summable (fun i => ∫ x, |(Z i).indicator b x| ∂μ) := by
      have hmeas : (Measure.sum (fun i => μ.restrict (Z i))) = μ.restrict (⋃ i, Z i) :=
        (Measure.restrict_iUnion hd hZ).symm
      have hI : Integrable (fun x => |b x|) (Measure.sum (fun i => μ.restrict (Z i))) := by
        rw [hmeas]
        exact hb.abs.restrict
      convert hI.summable_integral using 1
      all_goals try with_reducible_and_instances rfl
      ext i
      rw [←integral_indicator (hZ i)]
      exact integral_congr_ae (Eventually.of_forall fun x => by
        by_cases hx : x ∈ Z i <;> simp [hx])
    apply (hsum.mul_left (∏ i, (K i : ℝ))).of_norm_bounded
    exact fun i => borelAction_bound μ hT hμ (hb.indicator (hZ i)) π K hK
  apply (hasSum_iff_tendsto_nat_of_summable_norm htsum.norm).mpr
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  rw [heq,borelAction_finset_sum μ hT _ (fun i => hb.indicator (hZ i)) π hπ]

end BorelCoefficients
end CAT0Fillings
namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology

namespace BorelRestriction
open BorelCoefficients MassMeasure

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k}

lemma restrictCurrent_iUnion (hT : IsMetricCurrent T)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) (b : X → ℝ) (π : Fin k → X → ℝ) :
    restrictCurrent hT (⋃ i, Z i) b π = ∑' i, restrictCurrent hT (Z i) b π := by
  by_cases hab : Admissible b π
  · simp_rw [restrictCurrent_apply hT _ hab]
    exact (borelAction_iUnion (currentMassMeasure hT) hT (currentMassMeasure_controls hT)
      Z hZ hd (integrable_boundedLip _ hab.1) π hab.2).tsum_eq.symm
  · rw [(restrictCurrent_isMetricCurrent hT (MeasurableSet.iUnion hZ)).offDomain b π hab]
    symm
    calc (∑' i, restrictCurrent hT (Z i) b π) = ∑' (_i : ℕ), (0 : ℝ) :=
            tsum_congr fun i => (restrictCurrent_isMetricCurrent hT (hZ i)).offDomain b π hab
      _ = 0 := tsum_zero

lemma summable_restriction_mass (hT : IsMetricCurrent T)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) :
    Summable (fun i => mass (restrictCurrent hT (Z i))) := by
  simp_rw [restriction_mass hT (hZ _)]
  exact summable_measure_toReal hZ hd

lemma tsum_restriction_mass_le (hT : IsMetricCurrent T)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) :
    (∑' i, mass (restrictCurrent hT (Z i))) ≤ mass T := by
  simp_rw [restriction_mass hT (hZ _),Measure.real]
  rw [← ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _),←measure_iUnion hd hZ]
  change (currentMassMeasure hT).real (⋃ i, Z i) ≤ mass T
  rw [←currentMassMeasure_total hT]
  exact measureReal_mono (subset_univ _)

end BorelRestriction
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ChartSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter BorelCoefficients BorelRestriction MassMeasure
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
lemma restrictCurrent_sum {T : Functional X k} {S : ℕ → Functional X k}
    (hT : IsMetricCurrent T) (hS : ∀ i, IsMetricCurrent (S i))
    (hsum : Summable (fun i => mass (S i)))
    (heq : ∀ b π, T b π = ∑' i, S i b π) {E : Set X} (hE : MeasurableSet E)
    (b : X → ℝ) (π : Fin k → X → ℝ) :
    restrictCurrent hT E b π = ∑' i, restrictCurrent (hS i) E b π := by
  let μ (i) := currentMassMeasure (hS i)
  have hμfin : ∀ i, IsFiniteMeasure (μ i) := fun i => inferInstance
  let := hμfin
  have hμsum : Summable (fun i => (μ i).real univ) := by
    simpa only [μ,currentMassMeasure_total] using hsum
  let := finite_sum_measure_of_summable_total μ hμsum
  have hμ (i) : Controls (S i) (μ i) := currentMassMeasure_controls (hS i)
  by_cases hab : Admissible b π
  · rw [restrictCurrent_apply hT E hab,
      borelAction_independent (currentMassMeasure hT) hT
        (currentMassMeasure_controls hT) (controls_sum hμ heq)
        ((integrable_boundedLip _ hab.1).indicator hE)
        ((integrable_boundedLip _ hab.1).indicator hE) π hab.2,
      borelAction_sum μ hT hS hμ heq
        ((integrable_boundedLip _ hab.1).indicator hE) π hab.2]
    exact tsum_congr fun i => (restrictCurrent_apply (hS i) E hab).symm
  · rw [(restrictCurrent_isMetricCurrent hT hE).offDomain b π hab]
    symm
    calc (∑' i, restrictCurrent (hS i) E b π) = ∑' (_i : ℕ), (0 : ℝ) :=
            tsum_congr fun i => (restrictCurrent_isMetricCurrent (hS i) hE).offDomain b π hab
      _ = 0 := tsum_zero

theorem integerRectifiable_chartSum [Nonempty X] (C : ℕ → IntegerChart X k)
    (hC : ∀ i, IsMetricCurrent (C i).action)
    (hsum : Summable (fun i => mass (C i).action)) :
    IntegerRectifiable (fun b π => ∑' i, (C i).action b π) := by
  let T : Functional X k := fun b π => ∑' i, (C i).action b π
  have hT : IsMetricCurrent T := isMetricCurrent_tsum hC hsum
  let Z : ℕ → Set X := disjointed (fun i => (C i).image)
  have hZ i : MeasurableSet (Z i) := MeasurableSet.disjointed (fun i => (C i).measurableSet_image) i
  have hd : Pairwise (fun i j => Disjoint (Z i) (Z j)) := disjoint_disjointed _
  have hZi i : Z i ⊆ (C i).image := disjointed_subset _ i
  have hZunion : (⋃ i, Z i) = ⋃ i, (C i).image := iUnion_disjointed
  let D i := (C i).restrictImage (Z i) (hZ i)
  have hDim i : (D i).image = Z i := by
    rw [IntegerChart.restrictImage_image,inter_eq_right.mpr (hZi i)]
  let F i j := (C j).restrictImage (Z i) (hZ i)
  have hF i j : IsMetricCurrent (F i j).action := (C j).restrictImage_isMetricCurrent _ _ (hC j)
  have hFS i : Summable (fun j => mass (F i j).action) :=
    hsum.of_nonneg_of_le (fun j => mass_nonneg _) (fun j => (C j).restrictImage_mass_le _ _ (hC j))
  have hFD i j : (F i j).image ⊆ (D i).image := by
    rw [hDim,IntegerChart.restrictImage_image]
    exact inter_subset_right
  choose E hEim hEact using fun i => IntegerChart.exists_overlap_sum (D i) (F i) (hFD i) (hF i) (hFS i)
  have hEeq i : (E i).action = restrictCurrent hT (Z i) := by
    funext b π
    rw [hEact,restrictCurrent_sum hT hC hsum (fun _ _ => rfl) (hZ i)]
    apply tsum_congr
    intro j
    exact congrFun (congrFun ((C j).restrictImage_action _ _ (hC j)) b) π
  have hEcurrent i : IsMetricCurrent (E i).action := by
    rw [hEeq]
    exact restrictCurrent_isMetricCurrent hT (hZ i)
  refine ⟨E,?_,hEcurrent,?_,?_⟩
  · intro i j hij
    simpa only [hEim,hDim] using hd hij
  · simp_rw [hEeq]
    exact summable_restriction_mass hT Z hZ hd
  · intro b π
    simp_rw [hEeq]
    rw [←restrictCurrent_iUnion hT Z hZ hd,hZunion,
      restrictCurrent_sum hT hC hsum (fun _ _ => rfl)
        (MeasurableSet.iUnion fun i => (C i).measurableSet_image)]
    apply tsum_congr
    intro i
    rw [(C i).restrictCurrent_image_eq (hC i)
      (MeasurableSet.iUnion fun i => (C i).measurableSet_image) (subset_iUnion (fun i => (C i).image) i)]

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter BorelRestriction MassMeasure
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}

lemma IntegerChart.restrictCurrent_disjoint_eq_zero (C : IntegerChart X k)
    (hC : IsMetricCurrent C.action) {E : Set X} (hE : MeasurableSet E)
    (hd : Disjoint C.image E) : restrictCurrent hC E = 0 := by
  classical
  rw [←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hab : Admissible b π
  · simp only [IntegerChart.action,ite_eq_left hab,Pi.zero_apply]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem C.borel] with z hz
    change z ∈ C.domain at hz
    have hi : C.paramExtended z ∉ E := by
      apply Set.disjoint_left.mp hd
      exact ⟨⟨z,hz⟩,by simp only [IntegerChart.paramExtended,dite_eq_left hz]⟩
    change ↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) * C.scalar b z * C.jacobian π z = 0
    rw [indicator_of_notMem (show z ∉ C.paramExtended ⁻¹' E from hi),Int.cast_zero,zero_mul,zero_mul]
  · simp only [IntegerChart.action,ite_eq_right hab,Pi.zero_apply]

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Straightening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace EuclideanStraightening
variable {d : ℕ}
noncomputable def replaceMap (j : Fin d) (g : Euc d → ℝ) (z : Euc d) : Euc d :=
  z + (g z-z j) • EuclideanSpace.single j 1

@[simp] lemma replaceMap_apply (j : Fin d) (g : Euc d → ℝ) (z : Euc d) (i : Fin d) :
    replaceMap j g z i = if i=j then g z else z i := by
  simp only [replaceMap,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,
    smul_eq_mul,mul_ite,mul_one,mul_zero]
  split_ifs with hi
  · subst i; ring
  · ring

noncomputable def switchZero {k : ℕ} (j : Fin (k+1)) : Euc (k+1) ≃ₗᵢ[ℝ] Euc (k+1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 j)

@[simp] lemma switchZero_apply_zero {k : ℕ} (j : Fin (k+1)) (z : Euc (k+1)) :
    switchZero j z 0 = z j := by
  simp [switchZero,Equiv.piCongrLeft']

noncomputable def straightenMap {k : ℕ} (j : Fin (k+1)) (g : Euc (k+1) → ℝ) :
    Euc (k+1) → Euc (k+1) := switchZero j ∘ replaceMap j g

@[simp] lemma straightenMap_zero {k : ℕ} (j : Fin (k+1)) (g : Euc (k+1) → ℝ) (z : Euc (k+1)) :
    straightenMap j g z 0 = g z := by simp [straightenMap]

end EuclideanStraightening
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_RectifiableCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter BorelRestriction MassMeasure
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}
lemma chartFamily_restrict_eq {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hC : ∀ i, IsMetricCurrent (C i).action)
    (hsum : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π) (i : ℕ) :
    restrictCurrent hT (C i).image = (C i).action := by
  funext b π
  rw [restrictCurrent_sum hT hC hsum heq (C i).measurableSet_image,
    tsum_eq_single i (fun j hj => by
      rw [(C j).restrictCurrent_disjoint_eq_zero (hC j) (C i).measurableSet_image (hd hj)]
      rfl),
    (C i).restrictCurrent_image_eq (hC i) (C i).measurableSet_image (subset_refl _)]

lemma chartFamily_mass_sum_le {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hC : ∀ i, IsMetricCurrent (C i).action)
    (hsum : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π) :
    (∑' i, mass (C i).action) ≤ mass T := by
  have hr i := chartFamily_restrict_eq hT C hd hC hsum heq i
  simpa only [hr] using tsum_restriction_mass_le hT (fun i => (C i).image)
    (fun i => (C i).measurableSet_image) hd

theorem integerRectifiable_tsum {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hI : ∀ i, IntegerRectifiable (T i))
    (hsum : Summable (fun i => mass (T i))) :
    IntegerRectifiable (fun b π => ∑' i, T i b π) := by
  choose C hd hC hCS heq using hI
  have hmass i := chartFamily_mass_sum_le (hT i) (C i) (hd i) (hC i) (hCS i) (heq i)
  have hpair : Summable (fun p : ℕ × ℕ => mass (C p.1 p.2).action) := by
    apply (summable_prod_of_nonneg (fun p => mass_nonneg _)).mpr
    exact ⟨hCS,hsum.of_nonneg_of_le (fun i => tsum_nonneg (fun j => mass_nonneg _)) hmass⟩
  let D (i : ℕ) := C (Nat.pairEquiv.symm i).1 (Nat.pairEquiv.symm i).2
  have hD i : IsMetricCurrent (D i).action := hC _ _
  have hDS : Summable (fun i => mass (D i).action) := (Nat.pairEquiv.symm.summable_iff (f := fun p : ℕ × ℕ => mass (C p.1 p.2).action)).mpr hpair
  have heq' : (fun b π => ∑' i, T i b π) = (fun b π => ∑' i, (D i).action b π) := by
    funext b π
    have hact : Summable (fun p : ℕ × ℕ => (C p.1 p.2).action b π) :=
      (Nat.pairEquiv.symm.summable_iff (f := fun p : ℕ × ℕ => (C p.1 p.2).action b π)).mp (summable_actions_all hD hDS b π)
    change (∑' i, T i b π) = ∑' i, (C (Nat.pairEquiv.symm i).1 (Nat.pairEquiv.symm i).2).action b π
    calc
      (∑' i, T i b π) = ∑' i, ∑' j, (C i j).action b π := tsum_congr (fun i => heq i b π)
      _ = ∑' p : ℕ × ℕ, (C p.1 p.2).action b π := hact.tsum_prod.symm
      _ = _ := (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => (C p.1 p.2).action b π)).symm
  rw [heq']
  exact integerRectifiable_chartSum D hD hDS

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_BorelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.BorelCoefficients
open Foundations MassMeasure

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma integrable_bounded_measurable {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)

lemma borelAction_tendsto_of_bounded_pointwise {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {f : X → ℝ} {fs : ℕ → X → ℝ}
    (hf : Measurable f) (hfs : ∀ j, Measurable (fs j))
    (B : ℝ) (hB : ∀ j x, |fs j x| ≤ B)
    (hlim : ∀ x, Tendsto (fun j => fs j x) atTop (𝓝 (f x)))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Tendsto (fun j => borelAction μ hT (fs j) π) atTop (𝓝 (borelAction μ hT f π)) := by
  have hfB (x : X) : |f x| ≤ B := le_of_tendsto' (hlim x).abs (fun j => hB j x)
  have hfI := integrable_bounded_measurable μ hf hfB
  have hfsI j := integrable_bounded_measurable μ (hfs j) (hB j)
  have hL : Tendsto (fun j => ∫ x, |fs j x - f x| ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ : X => (0 : ℝ)) (fun _ : X => B+B)
      (fun j => ((hfs j).sub hf).abs.aestronglyMeasurable) (integrable_const (B+B))
      (fun j => Eventually.of_forall fun x => show ‖|fs j x - f x|‖ ≤ B+B by
        simpa only [Real.norm_eq_abs,abs_abs] using (abs_sub (fs j x) (f x)).trans
          (add_le_add (hB j x) (hfB x)))
      (Eventually.of_forall fun x => by simpa only [Pi.sub_apply, sub_self,abs_zero] using
        ((hlim x).sub_const (f x)).abs)
    simpa only [integral_zero, Pi.sub_apply] using hh
  exact borelAction_tendsto μ hT hμ hfI hfsI hL π hπ

noncomputable def currentBorelAction {k : ℕ} (T : Functional X k)
    (f : X → ℝ) (π : Fin k → X → ℝ) : ℝ :=
  if hT : IsMetricCurrent T then borelAction (currentMassMeasure hT) hT f π else 0

lemma currentBorelAction_eq {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (f : X → ℝ) (π : Fin k → X → ℝ) :
    currentBorelAction T f π = borelAction (currentMassMeasure hT) hT f π := by
  simp only [currentBorelAction,dite_eq_left hT]

lemma currentBorelAction_eq_action {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {f : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible f π) :
    currentBorelAction T f π = T f π := by
  rw [currentBorelAction_eq hT]
  exact borelAction_eq _ hT (currentMassMeasure_controls hT) h

lemma currentBorelAction_bound {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |currentBorelAction T f π| ≤ (∏ i, (K i : ℝ)) * B * mass T := by
  rw [currentBorelAction_eq hT]
  calc
    _ ≤ (∏ i, (K i : ℝ)) * ∫ x, |f x| ∂currentMassMeasure hT :=
      borelAction_bound _ hT (currentMassMeasure_controls hT)
        (integrable_bounded_measurable _ hf hB) π K hK
    _ ≤ (∏ i, (K i : ℝ)) * ∫ _ : X, B ∂currentMassMeasure hT :=
      mul_le_mul_of_nonneg_left (integral_mono
        (integrable_bounded_measurable _ hf hB).abs (integrable_const B) hB) (by positivity)
    _ = _ := by rw [integral_const,smul_eq_mul,currentMassMeasure_total hT]; ring

lemma currentBorelAction_tendsto {k : ℕ} (T : Functional X k)
    {f : X → ℝ} {fs : ℕ → X → ℝ}
    (hf : Measurable f) (hfs : ∀ j, Measurable (fs j))
    (B : ℝ) (hB : ∀ j x, |fs j x| ≤ B)
    (hlim : ∀ x, Tendsto (fun j => fs j x) atTop (𝓝 (f x)))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Tendsto (fun j => currentBorelAction T (fs j) π) atTop
      (𝓝 (currentBorelAction T f π)) := by
  by_cases hT : IsMetricCurrent T
  · simp only [currentBorelAction_eq hT]
    exact borelAction_tendsto_of_bounded_pointwise hT _ (currentMassMeasure_controls hT)
      hf hfs B hB hlim π hπ
  · simp only [currentBorelAction,dite_eq_right hT]
    exact tendsto_const_nhds

lemma currentBorelAction_add {k : ℕ} (T : Functional X k)
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    currentBorelAction T (f+g) π = currentBorelAction T f π + currentBorelAction T g π := by
  by_cases hT : IsMetricCurrent T
  · simp only [currentBorelAction_eq hT]
    exact borelAction_add _ hT (integrable_bounded_measurable _ hf hB)
      (integrable_bounded_measurable _ hg hC) π hπ
  · simp [currentBorelAction, hT]

lemma currentBorelAction_sub {k : ℕ} (T : Functional X k)
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    currentBorelAction T (f-g) π = currentBorelAction T f π - currentBorelAction T g π := by
  by_cases hT : IsMetricCurrent T
  · simp only [currentBorelAction_eq hT]
    exact borelAction_sub _ hT (integrable_bounded_measurable _ hf hB)
      (integrable_bounded_measurable _ hg hC) π hπ
  · simp [currentBorelAction, hT]

lemma currentBorelAction_smul {k : ℕ} (T : Functional X k)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (c : ℝ) (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    currentBorelAction T (c • f) π = c * currentBorelAction T f π := by
  by_cases hT : IsMetricCurrent T
  · simp only [currentBorelAction_eq hT]
    exact borelAction_smul _ hT (integrable_bounded_measurable _ hf hB) π c hπ
  · simp [currentBorelAction, hT]

lemma exists_lipschitz_closed_indicator_approximation {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] (E : Set X) (hE : IsClosed E) :
    ∃ fs : ℕ → X → ℝ, (∀ j, BoundedLip (fs j)) ∧
      (∀ j x, |fs j x| ≤ 1) ∧
      (∀ x, Tendsto (fun j => fs j x) atTop (𝓝 (E.indicator (fun _ => (1 : ℝ)) x))) := by
  classical
  by_cases hne : E.Nonempty
  · let fs (j : ℕ) (x : X) : ℝ := max 0 (1 - (j+1 : ℝ) * Metric.infDist x E)
    have hLip (j : ℕ) : LipschitzWith (j+1 : ℝ≥0) (fs j) := by
      apply LipschitzWith.const_max _ 0
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (1-(j+1 : ℝ)*Metric.infDist x E) (1-(j+1 : ℝ)*Metric.infDist y E) ≤
        ((j : ℝ)+1)*dist x y
      calc
        _ = ((j : ℝ)+1)*|Metric.infDist x E-Metric.infDist y E| := by
          rw [Real.dist_eq, show (1-(j+1 : ℝ)*Metric.infDist x E) -
            (1-(j+1 : ℝ)*Metric.infDist y E) = -((j+1 : ℝ)*(Metric.infDist x E-Metric.infDist y E)) by ring,
            abs_neg,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ j+1)]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((Metric.lipschitz_infDist_pt E).dist_le_mul x y) (by positivity) |>.trans_eq (by simp)
    have hb (j : ℕ) (x : X) : |fs j x| ≤ 1 := by
      rw [abs_of_nonneg (le_max_left _ _)]
      apply max_le (by norm_num)
      have := Metric.infDist_nonneg (s := E) (x := x)
      have : 0 ≤ (j+1 : ℝ)*Metric.infDist x E := mul_nonneg (by positivity) this
      linarith
    refine ⟨fs,fun j => ⟨⟨j+1,hLip j⟩,1,hb j⟩,hb,fun x => ?_⟩
    by_cases hx : x ∈ E
    · simp [fs,Metric.infDist_zero_of_mem hx,hx]
    · have hd : 0 < Metric.infDist x E := (hE.notMem_iff_infDist_pos hne).mp hx
      obtain ⟨N,hN⟩ := exists_nat_gt (1 / Metric.infDist x E)
      have hN' : 1 < (N : ℝ)*Metric.infDist x E := (div_lt_iff₀ hd).mp hN
      have hev : ∀ᶠ j : ℕ in atTop, fs j x = 0 := by
        filter_upwards [eventually_ge_atTop N] with j hj
        have hj' : (N : ℝ) ≤ j+1 := by exact_mod_cast (Nat.le_succ_of_le hj)
        have hd' := mul_le_mul_of_nonneg_right hj' hd.le
        exact max_eq_left (by linarith)
      simpa only [indicator_of_notMem hx] using
        (tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm) : Tendsto (fun j => fs j x) atTop (𝓝 (0 : ℝ)))
  · have he : E = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ _ => 0, fun _ => BoundedLip.const 0, fun _ _ => by norm_num, fun x => ?_⟩
    simp [he]

section Integrated
variable {A : Type*} [MeasurableSpace A] (ν : Measure A)
variable {k l : ℕ} (T : Functional X k) (ρ : Fin k → X → ℝ)
  (S : A → Functional X l) (π : Fin l → X → ℝ)

def ActionIntegralAgreement (f : X → ℝ) : Prop :=
  Integrable (fun a => currentBorelAction (S a) f π) ν ∧
    currentBorelAction T f ρ = ∫ a, currentBorelAction (S a) f π ∂ν

variable {ν T ρ S π}
lemma ActionIntegralAgreement.of_bounded_pointwise
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hS : ∀ᵐ a ∂ν, IsMetricCurrent (S a))
    {g : A → ℝ} (hg : Integrable g ν) (hg0 : ∀ᵐ a ∂ν, 0 ≤ g a)
    (hgb : ∀ᵐ a ∂ν, mass (S a) ≤ g a)
    {f : X → ℝ} {fs : ℕ → X → ℝ}
    (hf : Measurable f) (hfs : ∀ j, Measurable (fs j))
    (B : ℝ≥0) (hB : ∀ j x, |fs j x| ≤ B)
    (hlim : ∀ x, Tendsto (fun j => fs j x) atTop (𝓝 (f x)))
    (hA : ∀ j, ActionIntegralAgreement ν T ρ S π (fs j)) :
    ActionIntegralAgreement ν T ρ S π f := by
  choose K hK using hπ
  let C : ℝ := (∏ i, (K i : ℝ)) * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdom (j : ℕ) : ∀ᵐ a ∂ν, ‖currentBorelAction (S a) (fs j) π‖ ≤ C*g a := by
    filter_upwards [hS,hgb,hg0] with a ha hb hg_nonneg
    simpa only [Real.norm_eq_abs,C,mul_assoc] using
      (currentBorelAction_bound ha (hfs j) (hB j) π K hK).trans
        (mul_le_mul_of_nonneg le_rfl hb hC hg_nonneg)
  have hconv (a : A) := currentBorelAction_tendsto (S a) hf hfs B hB hlim π (fun i => ⟨K i,hK i⟩)
  have hfi : Integrable (fun a => currentBorelAction (S a) f π) ν :=
    (hg.const_mul C).mono'
      (aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hA j).1.aestronglyMeasurable)
        (Eventually.of_forall hconv)) (by
          filter_upwards [ae_all_iff.mpr hdom] with a ha
          exact le_of_tendsto' (hconv a).norm ha)
  have hright := tendsto_integral_of_dominated_convergence (fun a => C*g a)
    (fun j => (hA j).1.aestronglyMeasurable) (hg.const_mul C) hdom
    (Eventually.of_forall hconv)
  have hleft := currentBorelAction_tendsto T hf hfs B hB hlim ρ hρ
  exact ⟨hfi,tendsto_nhds_unique (hleft.congr fun j => (hA j).2) hright⟩

lemma ActionIntegralAgreement.add
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (hAf : ActionIntegralAgreement ν T ρ S π f)
    (hAg : ActionIntegralAgreement ν T ρ S π g) :
    ActionIntegralAgreement ν T ρ S π (f+g) := by
  constructor
  · exact (hAf.1.add hAg.1).congr (Eventually.of_forall fun a =>
      (currentBorelAction_add (S a) hf hg hB hC _ hπ).symm)
  · simp only [currentBorelAction_add T hf hg hB hC _ hρ,
      currentBorelAction_add _ hf hg hB hC _ hπ]
    rw [integral_add hAf.1 hAg.1,hAf.2,hAg.2]

lemma ActionIntegralAgreement.sub
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (hAf : ActionIntegralAgreement ν T ρ S π f)
    (hAg : ActionIntegralAgreement ν T ρ S π g) :
    ActionIntegralAgreement ν T ρ S π (f-g) := by
  constructor
  · exact (hAf.1.sub hAg.1).congr (Eventually.of_forall fun a =>
      (currentBorelAction_sub (S a) hf hg hB hC _ hπ).symm)
  · simp only [currentBorelAction_sub T hf hg hB hC _ hρ,
      currentBorelAction_sub _ hf hg hB hC _ hπ]
    rw [integral_sub hAf.1 hAg.1,hAf.2,hAg.2]

lemma ActionIntegralAgreement.smul
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hA : ActionIntegralAgreement ν T ρ S π f) (c : ℝ) :
    ActionIntegralAgreement ν T ρ S π (c • f) := by
  constructor
  · exact (hA.1.const_mul c).congr (Eventually.of_forall fun a =>
      (currentBorelAction_smul (S a) hf hB c _ hπ).symm)
  · simp only [currentBorelAction_smul T hf hB c _ hρ,
      currentBorelAction_smul _ hf hB c _ hπ,integral_const_mul,hA.2]

theorem ActionIntegralAgreement.indicator
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hS : ∀ᵐ a ∂ν, IsMetricCurrent (S a))
    {g : A → ℝ} (hg : Integrable g ν) (hg0 : ∀ᵐ a ∂ν, 0 ≤ g a)
    (hgb : ∀ᵐ a ∂ν, mass (S a) ≤ g a)
    (hLip : ∀ f : X → ℝ, BoundedLip f → ActionIntegralAgreement ν T ρ S π f)
    (E : Set X) (hE : MeasurableSet E) :
    ActionIntegralAgreement ν T ρ S π (E.indicator (fun _ => (1 : ℝ))) := by
  classical
  have hb (E : Set X) (x : X) : |E.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ E <;> simp [hx]
  have hcompl (E : Set X) (he : MeasurableSet E)
      (ha : ActionIntegralAgreement ν T ρ S π (E.indicator (fun _ => (1 : ℝ)))) :
      ActionIntegralAgreement ν T ρ S π (Eᶜ.indicator (fun _ => (1 : ℝ))) := by
    rw [indicator_compl]
    exact ActionIntegralAgreement.sub hρ hπ measurable_const
      (measurable_const.indicator he) (fun _ => le_rfl) (hb E)
      (hLip _ (BoundedLip.const 1)) ha
  have hclosed (F : Set X) (hF : IsClosed F) :
      ActionIntegralAgreement ν T ρ S π (F.indicator (fun _ => (1 : ℝ))) := by
    obtain ⟨fs,hf,hfb,hflim⟩ := exists_lipschitz_closed_indicator_approximation F hF
    exact ActionIntegralAgreement.of_bounded_pointwise hρ hπ hS hg hg0 hgb
      (measurable_const.indicator hF.measurableSet) (fun j => (hf j).continuous.measurable)
      1 hfb hflim (fun j => hLip _ (hf j))
  apply MeasurableSet.induction_on_open (C := fun F _ =>
    ActionIntegralAgreement ν T ρ S π (F.indicator (fun _ => (1 : ℝ)))) ?_ hcompl ?_ E hE
  · intro U hU
    simpa only [compl_compl] using hcompl Uᶜ hU.measurableSet.compl (hclosed Uᶜ hU.isClosed_compl)
  · intro f hdisj hf hA
    let F (m : ℕ) : Set X := ⋃ i ∈ (Finset.range m : Set ℕ), f i
    have hFmeas (m : ℕ) : MeasurableSet (F m) :=
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hf i
    have hmono : Monotone F := by
      intro m n hmn
      exact iUnion₂_mono' fun i hi => ⟨i, Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hmn), subset_rfl⟩
    have hFam (m : ℕ) : ActionIntegralAgreement ν T ρ S π (F m |>.indicator (fun _ => (1 : ℝ))) := by
      induction m with
      | zero => simpa [F] using hLip (fun _ => 0) (BoundedLip.const 0)
      | succ m ih =>
        have hFm : F (m+1) = f m ∪ F m := by
          simp only [F,Finset.range_add_one,Finset.coe_insert,biUnion_insert]
        have hd : Disjoint (f m) (F m) := by
          apply disjoint_iUnion_right.mpr
          intro j
          apply disjoint_iUnion_right.mpr
          intro hj
          exact hdisj (ne_of_gt (Finset.mem_range.mp hj))
        rw [hFm,indicator_union_of_disjoint hd]
        exact ActionIntegralAgreement.add hρ hπ (measurable_const.indicator (hf m))
          (measurable_const.indicator (hFmeas m)) (hb (f m)) (hb (F m)) (hA m) ih
    have hUnion : (⋃ m, F m) = ⋃ i, f i := by
      ext x
      simp only [F,mem_iUnion,Finset.mem_coe,Finset.mem_range]
      constructor
      · rintro ⟨m,i,hi,hx⟩
        exact ⟨i,hx⟩
      · rintro ⟨i,hx⟩
        exact ⟨i+1,i,Nat.lt_succ_self i,hx⟩
    apply ActionIntegralAgreement.of_bounded_pointwise hρ hπ hS hg hg0 hgb
      (measurable_const.indicator (MeasurableSet.iUnion hf))
      (fun m => measurable_const.indicator (hFmeas m)) 1 (fun m => hb (F m)) ?_ hFam
    intro x
    have hh := (hmono.tendsto_indicator F (fun _ => (1 : ℝ)) x).mono_right (pure_le_nhds _)
    simpa only [hUnion] using hh

theorem ActionIntegralAgreement.bounded_measurable
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hS : ∀ᵐ a ∂ν, IsMetricCurrent (S a))
    {g : A → ℝ} (hg : Integrable g ν) (hg0 : ∀ᵐ a ∂ν, 0 ≤ g a)
    (hgb : ∀ᵐ a ∂ν, mass (S a) ≤ g a)
    (hLip : ∀ f : X → ℝ, BoundedLip f → ActionIntegralAgreement ν T ρ S π f)
    {f : X → ℝ} (hf : Measurable f) (B : ℝ≥0) (hB : ∀ x, |f x| ≤ B) :
    ActionIntegralAgreement ν T ρ S π f := by
  classical
  have hsimp : ∀ s : SimpleFunc X ℝ, ActionIntegralAgreement ν T ρ S π s := by
    intro s
    induction s using SimpleFunc.induction with
    | @const c E hE =>
      have hbase := ActionIntegralAgreement.indicator hρ hπ hS hg hg0 hgb hLip E hE
      have hb (x : X) : |E.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
        by_cases hx : x ∈ E <;> simp [hx]
      have hc := ActionIntegralAgreement.smul hρ hπ (measurable_const.indicator hE) hb hbase c
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    | @add s t hd hs ht =>
      obtain ⟨C,hC⟩ := (s.finite_range.image abs).bddAbove
      obtain ⟨D,hD⟩ := (t.finite_range.image abs).bddAbove
      exact ActionIntegralAgreement.add hρ hπ s.measurable t.measurable
        (fun x => hC (mem_image_of_mem _ (mem_range_self x)))
        (fun x => hD (mem_image_of_mem _ (mem_range_self x))) hs ht
  let E : Set ℝ := Icc (-(B : ℝ)) (B : ℝ)
  have h0 : (0 : ℝ) ∈ E := ⟨neg_nonpos.mpr B.coe_nonneg,B.coe_nonneg⟩
  let fs (j : ℕ) := SimpleFunc.approxOn f hf E 0 h0 j
  have hfs (j : ℕ) (x : X) : |fs j x| ≤ B := by
    exact abs_le.mpr (SimpleFunc.approxOn_mem hf h0 j x)
  apply ActionIntegralAgreement.of_bounded_pointwise hρ hπ hS hg hg0 hgb hf
    (fun j => (fs j).measurable) B hfs ?_ (fun j => hsimp (fs j))
  intro x
  exact SimpleFunc.tendsto_approxOn hf h0 (subset_closure (abs_le.mp (hB x)))

end Integrated

end CAT0Fillings.BorelCoefficients
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Negation
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
omit [BorelSpace X] in
lemma controls_neg_iff {T : Functional X k} {μ : Measure X} :
    Controls (-T) μ ↔ Controls T μ := by
  simp only [Controls,Pi.neg_apply,abs_neg]

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_BoundaryTests
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings.Foundations
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
omit [BorelSpace X] in
lemma IsMetricCurrent.boundary_testClass_continuous {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (K : ℕ) :
    Continuous (TestClass.eval (X := X) (K := K) (boundarySucc T)) := by
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have had (q : TestClass (X := X) k K) : Admissible (q.val.1 : X → ℝ) (fun i => q.val.2 i) :=
    ⟨q.boundedLip,fun i => ⟨K,q.property.2.2 i⟩⟩
  simp only [Function.comp_def,TestClass.eval,boundarySucc,ite_eq_left (had _)]
  apply hT.sequentialContinuity _ _ _ (BoundedLip.const 1)
  · intro i
    exact ⟨K,fun n => Fin.cases (ps n).property.1 (fun j => (ps n).property.2.2 j) i⟩
  · intro i x
    refine Fin.cases ?_ (fun j => ?_) i
    · have hc : Continuous (fun q : TestClass (X := X) k K => q.val.1 x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp
    · have hc : Continuous (fun q : TestClass (X := X) k K => q.val.2 j x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp

theorem ae_boundary_eq_of_ae_test_eq {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {S : A → Functional X (k+1)} {T : A → Functional X k}
    (hS : ∀ᵐ a ∂μ, IsMetricCurrent (S a)) (hT : ∀ᵐ a ∂μ, IsMetricCurrent (T a))
    (he : ∀ b π, Admissible b π → ∀ᵐ a ∂μ, boundarySucc (S a) b π = T a b π) :
    ∀ᵐ a ∂μ, boundarySucc (S a) = T a := by
  choose p hp using fun K : ℕ => TopologicalSpace.exists_dense_seq (TestClass (X := X) k K)
  have ha K j : Admissible ((p K j).val.1 : X → ℝ) (fun i => (p K j).val.2 i) :=
    ⟨(p K j).boundedLip,fun i => ⟨K,(p K j).property.2.2 i⟩⟩
  have hc : ∀ᵐ a ∂μ, ∀ K j, TestClass.eval (boundarySucc (S a)) (p K j) = TestClass.eval (T a) (p K j) :=
    ae_all_iff.mpr fun K => ae_all_iff.mpr fun j => he _ _ (ha K j)
  filter_upwards [hS,hT,hc] with a hs ht h
  have hh K : TestClass.eval (K := K) (boundarySucc (S a)) = TestClass.eval (K := K) (T a) := by
    apply (hp K).equalizer (IsMetricCurrent.boundary_testClass_continuous hs K) (IsMetricCurrent.testClass_continuous ht K)
    funext j; exact h K j
  funext b π
  by_cases hab : Admissible b π
  · obtain ⟨K,q,hb,hπ⟩ := admissible_mem_testClass hab
    have hz := congrFun (hh K) q
    simpa only [TestClass.eval,hb,hπ] using hz
  · rw [ht.offDomain b π hab,boundarySucc,ite_eq_right hab]

end CAT0Fillings.Foundations
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_BoundaryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter

lemma vecCons_update_head {α : Type*} {k : ℕ} (b f : α) (π : Fin k → α) :
    Function.update (Matrix.vecCons b π) 0 f = Matrix.vecCons f π := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp


open Set MeasureTheory Filter

attribute [local instance] Classical.propDecidable

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Contraction
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {k : ℕ}
noncomputable def contractCurrent (u : X → ℝ) (T : Functional X (k+1)) : Functional X k :=
  fun b π => if Admissible b π then T b (Matrix.vecCons u π) else 0

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_SmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings.SmoothCutoff
lemma deriv_transition_eq_zero {x : ℝ} (hx : x ∉ Icc (0:ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  have hcases : x < 0 ∨ 1 < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
  rcases hcases with hx | hx
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [heq.deriv_eq]
    simp
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [heq.deriv_eq]
    simp

lemma tsupport_deriv_transition :
    tsupport (deriv Real.smoothTransition) ⊆ Icc (0:ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  exact hx (deriv_transition_eq_zero h)

lemma exists_derivative_bound : ∃ C : ℝ≥0, (∀ x, ‖deriv Real.smoothTransition x‖ ≤ C) ∧
    (∀ x, ‖deriv (deriv Real.smoothTransition) x‖ ≤ C) := by
  have hd : ContDiff ℝ (1:ℕ) (deriv Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff 2).deriv'
  have hc := hd.continuous
  have hc2 := hd.continuous_deriv (by norm_num)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2.continuousOn
  refine ⟨⟨max 0 (max C D),le_max_left _ _⟩,?_,?_⟩
  · intro x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · exact (hC x hx).trans ((le_max_left C D).trans (le_max_right _ _))
    · rw [deriv_transition_eq_zero hx,norm_zero]
      exact le_max_left _ _
  · intro x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · exact (hD x hx).trans ((le_max_right C D).trans (le_max_right _ _))
    · have hz : deriv (deriv Real.smoothTransition) x = 0 := by
        exact deriv_of_notMem_tsupport (fun h => hx (tsupport_deriv_transition h))
      rw [hz,norm_zero]
      exact le_max_left _ _

lemma exists_lipschitz_transition : ∃ C : ℝ≥0, LipschitzWith C Real.smoothTransition ∧
    LipschitzWith C (deriv Real.smoothTransition) ∧
    ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  obtain ⟨C,hC,hD⟩ := exists_derivative_bound
  refine ⟨C,?_,?_,?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le ((@Real.smoothTransition.contDiff 1).differentiable (by norm_num))
    exact fun x => hC x
  · apply lipschitzWith_of_nnnorm_deriv_le ((show ContDiff ℝ (1:ℕ) (deriv Real.smoothTransition) from (@Real.smoothTransition.contDiff 2).deriv').differentiable (by norm_num))
    exact fun x => hD x
  · simpa only [Real.norm_eq_abs] using hC

end CAT0Fillings.SmoothCutoff

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings.SmoothCutoff
open Set Filter
open scoped Topology NNReal

noncomputable def profile (a : ℝ≥0) (t x : ℝ) : ℝ :=
  Real.smoothTransition ((a:ℝ) * (x-t))
noncomputable def dprofile (a : ℝ≥0) (t x : ℝ) : ℝ :=
  (a:ℝ) * deriv Real.smoothTransition ((a:ℝ) * (x-t))

lemma affine_lipschitz (a : ℝ≥0) (t : ℝ) :
    LipschitzWith a (fun x : ℝ => (a:ℝ)*(x-t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,←mul_sub,sub_sub_sub_cancel_right,abs_mul,abs_of_nonneg a.coe_nonneg]
  exact le_rfl

lemma profile_bounds (a : ℝ≥0) (t x : ℝ) :
    0 ≤ profile a t x ∧ profile a t x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma profile_zero (a : ℝ≥0) {t x : ℝ} (hx : x ≤ t) : profile a t x = 0 :=
  Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos a.coe_nonneg (sub_nonpos.mpr hx))

lemma exists_profile_bounds : ∃ C : ℝ≥0, ∀ (a : ℝ≥0) (t : ℝ),
    LipschitzWith (C*a) (profile a t) ∧
    LipschitzWith (a*(C*a)) (dprofile a t) ∧
    ∀ x, |dprofile a t x| ≤ (C*a:ℝ≥0) := by
  obtain ⟨C,hC,hD,hb⟩ := exists_lipschitz_transition
  refine ⟨C,fun a t => ⟨hC.comp (affine_lipschitz a t),?_,?_⟩⟩
  · change LipschitzWith (a*(C*a)) (fun x => (a:ℝ)*deriv Real.smoothTransition ((a:ℝ)*(x-t)))
    simpa only [sub_zero,Function.comp_def] using
      (affine_lipschitz a 0).comp (hD.comp (affine_lipschitz a t))
  · intro x
    simp only [dprofile,abs_mul,abs_of_nonneg a.coe_nonneg,NNReal.coe_mul]
    calc
      (a:ℝ) * |deriv Real.smoothTransition ((a:ℝ)*(x-t))| ≤ (a:ℝ)*C :=
        mul_le_mul_of_nonneg_left (hb _) a.coe_nonneg
      _ = (C:ℝ)*a := mul_comm _ _

lemma profile_sequence_tendsto (t x : ℝ) :
    Tendsto (fun n : ℕ => profile ((n:ℝ≥0)+1) t x) atTop
      (𝓝 ((Ioi t).indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : t < x
  · rw [indicator_of_mem (show x ∈ Ioi t from hx)]
    have hlim : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(x-t)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const (sub_pos.mpr hx)
    have heq : (fun n : ℕ => profile ((n:ℝ≥0)+1) t x) =ᶠ[atTop] fun _ => (1:ℝ) := by
      filter_upwards [hlim.eventually (eventually_ge_atTop 1)] with n hn
      apply Real.smoothTransition.one_of_one_le
      simpa only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hn
    exact tendsto_const_nhds.congr' heq.symm
  · rw [indicator_of_notMem (show x ∉ Ioi t from hx)]
    simpa only [profile_zero _ (le_of_not_gt hx)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end CAT0Fillings.SmoothCutoff
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_NormalRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter BorelCoefficients BorelRestriction MassMeasure SmoothCutoff
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma profile_comp_boundedLip {u : X → ℝ} (hu : BoundedLip u)
    (a : ℝ≥0) (t : ℝ) : BoundedLip (profile a t ∘ u) := by
  obtain ⟨K,hK⟩ := hu.1
  obtain ⟨C,hC⟩ := exists_profile_bounds
  refine ⟨⟨_,(hC a t).1.comp hK⟩,1,fun x => ?_⟩
  change |profile a t (u x)| ≤ 1
  rw [abs_of_nonneg (profile_bounds a t (u x)).1]
  exact (profile_bounds a t (u x)).2

lemma profile_L1_tendsto (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ}
    (hu : BoundedLip u) (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ x, |profile ((n:ℝ≥0)+1) t (u x) -
      ({x | t < u x}.indicator (fun _ => (1:ℝ)) x)| ∂μ) atTop (𝓝 0) := by
  let E : Set X := {x | t < u x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hu.continuous.measurable
  have hI : Integrable (E.indicator (fun _ : X => (1:ℝ))) μ :=
    (integrable_const _).indicator hE
  have hP (n : ℕ) : Integrable (fun x => profile ((n:ℝ≥0)+1) t (u x)) μ :=
    integrable_boundedLip μ (profile_comp_boundedLip hu _ t)
  have hpt (x : X) : Tendsto (fun n : ℕ => profile ((n:ℝ≥0)+1) t (u x)) atTop
      (𝓝 (E.indicator (fun _ => (1:ℝ)) x)) := by
    simpa only [E,indicator_apply,mem_Ioi,mem_ofPred_eq] using profile_sequence_tendsto t (u x)
  have hdom (n : ℕ) : ∀ᵐ x ∂μ,
      ‖|profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x|‖ ≤ (2:ℝ) := by
    filter_upwards [] with x
    have hp := profile_bounds ((n:ℝ≥0)+1) t (u x)
    have hi : 0 ≤ E.indicator (fun _ => (1:ℝ)) x ∧ E.indicator (fun _ => (1:ℝ)) x ≤ 1 := by
      by_cases hx : x ∈ E <;> simp [hx]
    simpa only [Real.norm_eq_abs,abs_abs] using
      (abs_le.mpr (show -2 ≤ profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x ∧
        profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x ≤ 2 from by
          constructor <;> linarith [hp.1,hp.2,hi.1,hi.2]))
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => |profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x|)
    (f := fun _ => (0:ℝ)) (fun _ => (2:ℝ))
    (fun n => ((hP n).sub hI).abs.aestronglyMeasurable) (integrable_const _) hdom
    (Eventually.of_forall fun x => by
      simpa only [sub_self,abs_zero] using ((hpt x).sub (tendsto_const_nhds (x := E.indicator (fun _ => (1:ℝ)) x))).abs)
  simpa only [integral_zero] using h

end CAT0Fillings.Slicing
open Set MeasureTheory Filter
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_GeneralCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter BorelCoefficients SmoothCutoff BorelRestriction MassMeasure
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}

omit [Nonempty X] in
lemma profile_current_tendsto {T : Functional X k} (hT : IsMetricCurrent T)
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
    Tendsto (fun n : ℕ => weightedCurrent (currentMassMeasure hT) hT
      (profile ((n:ℝ≥0)+1) t ∘ u) b π) atTop
      (𝓝 (restrictCurrent hT {x | t < u x} b π)) := by
  let μ := currentMassMeasure hT
  let E := {x | t < u x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hu.continuous.measurable
  obtain ⟨M,hM⟩ := hab.1.2
  let N := max M 0
  have hN : 0 ≤ N := le_max_right _ _
  have hnb : ∀ x, |b x| ≤ N := fun x => (hM x).trans (le_max_left _ _)
  have hlim : Tendsto (fun n : ℕ => ∫ x, |profile ((n:ℝ≥0)+1) t (u x)*b x - E.indicator b x| ∂μ)
      atTop (𝓝 0) := by
    have hbfun (n : ℕ) (x : X) :
      |profile ((n:ℝ≥0)+1) t (u x)*b x - E.indicator b x| ≤
        N * |profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x| := by
      have hi : E.indicator b x = E.indicator (fun _ => (1:ℝ)) x*b x := by
        by_cases hx : x ∈ E <;> simp [hx]
      rw [hi,←sub_mul,abs_mul,mul_comm]
      exact mul_le_mul_of_nonneg_right (hnb x) (abs_nonneg _)
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_)
      (by simpa only [mul_zero] using (profile_L1_tendsto μ hu t).const_mul N)
    rw [←integral_const_mul]
    apply integral_mono
    · exact ((integrable_boundedLip μ ((profile_comp_boundedLip hu _ t).mul hab.1)).sub
        ((integrable_boundedLip μ hab.1).indicator hE)).abs
    · exact (((integrable_boundedLip μ (profile_comp_boundedLip hu _ t)).sub
        ((integrable_const _).indicator hE)).abs).const_mul N
    · exact hbfun n
  simp only [weightedCurrent,restrictCurrent,ite_eq_left hab,Function.comp_apply]
  exact borelAction_tendsto μ hT (currentMassMeasure_controls hT)
    ((integrable_boundedLip μ hab.1).indicator hE)
    (fun n => integrable_boundedLip μ ((profile_comp_boundedLip hu _ t).mul hab.1))
    hlim π hab.2

end CAT0Fillings.Slicing

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_WeakRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter SmoothCutoff BorelCoefficients BorelRestriction MassMeasure Foundations
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

noncomputable def levelBarrier (a : ℝ≥0) (t : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  1-profile a 0 |u x-t|

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelBarrier_bounds (a : ℝ≥0) (t : ℝ) (u : X → ℝ) (x : X) :
    0 ≤ levelBarrier a t u x ∧ levelBarrier a t u x ≤ 1 := by
  have hp := profile_bounds a 0 |u x-t|
  dsimp only [levelBarrier]
  constructor <;> linarith [hp.1,hp.2]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelBarrier_boundedLip {u : X → ℝ} (hu : BoundedLip u) (a : ℝ≥0) (t : ℝ) :
    BoundedLip (levelBarrier a t u) := by
  obtain ⟨K,hK⟩ := hu.1
  have hv : BoundedLip (fun x => |u x-t|) := by
    obtain ⟨M,hM⟩ := hu.2
    refine ⟨⟨K,?_⟩, M+|t|, fun x => ?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq]
      calc
        _ ≤ |(u x-t)-(u y-t)| := abs_abs_sub_abs_le_abs_sub _ _
        _ = dist (u x) (u y) := by rw [Real.dist_eq]; congr 1; ring
        _ ≤ K*dist x y := hK.dist_le_mul x y
    · rw [abs_abs]
      exact (abs_sub (u x) t).trans (by linarith [hM x])
  have h := (BoundedLip.const (X := X) 1).add
    ((profile_comp_boundedLip hv a 0).const_mul (-1))
  change BoundedLip (fun x => 1-profile a 0 |u x-t|)
  simpa only [Function.comp_def,neg_one_mul,sub_eq_add_neg] using h

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma profile_error_le_levelBarrier (a : ℝ≥0) (t : ℝ) (u : X → ℝ) (x : X) :
    |profile a t (u x)-({x | t < u x}.indicator (fun _ => (1:ℝ)) x)| ≤
      levelBarrier a t u x := by
  by_cases hx : t < u x
  · rw [indicator_of_mem (show x ∈ {x | t < u x} from hx),abs_of_nonpos (by linarith [(profile_bounds a t (u x)).2])]
    dsimp only [levelBarrier,profile]
    rw [abs_of_pos (sub_pos.mpr hx),sub_zero]
    linarith
  · rw [indicator_of_notMem (show x ∉ {x | t < u x} from hx),profile_zero a (le_of_not_gt hx),sub_self,abs_zero]
    exact (levelBarrier_bounds a t u x).1

omit [CompactSpace X] in
lemma levelBarrier_integral_tendsto (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ) (ht : μ {x | u x = t} = 0) :
    Tendsto (fun n : ℕ => ∫ x, levelBarrier ((n:ℝ≥0)+1) t u x ∂μ) atTop (𝓝 0) := by
  have hne : ∀ᵐ x ∂μ, u x ≠ t := by simpa only [ae_iff,not_not] using ht
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => levelBarrier ((n:ℝ≥0)+1) t u x) atTop (𝓝 0) := by
    filter_upwards [hne] with x hx
    have hpos : 0 < |u x-t| := abs_pos.mpr (sub_ne_zero.mpr hx)
    have hp : Tendsto (fun n : ℕ => profile ((n:ℝ≥0)+1) 0 |u x-t|) atTop (𝓝 1) := by
      simpa only [indicator_of_mem (show |u x-t| ∈ Ioi 0 from hpos)] using profile_sequence_tendsto 0 |u x-t|
    simpa only [levelBarrier,sub_self] using (tendsto_const_nhds (x := (1:ℝ))).sub hp
  have hdom (n : ℕ) : ∀ᵐ x ∂μ, ‖levelBarrier ((n:ℝ≥0)+1) t u x‖ ≤ (1:ℝ) := by
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (levelBarrier_bounds _ _ _ _).1]
      exact (levelBarrier_bounds _ _ _ _).2
  have hh := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => (1:ℝ)) (fun n => (levelBarrier_boundedLip hu _ t).continuous.aestronglyMeasurable)
    (integrable_const _) hdom hpt
  simpa only [integral_zero] using hh

lemma restrictCurrent_apply_of_controls {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {E : Set X} (hE : MeasurableSet E) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) :
    restrictCurrent hT E b π = borelAction μ hT (E.indicator b) π := by
  rw [restrictCurrent_apply hT E hab]
  exact borelAction_independent _ hT (currentMassMeasure_controls hT) hμ
    ((integrable_boundedLip _ hab.1).indicator hE)
    ((integrable_boundedLip _ hab.1).indicator hE) π hab.2

lemma restriction_profile_error_bound {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {u : X → ℝ} (hu : BoundedLip u) (a : ℝ≥0) (t : ℝ)
    {b : X → ℝ} (hb : BoundedLip b) (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) (M : ℝ) (hM : ∀ x, |b x| ≤ M) :
    |restrictCurrent hT {x | t < u x} b π - T (fun x => profile a t (u x)*b x) π| ≤
      ((∏ i, (K i : ℝ))*M) * ∫ x, levelBarrier a t u x ∂μ := by
  have hab : Admissible b π := ⟨hb,fun i => ⟨K i,hK i⟩⟩
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have hpb : BoundedLip (fun x => profile a t (u x)*b x) := (profile_comp_boundedLip hu a t).mul hb
  rw [restrictCurrent_apply_of_controls hT μ hμ hE hab,
    ←borelAction_eq μ hT hμ ⟨hpb,hab.2⟩]
  apply (borelAction_difference_bound μ hT hμ ((integrable_boundedLip μ hb).indicator hE)
    (integrable_boundedLip μ hpb) π K hK).trans
  have hi : ∫ x, |({x | t < u x}.indicator b x)-profile a t (u x)*b x| ∂μ ≤
      M*∫ x, levelBarrier a t u x ∂μ := by
    rw [←integral_const_mul]
    apply integral_mono ((integrable_boundedLip μ hb).indicator hE |>.sub
      (integrable_boundedLip μ hpb) |>.abs)
      ((integrable_boundedLip μ (levelBarrier_boundedLip hu a t)).const_mul M)
    intro x
    have he : ({x | t < u x}.indicator b x)-profile a t (u x)*b x =
        (profile a t (u x)-({x | t < u x}.indicator (fun _ => (1:ℝ)) x)) * (-b x) := by
      by_cases hx : t < u x <;> simp [hx]
      ring
    change |({x | t < u x}.indicator b x)-profile a t (u x)*b x| ≤ M*levelBarrier a t u x
    rw [he,abs_mul,abs_neg,mul_comm]
    exact mul_le_mul (hM x) (profile_error_le_levelBarrier a t u x) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hM x))
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

theorem restrictCurrent_weak_tendsto {ι : Type*} {l : Filter ι} {k : ℕ}
    {Ts : ι → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hT : IsMetricCurrent T)
    (μs : ι → FiniteMeasure X) (μ : FiniteMeasure X)
    (hμs : ∀ j, Controls (Ts j) (μs j)) (hμ : Controls T μ)
    (hμlim : Tendsto μs l (𝓝 μ))
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π)))
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ) (ht : (μ : Measure X) {x | u x = t} = 0)
    (b : X → ℝ) (π : Fin k → X → ℝ) :
    Tendsto (fun j => restrictCurrent (hTs j) {x | t < u x} b π) l
      (𝓝 (restrictCurrent hT {x | t < u x} b π)) := by
  by_cases hab : Admissible b π
  swap
  · simp only [restrictCurrent,ite_eq_right hab]
    exact tendsto_const_nhds
  choose K hK using hab.2
  obtain ⟨M,hM⟩ := hab.1.2
  let C := (∏ i, (K i : ℝ)) * max M 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (x : X) : |b x| ≤ max M 0 := (hM x).trans (le_max_left _ _)
  let P (n : ℕ) (U : Functional X k) := U (fun x => profile ((n:ℝ≥0)+1) t (u x)*b x) π
  let A (n : ℕ) (ν : FiniteMeasure X) := C*∫ x, levelBarrier ((n:ℝ≥0)+1) t u x ∂(ν : Measure X)
  have hA : Tendsto (fun n => A n μ) atTop (𝓝 0) := by
    simpa only [A,mul_zero] using (levelBarrier_integral_tendsto (μ : Measure X) hu t ht).const_mul C
  have hAlim (n : ℕ) : Tendsto (fun j => A n (μs j)) l (𝓝 (A n μ)) := by
    let f : C(X,ℝ) := ⟨levelBarrier ((n:ℝ≥0)+1) t u,(levelBarrier_boundedLip hu _ t).continuous⟩
    exact ((FiniteMeasure.continuous_integral_continuousMap f).tendsto μ |>.comp hμlim).const_mul C
  have hbT (n : ℕ) : dist (restrictCurrent hT {x | t < u x} b π) (P n T) ≤ A n μ :=
    restriction_profile_error_bound hT μ hμ hu _ t hab.1 π K hK _ hbound
  have hbTs (n : ℕ) (j : ι) : dist (restrictCurrent (hTs j) {x | t < u x} b π) (P n (Ts j)) ≤ A n (μs j) :=
    restriction_profile_error_bound (hTs j) (μs j) (hμs j) hu _ t hab.1 π K hK _ hbound
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := ((hA.eventually (gt_mem_nhds (show (0:ℝ) < ε/4 by positivity))).exists)
  have he1 : ∀ᶠ j in l, A n (μs j) < ε/3 :=
    (hAlim n).eventually (gt_mem_nhds (show A n μ < ε/3 by linarith))
  have he2 : ∀ᶠ j in l, dist (P n (Ts j)) (P n T) < ε/3 :=
    Metric.tendsto_nhds.mp (hlim _ _) (ε/3) (by positivity)
  filter_upwards [he1,he2] with j hj1 hj2
  have htri := dist_triangle (restrictCurrent (hTs j) {x | t < u x} b π) (P n (Ts j)) (P n T)
  have htri2 := dist_triangle (restrictCurrent (hTs j) {x | t < u x} b π) (P n T)
    (restrictCurrent hT {x | t < u x} b π)
  have hb := hbT n
  rw [dist_comm] at hb
  linarith [hbTs n j]

end CAT0Fillings.Slicing

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_Superlevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter SmoothCutoff BorelCoefficients BorelRestriction MassMeasure Foundations
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
omit [CompactSpace X] in
lemma ae_level_measure_zero (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : BoundedLip u) : ∀ᵐ t : ℝ, μ {x | u x = t} = 0 := by
  have hc := Measure.countable_meas_level_set_pos (μ := μ) hu.continuous.measurable
  filter_upwards [hc.ae_notMem volume] with t ht
  exact le_antisymm (le_of_not_gt ht) (bot_le)

noncomputable def superlevelSlice {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (u : X → ℝ) (t : ℝ) : Functional X k :=
  restrictCurrent hB {x | t < u x} - boundarySucc (restrictCurrent hT {x | t < u x})

lemma superlevelSlice_weak_tendsto {ι : Type*} {l : Filter ι} {k : ℕ}
    {Ts : ι → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hT : IsMetricCurrent T)
    (hBs : ∀ j, IsMetricCurrent (boundarySucc (Ts j))) (hB : IsMetricCurrent (boundarySucc T))
    (μs νs : ι → FiniteMeasure X) (μ ν : FiniteMeasure X)
    (hμs : ∀ j, Controls (Ts j) (μs j)) (hμ : Controls T μ)
    (hνs : ∀ j, Controls (boundarySucc (Ts j)) (νs j)) (hν : Controls (boundarySucc T) ν)
    (hμlim : Tendsto μs l (𝓝 μ)) (hνlim : Tendsto νs l (𝓝 ν))
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π)))
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (htμ : (μ : Measure X) {x | u x = t} = 0) (htν : (ν : Measure X) {x | u x = t} = 0)
    (b : X → ℝ) (π : Fin k → X → ℝ) :
    Tendsto (fun j => superlevelSlice (hTs j) (hBs j) u t b π) l
      (𝓝 (superlevelSlice hT hB u t b π)) := by
  have hrestr := restrictCurrent_weak_tendsto hTs hT μs μ hμs hμ hμlim hlim hu t htμ
  have hbd := boundarySucc_weak_limit (fun b π => hrestr b π)
  have hrestrB := restrictCurrent_weak_tendsto hBs hB νs ν hνs hν hνlim
    (boundarySucc_weak_limit hlim) hu t htν b π
  exact hrestrB.sub (hbd b π)

lemma ae_superlevelSlice_weak_tendsto {ι : Type*} {l : Filter ι} {k : ℕ}
    {Ts : ι → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hT : IsMetricCurrent T)
    (hBs : ∀ j, IsMetricCurrent (boundarySucc (Ts j))) (hB : IsMetricCurrent (boundarySucc T))
    (μs νs : ι → FiniteMeasure X) (μ ν : FiniteMeasure X)
    (hμs : ∀ j, Controls (Ts j) (μs j)) (hμ : Controls T μ)
    (hνs : ∀ j, Controls (boundarySucc (Ts j)) (νs j)) (hν : Controls (boundarySucc T) ν)
    (hμlim : Tendsto μs l (𝓝 μ)) (hνlim : Tendsto νs l (𝓝 ν))
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π)))
    {u : X → ℝ} (hu : BoundedLip u) :
    ∀ᵐ t : ℝ, ∀ b π, Tendsto (fun j => superlevelSlice (hTs j) (hBs j) u t b π) l
      (𝓝 (superlevelSlice hT hB u t b π)) := by
  filter_upwards [ae_level_measure_zero (μ : Measure X) hu,ae_level_measure_zero (ν : Measure X) hu]
    with t hμt hνt
  exact superlevelSlice_weak_tendsto hTs hT hBs hB μs νs μ ν hμs hμ hνs hν hμlim hνlim hlim hu t hμt hνt

end CAT0Fillings.Slicing

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Set MeasureTheory Filter
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_WeakApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

def NormalApprox (k : ℕ) (T : Functional X k) : Prop :=
  ∃ C : ℕ, ∃ Ts : ℕ → Functional X k,
    (∀ j, IsIntegral k (Ts j)) ∧
    (∀ j, mass (Ts j) ≤ C) ∧ (∀ j, mass (boundary (Ts j)) ≤ C) ∧
    ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))

lemma normalApprox_of_weak_limit {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] {k : ℕ} {Ts : ℕ → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsIntegral k (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundary (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    NormalApprox k T := by
  obtain ⟨C,hC⟩ := exists_nat_gt (max (M : ℝ) N)
  exact ⟨C,Ts,hTs,fun j => (hM j).trans ((le_max_left _ _).trans hC.le),
    fun j => (hN j).trans ((le_max_right _ _).trans hC.le),hlim⟩

noncomputable def denseCurrentTest (k K : ℕ) : ℕ → TestClass (X := X) k K :=
  (exists_dense_seq (TestClass (X := X) k K)).choose

lemma denseCurrentTest_dense {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] (k K : ℕ) : DenseRange (denseCurrentTest (X := X) k K) :=
  (exists_dense_seq (TestClass (X := X) k K)).choose_spec

noncomputable def currentCoordinates (k : ℕ) (T : Functional X k) : (ℕ × ℕ) → ℝ :=
  fun ij => TestClass.eval T (denseCurrentTest k ij.1 ij.2)

noncomputable def normalApproxClosed (k C : ℕ) : Set ((ℕ × ℕ) → ℝ) :=
  closure (currentCoordinates k ''
    {T : Functional X k | IsIntegral k T ∧ mass T ≤ C ∧ mass (boundary T) ≤ C})

lemma lipschitz_of_dense_limit {Z : Type*} [PseudoMetricSpace Z]
    {q : ℕ → Z} (hq : DenseRange q) {f : ℕ → Z → ℝ} {F : Z → ℝ}
    {C : ℝ≥0} (hf : ∀ j, LipschitzWith C (f j)) (hF : Continuous F)
    (hlim : ∀ i, Tendsto (fun j => f j (q i)) atTop (𝓝 (F (q i)))) :
    LipschitzWith C F := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact hq.induction_on₂
    (isClosed_le ((hF.comp continuous_fst).dist (hF.comp continuous_snd))
      (continuous_const.mul (continuous_fst.dist continuous_snd)))
    (fun i j => le_of_tendsto ((hlim i).dist (hlim j))
      (Eventually.of_forall fun a => (hf a).dist_le_mul (q i) (q j))) x y

lemma IsMetricCurrent.testClass_lipschitz_zero {T : Functional X 0}
    (hT : IsMetricCurrent T) (M : ℝ≥0) (hM : mass T ≤ M) (K : ℕ) :
    LipschitzWith M (TestClass.eval (K := K) T) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hπ : (fun i => (p.val.2 i : X → ℝ)) = fun i => (q.val.2 i : X → ℝ) :=
    funext fun i => Fin.elim0 i
  have hb : ∀ x, |p.val.1 x - q.val.1 x| ≤ (nndist p q : ℝ≥0) := by
    intro x
    exact (ContinuousMap.dist_apply_le_dist (f := p.val.1) (g := q.val.1) x).trans
      (le_max_left (dist p.val.1 q.val.1) (dist p.val.2 q.val.2))
  have hh := IsMetricCurrent.first_difference_bound hT p.boundedLip q.boundedLip
    (fun i => p.val.2 i) K p.property.2.2 (nndist p q) hb
  have hh' : |T p.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => q.val.2 i)| ≤
      dist p q * mass T := by
    simpa only [hπ,pow_zero,one_mul,coe_nndist] using hh
  exact hh'.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hM (dist_nonneg : 0 ≤ dist p q))

lemma IsIntegral.uniform_testClass_lipschitz {k : ℕ} {T : Functional X k}
    (hT : IsIntegral k T) (M N : ℝ≥0)
    (hM : mass T ≤ M) (hN : mass (boundary T) ≤ N) (K : ℕ) :
    LipschitzWith ((K : ℝ≥0)^k*M + k*((K : ℝ≥0)+K)^(k-1)*(K*N+K*M))
      (TestClass.eval (K := K) T) := by
  cases k with
  | zero => simpa using IsMetricCurrent.testClass_lipschitz_zero hT.1 M hM K
  | succ k => simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using
      IntegerRectifiable.testClass_lipschitz hT.2.1 hT.1 hT.2.2.1 M N hM hN K

lemma weak_limit_of_coordinate_limit {k : ℕ}
    {Ts : ℕ → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsIntegral k (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundary (Ts j)) ≤ N)
    (hOff : ∀ b π, ¬Admissible b π → T b π = 0)
    (hCont : ∀ K, Continuous (TestClass.eval (K := K) T))
    (hlim : Tendsto (fun j => currentCoordinates k (Ts j)) atTop
      (𝓝 (currentCoordinates k T))) :
    ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)) := by
  have hall (K : ℕ) (p : TestClass (X := X) k K) :
      Tendsto (fun j => TestClass.eval (Ts j) p) atTop (𝓝 (TestClass.eval T p)) := by
    let C : ℝ≥0 := (K : ℝ≥0)^k*M +
      k*((K : ℝ≥0)+K)^(k-1)*(K*N+K*M)
    have hL (j : ℕ) : LipschitzWith C (TestClass.eval (K := K) (Ts j)) :=
      IsIntegral.uniform_testClass_lipschitz (hTs j) M N (hM j) (hN j) K
    have hd (i : ℕ) : Tendsto
        (fun j => TestClass.eval (Ts j) (denseCurrentTest k K i)) atTop
        (𝓝 (TestClass.eval T (denseCurrentTest k K i))) :=
      tendsto_pi_nhds.mp hlim (K,i)
    have hLT := lipschitz_of_dense_limit (denseCurrentTest_dense k K) hL (hCont K) hd
    exact tendsto_of_lipschitz_dense hL hLT (denseCurrentTest_dense k K) hd p
  have hcur j : IsMetricCurrent (Ts j) := by
    cases k <;> exact (hTs j).1
  intro b π
  by_cases hab : Admissible b π
  · obtain ⟨K,p,hb,hπ⟩ := admissible_mem_testClass hab
    simpa only [TestClass.eval,hb,hπ] using hall K p
  · simpa only [(fun j => (hcur j).offDomain b π hab),hOff b π hab] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

theorem normalApprox_iff_coordinates {k : ℕ} {T : Functional X k}
    (hOff : ∀ b π, ¬Admissible b π → T b π = 0)
    (hCont : ∀ K, Continuous (TestClass.eval (K := K) T)) :
    NormalApprox k T ↔
      ∃ C : ℕ, currentCoordinates k T ∈ normalApproxClosed (X := X) k C := by
  classical
  constructor
  · rintro ⟨C,Ts,hTs,hM,hN,hlim⟩
    refine ⟨C, isClosed_closure.mem_of_tendsto
      (tendsto_pi_nhds.mpr fun ij => hlim _ _) ?_⟩
    exact Eventually.of_forall fun j => subset_closure ⟨Ts j,⟨hTs j,hM j,hN j⟩,rfl⟩
  · rintro ⟨C,hC⟩
    obtain ⟨ys,hys,hlim⟩ := mem_closure_iff_seq_limit.mp hC
    choose Ts hTs heq using hys
    have hlim' : Tendsto (fun j => currentCoordinates k (Ts j)) atTop
        (𝓝 (currentCoordinates k T)) := by
      simpa only [heq] using hlim
    refine ⟨C,Ts,fun j => (hTs j).1,fun j => (hTs j).2.1,fun j => (hTs j).2.2,?_⟩
    exact weak_limit_of_coordinate_limit (fun j => (hTs j).1) C C
      (fun j => (hTs j).2.1) (fun j => (hTs j).2.2) hOff hCont hlim'

lemma measurableSet_normalApprox {A : Type*} [MeasurableSpace A] {k : ℕ}
    (T : A → Functional X k)
    (hOff : ∀ a b π, ¬Admissible b π → T a b π = 0)
    (hCont : ∀ a K, Continuous (TestClass.eval (K := K) (T a)))
    (hMeas : ∀ b π, Measurable (fun a => T a b π)) :
    MeasurableSet {a | NormalApprox k (T a)} := by
  have he : {a | NormalApprox k (T a)} =
      ⋃ C : ℕ, (fun a => currentCoordinates k (T a)) ⁻¹' normalApproxClosed (X := X) k C := by
    ext a
    simpa only [mem_ofPred_eq,mem_iUnion,mem_preimage] using
      normalApprox_iff_coordinates (hOff a) (hCont a)
  rw [he]
  apply MeasurableSet.iUnion
  intro C
  exact isClosed_closure.measurableSet.preimage (Measurable.of_eval fun index =>
    hMeas (denseCurrentTest k index.1 index.2).val.1
      (fun coordinate => (denseCurrentTest k index.1 index.2).val.2 coordinate))

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction SmoothCutoff

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma continuous_profile_action {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {u : X → ℝ} (hu : BoundedLip u)
    (a : ℝ≥0) {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    Continuous (fun t : ℝ => T (fun x => profile a t (u x) * b x) π) := by
  apply continuous_iff_seqContinuous.mpr
  intro ts t ht
  let f (s : ℝ) (x : X) := profile a s (u x) * b x
  have hf (s : ℝ) : BoundedLip (f s) := (profile_comp_boundedLip hu a s).mul hab.1
  obtain ⟨B,hB⟩ := hab.1.2
  have hbound (s : ℝ) (x : X) : |f s x| ≤ B := by
    dsimp [f]
    rw [abs_mul,abs_of_nonneg (profile_bounds a s (u x)).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (profile_bounds a s (u x)).2).trans (hB x)
  have hlim (x : X) : Tendsto (fun j => f (ts j) x) atTop (𝓝 (f t x)) := by
    have hp : Continuous (fun s : ℝ => profile a s (u x)) := by
      unfold profile
      fun_prop
    exact ((hp.tendsto t).comp ht).mul_const (b x)
  have h := borelAction_tendsto_of_bounded_pointwise hT (currentMassMeasure hT)
    (currentMassMeasure_controls hT) (hf t).continuous.measurable
    (fun j => (hf (ts j)).continuous.measurable) B (fun j => hbound (ts j)) hlim π hab.2
  simpa only [borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨hf _,hab.2⟩,
    f, Function.comp_def] using h

variable {A : Type*} [MeasurableSpace A]

lemma measurable_profile_action_family {k : ℕ} (T : A → Functional X k)
    (hT : ∀ a, IsMetricCurrent (T a))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) (c : ℝ≥0)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    Measurable (fun p : ℝ × A => T p.2 (fun x => profile c p.1 (u x) * b x) π) := by
  exact (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun a => continuous_profile_action (hT a) hu c hab)
    (fun t => (hTm (fun x => profile c t (u x)*b x) π).stronglyMeasurable)).measurable

lemma measurable_restriction_family {k : ℕ} (T : A → Functional X k)
    (hT : ∀ a, IsMetricCurrent (T a))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) (b : X → ℝ) (π : Fin k → X → ℝ) :
    Measurable (fun p : ℝ × A => restrictCurrent (hT p.2) {x | p.1 < u x} b π) := by
  classical
  by_cases hab : Admissible b π
  · have hlim (p : ℝ × A) : Tendsto
        (fun n : ℕ => T p.2 (fun x => profile ((n:ℝ≥0)+1) p.1 (u x)*b x) π) atTop
        (𝓝 (restrictCurrent (hT p.2) {x | p.1 < u x} b π)) := by
      have h := profile_current_tendsto (hT p.2) hu p.1 b π hab
      have he (n : ℕ) : weightedCurrent (currentMassMeasure (hT p.2)) (hT p.2)
          (profile ((n:ℝ≥0)+1) p.1 ∘ u) b π =
          T p.2 (fun x => profile ((n:ℝ≥0)+1) p.1 (u x)*b x) π := by
        rw [weightedCurrent,ite_eq_left hab]
        exact borelAction_eq _ (hT p.2) (currentMassMeasure_controls (hT p.2))
          ⟨(profile_comp_boundedLip hu _ _).mul hab.1,hab.2⟩
      simpa only [he] using h
    exact measurable_of_tendsto_metrizable
      (fun n => measurable_profile_action_family T hT hTm hu ((n:ℝ≥0)+1) hab) (tendsto_pi_nhds.mpr hlim)
  · have he (p : ℝ × A) : restrictCurrent (hT p.2) {x | p.1 < u x} b π = 0 := by
      simp only [restrictCurrent,ite_eq_right hab]
    simpa only [he] using (measurable_const : Measurable (fun _ : ℝ × A => (0:ℝ)))

theorem measurable_superlevelSlice_family {k : ℕ} (T : A → Functional X (k+1))
    (hT : ∀ a, IsMetricCurrent (T a))
    (hB : ∀ a, IsMetricCurrent (boundarySucc (T a)))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) (b : X → ℝ) (π : Fin k → X → ℝ) :
    Measurable (fun p : ℝ × A => superlevelSlice (hT p.2) (hB p.2) u p.1 b π) := by
  classical
  have hBm (b : X → ℝ) (π : Fin k → X → ℝ) :
      Measurable (fun a => boundarySucc (T a) b π) := by
    by_cases h : Admissible b π
    · simpa only [boundarySucc,ite_eq_left h] using hTm (fun _ => 1) (Matrix.vecCons b π)
    · simp only [boundarySucc,ite_eq_right h]
      exact measurable_const
  by_cases hab : Admissible b π
  · have hleft := measurable_restriction_family (fun a => boundarySucc (T a)) hB hBm hu b π
    have hright := measurable_restriction_family T hT hTm hu (fun _ => 1) (Matrix.vecCons b π)
    convert hleft.sub hright using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp only [superlevelSlice,Pi.sub_apply,boundarySucc,ite_eq_left hab]
  · have he (p : ℝ × A) : superlevelSlice (hT p.2) (hB p.2) u p.1 b π = 0 := by
      simp only [superlevelSlice,Pi.sub_apply,restrictCurrent,boundarySucc,ite_eq_right hab,sub_zero]
    simpa only [he] using (measurable_const : Measurable (fun _ : ℝ × A => (0:ℝ)))

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Atoms
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
noncomputable def atomCurrent (a : ℤ) (x : X) : Functional X 0 :=
  fun b π => if Admissible b π then (a : ℝ)*b x else 0

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomCurrent_apply (a : ℤ) (x : X) {b : X → ℝ} {π : Fin 0 → X → ℝ}
    (hb : BoundedLip b) : atomCurrent a x b π = (a : ℝ)*b x :=
  ite_eq_left ⟨hb,fun i => Fin.elim0 i⟩

lemma atomCurrent_controls (a : ℤ) (x : X) :
    Controls (atomCurrent a x) (ENNReal.ofReal |(a : ℝ)| • Measure.dirac x) := by
  intro b π hb _
  rw [atomCurrent_apply a x hb,integral_smul_measure,integral_dirac,
    ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,abs_mul]

omit [MetricSpace X] [BorelSpace X] in
lemma finite_atom_measure (a : ℤ) (x : X) :
    IsFiniteMeasure (ENNReal.ofReal |(a : ℝ)| • Measure.dirac x) := by
  constructor
  simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ x),smul_eq_mul,mul_one]
  exact ENNReal.ofReal_lt_top

lemma atomCurrent_isMetricCurrent (a : ℤ) (x : X) : IsMetricCurrent (atomCurrent a x) := by
  refine ⟨fun b π h => ite_eq_right h,?_,?_,?_,?_,?_⟩
  · intro b c π r s hb hc _
    rw [atomCurrent_apply a x ((hb.const_mul r).add (hc.const_mul s)),
      atomCurrent_apply a x hb,atomCurrent_apply a x hc]
    ring
  · intro b π i
    exact Fin.elim0 i
  · intro b π πs hb _ _
    simp_rw [atomCurrent_apply a x hb]
    exact tendsto_const_nhds
  · rintro b π _ ⟨i,_⟩
    exact Fin.elim0 i
  · exact ⟨ENNReal.ofReal |(a : ℝ)| • Measure.dirac x,finite_atom_measure a x,atomCurrent_controls a x⟩

lemma mass_atomCurrent [CompactSpace X] (a : ℤ) (x : X) :
    mass (atomCurrent a x) = |(a : ℝ)| := by
  apply le_antisymm
  · apply (mass_le_measure (finite_atom_measure a x) (atomCurrent_controls a x)).trans_eq
    simp only [Measure.real,Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ x),
      smul_eq_mul,mul_one,ENNReal.toReal_ofReal (abs_nonneg _)]
  · have h := (atomCurrent_isMetricCurrent a x).mass_bound_uniform
      (BoundedLip.const (X := X) 1) (π := fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (M := 1) (fun _ => by norm_num)
    simpa only [atomCurrent_apply a x (BoundedLip.const 1),mul_one,
      Finset.univ_eq_empty,Finset.prod_empty,one_mul] using h

omit [MeasurableSpace X] [BorelSpace X] in
lemma IntegerChart.zero_action (C : IntegerChart X 0) (h : (0 : Euc 0) ∈ C.domain) :
    C.action = atomCurrent (C.multiplicity 0) (C.param ⟨0,h⟩) := by
  funext b π
  by_cases hab : Admissible b π
  · rw [IntegerChart.action,ite_eq_left hab,atomCurrent,ite_eq_left hab,volume_euclideanSpace_eq_dirac,
      restrict_dirac,ite_eq_left h,integral_dirac]
    have hj : C.jacobian π 0 = 1 := Matrix.det_isEmpty
    rw [hj,mul_one]
    simp only [IntegerChart.scalar,dite_eq_left h]
  · simp only [IntegerChart.action,atomCurrent,ite_eq_right hab]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IntegerChart.zero_action_eq_zero (C : IntegerChart X 0) (h : (0 : Euc 0) ∉ C.domain) :
    C.action = 0 := by
  have hd : C.domain = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact h ((Subsingleton.elim z 0) ▸ hz)
  funext b π
  simp only [IntegerChart.action,hd,Measure.restrict_empty,integral_zero_measure,ite_self,Pi.zero_apply]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IntegerChart.zero_exists_atom [Nonempty X] (C : IntegerChart X 0) :
    ∃ a : ℤ, ∃ x : X, C.action = atomCurrent a x := by
  by_cases h : (0 : Euc 0) ∈ C.domain
  · exact ⟨C.multiplicity 0,C.param ⟨0,h⟩,C.zero_action h⟩
  · refine ⟨0,Classical.arbitrary X,?_⟩
    rw [C.zero_action_eq_zero h]
    funext b π
    simp only [atomCurrent,Int.cast_zero,zero_mul,ite_self,Pi.zero_apply]

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Atoms
attribute [-instance] _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
noncomputable def atomChart (a : ℤ) (x : X) : IntegerChart X 0 where
  domain := univ
  borel := MeasurableSet.univ
  bounded := Set.finite_univ.isCompact.isBounded
  param := fun _ => x
  bilipschitz := ⟨0,0,LipschitzWith.const x,AntilipschitzWith.of_subsingleton⟩
  multiplicity := fun _ => a
  integrable := by
    rw [Measure.restrict_univ,volume_euclideanSpace_eq_dirac]
    exact integrable_const _

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomChart_action (a : ℤ) (x : X) : (atomChart a x).action = atomCurrent a x :=
  (atomChart a x).zero_action (mem_univ _)

lemma atomCurrent_integerRectifiable (a : ℤ) (x : X) : IntegerRectifiable (atomCurrent a x) := by
  classical
  let C : ℕ → IntegerChart X 0 := fun i => if i = 0 then atomChart a x else emptyChart 0
  have hC i : IsMetricCurrent (C i).action := by
    dsimp [C]
    split_ifs
    · rw [atomChart_action]; exact atomCurrent_isMetricCurrent a x
    · rw [emptyChart_action]; exact isMetricCurrent_zero 0
  have hzero i (hi : i ≠ 0) : (C i).action = 0 := by
    dsimp [C]
    rw [ite_eq_right hi,emptyChart_action]
    rfl
  refine ⟨C,?_,hC,?_,?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · have hj : j ≠ 0 := by omega
      simp only [C,ite_eq_right hj,emptyChart_image,disjoint_empty]
    · simp only [C,ite_eq_right hi,emptyChart_image,empty_disjoint]
  · apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    have hi' : i ≠ 0 := by simpa using hi
    rw [hzero i hi']
    exact mass_zero 0
  · intro b π
    rw [tsum_eq_single 0 (fun i hi => by rw [hzero i hi]; rfl)]
    simp only [C,ite_true, if_true,atomChart_action]

lemma atomCurrent_integral (a : ℤ) (x : X) : IsIntegral 0 (atomCurrent a x) :=
  ⟨atomCurrent_isMetricCurrent a x,atomCurrent_integerRectifiable a x⟩

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_FiniteAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology

lemma finite_support_int_of_summable_abs {ι : Type*} (a : ι → ℤ)
    (h : Summable (fun i => |(a i : ℝ)|)) : (Function.support a).Finite := by
  have he : ∀ᶠ i in cofinite, |(a i : ℝ)| < 1 :=
    h.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply (eventually_cofinite.mp he).subset
  intro i hi
  have hi' : a i ≠ 0 := hi
  have hab : (1 : ℝ) ≤ |(a i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  exact not_lt.mpr hab

noncomputable def padFinite {A : Type*} {m N : ℕ} (hm : m ≤ N) (f : Fin m → A) (z : A) : Fin N → A :=
  fun i => Fin.addCases f (fun _ => z) ((finCongr (Nat.add_sub_of_le hm).symm) i)

lemma padFinite_property {A : Type*} {m N : ℕ} (hm : m ≤ N) (f : Fin m → A) (z : A)
    (P : A → Prop) (hf : ∀ i, P (f i)) (hz : P z) : ∀ i, P (padFinite hm f z i) := by
  intro i
  dsimp only [padFinite]
  generalize (finCongr (Nat.add_sub_of_le hm).symm) i = j
  exact Fin.addCases (fun i => by simp only [Fin.addCases_left]; exact hf i)
    (fun i => by simp only [Fin.addCases_right]; exact hz) j

lemma sum_padFinite {A : Type*} {m N : ℕ} (hm : m ≤ N) (f : Fin m → A) (z : A)
    (g : A → ℝ) (hz : g z = 0) :
    (∑ i, g (padFinite hm f z i)) = ∑ i, g (f i) := by
  classical
  unfold padFinite
  rw [(finCongr (Nat.add_sub_of_le hm).symm).sum_comp (fun j => g (Fin.addCases f (fun _ => z) j)),
    Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,hz,Finset.sum_const_zero,add_zero]

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

theorem integerRectifiable_zero_finite_representation {T : Functional X 0}
    (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) :
    ∃ (m : ℕ) (a : Fin m → ℤ) (x : Fin m → X),
      (m : ℝ) ≤ mass T ∧ (∀ i, |(a i : ℝ)| ≤ mass T) ∧
      ∀ b π, T b π = ∑ i, atomCurrent (a i) (x i) b π := by
  classical
  obtain ⟨C,hd,hC,hCS,heq⟩ := hI
  choose a x hact using fun i => (C i).zero_exists_atom
  have hmass i : mass (C i).action = |(a i : ℝ)| := by rw [hact i,mass_atomCurrent]
  have haS : Summable (fun i => |(a i : ℝ)|) := by simpa only [hmass] using hCS
  have hfinite := finite_support_int_of_summable_abs a haS
  let s := hfinite.toFinset
  have hs : ∀ i, i ∈ s ↔ a i ≠ 0 := fun i => hfinite.mem_toFinset
  let e := s.equivFin.symm
  have hnorm i : |(a i : ℝ)| ≤ mass T := by
    apply (haS.le_tsum i (fun j _ => abs_nonneg ((a j : ℤ) : ℝ))).trans
    have hm := chartFamily_mass_sum_le hT C hd hC hCS heq
    simpa only [hmass] using hm
  have hmcard : (s.card : ℝ) ≤ mass T := by
    calc (s.card : ℝ) = ∑ i ∈ s, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ s, |(a i : ℝ)| := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast Int.one_le_abs ((hs i).mp hi)
      _ ≤ ∑' i, |(a i : ℝ)| := haS.sum_le_tsum s (fun i _ => abs_nonneg _)
      _ ≤ mass T := by
        have hm := chartFamily_mass_sum_le hT C hd hC hCS heq
        simpa only [hmass] using hm
  refine ⟨s.card,fun i => a (e i),fun i => x (e i),hmcard,fun i => hnorm (e i),?_⟩
  intro b π
  rw [heq]
  simp_rw [hact]
  rw [tsum_eq_sum (s := s) (fun i hi => by
    have hai : a i = 0 := not_not.mp (fun hn => hi ((hs i).mpr hn))
    simp only [atomCurrent,hai,Int.cast_zero,zero_mul,ite_self])]
  rw [←Finset.sum_attach]
  exact (e.sum_comp (fun i : s => atomCurrent (a i) (x i) b π)).symm

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_AtomCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
theorem exists_integer_configuration_subsequence {X : Type*} [MetricSpace X] [CompactSpace X]
    {N : ℕ} (a : ℕ → Fin N → ℤ) (x : ℕ → Fin N → X)
    (M : ℝ) (hM : ∀ j i, |(a j i : ℝ)| ≤ M) :
    ∃ (b : Fin N → ℤ) (y : Fin N → X) (ψ : ℕ → ℕ), StrictMono ψ ∧
      (∀ i, Tendsto (fun j => (a (ψ j) i : ℝ)) atTop (𝓝 ((b i : ℤ) : ℝ))) ∧
      (∀ i, Tendsto (fun j => x (ψ j) i) atTop (𝓝 (y i))) := by
  classical
  let K : Set ((Fin N → ℝ) × (Fin N → X)) :=
    {v | ∀ i, v i ∈ Icc (-M) M} ×ˢ univ
  have hK : IsCompact K := (isCompact_pi_infinite (fun _ : Fin N => isCompact_Icc)).prod isCompact_univ
  let seq j : (Fin N → ℝ) × (Fin N → X) := (fun i => (a j i : ℝ),x j)
  have hseq j : seq j ∈ K := ⟨fun i => abs_le.mp (hM j i),mem_univ _⟩
  obtain ⟨v,_,ψ,hψ,hlim⟩ := hK.isSeqCompact hseq
  have ha i : Tendsto (fun j => (a (ψ j) i : ℝ)) atTop (𝓝 (v.1 i)) :=
    (continuous_apply i).tendsto _ |>.comp (continuous_fst.tendsto _ |>.comp hlim)
  have hx i : Tendsto (fun j => x (ψ j) i) atTop (𝓝 (v.2 i)) :=
    (continuous_apply i).tendsto _ |>.comp (continuous_snd.tendsto _ |>.comp hlim)
  have hInt i : ∃ b : ℤ, (b : ℝ) = v.1 i :=
    Real.isClosed_range_intCast.mem_of_tendsto (ha i) (Eventually.of_forall fun j => ⟨a (ψ j) i,rfl⟩)
  choose b hb using hInt
  exact ⟨b,v.2,ψ,hψ,fun i => (hb i) ▸ ha i,hx⟩


open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

lemma integral_finite_atoms {N : ℕ} (a : Fin N → ℤ) (x : Fin N → X) :
    IsIntegral 0 (fun b π => ∑ i, atomCurrent (a i) (x i) b π) := by
  classical
  let U (j : ℕ) : Functional X 0 := if h : j < N then atomCurrent (a ⟨j,h⟩) (x ⟨j,h⟩) else 0
  have hUI j : IsIntegral 0 (U j) := by
    dsimp [U]
    split_ifs
    · exact atomCurrent_integral _ _
    · exact isIntegral_zero 0
  have hUS : Summable (fun j => mass (U j)) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro j hj
    have hj' : ¬ j < N := by simpa only [Finset.mem_range] using hj
    dsimp [U]
    rw [dite_eq_right hj']
    exact mass_zero 0
  have hEq : (fun b π => ∑ i, atomCurrent (a i) (x i) b π) = (fun b π => ∑' j, U j b π) := by
    funext b π
    rw [tsum_eq_sum (s := Finset.range N) (fun j hj => by
      dsimp [U]
      rw [dite_eq_right (show ¬j < N by simpa only [Finset.mem_range] using hj)]
      rfl),←Fin.sum_univ_eq_sum_range (fun j => U j b π) N]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [U]
    rw [ite_eq_left i.isLt]
  rw [hEq]
  exact ⟨isMetricCurrent_tsum (fun j => (hUI j).1) hUS,
    integerRectifiable_tsum (fun j => (hUI j).1) (fun j => (hUI j).2) hUS⟩

lemma integral_zero_uniform_representation {T : Functional X 0} (hT : IsIntegral 0 T)
    (M : ℝ) (hM : mass T ≤ M) :
    ∃ (a : Fin (Nat.ceil M) → ℤ) (x : Fin (Nat.ceil M) → X),
      (∀ i, |(a i : ℝ)| ≤ M) ∧
      ∀ b π, T b π = ∑ i, atomCurrent (a i) (x i) b π := by
  classical
  obtain ⟨m,a,x,hm,ha,heq⟩ := integerRectifiable_zero_finite_representation hT.1 hT.2
  have hmN : m ≤ Nat.ceil M := by exact_mod_cast (hm.trans hM).trans (Nat.le_ceil M)
  let p := padFinite hmN (fun i => (a i,x i)) (0,Classical.arbitrary X)
  refine ⟨fun i => (p i).1,fun i => (p i).2,?_,?_⟩
  · exact padFinite_property hmN (fun i => (a i,x i)) (0,Classical.arbitrary X)
      (fun z : ℤ × X => |(z.1 : ℝ)| ≤ M) (fun i => (ha i).trans hM)
      (by simpa only [Int.cast_zero,abs_zero] using (mass_nonneg T).trans hM)
  · intro b π
    rw [heq]
    exact (sum_padFinite hmN (fun i => (a i,x i)) (0,Classical.arbitrary X)
      (fun z : ℤ × X => atomCurrent z.1 z.2 b π)
      (by simp only [atomCurrent,Int.cast_zero,zero_mul,ite_self])).symm

theorem integral_zero_weak_closed {Ts : ℕ → Functional X 0} {T : Functional X 0}
    (hTs : ∀ j, IsIntegral 0 (Ts j)) (M : ℝ) (hM : ∀ j, mass (Ts j) ≤ M)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    IsIntegral 0 T := by
  classical
  choose a x ha heq using fun j => integral_zero_uniform_representation (hTs j) M (hM j)
  obtain ⟨c,y,ψ,hψ,hc,hy⟩ := exists_integer_configuration_subsequence a x M ha
  let S : Functional X 0 := fun b π => ∑ i, atomCurrent (c i) (y i) b π
  have hSLim b π : Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (S b π)) := by
    simp_rw [heq]
    apply tendsto_finsetSum
    intro i _
    by_cases hab : Admissible b π
    · simp only [atomCurrent,ite_eq_left hab]
      exact (hc i).mul ((hab.1.1.choose_spec.continuous.tendsto (y i)).comp (hy i))
    · simp only [atomCurrent,ite_eq_right hab]
      exact tendsto_const_nhds
  have hTS : T = S := by
    funext b π
    exact tendsto_nhds_unique ((hlim b π).comp hψ.tendsto_atTop) (hSLim b π)
  rw [hTS]
  exact integral_finite_atoms c y

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_WeakSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter MassMeasure Foundations
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
lemma normal_one_of_bounded_integral_weak_limit
    {Ts : ℕ → Functional X 1} {T : Functional X 1}
    (hTs : ∀ j, IsIntegral 1 (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    IsMetricCurrent T ∧ IsIntegral 0 (boundarySucc T) := by
  exact ⟨metricCurrent_of_bounded_weak_limit (fun j => (hTs j).2.1)
    (fun j => (hTs j).1) (fun j => (hTs j).2.2.1) M N hM hN hlim,
    integral_zero_weak_closed (fun j => (hTs j).2.2) N hN (boundarySucc_weak_limit hlim)⟩

end CAT0Fillings.Slicing

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_NormalBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma NormalApprox.normal {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) :
    IsMetricCurrent T ∧ IsMetricCurrent (boundarySucc T) := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := h
  cases k with
  | zero =>
    obtain ⟨hT,hB⟩ := normal_one_of_bounded_integral_weak_limit hTs C C hM hN hlim
    exact ⟨hT,hB.1⟩
  | succ k => exact normal_of_bounded_integral_weak_limit hTs C C hM hN hlim

lemma NormalApprox.integral_zero {T : Functional X 0} (h : NormalApprox 0 T) :
    IsIntegral 0 T := by
  obtain ⟨C,Ts,hTs,hM,_,hlim⟩ := h
  exact integral_zero_weak_closed hTs C hM hlim

omit [Nonempty X] in
lemma superlevelSlice_offDomain [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (u : X → ℝ) (t : ℝ) (b : X → ℝ) (π : Fin k → X → ℝ)
    (hab : ¬Admissible b π) : superlevelSlice hT hB u t b π = 0 := by
  simp only [superlevelSlice,Pi.sub_apply,restrictCurrent,boundarySucc,ite_eq_right hab,sub_zero]

omit [Nonempty X] in
lemma superlevelSlice_testClass_continuous [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (t : ℝ) (K : ℕ) :
    Continuous (TestClass.eval (K := K) (superlevelSlice hT hB u t)) := by
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.measurable
  have hR := Foundations.IsMetricCurrent.testClass_continuous
    (restrictCurrent_isMetricCurrent hB hE) K
  have hQ := Foundations.IsMetricCurrent.boundary_testClass_continuous
    (restrictCurrent_isMetricCurrent hT hE) K
  convert hR.sub hQ using 1
  all_goals try with_reducible_and_instances rfl
  rfl

theorem measurableSet_slice_normalApprox {A : Type*} [MeasurableSpace A] {k : ℕ}
    (T : A → Functional X (k+1))
    (hT : ∀ a, IsMetricCurrent (T a)) (hB : ∀ a, IsMetricCurrent (boundarySucc (T a)))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) :
    MeasurableSet {p : ℝ × A | NormalApprox k (superlevelSlice (hT p.2) (hB p.2) u p.1)} := by
  apply measurableSet_normalApprox
  · intro p
    exact superlevelSlice_offDomain (hT p.2) (hB p.2) u p.1
  · intro p K
    exact superlevelSlice_testClass_continuous (hT p.2) (hB p.2) hu.continuous p.1 K
  · exact measurable_superlevelSlice_family T hT hB hTm hu

lemma NormalApprox.current {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) : IsMetricCurrent T := by
  cases k with
  | zero => exact h.integral_zero.1
  | succ k => exact h.normal.1

omit [Nonempty X] in
lemma normalApprox_of_integral [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsIntegral k T) : NormalApprox k T := by
  have hM : 0 ≤ mass T := mass_nonneg T
  have hN : 0 ≤ mass (boundary T) := mass_nonneg _
  exact normalApprox_of_weak_limit (fun _ => hT) ⟨mass T,hM⟩ ⟨mass (boundary T),hN⟩
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ _ => tendsto_const_nhds)

lemma normalApprox_zero (k : ℕ) : NormalApprox k (0 : Functional X k) :=
  normalApprox_of_integral (isIntegral_zero k)

noncomputable def normalSlice {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (u : X → ℝ) (t : ℝ) : Functional X k := by
  classical
  exact if NormalApprox k (superlevelSlice h.normal.1 h.normal.2 u t)
  then superlevelSlice h.normal.1 h.normal.2 u t else 0

lemma normalSlice_approx {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (u : X → ℝ) (t : ℝ) :
    NormalApprox k (normalSlice h u t) := by
  classical
  unfold normalSlice
  split_ifs with hh
  · exact hh
  · exact normalApprox_zero k

lemma measurable_normalSlice_family {A : Type*} [MeasurableSpace A] {k : ℕ}
    (T : A → Functional X (k+1)) (h : ∀ a, NormalApprox (k+1) (T a))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) (b : X → ℝ) (π : Fin k → X → ℝ) :
    Measurable (fun p : ℝ × A => normalSlice (h p.2) u p.1 b π) := by
  classical
  have hE := measurableSet_slice_normalApprox T (fun a => (h a).normal.1)
    (fun a => (h a).normal.2) hTm hu
  have hS := measurable_superlevelSlice_family T (fun a => (h a).normal.1)
    (fun a => (h a).normal.2) hTm hu b π
  simpa only [normalSlice,ite_apply,Pi.zero_apply] using
    (Measurable.ite hE hS (measurable_const (a := (0:ℝ))))

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

def NormalApproxAt (k C : ℕ) (T : Functional X k) : Prop :=
  ∃ Ts : ℕ → Functional X k, (∀ j, IsIntegral k (Ts j)) ∧
    (∀ j, mass (Ts j) ≤ C) ∧ (∀ j, mass (boundary (Ts j)) ≤ C) ∧
    ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))

omit [Nonempty X] in
lemma normalApproxAt_iff_closed [Nonempty X] {k C : ℕ} {T : Functional X k}
    (hOff : ∀ b π, ¬Admissible b π → T b π = 0)
    (hCont : ∀ K, Continuous (TestClass.eval (K := K) T)) :
    NormalApproxAt k C T ↔ currentCoordinates k T ∈ normalApproxClosed (X := X) k C := by
  classical
  constructor
  · rintro ⟨Ts,hTs,hM,hN,hlim⟩
    apply isClosed_closure.mem_of_tendsto (tendsto_pi_nhds.mpr fun ij => hlim _ _)
    exact Eventually.of_forall fun j => subset_closure ⟨Ts j,⟨hTs j,hM j,hN j⟩,rfl⟩
  · intro hC
    obtain ⟨ys,hys,hlim⟩ := mem_closure_iff_seq_limit.mp hC
    choose Ts hTs heq using hys
    refine ⟨Ts,fun j => (hTs j).1,fun j => (hTs j).2.1,fun j => (hTs j).2.2,?_⟩
    apply weak_limit_of_coordinate_limit (fun j => (hTs j).1) C C
      (fun j => (hTs j).2.1) (fun j => (hTs j).2.2) hOff hCont
    simpa only [heq] using hlim

lemma measurableSet_normalApproxAt {A : Type*} [MeasurableSpace A] {k C : ℕ}
    (T : A → Functional X k) (h : ∀ a, IsMetricCurrent (T a))
    (hm : ∀ b π, Measurable (fun a => T a b π)) :
    MeasurableSet {a | NormalApproxAt k C (T a)} := by
  have he : {a | NormalApproxAt k C (T a)} =
      (fun a => currentCoordinates k (T a)) ⁻¹' normalApproxClosed (X := X) k C := by
    ext a
    exact normalApproxAt_iff_closed (h a).offDomain
      (fun K => Foundations.IsMetricCurrent.testClass_continuous (h a) K)
  rw [he]
  exact isClosed_closure.measurableSet.preimage (Measurable.of_eval fun ij => hm _ _)

noncomputable def NormalApprox.cost {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) : ℕ := by
  classical
  exact Nat.find h

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma NormalApprox.cost_spec [BorelSpace X] [CompactSpace X] [Nonempty X]
    {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) : NormalApproxAt k h.cost T := by
  classical
  exact Nat.find_spec h

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma NormalApprox.cost_le [BorelSpace X] [CompactSpace X] [Nonempty X]
    {k C : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hC : NormalApproxAt k C T) : h.cost ≤ C := by
  classical
  exact Nat.find_min' h hC

lemma measurable_normalApprox_cost {A : Type*} [MeasurableSpace A] {k : ℕ}
    (T : A → Functional X k) (h : ∀ a, NormalApprox k (T a))
    (hm : ∀ b π, Measurable (fun a => T a b π)) :
    Measurable (fun a => (h a).cost) := by
  classical
  exact measurable_find h (fun C => measurableSet_normalApproxAt T (fun a => (h a).current) hm)

lemma NormalApprox.mass_le_cost {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) : mass T ≤ h.cost := by
  obtain ⟨Ts,hTs,hM,hN,hlim⟩ := h.cost_spec
  have hcur j : IsMetricCurrent (Ts j) := by cases k <;> exact (hTs j).1
  exact mass_le_of_bounded_weak_limit (h.cost : ℝ≥0) hcur hM (fun b π _ => hlim b π)

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma normalApproxAt_zero [BorelSpace X] [CompactSpace X] [Nonempty X]
    (k C : ℕ) : NormalApproxAt k C (0 : Functional X k) := by
  refine ⟨fun _ => 0,fun _ => isIntegral_zero k,?_,?_,fun _ _ => tendsto_const_nhds⟩
  · intro j
    change mass (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) ≤ (C:ℝ)
    rw [mass_zero]
    positivity
  · intro j
    change mass (boundary (0 : Functional X k)) ≤ (C:ℝ)
    cases k with
    | zero => change mass (fun (_ : X → ℝ) (_ : Fin 0 → X → ℝ) => 0) ≤ (C:ℝ); rw [mass_zero]; positivity
    | succ k => change mass (boundarySucc (fun (_ : X → ℝ) (_ : Fin (k+1) → X → ℝ) => 0)) ≤ (C:ℝ)
                rw [boundarySucc_zero,mass_zero]
                positivity

lemma NormalApprox.cost_zero {k : ℕ} (h : NormalApprox k (0 : Functional X k)) :
    h.cost = 0 := Nat.eq_zero_of_le_zero (h.cost_le (normalApproxAt_zero k 0))

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.BorelCoefficients
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k}
variable (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def levelClamp (c ε : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  max (c - ε) (min (c + ε) (u x))

end CAT0Fillings.BorelCoefficients
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_FullSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma NormalApprox.eq_zero_of_cost_zero {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hz : h.cost = 0) : T = 0 := by
  apply h.current.eq_zero_of_mass_eq_zero
  apply le_antisymm _ (mass_nonneg _)
  simpa only [hz,Nat.cast_zero] using h.mass_le_cost

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma NormalApprox.cost_congr [BorelSpace X] [CompactSpace X] [Nonempty X]
    {k : ℕ} {T U : Functional X k}
    (hT : NormalApprox k T) (hU : NormalApprox k U) (he : T = U) : hT.cost = hU.cost := by
  subst U
  rfl

lemma measurable_normalSlice_cost {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) {u : X → ℝ} (hu : BoundedLip u) :
    Measurable (fun t : ℝ => (normalSlice_approx h u t).cost) := by
  apply measurable_normalApprox_cost (normalSlice h u) (normalSlice_approx h u)
  intro b π
  have hm : Measurable (fun p : ℝ × Unit => normalSlice h u p.1 b π) :=
    measurable_normalSlice_family (fun _ : Unit => T) (fun _ => h)
      (fun _ _ => measurable_const) hu b π
  change Measurable ((fun p : ℝ × Unit => normalSlice h u p.1 b π) ∘ (fun t : ℝ => (t,())))
  exact hm.comp (measurable_id.prodMk measurable_const)

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

noncomputable def fullSlice : {k : ℕ} → {T : Functional X k} →
    NormalApprox k T → (Fin k → X → ℝ) → Euc k → Functional X 0
  | 0, T, _, _, _ => T
  | k+1, _, h, π, z => fullSlice (normalSlice_approx h (π 0) ((Prism.split k z).1))
      (Fin.tail π) ((Prism.split k z).2)

lemma fullSlice_approx : {k : ℕ} → {T : Functional X k} →
    (h : NormalApprox k T) → (π : Fin k → X → ℝ) → (z : Euc k) →
    NormalApprox 0 (fullSlice h π z)
  | 0, _, h, _, _ => h
  | k+1, _, h, π, z => fullSlice_approx (normalSlice_approx h (π 0) ((Prism.split k z).1))
      (Fin.tail π) ((Prism.split k z).2)

lemma measurable_fullSlice_family {k : ℕ} {A : Type*} [MeasurableSpace A]
    (T : A → Functional X k) (h : ∀ a, NormalApprox k (T a))
    (hm : ∀ b π, Measurable (fun a => T a b π))
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    (b : X → ℝ) (σ : Fin 0 → X → ℝ) :
    Measurable (fun p : A × Euc k => fullSlice (h p.1) π p.2 b σ) := by
  induction k generalizing A with
  | zero => exact (hm b σ).comp measurable_fst
  | succ k ih =>
    let S : ℝ × A → Functional X k := fun p => normalSlice (h p.2) (π 0) p.1
    have hS (p : ℝ × A) : NormalApprox k (S p) := normalSlice_approx (h p.2) (π 0) p.1
    have hSm b σ : Measurable (fun p : ℝ × A => S p b σ) :=
      measurable_normalSlice_family T h hm (hπ 0) b σ
    have hall : Measurable (fun p : (ℝ × A) × Euc k => fullSlice (hS p.1) (Fin.tail π) p.2 b σ) :=
      ih S hS hSm (Fin.tail π) (fun i => hπ i.succ)
    have hsplit : Measurable (fun p : A × Euc (k+1) => Prism.split k p.2) :=
      (Prism.split k).continuous.measurable.comp measurable_snd
    have hchange : Measurable (fun p : A × Euc (k+1) => (((Prism.split k p.2).1,p.1),(Prism.split k p.2).2)) :=
      (hsplit.fst.prodMk measurable_fst).prodMk hsplit.snd
    exact hall.comp hchange

lemma measurable_fullSlice {k : ℕ} {T : Functional X k} (h : NormalApprox k T)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    (b : X → ℝ) (σ : Fin 0 → X → ℝ) :
    Measurable (fun z => fullSlice h π z b σ) := by
  have hm : Measurable (fun p : Unit × Euc k => fullSlice h π p.2 b σ) :=
    measurable_fullSlice_family (fun _ : Unit => T) (fun _ => h) (fun _ _ => measurable_const) π hπ b σ
  change Measurable ((fun p : Unit × Euc k => fullSlice h π p.2 b σ) ∘ (fun z => ((),z)))
  exact hm.comp (measurable_const.prodMk measurable_id)

lemma measurable_fullSlice_cost {k : ℕ} {T : Functional X k} (h : NormalApprox k T)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) :
    Measurable (fun z => (fullSlice_approx h π z).cost) :=
  measurable_normalApprox_cost (fullSlice h π) (fullSlice_approx h π) (measurable_fullSlice h π hπ)

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_FullCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma NormalApprox.metric {k : ℕ} {T : Functional X k} (h : NormalApprox k T) : IsMetricCurrent T := by
  cases k with
  | zero => exact h.integral_zero.1
  | succ k => exact h.normal.1

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

abbrev coordinateMap {k : ℕ} (π : Fin k → X → ℝ) (x : X) : Euc k := WithLp.toLp 2 (fun i => π i x)

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_TestBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Filter MeasureTheory Set Metric Matrix
open scoped Topology NNReal BigOperators

noncomputable def differentialRow {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) : Fin n → ℝ :=
  fun j => L (EuclideanSpace.single j 1)

lemma differentialRow_dot {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (v : Fin n → ℝ) :
    differentialRow L ⬝ᵥ v = L (WithLp.toLp 2 v) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hrepr : b.repr (WithLp.toLp 2 v) = v := by ext j; simp [b]
  have hb : ∑ j, v j • EuclideanSpace.single j (1:ℝ) = WithLp.toLp 2 v := by
    convert b.sum_repr (WithLp.toLp 2 v) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,_root_.map_sum]
  simp only [differentialRow,map_smul,smul_eq_mul,dotProduct,mul_comm]

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_Measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

local instance instMeasurableSpaceMatrixFinReal_solutions {k : ℕ} : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) := borel _
local instance instBorelSpaceMatrixFinReal_solutions {k : ℕ} : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩

lemma measurable_matrix_inverse {E : Type*} [MeasurableSpace E] {k : ℕ}
    (P : E → Matrix (Fin k) (Fin k) ℝ) (hm : Measurable P) :
    Measurable (fun z => (P z)⁻¹) := by
  have hd : Measurable (fun z => (P z).det) := continuous_id.matrix_det.measurable.comp hm
  have ha : Measurable (fun z => (P z).adjugate) := continuous_id.matrix_adjugate.measurable.comp hm
  simp only [Matrix.inv_def,Ring.inverse_eq_inv]
  convert hd.inv.smul ha using 1
  all_goals try with_reducible_and_instances rfl

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_Current
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

structure ChartGeometry {T : Functional X k} (hT : IsMetricCurrent T) where
  chart : ℕ → IntegerChart X k
  field : ℕ → Euc k → Seminorm ℝ (Euc k)
  disjoint : Pairwise (fun i j => Disjoint (chart i).image (chart j).image)
  summable : Summable (fun i => mass (chart i).action)
  action : ∀ b π, T b π = ∑' i, (chart i).action b π
  measurable : ∀ i v, Measurable (fun z => field i z v)
  differential : ∀ i, ∀ᵐ z ∂volume.restrict (chart i).domain,
    (∀ hz : z ∈ (chart i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
      (chart i).domain (chart i).param (field i z) ⟨z,hz⟩) ∧
    (∀ u v, field i z (u+v)^2+field i z (u-v)^2 = 2*field i z u^2+2*field i z v^2) ∧
    (∀ v, field i z v = 0 ↔ v = 0)
  integrable : ∀ i, Integrable (fun z => |((chart i).multiplicity z : ℝ)| *Real.sqrt
    (polarizationMatrix (field i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
    (volume.restrict (chart i).domain)
  chart_mass : ∀ i, mass (chart i).action = ∫ z, |((chart i).multiplicity z : ℝ)| *Real.sqrt
    (polarizationMatrix (field i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
    ∂volume.restrict (chart i).domain
  measure_eq : MassMeasure.currentMassMeasure hT = Measure.sum (fun i =>
    (chart i).majorantMeasure (fun z => Real.sqrt
      (polarizationMatrix (field i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det))
  total_mass : mass T = ∑' i, mass (chart i).action
  current : ∀ i, IsMetricCurrent (chart i).action
  control : ∀ i, Controls (chart i).action ((chart i).majorantMeasure (fun z =>
    Real.sqrt (polarizationMatrix (field i z)
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det))

namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def gram (i : ℕ) (z : Euc k) : Matrix (Fin k) (Fin k) ℝ :=
  polarizationMatrix (q.field i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
noncomputable def density (i : ℕ) (z : Euc k) : ℝ :=
  |((q.chart i).multiplicity z : ℝ)| *Real.sqrt (q.gram i z).det

lemma density_integrable (i : ℕ) : Integrable (q.density i)
    (volume.restrict (q.chart i).domain) := q.integrable i
lemma density_summable : Summable (fun i => ∫ z, q.density i z
    ∂volume.restrict (q.chart i).domain) := by
  simpa only [density,gram,q.chart_mass] using q.summable

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_WeightedCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open MassMeasure

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma density_nonneg (i : ℕ) (z : Euc k) : 0 ≤ q.density i z :=
  mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

end ChartGeometry

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Chart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators Matrix.Norms.L2Operator

namespace CAT0Fillings

lemma inverse_quadratic_le {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ)
    (α : Fin k → ℝ) (hG : G.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (hα : ∀ v, |α ⬝ᵥ v| ≤ K * Real.sqrt (v ⬝ᵥ G.mulVec v)) :
    α ⬝ᵥ G⁻¹.mulVec α ≤ K^2 := by
  have hi : G.mulVec (G⁻¹.mulVec α) = α := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne'),
      Matrix.one_mulVec]
  have hq : 0 ≤ α ⬝ᵥ G⁻¹.mulVec α := hG.inv.posSemidef.dotProduct_mulVec_nonneg α
  have hh := hα (G⁻¹.mulVec α)
  rw [hi,dotProduct_comm (G⁻¹.mulVec α),abs_of_nonneg hq] at hh
  have hs := Real.sq_sqrt hq
  have hb : Real.sqrt (α ⬝ᵥ G⁻¹.mulVec α) ≤ K := by
    by_contra! hn
    have hp := mul_pos (lt_of_le_of_lt hK hn) (sub_pos.mpr hn)
    nlinarith
  nlinarith [Real.sqrt_nonneg (α ⬝ᵥ G⁻¹.mulVec α)]

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

local instance instMeasurableSpaceMatrixFinReal : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) := borel _

noncomputable def covector (i : ℕ) (u : X → ℝ) (z : Euc k) : Fin k → ℝ :=
  differentialRow (fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z)

noncomputable def normSq (i : ℕ) (u : X → ℝ) (z : Euc k) : ℝ :=
  q.covector i u z ⬝ᵥ (q.gram i z)⁻¹.mulVec (q.covector i u z)

noncomputable def duNorm (i : ℕ) (u : X → ℝ) (z : Euc k) : ℝ :=
  Real.sqrt (q.normSq i u z)

local instance instBorelSpaceMatrixFinReal_rfc7ba8_1 : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩
lemma measurable_gram (i : ℕ) : Measurable (q.gram i) := by
  have hh : Measurable (fun z a b => q.gram i z a b) :=
    measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b =>
      measurable_polarizationMatrix (q.field i)
        (EuclideanSpace.basisFun (Fin k) ℝ).toBasis (q.measurable i) a b
  have heq : _root_.borel (Fin k → Fin k → ℝ) = MeasurableSpace.pi :=
    BorelSpace.measurable_eq.symm
  change @Measurable (Euc k) (Fin k → Fin k → ℝ) _ (_root_.borel _) _
  rw [heq]
  exact hh

lemma aestronglyMeasurable_covector (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.covector i u)
      (volume.restrict (q.chart i).domain) := by
  obtain ⟨L,U,hL,_⟩ := (q.chart i).bilipschitz
  obtain ⟨R,hR,heR⟩ := ((q.chart i).scalar_lipschitzOn hL hu).extend_real
  have hm : Measurable (fun z => differentialRow (fderiv ℝ R z)) := by
    apply measurable_pi_iff.mpr
    intro j
    simp only [differentialRow]
    fun_prop
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume (q.chart i).borel hR heR] with z hz
  simp only [covector,hz]

lemma ae_normSq_bounds (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      0 ≤ q.normSq i u z ∧ q.normSq i u z ≤ (K : ℝ)^2 := by
  obtain ⟨L,U,hL,_⟩ := (q.chart i).bilipschitz
  have hb := MetricDifferentiation.ae_scalarOn_derivative_bound volume (q.chart i).borel hL
    ((q.differential i).mono fun z hz => hz.1) hu
  filter_upwards [q.differential i,hb] with z hz hbz
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  refine ⟨hG.inv.posSemidef.dotProduct_mulVec_nonneg _,?_⟩
  apply inverse_quadratic_le _ _ hG K.coe_nonneg
  intro v
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let w : Euc k := WithLp.toLp 2 v
  have hr : b.repr w = v := by ext j; simp [b,w]
  have hquad : v ⬝ᵥ (q.gram i z).mulVec v = (q.field i z w)^2 := by
    simpa only [gram,hr] using polarizationMatrix_quadratic b (q.field i z) hz.2.2 hz.2.1 w
  rw [hquad,Real.sqrt_sq (apply_nonneg (q.field i z) w)]
  have he : (q.chart i).scalar u = MetricDifferentiation.scalarOn (q.chart i).param u := by
    ext x
    rfl
  simpa only [covector,differentialRow_dot,he,w] using hbz w

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_HilbertAtlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def weightedMeasure (v : ℕ → Euc k → ℝ) : Measure X :=
  Measure.sum (fun i => densityPush (volume.restrict (q.chart i).domain)
    (q.chart i).paramExtended (fun z => q.density i z * v i z))

noncomputable def gradientMeasure (u : X → ℝ) : Measure X :=
  q.weightedMeasure (fun i => q.duNorm i u)
noncomputable def energyMeasure (u : X → ℝ) : Measure X :=
  q.weightedMeasure (fun i => q.normSq i u)

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace CAT0Fillings

local instance instMeasurableSpaceMatrixFinReal_solutions_1 {n : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
local instance instBorelSpaceMatrixFinReal_solutions_1 {n : ℕ} : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma matrix_posSemidef_closed {n : ℕ} :
    IsClosed {P : Matrix (Fin n) (Fin n) ℝ | P.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply IsClosed.inter
  · change IsClosed {P : Matrix (Fin n) (Fin n) ℝ | P.conjTranspose = P}
    exact isClosed_eq (by fun_prop) continuous_id
  · have hh (v : Fin n → ℝ) : IsClosed {P : Matrix (Fin n) (Fin n) ℝ |
        0 ≤ star v ⬝ᵥ P.mulVec v} := isClosed_le continuous_const (by fun_prop)
    have hs : {P : Matrix (Fin n) (Fin n) ℝ | ∀ v, 0 ≤ star v ⬝ᵥ P.mulVec v} =
        ⋂ v, {P : Matrix (Fin n) (Fin n) ℝ | 0 ≤ star v ⬝ᵥ P.mulVec v} := by
      ext P
      simp only [mem_iInter,mem_ofPred_eq]
    change IsClosed {P : Matrix (Fin n) (Fin n) ℝ | ∀ v, 0 ≤ star v ⬝ᵥ P.mulVec v}
    rw [hs]
    exact isClosed_iInter hh

lemma measurable_matrix_sqrt {n : ℕ} :
    Measurable (CFC.sqrt : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
  classical
  have hm : MeasurableSet {P : Matrix (Fin n) (Fin n) ℝ | 0 ≤ P} := by
    simpa only [Matrix.nonneg_iff_posSemidef] using (matrix_posSemidef_closed (n := n)).measurableSet
  have h := (CFC.continuousOn_sqrt (A := Matrix (Fin n) (Fin n) ℝ)).measurable_piecewise
    (g := fun _ => 0) continuousOn_const hm
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext P
  by_cases hp : 0 ≤ P
  · simp only [Set.piecewise,mem_ofPred_eq,hp,ite_true, if_true]
  · simp only [Set.piecewise,mem_ofPred_eq,hp,ite_false, if_false,CFC.sqrt_of_not_nonneg hp]

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def normalizedCovector (i : ℕ) (u : X → ℝ) (z : Euc n) : Euc n :=
  WithLp.toLp 2 ((CFC.sqrt (q.gram i z)⁻¹).mulVec (q.covector i u z))

lemma aestronglyMeasurable_normalizedCovector (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.normalizedCovector i u)
      (volume.restrict (q.chart i).domain) := by
  have hM := measurable_matrix_sqrt.comp (measurable_matrix_inverse _ (q.measurable_gram i))
  have hc : Continuous (fun r : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) =>
    (WithLp.toLp 2 (r.1.mulVec r.2) : Euc n)) := by fun_prop
  exact hc.comp_aestronglyMeasurable
    (hM.aestronglyMeasurable.prodMk (q.aestronglyMeasurable_covector i hu))

lemma ae_normalizedCovector_norm_sq (i : ℕ) (u : X → ℝ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      ‖q.normalizedCovector i u z‖^2 = q.normSq i u z := by
  filter_upwards [q.differential i] with z hz
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  rw [←real_inner_self_eq_norm_sq]
  simp only [normalizedCovector,EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  exact (dot_mulVec_sqrt _ hG.inv.posSemidef _).symm

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def coordinateMeasure (i : ℕ) : Measure (Euc n) :=
  (volume.restrict (q.chart i).domain).withDensity (fun z => ENNReal.ofReal (q.density i z))
noncomputable def atlasMeasure : Measure (ℕ × Euc n) :=
  Measure.sum (fun i => (q.coordinateMeasure i).map (Prod.mk i))

instance coordinateMeasure_finite (i : ℕ) : IsFiniteMeasure (q.coordinateMeasure i) :=
  isFiniteMeasure_withDensity_ofReal (q.density_integrable i).hasFiniteIntegral

lemma coordinateMeasure_total (i : ℕ) : (q.coordinateMeasure i).real univ =
    ∫ z, q.density i z ∂volume.restrict (q.chart i).domain := by
  rw [show (q.coordinateMeasure i).real univ = ∫ _ : Euc n, (1:ℝ) ∂q.coordinateMeasure i by simp]
  rw [coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i _),smul_eq_mul,mul_one]

instance atlasMeasure_finite : IsFiniteMeasure q.atlasMeasure := by
  apply finite_sum_measure_of_summable_total
  apply q.density_summable.congr
  intro i
  rw [←q.coordinateMeasure_total]
  simp only [measureReal_def,Measure.map_apply measurable_prodMk_left MeasurableSet.univ,preimage_univ]

noncomputable def gradientFunction (u : X → ℝ) (w : ℕ × Euc n) : Euc n :=
  q.normalizedCovector w.1 u w.2

lemma aestronglyMeasurable_gradientFunction {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.gradientFunction u) q.atlasMeasure := by
  apply aestronglyMeasurable_sum_measure_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).aestronglyMeasurable_map_iff.mpr
  exact (q.aestronglyMeasurable_normalizedCovector i hu).mono_ac
    (withDensity_absolutelyContinuous _ _)

lemma ae_gradientFunction_bound {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ w ∂q.atlasMeasure, ‖q.gradientFunction u w‖ ≤ K := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [q.ae_normalizedCovector_norm_sq i u,q.ae_normSq_bounds i hu] with z hz hb
  change ‖q.normalizedCovector i u z‖ ≤ K
  nlinarith [norm_nonneg (q.normalizedCovector i u z),K.coe_nonneg]

lemma memLp_gradientFunction {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    MemLp (q.gradientFunction u) 2 q.atlasMeasure :=
  MemLp.of_bound (q.aestronglyMeasurable_gradientFunction hu) K (q.ae_gradientFunction_bound hu)

noncomputable def gradient {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Lp (Euc n) 2 q.atlasMeasure := (q.memLp_gradientFunction hu).toLp _

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Atlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_gradient_eq {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ w ∂q.atlasMeasure, q.gradient hu w = q.normalizedCovector w.1 u w.2 :=
  (q.memLp_gradientFunction hu).coeFn_toLp

lemma ae_gradient_bound {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ w ∂q.atlasMeasure, ‖q.gradient hu w‖ ≤ K := by
  filter_upwards [q.ae_gradient_eq hu,q.ae_gradientFunction_bound hu] with w he hb
  rw [he]
  exact hb
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def atlasParam (w : ℕ × Euc n) : X := (q.chart w.1).paramExtended w.2
def atlasDomain : Set (ℕ × Euc n) := {w | w.2 ∈ (q.chart w.1).domain}

lemma measurable_atlasParam : Measurable q.atlasParam :=
  measurable_from_prod_countable_right (fun i => (q.chart i).measurable_paramExtended)

lemma map_atlasMeasure : q.atlasMeasure.map q.atlasParam = MassMeasure.currentMassMeasure hT := by
  rw [atlasMeasure,Measure.map_sum q.measurable_atlasParam.aemeasurable, q.measure_eq]
  congr 1
  funext i
  rw [Measure.map_map q.measurable_atlasParam measurable_prodMk_left]
  rfl

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_CyclePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings

lemma BoundedLip.memLp {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ] {u : X → ℝ}
    (hu : BoundedLip u) (p : ℝ≥0∞) : MemLp u p μ := by
  obtain ⟨K,hK⟩ := hu.1
  obtain ⟨B,hB⟩ := hu.2
  exact MemLp.of_bound hK.continuous.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_ClosedLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradient_add {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    q.gradient (hu.add hv) = q.gradient hu + q.gradient hv := by
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_add _ _).symm
  have hea := (q.memLp_gradientFunction (hu.add hv)).coeFn_toLp
  have heb := (q.memLp_gradientFunction hu).coeFn_toLp
  have hec := (q.memLp_gradientFunction hv).coeFn_toLp
  have he : q.gradientFunction (fun x => u x+v x) =ᵐ[q.atlasMeasure]
      fun w => q.gradientFunction u w+q.gradientFunction v w := by
    apply Measure.ae_sum_iff.mpr
    intro i
    apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_uniqueDiffWithinAt volume (q.chart i).domain,
      (q.chart i).ae_differentiableWithinAt_scalar hu,
      (q.chart i).ae_differentiableWithinAt_scalar hv] with z hz hdu hdv
    have hs : (q.chart i).scalar (fun x => u x+v x) =
        (q.chart i).scalar u+(q.chart i).scalar v := by
      funext z
      by_cases hz : z ∈ (q.chart i).domain <;> simp [IntegerChart.scalar,hz]
    change q.normalizedCovector i (fun x => u x+v x) z =
      q.normalizedCovector i u z+q.normalizedCovector i v z
    unfold normalizedCovector covector
    rw [hs,fderivWithin_add hz hdu hdv]
    have he : differentialRow (fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z +
        fderivWithin ℝ ((q.chart i).scalar v) (q.chart i).domain z) =
        differentialRow (fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z)+
        differentialRow (fderivWithin ℝ ((q.chart i).scalar v) (q.chart i).domain z) := rfl
    rw [he,Matrix.mulVec_add,WithLp.toLp_add]
  filter_upwards [hea,heb,hec,he] with w ha hb hc he
  change (q.gradient (hu.add hv)) w = (q.gradient hu) w+(q.gradient hv) w
  exact ha.trans (he.trans (congrArg₂ (·+·) hb.symm hc.symm))

lemma gradient_smul {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (c : ℝ) :
    q.gradient ((lipschitzWith_smul c).comp hu) = c • q.gradient hu := by
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_smul c _).symm
  have hea := (q.memLp_gradientFunction ((lipschitzWith_smul c).comp hu)).coeFn_toLp
  have heb := (q.memLp_gradientFunction hu).coeFn_toLp
  have he : q.gradientFunction (fun x => c • u x) =ᵐ[q.atlasMeasure]
      fun w => c • q.gradientFunction u w := by
    apply Measure.ae_sum_iff.mpr
    intro i
    apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_uniqueDiffWithinAt volume (q.chart i).domain,
      (q.chart i).ae_differentiableWithinAt_scalar hu] with z hz hdu
    have hs : (q.chart i).scalar (fun x => c • u x) = c • (q.chart i).scalar u := by
      funext z
      by_cases hz : z ∈ (q.chart i).domain <;> simp [IntegerChart.scalar,hz]
    change q.normalizedCovector i (fun x => c • u x) z = c • q.normalizedCovector i u z
    unfold normalizedCovector covector
    rw [hs,fderivWithin_const_smul hz hdu]
    have he : differentialRow (c • fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z) =
        c • differentialRow (fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z) := rfl
    rw [he,Matrix.mulVec_smul,WithLp.toLp_smul]
  filter_upwards [hea,heb,he] with w ha hb he
  change (q.gradient ((lipschitzWith_smul c).comp hu)) w = c • (q.gradient hu) w
  exact ha.trans (he.trans (congrArg (c • ·) hb.symm))

noncomputable def value {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  ((Foundations.boundedLip_of_lipschitz hu).memLp 2).toLp u

lemma value_add {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    value (hT := hT) (hu.add hv) = value hu + value hv :=
  MemLp.toLp_add _ _

lemma value_smul {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (c : ℝ) :
    value (hT := hT) ((lipschitzWith_smul c).comp hu) = c • value hu :=
  MemLp.toLp_const_smul c ((Foundations.boundedLip_of_lipschitz hu).memLp 2)

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Bivariate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
lemma lip_comp_memLp_finite [IsFiniteMeasure μ] {p : ℝ≥0∞} {f : α → E}
    {g : E → F} {K : ℝ≥0} (hg : LipschitzWith K g) (hf : MemLp f p μ) :
    MemLp (g ∘ f) p μ := by
  have h := ((hg.sub (LipschitzWith.const (g 0))).comp_memLp (by simp) hf).add (memLp_const (g 0))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Function.comp_def,Pi.add_apply,sub_add_cancel]
end CAT0Fillings.ClosedCalculus

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

include q in
lemma memLp_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) :
    MemLp (fun x => F (r x,f x)) 2 (MassMeasure.currentMassMeasure hT) := by
  let : IsFiniteMeasure (MassMeasure.currentMassMeasure hT) := by
    rw [←q.map_atlasMeasure]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact lip_comp_memLp_finite hF (MemLp.of_fst_snd
    ⟨((Foundations.boundedLip_of_lipschitz hr).memLp 2), (Lp.memLp f)⟩)

noncomputable def bivariateValue {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) : Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  (q.memLp_bivariate hr hF f).toLp (fun x => F (r x,f x))

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

abbrev GraphAmbient := WithLp 2
  ((Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) × (Lp (Euc n) 2 q.atlasMeasure))

noncomputable def graphPoint {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) : q.GraphAmbient :=
  WithLp.toLp 2 (value hu,q.gradient hu)

lemma graphPoint_add {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    q.graphPoint (hu.add hv) = q.graphPoint hu+q.graphPoint hv := by
  change WithLp.toLp 2 (value (hu.add hv),q.gradient (hu.add hv)) = _
  rw [value_add hu hv,q.gradient_add hu hv]
  exact WithLp.toLp_add 2 (value hu,q.gradient hu) (value hv,q.gradient hv)

lemma graphPoint_smul {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (c : ℝ) :
    q.graphPoint ((lipschitzWith_smul c).comp hu) = c • q.graphPoint hu := by
  change WithLp.toLp 2 (value ((lipschitzWith_smul c).comp hu),q.gradient ((lipschitzWith_smul c).comp hu)) = _
  rw [value_smul hu c,q.gradient_smul hu c]
  exact WithLp.toLp_smul 2 c (value hu,q.gradient hu)

noncomputable def lipschitzGraph : Submodule ℝ q.GraphAmbient where
  carrier := {P | ∃ (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u), P = q.graphPoint hu}
  zero_mem' := by
    refine ⟨fun x => (0:ℝ) • (0:ℝ),_,(lipschitzWith_smul (0:ℝ)).comp (LipschitzWith.const (0:ℝ)),?_⟩
    simpa only [zero_smul] using (q.graphPoint_smul (LipschitzWith.const (0:ℝ)) (0:ℝ)).symm
  add_mem' := by
    rintro P Q ⟨u,K,hu,rfl⟩ ⟨v,J,hv,rfl⟩
    exact ⟨_,_,hu.add hv,(q.graphPoint_add hu hv).symm⟩
  smul_mem' := by
    rintro c P ⟨u,K,hu,rfl⟩
    exact ⟨_,_,(lipschitzWith_smul c).comp hu,(q.graphPoint_smul hu c).symm⟩

noncomputable def closedGraph : Submodule ℝ q.GraphAmbient := q.lipschitzGraph.topologicalClosure

noncomputable abbrev Sobolev := q.closedGraph

noncomputable def valueProjection : q.GraphAmbient →L[ℝ] Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

noncomputable def gradientProjection : q.GraphAmbient →L[ℝ] Lp (Euc n) 2 q.atlasMeasure :=
  (ContinuousLinearMap.snd ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

@[simp] lemma valueProjection_graphPoint {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.valueProjection (q.graphPoint hu) = value hu := rfl
@[simp] lemma gradientProjection_graphPoint {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.gradientProjection (q.graphPoint hu) = q.gradient hu := rfl

lemma graphPoint_mem {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.graphPoint hu ∈ q.closedGraph :=
  subset_closure (show q.graphPoint hu ∈ q.lipschitzGraph from ⟨u,K,hu,rfl⟩)

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def inclusion : q.Sobolev →L[ℝ] Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  q.valueProjection.comp q.closedGraph.subtypeL

noncomputable def closedGradient : q.Sobolev →L[ℝ] Lp (Euc (k+1)) 2 q.atlasMeasure :=
  q.gradientProjection.comp q.closedGraph.subtypeL

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_CriticalNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory ENNReal
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def criticalNorm (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u : H) :=
  lpNorm (I u) (ENNReal.ofReal p) μ

noncomputable def criticalMass (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u : H) :=
  ∫ x, |(I u) x|^p ∂μ

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Constant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def lipSobolev {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) : q.Sobolev :=
  ⟨q.graphPoint hu,q.graphPoint_mem hu⟩

@[simp] lemma inclusion_lipSobolev {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.inclusion (q.lipSobolev hu) = value hu := rfl
@[simp] lemma closedGradient_lipSobolev {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.closedGradient (q.lipSobolev hu) = q.gradient hu := rfl

noncomputable def constant (c : ℝ) : q.Sobolev := q.lipSobolev (LipschitzWith.const c)

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_ClosedChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma atlas_preserving : MeasurePreserving q.atlasParam q.atlasMeasure
    (MassMeasure.currentMassMeasure hT) := ⟨q.measurable_atlasParam,q.map_atlasMeasure⟩

noncomputable def composeValue {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) : Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  (hF.sub (LipschitzWith.const (F 0))).compLp (by simp) f + q.inclusion (q.constant (F 0))

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_CriticalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter Metric TopologicalSpace
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {H E F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def energy (I : H →L[ℝ] E) (G : H →L[ℝ] F) (A B : ℝ) (u : H) : ℝ :=
  A*‖G u‖^2+B*‖I u‖^2

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_GroundProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def chordXi (o : X) (v : q.Sobolev) (κ β : ℝ) (z : ℕ × Euc (k+1)) : Euc (k+1) :=
  (κ*(q.inclusion v (q.atlasParam z))^(1+β)) • q.gradient (LipschitzWith.dist_right o) z+
    (κ*β*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β) • q.closedGradient v z

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_NonnegativeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (ρ : α → ℝ)
noncomputable def total : ℝ := ∫ x, ρ x ∂μ
end CAT0Fillings.ChordMeasure
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_RadialIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
noncomputable def completedExpression (o : X) (G : q.Sobolev) (z : ℕ × Euc (k+1)) : ℝ :=
  ((k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) z‖^2-
    (k+1:ℝ)/4*dist o (q.atlasParam z)^2)*q.inclusion G (q.atlasParam z)+
    dist o (q.atlasParam z)*inner ℝ (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient G z)
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_IntrinsicBV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations MassMeasure Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def intrinsicSliceControl (π : Fin (k+1) → X → ℝ) (K : ℝ≥0) (u : X → ℝ) :
    Measure (Euc (k+1)) :=
  (K^k) • Measure.map (fun w => coordinateMap π (q.atlasParam w))
    (q.atlasMeasure.withDensity (fun w => ENNReal.ofReal ‖q.gradientFunction u w‖))

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_ChartDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings

namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def lipToL2 : lipAlgebra (X := X) →ₗ[ℝ] Lp ℝ 2 μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp (lipAlgebra (X := X)).val.toLinearMap

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Slicing Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma coordinate_memLp (i : ℕ) {u : X → ℝ} (hu : Measurable u) (U : ℝ≥0)
    (hU : ∀ x, |u x| ≤ U) (p : ℝ≥0∞) :
    MemLp (fun z => u ((q.chart i).paramExtended z)) p (q.coordinateMeasure i) :=
  MemLp.of_bound (hu.comp (q.chart i).measurable_paramExtended).aestronglyMeasurable U
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hU ((q.chart i).paramExtended z))

noncomputable def coordinateL1 (i : ℕ) {u : X → ℝ} (hu : Measurable u) (U : ℝ≥0)
    (hU : ∀ x, |u x| ≤ U) : Lp ℝ 1 (q.coordinateMeasure i) :=
  (q.coordinate_memLp i hu U hU 1).toLp _

lemma indicator_bound (i : ℕ) {u : X → ℝ} {U : ℝ≥0} (hU : ∀ x, |u x| ≤ U) :
    ∀ x, |(q.chart i).image.indicator u x| ≤ U := by
  intro x
  by_cases hx : x ∈ (q.chart i).image
  · simpa only [indicator_of_mem hx] using hU x
  · simpa only [indicator_of_notMem hx,abs_zero] using U.coe_nonneg

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Mass_TestDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma integrable_l2 (f : Lp ℝ 2 μ) : Integrable (fun x => f x) μ :=
  MemLp.integrable (by norm_num) (Lp.memLp f)

lemma integral_abs_le_l2 (f : Lp ℝ 2 μ) :
    (∫ x, |f x| ∂μ) ≤ (μ.real univ)^(1/2:ℝ)*‖f‖ := by
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1:ℝ≥0∞) ≤ 2) (Lp.aestronglyMeasurable f)
  have hfi : Integrable (fun x => f x) μ := integrable_l2 μ f
  have heq : eLpNorm (fun x => f x) 1 μ = ENNReal.ofReal (∫ x, |f x| ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,ofReal_integral_eq_lintegral_ofReal hfi.abs
      (Eventually.of_forall fun _ => abs_nonneg _)]
    congr 1
    ext x
    simp only [Real.enorm_eq_ofReal_abs]
  rw [heq] at hh
  have hhfin : eLpNorm (fun x => f x) 2 μ * μ univ ^ (1 / (1:ℝ) - 1 / (2:ℝ)) ≠ ∞ := by
    apply ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  have hh' := ENNReal.toReal_mono (by simpa using hhfin) hh
  simp only [ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _),
    ENNReal.toReal_mul,ENNReal.toReal_one,ENNReal.toReal_ofNat,
    one_div,inv_one] at hh'
  rw [show (1:ℝ)-2⁻¹ = 1/2 by norm_num] at hh'
  simpa only [ENNReal.toReal_rpow,Lp.norm_def,measureReal_def,mul_comm] using hh'

noncomputable def l2ToL1Linear : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 1 μ where
  toFun f := (integrable_l2 μ f).toL1 f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(integrable_l2 μ (f+g)).coeFn_toL1,
      Lp.coeFn_add f g,Lp.coeFn_add ((integrable_l2 μ f).toL1 f)
        ((integrable_l2 μ g).toL1 g),
      (integrable_l2 μ f).coeFn_toL1,
      (integrable_l2 μ g).coeFn_toL1] with x h1 h2 h3 h4 h5
    simp only [h1,h2,h3,Pi.add_apply,h4,h5]
  map_smul' r f := by
    apply Lp.ext
    filter_upwards [(integrable_l2 μ (r • f)).coeFn_toL1,
      Lp.coeFn_smul r f,Lp.coeFn_smul r ((integrable_l2 μ f).toL1 f),
      (integrable_l2 μ f).coeFn_toL1] with x h1 h2 h3 h4
    simp only [h1,h2,h3,Pi.smul_apply,h4,RingHom.id_apply]

noncomputable def l2ToL1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
  (l2ToL1Linear μ).mkContinuous ((μ.real univ)^(1/2:ℝ)) (by
    intro f
    change ‖(integrable_l2 μ f).toL1 f‖ ≤ _
    rw [norm_toL1_integral_abs]
    exact integral_abs_le_l2 μ f)

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Mass_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace BorelCoefficients

variable {ι : Type*} [Fintype ι]
noncomputable def coefficientScale (v : ι → ℝ) : ℝ := max 1 (∑ i, |v i|)
noncomputable def normalizeCoefficients (v : ι → ℝ) (i : ι) : ℝ := v i/coefficientScale v

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Mass_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

abbrev CoefficientList (N : ℕ) :=
  {b : Fin N → C(X,ℝ) // (∀ i, BoundedLip (b i)) ∧ ∀ x, ∑ i, |b i x| ≤ 1}

instance coefficientList_nonempty (N : ℕ) : Nonempty (CoefficientList (X := X) N) := by
  refine ⟨⟨fun _ => 0,?_,?_⟩⟩
  · intro i
    exact ⟨⟨0,LipschitzWith.const 0⟩,0,by simp⟩
  · simp

end BorelCoefficients
end CAT0Fillings
end

end OAI
end


