-- Prove2me | Definitions.Def_OAIB3Sp000
-- name    : OAIB3Sp000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T17:45:00.794193+00:00
-- url     : https://prove2.me/theorems/8d6d06ed-1965-4437-8d8f-f53c0a3d494a
-- title:
--   Definitions bundle OAIB3Sp000 of the split of OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SphericalPerceptron.spherical_linear_field_formula`, carved from OpenAI's openai/math development (OpenAI, *Perceptron free energies and microscopic jamming exponents (result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 115 declarations of OpenAI's Lean: 86 definitions, 11 instances and 18 theorems. The definitions and types are `OAI.SphericalPerceptron.CascadeVisitShape`, `OAI.SphericalPerceptron.FiniteFieldModel.coupling`, `OAI.SphericalPerceptron.FiniteFieldModel.quantile`, `OAI.SphericalPerceptron.FiniteFieldModel.stationaryModel`, `OAI.SphericalPerceptron.RadialSpace`, `OAI.SphericalPerceptron.StableCascade`, `OAI.SphericalPerceptron.amplitudeCovarianceLevels`, `OAI.SphericalPerceptron.amplitudeSphereDual`, `OAI.SphericalPerceptron.amplitudeSphereLog`, `OAI.SphericalPerceptron.amplitudeSphereValue`, `OAI.SphericalPerceptron.canonicalBandRadiusWeight`, `OAI.SphericalPerceptron.canonicalCoordinateBandTotalE`, `OAI.SphericalPerceptron.canonicalCoordinateLog`, `OAI.SphericalPerceptron.canonicalCoordinatePotential`, `OAI.SphericalPerceptron.canonicalGaussianFreeValue`, `OAI.SphericalPerceptron.canonicalRadialDensity`, `OAI.SphericalPerceptron.canonicalRadialMass`, `OAI.SphericalPerceptron.cascadeHeatWord`, `OAI.SphericalPerceptron.cascadeLaw`, `OAI.SphericalPerceptron.cascadeLogFluctuationConstant`, `OAI.SphericalPerceptron.cascadeTotal`, `OAI.SphericalPerceptron.cascadeTotalE`, `OAI.SphericalPerceptron.coordinateDepthField`, `OAI.SphericalPerceptron.coordinateRootScale`, `OAI.SphericalPerceptron.countablePoissonIntensity`, `OAI.SphericalPerceptron.decoratedCascadeTransform`, `OAI.SphericalPerceptron.decoratedWeightedTotal`, `OAI.SphericalPerceptron.decoratedWeightedTotalE`, `OAI.SphericalPerceptron.entropicMean`, `OAI.SphericalPerceptron.expNegENNReal`, `OAI.SphericalPerceptron.extendedFieldExponents`, `OAI.SphericalPerceptron.fieldAmplitudes`, `OAI.SphericalPerceptron.fieldExponents`, `OAI.SphericalPerceptron.fieldL1`, `OAI.SphericalPerceptron.fieldVariances`, `OAI.SphericalPerceptron.finiteAmplitudeIncrement`, `OAI.SphericalPerceptron.finiteAmplitudeSphereDual`, `OAI.SphericalPerceptron.finiteAmplitudeSphereValue`, `OAI.SphericalPerceptron.finiteCascadeFractionalIntegrable`, `OAI.SphericalPerceptron.finiteCascadeLogRecursion` and 46 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SphericalField_Cascade_Bias`, `SphericalField_Cascade_CoordinateBounds`, `SphericalField_Cascade_Coordinates`, `SphericalField_Cascade_Decorated`, `SphericalField_Cascade_HeatWord`, `SphericalField_Cascade_LogFluctuations`, `SphericalField_Cascade_MarkedStable`, `SphericalField_Cascade_Recursion`, `SphericalField_Cascade_TotalLaw`, `SphericalField_Entropy_StationaryExistence`, `SphericalField_Entropy_StepIntegral`, `SphericalField_Entropy_StepStationary`, `SphericalField_Fields_BoundedPressure`, `SphericalField_Fields_FiniteModels`, `SphericalField_Fields_HeightCost`, `SphericalField_Fields_HeightPartition`, `SphericalField_Fields_HeightWord`, `SphericalField_Fields_Transport`, `SphericalField_Fields_UniformGrid`, `SphericalField_Fields_Words`, `SphericalField_Gaussian_Fractional`, `SphericalField_Heat_Backward`, `SphericalField_Heat_Entropic`, `SphericalField_Heat_Grid`, `SphericalField_Heat_Semigroup`, `SphericalField_Perceptron_TimeLaw`, `SphericalField_Poisson_DistinctMoments`, `SphericalField_Poisson_Intensity`, `SphericalField_Poisson_Laplace`, `SphericalField_Poisson_Mecke`, `SphericalField_Poisson_RandomMeasure`, `SphericalField_Poisson_StableMoments`, `SphericalField_Poisson_Superposition`, `SphericalField_Poisson_WeightedTotal`, `SphericalField_Quantiles_FiniteStationary`, `SphericalField_Quantiles_RoundGrid`, `SphericalField_Sphere_AmplitudeConvex`, `SphericalField_Sphere_AmplitudeLimit`, `SphericalField_Sphere_Bridge`, `SphericalField_Sphere_EntropicParameter`, `SphericalField_Sphere_FiniteUniform`, `SphericalField_Sphere_Heat`, `SphericalField_Sphere_Invariance`, `SphericalField_Sphere_Polar`, `SphericalField_Sphere_RadialBands`, `SphericalField_Sphere_RadialDensity`, `SphericalField_Sphere_Shell`.
--
--   **Imports.** It imports the published bundle `Def_SphericalField`.
--
--   **Imported by** (directly, in this split): the statements `OAI.SphericalPerceptron.FiniteFieldModel.pressure_bound`, `OAI.SphericalPerceptron.finiteAmplitudeSphereValue_tendsto`, `OAI.SphericalPerceptron.sphericalGridValue_compact_uniform` and `OAI.SphericalPerceptron.sphericalGridValue_tendsto`; the proofs of `OAI.SphericalPerceptron.FiniteFieldModel.pressure_bound`, `OAI.SphericalPerceptron.finiteAmplitudeSphereValue_tendsto`, `OAI.SphericalPerceptron.finiteSphericalFieldValue_all_depths_uniform`, `OAI.SphericalPerceptron.finiteSphericalFieldValue_pointwise_dual`, `OAI.SphericalPerceptron.sphericalGridValue_compact_uniform`, `OAI.SphericalPerceptron.sphericalGridValue_tendsto` and `OAI.SphericalPerceptron.spherical_linear_field_formula`.
-- source:
--   OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SphericalField.lean; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_SphericalField

section
-- module Solutions.OAIB3_Sph.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_Intensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def expNegENNReal (u : ℝ≥0∞) : ℝ := (EReal.exp (-(u : EReal))).toReal

lemma expNegENNReal_continuous : Continuous expNegENNReal := by
  have hc : Continuous (fun u : ℝ≥0∞ => EReal.exp (-(u : EReal))) := ENNReal.continuous_exp.comp continuous_coe_ennreal_ereal.neg
  rw [continuous_iff_continuousAt]
  intro u
  apply (ENNReal.continuousAt_toReal ?_).comp hc.continuousAt
  apply ne_of_lt
  exact lt_of_le_of_lt (EReal.exp_le_one_iff.mpr
    (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg u))) ENNReal.one_lt_top

@[simp] lemma expNegENNReal_top : expNegENNReal ⊤ = 0 := by simp [expNegENNReal]

def poissonLaplace {S : Type*} [MeasurableSpace S] (f : S → ℝ) (η : Measure S) : ℝ :=
  expNegENNReal (∫⁻ x, ENNReal.ofReal (f x) ∂η)

@[simp] lemma expNegENNReal_zero : expNegENNReal 0 = 1 := by simp [expNegENNReal]

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_Laplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def laplaceTest {ι : Type*} [Fintype ι] (a : ι → ℝ≥0) : (ι → ℝ≥0∞) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => expNegENNReal (∑ i, (a i : ℝ≥0∞) * x i), by
      apply expNegENNReal_continuous.comp
      exact continuous_finsetSum _ fun i _ =>
        (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (continuous_apply i)⟩

@[simp] lemma laplaceTest_zero {ι : Type*} [Fintype ι] :
    laplaceTest (0 : ι → ℝ≥0) = 1 := by
  ext x
  simp [laplaceTest]

def countablePoissonIntensity {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) : Measure S :=
  Measure.sum fun i => (r i : ℝ≥0∞) • ν i

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_RandomMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def logMarkShift {S : Type*} (F : S → ℝ) (p : ℝ × S) : ℝ × S :=
  (p.1 + F p.2,p.2)

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_Mecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def stableLaplaceConstant (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1-Real.exp (-Real.exp x)) ∂stableLogIntensity b

def stablePoissonTotal (η : Measure ℝ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η).toReal

lemma stablePoissonTotal_measurable : Measurable stablePoissonTotal :=
  ENNReal.measurable_toReal.comp (Measure.measurable_lintegral (by fun_prop))

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_Superposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
@[fun_prop] lemma measurable_measure_restrict {S : Type*} [MeasurableSpace S]
    {E : Set S} (hE : MeasurableSet E) : Measurable (fun η : Measure S => η.restrict E) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hE)

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_StableMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable

def stableJumpMomentE (r : ℝ) (η : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (r*x)) ∂η

@[fun_prop] lemma stableJumpMomentE_measurable (r : ℝ) : Measurable (stableJumpMomentE r) :=
  Measure.measurable_lintegral (by fun_prop)

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_DistinctMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable

instance stableLogIntensity_noAtoms (b : ℝ) : NullSingletonClass (stableLogIntensity b) := by
  unfold stableLogIntensity
  infer_instance

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_MarkedStable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable
section MarkedStable
variable {S : Type*} [MeasurableSpace S]

instance markedStableCountKernel_sfinite : IsSFiniteKernel (markedStableCountKernel (S := S)) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

end MarkedStable
end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_WeightedTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
def poissonWeightedTotal {S : Type*} [MeasurableSpace S] (F : S → ℝ)
    (η : Measure (ℝ × S)) : ℝ :=
  (∫⁻ p, ENNReal.ofReal (Real.exp (p.1+F p.2)) ∂η).toReal

end SphericalPerceptron

end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_TotalLaw
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

def StableCascade : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (Measure (ℝ×StableCascade n))

instance stableCascadeNonempty (n : ℕ) : Nonempty (StableCascade n) := by
  cases n with
  | zero => exact ⟨()⟩
  | succ n => exact ⟨(0 : Measure (ℝ×StableCascade n))⟩

def cascadeTotalE : (n : ℕ) → StableCascade n → ℝ≥0∞
  | 0, _ => 1
  | n+1, η => ∫⁻ p : ℝ×StableCascade n,
      ENNReal.ofReal (Real.exp p.1)*cascadeTotalE n p.2 ∂η

def cascadeTotal (n : ℕ) (η : StableCascade n) : ℝ := (cascadeTotalE n η).toReal

def cascadeLaw : (n : ℕ) → (Fin n → ℝ) → ProbabilityMeasure (StableCascade n)
  | 0, _ => ⟨Measure.dirac (),by exact Measure.dirac.isProbabilityMeasure⟩
  | n+1, z => ⟨poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod
      (cascadeLaw n (fun i => z i.succ) : Measure (StableCascade n))),by exact poissonRandomMeasureLaw_probability _⟩

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_Bias
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable

@[reducible] def CascadeVisitShape : ℕ → Type
  | 0 => ℕ
  | n+1 => List (CascadeVisitShape n)

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_Decorated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

def decoratedCascadeTransform {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) → X×DecoratedCascade S n → StableCascade n
  | 0, _, _ => ()
  | n+1, F, p => (markedStableCountKernel p.2).map (fun q : ℝ×(S×DecoratedCascade S n) =>
      (q.1+F 0 (p.1,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,q.2.1),q.2.2)))

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_LogFluctuations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

def decoratedWeightedTotalE {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) → X×DecoratedCascade S n → ℝ≥0∞
  | 0, _, _ => 1
  | n+1, F, p => ∫⁻ q : ℝ×(S×DecoratedCascade S n),
      ENNReal.ofReal (Real.exp (q.1+F 0 (p.1,q.2.1))) *
        decoratedWeightedTotalE step n (fun i => F i.succ) (step (p.1,q.2.1),q.2.2)
          ∂markedStableCountKernel p.2

def decoratedWeightedTotal {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ) (p : X×DecoratedCascade S n) : ℝ :=
      (decoratedWeightedTotalE step n F p).toReal

def fractionalLogMoment {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (b : ℝ) (f : X×S → ℝ) (x : X) : ℝ :=
  Real.log (∫ s, Real.exp (b*f (x,s)) ∂ν)/b

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_Recursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
def finiteCascadeLogRecursion {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (X → ℝ) → X → ℝ
  | 0, _, H => H
  | n+1, z, H => fractionalLogMoment ν (z 0)
      (fun p => finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step p))

def finiteCascadeShifts {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (X → ℝ) → Fin n → X×S → ℝ
  | 0, _, _ => Fin.elim0
  | n+1, z, H => Fin.cases
      (fun p => finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step p) -
        finiteCascadeLogRecursion ν step (n+1) z H p.1)
      (finiteCascadeShifts ν step n (fun i => z i.succ) H)

def finiteCascadeFractionalIntegrable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (H : X → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → Prop
  | 0, _ => True
  | n+1, z => (∀ x, Integrable (fun s => Real.exp (z 0*
      finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step (x,s)))) ν) ∧
        finiteCascadeFractionalIntegrable ν step H n (fun i => z i.succ)

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Gaussian_Fractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

def quadraticCascadePrecision (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => b
  | n+1, z => quadraticCascadePrecision σ b n (fun i => z i.succ)-z 0*(σ n)^2

def quadraticCascadeOffset (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, z => quadraticCascadeOffset σ b n (fun i => z i.succ)+
      (Real.log (quadraticCascadePrecision σ b n (fun i => z i.succ))-
        Real.log (quadraticCascadePrecision σ b (n+1) z))/(2*z 0)

def quadraticCascadeReciprocalSlope (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, z => quadraticCascadeReciprocalSlope σ b n (fun i => z i.succ)+
      (1/(quadraticCascadePrecision σ b n (fun i => z i.succ))-
        1/(quadraticCascadePrecision σ b (n+1) z))/(2*z 0)

def canonicalGaussianFreeValue (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ) (r b : ℝ) : ℝ :=
  -Real.log b/2 + quadraticCascadeOffset σ b n z+r/(2*quadraticCascadePrecision σ b n z)

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_CoordinateBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
def cascadeLogFluctuationConstant (n : ℕ) (z : Fin n → ℝ) : ℝ :=
  4*∫ η, (Real.log (cascadeTotal n η))^2 ∂cascadeLaw n z

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

def canonicalCoordinatePotential (d : ℕ) (b : ℝ) (x : Fin d → ℕ → ℝ) : ℝ :=
  ∑ i, (-Real.log b/2+(x i 0)^2/(2*b))

def canonicalCoordinateLog (d n : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (p : (Fin d → ℕ → ℝ)×DecoratedCascade (Fin d → ℝ) n) : ℝ :=
  Real.log (decoratedTerminalTotal (canonicalCoordinateStep d σ) (canonicalCoordinatePotential d b) n p /
    decoratedTerminalTotal (canonicalCoordinateStep d σ) (fun _ => 0) n p)

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_EntropicParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SphericalPerceptron

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

def entropicMean (p : ℝ) (X : Ω → ℝ) : ℝ :=
  ∫ t : ℝ in (0:ℝ)..1, deriv (cgf X μ) (p*t)

end
end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Heat_Entropic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

def gaussianEntropic (p σ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  entropicMean μ p (fun y => f (x+σ • y))

def gaussianEntropicParamConstant (L S : ℝ) : ℝ :=
  L^2*(∫ y : E, ‖y‖^2*Real.exp (L*S*‖y‖) ∂μ) /
    mgf (fun y : E => ‖y‖) μ (-(L*S))

end
end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Heat_Semigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def scaledStdGaussian (σ : ℝ) : Measure E := (stdGaussian E).map (σ • ·)

instance instIsProbabilityMeasureScaledStdGaussian (σ : ℝ) : IsProbabilityMeasure (scaledStdGaussian (E := E) σ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

end
end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Heat_Backward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

def gaussianBackward (μ : Measure E) : List (ℝ×ℝ) → (E → ℝ) → E → ℝ
  | [], f => f
  | (p,σ)::l, f => gaussianEntropic μ p σ (gaussianBackward μ l f)

end

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Perceptron_TimeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

instance instNullSingletonClassElemRealTimeTimeLaw : NullSingletonClass timeLaw := by
  rw [timeLaw_eq_volume]
  infer_instance

instance instIsProbabilityMeasureElemSpinHAddNatOfNatSphereRealUnitSphereLaw (N : ℕ) : IsProbabilityMeasure (unitSphereLaw (N + 1)) := by
  have : NeZero ((volume : Measure (Spin (N + 1))).toSphere) :=
    ⟨Measure.toSphere_ne_zero volume⟩
  unfold unitSphereLaw
  infer_instance

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_Invariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
section SphereInvariance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sphereIsometryMap (e : E ≃ₗᵢ[ℝ] E) (x : Metric.sphere (0 : E) 1) :
    Metric.sphere (0 : E) 1 := ⟨e x, by simp⟩

end SphereInvariance

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_RadialDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

abbrev RadialSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n+1))

def radialNormalizer (n : ℕ) : ℝ := ((2*Real.pi)^(((n+1 : ℕ) : ℝ)/2))⁻¹

def canonicalRadialDensity (n : ℕ) (b : ℝ) (x : RadialSpace n) : ℝ :=
  radialNormalizer n * Real.exp (-(b/2)*‖x‖^2)

def canonicalRadialMass (n : ℕ) (b : ℝ) : Measure (RadialSpace n) :=
  volume.withDensity (fun x => ENNReal.ofReal (canonicalRadialDensity n b x))

def normSquareBand (n : ℕ) (ε : ℝ) : Set (RadialSpace n) :=
  {x | ((n+1 : ℕ) : ℝ)*(1-ε) ≤ ‖x‖^2 ∧ ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1+ε)}

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_RadialBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

def sphericalExp (n : ℕ) (z : Spin (n+1)) (r : ℝ) : ℝ :=
  ∫ u : Metric.sphere (0 : Spin (n+1)) 1, Real.exp (r * inner ℝ z (u:Spin (n+1))) ∂unitSphereLaw (n+1)

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_Polar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

section Polar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def normalizedAngular : Measure (Metric.sphere (0:E) 1) :=
  (μ.toSphere univ)⁻¹ • μ.toSphere

def haarRadiusMeasure : Measure (Ioi (0:ℝ)) :=
  μ.toSphere univ • Measure.volumeIoiPow (Module.finrank ℝ E - 1)

end Polar

def canonicalBandRadiusWeight (n : ℕ) (b ε : ℝ) : ℝ → ℝ≥0∞ :=
  {r : ℝ | ((n+1:ℕ):ℝ)*(1-ε) ≤ r^2 ∧ r^2 ≤ ((n+1:ℕ):ℝ)*(1+ε)}.indicator
    (fun r => ENNReal.ofReal (radialNormalizer n * Real.exp (-(b/2)*r^2)))

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_Bridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

instance coordinateCascadeLaw_probability (d k : ℕ) (z : Fin k → ℝ) (r : ℝ≥0) :
    IsProbabilityMeasure (coordinateCascadeLaw d k z r) := by
  unfold coordinateCascadeLaw
  infer_instance

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_Shell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

def canonicalCoordinateBandTotalE (n k : ℕ) (σ : ℕ → ℝ) (b ε : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ≥0∞ :=
  ∫⁻ x in normSquareBand n ε,
    decoratedFieldFactor (n+1) (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k p x ∂canonicalRadialMass n b

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_AmplitudeConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

def coordinateRootScale (d k : ℕ) (r : ℝ)
    (p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k) :
    (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k := ((fun i => r*p.1 i),p.2)

def amplitudeSphereLog (n k : ℕ) (σ : ℕ → ℝ) (r : ℝ)
    (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ :=
  coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) ((fun i _ => r*p.1 i),p.2)/(n+1:ℕ)

def amplitudeSphereValue (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ) (r : ℝ) : ℝ :=
  ∫ p, amplitudeSphereLog n k σ r p ∂coordinateCascadeLaw (n+1) k z 1

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_Heat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

def logSphericalExp (n : ℕ) (R : ℝ) (x : Spin (n+1)) : ℝ :=
  Real.log (sphericalExp n x R)

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_HeatWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

def cascadeHeatWord (σ : ℕ → ℝ) : (k : ℕ) → (Fin k → ℝ) → List (ℝ×ℝ)
  | 0, _ => []
  | k+1, z => (z 0,σ k)::cascadeHeatWord σ k (fun i => z i.succ)

def coordinateDepthField (d j : ℕ) (x : Fin d → ℕ → ℝ) : Spin d :=
  WithLp.toLp 2 (fun i => x i j)

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Entropy_StepStationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

def stepLogRatios : (k : ℕ) → (Fin (k+1) → ℝ) → (Fin k → ℝ) → ℝ
  | 0, _, _ => 0
  | k+1, D, z => stepLogRatios k (fun i => D i.succ) (fun i => z i.succ)+
      (Real.log (D 0)-Real.log (D 1))/(2*z 0)

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Entropy_StepIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

def weightedStepTail {I : Type*} [Fintype I] (w : I → ℝ) (q : I → ℝ) (t : ℝ) : ℝ :=
  ∑ i, w i*(1-max (q i) t)

def weightedStepA {I : Type*} [Fintype I] (w q : I → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..r, 1/(weightedStepTail w q t)^2

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Entropy_StationaryExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

def stepTailSum {k : ℕ} (v : Fin k → ℝ) (i : Fin (k+1)) : ℝ :=
  ∑ j : Fin k, if i ≤ j.castSucc then v j else 0

def finitePrecisionShift {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  stepTailSum (fun i => 2*z i*(h i.succ-h i.castSucc))

def finitePrecisionTail {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (b : ℝ) (i : Fin (k+1)) : ℝ := (b-finitePrecisionShift z h i)⁻¹

def finiteOverlapIncrement {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (b : ℝ) (i : Fin k) : ℝ :=
  2*(h i.succ-h i.castSucc)*finitePrecisionTail z h b i.castSucc*finitePrecisionTail z h b i.succ

def finiteStationarityMass {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ) (b : ℝ) : ℝ :=
  2*h 0*(finitePrecisionTail z h b 0)^2+(∑ i, finiteOverlapIncrement z h b i)+
    finitePrecisionTail z h b (Fin.last k)

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Heat_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianGrid (N : ℕ) (p v : Fin N → ℝ) (f : E → ℝ) : E → ℝ :=
  gaussianBackward (stdGaussian E) (List.ofFn fun i => (p i,Real.sqrt (v i))) f

end

def gridVariance {N : ℕ} (l : List (Fin N×ℝ)) (i : Fin N) : ℝ :=
  (l.map fun c => if c.1=i then c.2 else 0).sum

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_AmplitudeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

def amplitudeCovarianceLevels (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) (i : Fin (k+1)) : ℝ :=
  (r^2+stepTailSum (fun j : Fin k => (σ (k-1-j.val))^2) 0-
    stepTailSum (fun j : Fin k => (σ (k-1-j.val))^2) i)/2

def amplitudeSphereDual {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (σ : ℕ → ℝ) (r : ℝ) : ℝ :=
  sInf (finiteSphericalDualValues w (amplitudeCovarianceLevels k σ r) hw hw1)+
    amplitudeCovarianceLevels k σ r (Fin.last k)

def finiteAmplitudeIncrement (k : ℕ) (a : Fin (k+1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < k then a (⟨j,hj⟩ : Fin k).castSucc else 0

def finiteAmplitudeSphereValue (n k : ℕ) (w : Fin (k+1) → ℝ) (a : Fin (k+1) → ℝ) : ℝ :=
  amplitudeSphereValue n k (finiteAmplitudeIncrement k a) (stepCumulative w) (a (Fin.last k))

def finiteAmplitudeSphereDual {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (a : Fin (k+1) → ℝ) : ℝ :=
  amplitudeSphereDual w hw hw1 (finiteAmplitudeIncrement k a) (a (Fin.last k))

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_FiniteUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

def fieldAmplitudes (k : ℕ) (h : Fin (k+1) → ℝ) (i : Fin (k+1)) : ℝ :=
  if i.val < k then stepFieldIncrement k h i.val else Real.sqrt (2*h 0)

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_Words
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def fieldVariances (k : ℕ) (h : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  Fin.cases (2*h 0) (fun i => 2*(h i.succ-h i.castSucc))

def fieldExponents {k : ℕ} (w : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  Fin.cases 0 (stepCumulative w)

def sphericalHeatValue (n : ℕ) (l : List (ℝ×ℝ)) : ℝ :=
  gaussianBackward (stdGaussian (Spin (n+1))) l
    (logSphericalExp n (Real.sqrt (n+1:ℕ))) 0/(n+1:ℕ)-(l.map fun c => c.2^2).sum/2

def varianceLevels {k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin (k+1)) : ℝ :=
  (∑ j, if j ≤ i then v j else 0)/2

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_UniformGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def uniformWeights (k : ℕ) : Fin (k+1) → ℝ := fun _ => 1/(k+1:ℕ)
def uniformExponents (k : ℕ) (i : Fin (k+2)) : ℝ := (i:ℕ)/(k+1:ℕ)

lemma uniformWeights_pos (k : ℕ) (i : Fin (k+1)) : 0 < uniformWeights k i := by
  unfold uniformWeights
  positivity

lemma uniformWeights_sum (k : ℕ) : ∑ i, uniformWeights k i=1 := by
  simp only [uniformWeights,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,one_div]
  exact mul_inv_cancel₀ (by positivity)

def sphericalGridValue (n k : ℕ) (v : Fin (k+2) → ℝ) : ℝ :=
  sphericalHeatValue n (List.ofFn fun i => (uniformExponents k i,Real.sqrt (v i)))

def sphericalGridDual (k : ℕ) (v : Fin (k+2) → ℝ) : ℝ :=
  sInf (finiteSphericalDualValues (uniformWeights k) (varianceLevels (fun i => v i.castSucc))
    (fun i => (uniformWeights_pos k i).le) (uniformWeights_sum k))

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_HeightPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def heightIndex {d : ℕ} (h : Fin (d+1) → ℝ) (t : ℝ) : Fin (d+2) :=
  ⟨(Finset.univ.filter (fun r => h r < t)).card,by
    have H := Finset.card_le_card (Finset.filter_subset (fun r => h r < t) Finset.univ)
    simp only [Finset.card_univ,Fintype.card_fin] at H
    omega⟩

def heightVariances {K : ℕ} (z : Fin (K+1) → ℝ) (j : Fin K) : ℝ :=
  2*(z j.succ-z j.castSucc)

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_HeightWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def extendedFieldExponents {d : ℕ} (w : Fin (d+1) → ℝ) (i : Fin (d+2)) : ℝ :=
  ∑ r, if r.castSucc < i then w r else 0

def finiteFieldCDFLeft {d : ℕ} (w h : Fin (d+1) → ℝ) (t : ℝ) : ℝ :=
  ∑ r, if h r < t then w r else 0

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_HeightCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def heightIndicator (r t : ℝ) : ℝ := if r < t then 1 else 0

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def sphericalContinuityConstant (n : ℕ) (H : ℝ) : ℝ :=
  2*gaussianEntropicParamConstant (stdGaussian (Spin (n+1)))
    |Real.sqrt (n+1:ℕ)| (Real.sqrt (2*H))/(n+1:ℕ)

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_FiniteModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma integral_finite_label {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (a : Time → I) (ha : Measurable a) (F : I → ℝ) :
    (∫ u, F (a u) ∂timeLaw)=∑ i, timeLaw.real (a ⁻¹' {i})*F i := by
  classical
  have he (u : Time) : F (a u)=∑ i, (if a u=i then F i else 0) := by simp
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    change (∫ u, (a ⁻¹' {i}).indicator (fun _ => F i) u ∂timeLaw)=_
    rw [integral_indicator (ha (measurableSet_singleton i)),integral_const]
    simp only [Measure.restrict_apply_univ,smul_eq_mul,Measure.real]
  · intro i _
    exact (integrable_const (F i)).indicator (ha (measurableSet_singleton i))

lemma FiniteFieldModel.weight_pos {f : Time → ℝ} (M : FiniteFieldModel f) (i : Fin (M.depth+1)) :
    0 < M.weight i := M.positive i

lemma FiniteFieldModel.weight_sum {f : Time → ℝ} (M : FiniteFieldModel f) : ∑ i, M.weight i=1 := by
  have h := integral_finite_label M.label M.measurable_label (fun _ => 1)
  simpa [FiniteFieldModel.weight] using h.symm

def FiniteFieldModel.coupling {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (a : Fin (M.depth+1)×Fin (N.depth+1)) : ℝ :=
  timeLaw.real ((fun u => (M.label u,N.label u)) ⁻¹' {a})

lemma FiniteFieldModel.values_mem {f : Time → ℝ} (M : FiniteFieldModel f)
    {H : ℝ} (hf : ∀ᵐ u ∂timeLaw, f u ∈ Icc (0:ℝ) H) (i : Fin (M.depth+1)) :
    M.value i ∈ Icc (0:ℝ) H := by
  have hi : timeLaw (M.label ⁻¹' {i}) ≠ 0 := by
    intro hi
    have hp := M.positive i
    change 0 < (timeLaw (M.label ⁻¹' {i})).toReal at hp
    rw [hi] at hp
    simp at hp
  have hne : ∃ u, M.label u=i ∧ M.value (M.label u) ∈ Icc (0:ℝ) H := by
    by_contra! hn
    have hzero : ∀ᵐ u ∂timeLaw, u ∉ M.label ⁻¹' {i} := by
      filter_upwards [M.agrees,hf] with u hu hv
      intro hm
      exact hn u hm (hu ▸ hv)
    exact hi (by simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hzero)
  obtain ⟨u,hu,hv⟩ := hne
  simpa [hu] using hv

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_BoundedPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def fieldL1 (f g : Time → ℝ) : ℝ := ∫ u, |f u-g u| ∂timeLaw

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Quantiles_FiniteStationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def FiniteFieldModel.quantile {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B ≤ 1) :
    Fin (M.depth+1) → Time := fun i => ⟨M.value i,
      (M.values_mem (ae_of_all _ fun u => ⟨q.nonneg u,q.le_bound u⟩) i).1,
      (M.values_mem (ae_of_all _ fun u => ⟨q.nonneg u,q.le_bound u⟩) i).2.trans hB⟩

def FiniteFieldModel.stationaryModel {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B < 1) :
    FiniteFieldModel (q.stationary hB) where
  depth := M.depth
  value := fun i => quantileA (q.toQuantile hB.le) (M.value i)/2
  label := M.label
  measurable_label := M.measurable_label
  positive := M.positive
  monotone_value := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply quantileA_mono _ (q.toQuantile_measurable hB.le) hB (ae_of_all _ q.le_bound)
      (M.values_mem (ae_of_all _ fun u => ⟨q.nonneg u,q.le_bound u⟩) i)
      (M.values_mem (ae_of_all _ fun u => ⟨q.nonneg u,q.le_bound u⟩) j)
    exact M.monotone_value hij
  agrees := by
    filter_upwards [M.agrees] with u hu
    change quantileA (q.toQuantile hB.le) (M.value (M.label u))/2=quantileA (q.toQuantile hB.le) (q u)/2
    rw [hu]

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Quantiles_RoundGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def gridFloor (k : ℕ) (p : Time) : Fin (k+2) :=
  ⟨Nat.floor ((k+1:ℕ)*(p:ℝ)),by
    have hs : (k+1:ℕ)*(p:ℝ) ≤ (k+1:ℕ) := by nlinarith [p.2.2]
    have h : Nat.floor ((k+1:ℕ)*(p:ℝ)) ≤ k+1 := by
      exact Nat.floor_le_of_le hs
    omega⟩

def gridCeil (k : ℕ) (p : Time) : Fin (k+2) :=
  ⟨Nat.ceil ((k+1:ℕ)*(p:ℝ)),by
    have hs : (k+1:ℕ)*(p:ℝ) ≤ (k+1:ℕ) := by nlinarith [p.2.2]
    have h := Nat.ceil_le.mpr hs
    omega⟩

end SphericalPerceptron
end
end

end OAI
end


