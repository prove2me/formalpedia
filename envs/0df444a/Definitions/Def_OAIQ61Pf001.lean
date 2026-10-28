-- Prove2me | Definitions.Def_OAIQ61Pf001
-- name    : OAIQ61Pf001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:58:38.543003+00:00
-- url     : https://prove2.me/theorems/173b970e-c84b-483d-a961-56131add47be
-- title:
--   Definitions bundle OAIQ61Pf001 of the split of OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 39 definitions, 2 instances and 14 theorems. The definitions and types are `OAI.SphericalPerceptronFreeEnergy.orderedLevelCode`, `OAI.SphericalPerceptronFreeEnergy.paddedControlWeights`, `OAI.SphericalPerceptronFreeEnergy.pairMarkPower`, `OAI.SphericalPerceptronFreeEnergy.parameterMarkStep`, `OAI.SphericalPerceptronFreeEnergy.patternExtend`, `OAI.SphericalPerceptronFreeEnergy.planeSkew`, `OAI.SphericalPerceptronFreeEnergy.poissonRealMean`, `OAI.SphericalPerceptronFreeEnergy.poissonWeightedTotal`, `OAI.SphericalPerceptronFreeEnergy.quadraticBoxPenalty`, `OAI.SphericalPerceptronFreeEnergy.replaceIndex`, `OAI.SphericalPerceptronFreeEnergy.replicaMean`, `OAI.SphericalPerceptronFreeEnergy.resampleGaussianCoordinate`, `OAI.SphericalPerceptronFreeEnergy.restorationReplicaTest`, `OAI.SphericalPerceptronFreeEnergy.rightCoefficients`, `OAI.SphericalPerceptronFreeEnergy.scalarFrontMatrixTest`, `OAI.SphericalPerceptronFreeEnergy.secondPairMark`, `OAI.SphericalPerceptronFreeEnergy.shiftBCF`, `OAI.SphericalPerceptronFreeEnergy.skewFlow`, `OAI.SphericalPerceptronFreeEnergy.sourceFieldPolynomial`, `OAI.SphericalPerceptronFreeEnergy.sourcePenaltyWeight`, `OAI.SphericalPerceptronFreeEnergy.sourceStepFieldCap`, `OAI.SphericalPerceptronFreeEnergy.sphereKernel`, `OAI.SphericalPerceptronFreeEnergy.sphereTail`, `OAI.SphericalPerceptronFreeEnergy.stableJumpMomentE`, `OAI.SphericalPerceptronFreeEnergy.stablePoissonTotal`, `OAI.SphericalPerceptronFreeEnergy.stepBoundaryWeights`, `OAI.SphericalPerceptronFreeEnergy.stepLogRatios`, `OAI.SphericalPerceptronFreeEnergy.triangleConstraints`, `OAI.SphericalPerceptronFreeEnergy.tripleIndex`, `OAI.SphericalPerceptronFreeEnergy.tripleLabels`, `OAI.SphericalPerceptronFreeEnergy.uniformExponents`, `OAI.SphericalPerceptronFreeEnergy.uniformWeights`, `OAI.SphericalPerceptronFreeEnergy.uniqueEvent`, `OAI.SphericalPerceptronFreeEnergy.upperRoundedTrial`, `OAI.SphericalPerceptronFreeEnergy.varianceLevels`, `OAI.SphericalPerceptronFreeEnergy.weightedCDF`, `OAI.SphericalPerceptronFreeEnergy.weightedControlCoefficient`, `OAI.SphericalPerceptronFreeEnergy.weightedStepA`, `OAI.SphericalPerceptronFreeEnergy.weightedStepTail`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `Perceptron_Cascade_CascadeParameters`, `Perceptron_Cascade_PoissonDensityDerivative`, `Perceptron_Cascade_PoissonWeightedTotal`, `Perceptron_Cascade_StableCascade`, `Perceptron_Cascade_WeightedCDF`, `Perceptron_Cavity_FreshLogRatio`, `Perceptron_Control_StepControl`, `Perceptron_Control_StepControlTail`, `Perceptron_Interpolation_FieldArray`, `Perceptron_Interpolation_OverlapArray`, `Perceptron_Interpolation_PerturbationContact`, `Perceptron_Pressure_PatternMatrices`, `Perceptron_Sphere_CoordinateContact`, `Perceptron_Sphere_SphereIsometryMap`, `Perceptron_Sphere_SphereKernel`, `Perceptron_Variational_CountableGaussianResampling`, `Perceptron_Variational_CouplingKernel`, `Perceptron_Variational_CovarianceMatrix`, `Perceptron_Variational_FieldWord`, `Perceptron_Variational_GaussianCovarianceDerivative`, `Perceptron_Variational_GlobalContact`, `Perceptron_Variational_HeatTilt`, `Perceptron_Variational_LabelPairTestValue`, `Perceptron_Variational_OrderedCode`, `Perceptron_Variational_RestorationMoments`, `Perceptron_Variational_RoundedMarkedReference`, `Perceptron_Variational_StableLaplaceConstant`, `Perceptron_Variational_StepEntropy`, `Perceptron_Variational_StepStationary`, `Perceptron_Variational_TripleIndex`, `Perceptron_Variational_UniformGrid`.
--
--   **Imports.** It imports the published bundle `Def_PerceptronFreeEnergy`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ61Pf002`; the statement `OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists`.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_PerceptronFreeEnergy

section
-- module Solutions.OAIQ061_PF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
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
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLaplaceConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def stablePoissonTotal (η : Measure ℝ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η).toReal

lemma stablePoissonTotal_measurable : Measurable stablePoissonTotal :=
  ENNReal.measurable_toReal.comp (Measure.measurable_lintegral (by fun_prop))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_PoissonWeightedTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
@[fun_prop] lemma measurable_measure_restrict {S : Type*} [MeasurableSpace S]
    {E : Set S} (hE : MeasurableSet E) : Measurable (fun η : Measure S => η.restrict E) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hE)

def poissonWeightedTotal {S : Type*} [MeasurableSpace S] (F : S → ℝ)
    (η : Measure (ℝ × S)) : ℝ :=
  (∫⁻ p, ENNReal.ofReal (Real.exp (p.1+F p.2)) ∂η).toReal

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder

open TopologicalSpace

open scoped Polynomial

def upperRoundedTrial (m : Trial) (n : ℕ) : Trial where
  toFun := fun t => (⌈((n+1 : ℕ) : ℝ)*m t⌉₊ : ℝ) / (n+1 : ℕ)
  monotone := by
    intro s t hst
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_left (m.monotone hst) (by positivity))
  measurable :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (Nat.measurable_ceil.comp (measurable_const.mul m.measurable))).div_const _
  nonneg := by intro t; positivity
  le_one := by
    intro t
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (Nat.ceil_le.mpr (show (((n+1 : ℕ) : ℝ)*m t) ≤ ((n+1 : ℕ) : ℝ) by
      nlinarith [m.le_one t]))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereIsometryMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

section RotationCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def skewFlow (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (t : ℝ) : E ≃ₗᵢ[ℝ] E := by
  letI : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  exact Unitary.linearIsometryEquiv ⟨NormedSpace.exp (t • A),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
      rw [skewAdjoint.mem_iff] at hA ⊢
      simp [hA])⟩

variable [MeasurableSpace E] [BorelSpace E]

noncomputable def planeSkew (a y : E) : E →L[ℝ] E :=
  InnerProductSpace.rankOne ℝ a y - InnerProductSpace.rankOne ℝ y a

end RotationCalculus

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

def shiftBCF (f : ℝ →ᵇ ℝ) (a : ℝ) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨fun x => x+a,by fun_prop⟩

@[simp] lemma shiftBCF_apply (f : ℝ →ᵇ ℝ) (a x : ℝ) : shiftBCF f a x = f (x+a) := rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_StableCascade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
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

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CascadeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {P X S : Type} [MeasurableSpace P] [MeasurableSpace X] [MeasurableSpace S]

def parameterMarkStep (step : X×S → X) : (P×X)×S → P×X :=
  fun a => (a.1.1,step (a.1.2,a.2))

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_PoissonDensityDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

def poissonRealMean (F : ℕ→ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t)*(∑' n, t^n/(n.factorial:ℝ)*F n)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def uniqueEvent {Ω ι : Type*} (A : ι → Set Ω) (i : ι) : Set Ω :=
  {ω | ω ∈ A i ∧ ∀ j, j ≠ i → ω ∉ A j}

def replaceIndex {n : ℕ} (p : Fin n) (j : ℕ) (a : Fin n) : ℕ :=
  if a = p then j else a.val

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_PatternMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def tripleLabels (n : ℕ) (i : Fin n) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩

open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def replicaMean {n : ℕ} (v : Fin n → H) : H := (n : ℝ)⁻¹ • ∑ i, v i

def triangleConstraints (a b c t : ℝ) (k l : Fin 3) : Set ℝ :=
  if k = l then Iio t
  else if (k = 0 ∧ l = 1) ∨ (k = 1 ∧ l = 0) then Iio a
  else if (k = 0 ∧ l = 2) ∨ (k = 2 ∧ l = 0) then Ioo b t
  else Ioo c t

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TripleIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def tripleIndex {n : ℕ} (k : Fin 3) (i : Fin n) : Fin (3 * n) :=
  ⟨3 * i.val + k.val, by have := i.isLt; have := k.isLt; omega⟩

@[simp] lemma tripleLabels_tripleIndex {n : ℕ} (k : Fin 3) (i : Fin n) :
    tripleLabels (3 * n) (tripleIndex k i) = k := by
  apply Fin.ext
  simp [tripleLabels, tripleIndex, Nat.add_mod]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def sphereKernel (r s : Time) : ℝ := min (r : ℝ) (s : ℝ) - (r : ℝ) * (s : ℝ)

def sphereTail (μ : Measure Time) (r : Time) : ℝ :=
  ∫ s, 1 - max (r : ℝ) (s : ℝ) ∂μ

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_WeightedCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def weightedCDF (μ : Measure Time) (a : Time → ℝ) (x : ℝ) : ℝ :=
  ∫ s in {s : Time | (s : ℝ) ≤ x}, a s ∂μ

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshLogRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def patternExtend (N M : ℕ) (a : Fin M→Fin N→ℝ) : ℕ→Fin N→ℝ :=
  fun i => if hi : i<M then a ⟨i,hi⟩ else 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepStationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def stepLogRatios : (k : ℕ) → (Fin (k+1) → ℝ) → (Fin k → ℝ) → ℝ
  | 0, _, _ => 0
  | k+1, D, z => stepLogRatios k (fun i => D i.succ) (fun i => z i.succ)+
      (Real.log (D 0)-Real.log (D 1))/(2*z 0)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def weightedStepTail {I : Type*} [Fintype I] (w : I → ℝ) (q : I → ℝ) (t : ℝ) : ℝ :=
  ∑ i, w i*(1-max (q i) t)

def weightedStepA {I : Type*} [Fintype I] (w q : I → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..r, 1/(weightedStepTail w q t)^2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def weightedControlCoefficient (n : ℕ) (w : Fin (n+1)→ℝ) (hw : ∀ i, 0≤w i)
    (i : Fin n) : ℝ≥0 :=
  ⟨∑ j : Fin (n+1), if j ≤ i.castSucc then w j else 0,Finset.sum_nonneg fun j _ => by
    split_ifs <;> first | exact hw j | rfl⟩

def paddedControlWeights {n : ℕ} (w : Fin (n+1)→ℝ) : Fin (n+3)→ℝ :=
  Fin.cons 0 (Fin.snoc w 0)

lemma paddedControlWeights_nonneg {n : ℕ} (w : Fin (n+1)→ℝ) (hw : ∀ i, 0≤w i) :
    ∀ i, 0≤paddedControlWeights w i := by
  intro i
  refine Fin.cases (by simp [paddedControlWeights]) (fun j => ?_) i
  change 0≤(Fin.snoc w 0 : Fin (n+2)→ℝ) j
  refine Fin.lastCases (by simp) (fun l => ?_) j
  simpa using hw l

lemma paddedControlWeights_sum {n : ℕ} (w : Fin (n+1)→ℝ) (hw1 : ∑ i, w i=1) :
    ∑ i, paddedControlWeights w i=1 := by
  unfold paddedControlWeights
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,zero_add]
  rw [Fin.sum_univ_castSucc]
  simpa using hw1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControlTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def stepBoundaryWeights : (n : ℕ) → (Fin (n+1)→ℝ) → (Fin n→ℝ≥0) → List ℝ
  | 0,_,_ => []
  | 1,_,_ => []
  | n+2,v,d => ((d 1:ℝ)-(d 0:ℝ))*v 1 ::
      stepBoundaryWeights (n+1) (fun i => v i.succ) (fun i => d i.succ)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CountableGaussianResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

 def resampleGaussianCoordinate (i : ℕ) (p : ℝ×(ℕ → ℝ)) : ℕ → ℝ :=
  Function.update p.2 i p.1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CouplingKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma measurable_disorder_state_lift {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    {F : (ℕ → ℝ) → S → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun a : (A × (ℕ → ℝ)) × S => F a.1.2 a.2) :=
  hF.comp (measurable_fst.snd.prodMk measurable_snd)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_CoordinateContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

def quadraticBoxPenalty {I : Type*} [Fintype I] (c u : I → ℝ) : ℝ :=
  ∑ i, c i*(u i-3/2)^2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_PerturbationContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourcePenaltyWeight (N : ℕ) (j : Fin N) : ℝ := (2:ℝ)^(-((j.val+1:ℕ):ℤ))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianCovarianceDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {I : Type} [Fintype I] [DecidableEq I] {S : Type} [MeasurableSpace S]
variable (n : ℕ)

def rightCoefficients (C : Fin (n+1)→I→ℝ) (l : Fin (n+1)) : I ⊕ I→ℝ :=
  Sum.elim (fun _ => 0) (C l)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_FieldArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceFieldPolynomial {k : ℕ} (a : Fin (k+1)→ℝ) : Polynomial ℝ :=
  Lagrange.interpolate Finset.univ (fun l : Fin (k+1) => (l.val:ℝ)/(k+1:ℕ)) a

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def varianceLevels {k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin (k+1)) : ℝ :=
  (∑ j, if j ≤ i then v j else 0)/2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GlobalContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceStepFieldCap (k : ℕ) (H : ℝ) : Set (Fin (k+1)→ℝ) :=
  Icc (fun _ => 0) (fun _ => H) ∩ {h | Monotone h}

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RestorationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S]

def restorationReplicaTest (r : ℕ) (W : S→ℝ) (F : (Fin r→S)→ℝ) :
    (k : ℕ) → (Fin (r+k)→S)→ℝ
  | 0 => F
  | k+1 => fun x => W (x 0)*restorationReplicaTest r W F k (fun i => x i.succ)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UniformGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def uniformWeights (k : ℕ) : Fin (k+1) → ℝ := fun _ => 1/(k+1:ℕ)
def uniformExponents (k : ℕ) (i : Fin (k+2)) : ℝ := (i:ℕ)/(k+1:ℕ)

lemma uniformWeights_pos (k : ℕ) (i : Fin (k+1)) : 0 < uniformWeights k i := by
  unfold uniformWeights
  positivity

lemma uniformWeights_sum (k : ℕ) : ∑ i, uniformWeights k i=1 := by
  simp only [uniformWeights,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,one_div]
  exact mul_inv_cancel₀ (by positivity)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelPairTestValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def scalarFrontMatrixTest (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ) :
    (j : ℕ) → Matrix (Fin (r+j)) (Fin (r+j)) ℝ →ᵇ ℝ
  | 0 => F
  | j+1 => (scalarFrontMatrixTest r F j).compContinuous
      ⟨fun Q i l => Q i.succ l.succ,by fun_prop⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_OrderedCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction

def orderedLevelCode {k : ℕ} (v : Fin (k+1) → ℝ) (x : ℝ) : Fin (k+1) :=
  (Finset.univ.filter (fun i => v i ≤ x)).sup id

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedMarkedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def secondPairMark (v : ℝ→ᵇℝ) (b : Bool) : ℝ→ᵇℝ := if b then v else 1

def pairMarkPower (b : Bool) : ℕ := if b then 2 else 1

end SphericalPerceptronFreeEnergy
end

end OAI
end


