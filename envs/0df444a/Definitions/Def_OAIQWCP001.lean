-- Prove2me | Definitions.Def_OAIQWCP001
-- name    : OAIQWCP001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T23:53:35.729124+00:00
-- url     : https://prove2.me/theorems/8188a13b-2559-487f-8aa8-ad42ba950291
-- title:
--   Definitions bundle OAIQWCP001 of the split of OpenAI, Replacing Gaussian observations in memory-constrained inference
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CurrentProjection.fiberBlockMain`, `OAI.CurrentProjection.mixedMomentMain`, `OAI.CurrentProjection.hybridBlockMain`, `OAI.CurrentProjection.fiberTwoPointMain`, `OAI.CurrentProjection.actualRowSourceMain`, `OAI.CurrentProjection.actualRowRefinement`, `OAI.CurrentProjection.twoLabelComparisonMain`, `OAI.CurrentProjection.oneLevelComparisonMain` and `OAI.CurrentProjection.actualRowSourceRefinement`, carved from OpenAI's openai/math development (OpenAI, *Replacing Gaussian observations in memory-constrained inference*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 101 declarations of OpenAI's Lean: 85 definitions, 9 instances and 7 theorems. The definitions and types are `OAI.CurrentProjection.KernelHistory`, `OAI.CurrentProjection.Observations`, `OAI.CurrentProjection.actualFreshArrayLaw`, `OAI.CurrentProjection.appendEquiv`, `OAI.CurrentProjection.arrayReference`, `OAI.CurrentProjection.arrayResidualLaw`, `OAI.CurrentProjection.arrayResidualObservation`, `OAI.CurrentProjection.baselineCost`, `OAI.CurrentProjection.blockExposedBaseMap`, `OAI.CurrentProjection.blockObservedInput`, `OAI.CurrentProjection.cauchyMixture`, `OAI.CurrentProjection.cauchyObservation`, `OAI.CurrentProjection.cauchyObservationLaw`, `OAI.CurrentProjection.cauchyTiltConstant`, `OAI.CurrentProjection.conditionalReferenceKL`, `OAI.CurrentProjection.directionComplement`, `OAI.CurrentProjection.endingRowLaw`, `OAI.CurrentProjection.exchangeMiddle`, `OAI.CurrentProjection.fiberBilinearTest`, `OAI.CurrentProjection.fiberEnergyBound`, `OAI.CurrentProjection.fiberPairInverse`, `OAI.CurrentProjection.fiberPerpendicularTest`, `OAI.CurrentProjection.fiberSlab`, `OAI.CurrentProjection.fixedTargetPosterior`, `OAI.CurrentProjection.freshArrayLaw`, `OAI.CurrentProjection.freshReference`, `OAI.CurrentProjection.freshSlope`, `OAI.CurrentProjection.gaussianLabels`, `OAI.CurrentProjection.gaussianObservation`, `OAI.CurrentProjection.gaussianObservations`, `OAI.CurrentProjection.gaussianReconstruct`, `OAI.CurrentProjection.gaussianVectorPair`, `OAI.CurrentProjection.hybridBaselineConstant`, `OAI.CurrentProjection.hybridRowConstant`, `OAI.CurrentProjection.initialArray`, `OAI.CurrentProjection.kernelInverseVolume`, `OAI.CurrentProjection.kernelSmallBallConstant`, `OAI.CurrentProjection.liftActualLaw`, `OAI.CurrentProjection.liftActualObservation`, `OAI.CurrentProjection.logScaleExtended` and 45 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/GaussianReplacement, in whole or in part: `ArrayBounds`, `ConditionalLaw`, `Density`, `FiberConditional`, `FiberGeometry`, `FreshRows`, `KernelGeometry`, `KernelVolume`, `Mixture`, `Observation`, `Reference`, `RowOrder`, `Slab`, `Telescopes`, `Tilt`.
--
--   **Imports.** It imports the published bundle `Def_GaussianReplacement`; the bundle `OAIQWCP000` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.CurrentProjection.actual_fresh_row_bound`; the proofs of `OAI.CurrentProjection.actual_fresh_row_bound`, `OAI.CurrentProjection.fiberBlockMain`, `OAI.CurrentProjection.fiberTwoPointMain`, `OAI.CurrentProjection.hybridBlockMain`, `OAI.CurrentProjection.mixedMomentMain`, `OAI.CurrentProjection.oneLevelComparisonMain` and `OAI.CurrentProjection.twoLabelComparisonMain`.
-- source:
--   OpenAI, Replacing Gaussian observations in memory-constrained inference, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/GaussianReplacement at commit adc7f12

import Mathlib
import Definitions.Def_GaussianReplacement
import Definitions.Def_OAIQWCP000

section
-- module Solutions.OAIQW_CurrentProjection.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace





section AppendPi
variable {E : Type*} [MeasurableSpace E]

lemma measurable_append (m r : ℕ) :
    Measurable (fun z : (Fin m → E) × (Fin r → E) => Fin.append z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [Fin.append_left, Function.comp_def] using (measurable_pi_apply i).comp measurable_fst
  | right i => simpa only [Fin.append_right, Function.comp_def] using (measurable_pi_apply i).comp measurable_snd

end AppendPi




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.KernelGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



section KernelGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

def rowSpan {r : ℕ} (A : Fin r → E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range A)

def rowProjectionL {r : ℕ} (A : Fin r → E) : E →L[ℝ] E :=
  ∑ i, (‖gramSchmidt ℝ A i‖ ^ 2)⁻¹ •
    InnerProductSpace.rankOne ℝ (gramSchmidt ℝ A i) (gramSchmidt ℝ A i)

end KernelGeometry



def kernelSmallBallConstant : ℝ := 12^17




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.KernelVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

section KernelVolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

abbrev KernelHistory (r n : ℕ) (E : Type*) := Fin n → ((Fin r → E) × E)

def kernelInverseVolume {r n : ℕ} (h : KernelHistory r n E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (‖gramSchmidt ℝ (fun j => (h j).2) i‖⁻¹)

end KernelVolume



section KernelNormalizedMoment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

def normalizeKernelVector {r : ℕ} (z : (Fin r → E) × E) : (Fin r → E) × E :=
  (z.1, ‖z.2‖⁻¹ • z.2)

end KernelNormalizedMoment



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Tilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



section KernelTilt
variable {E : Type*} [NormedAddCommGroup E] [innerProductSpaceRealE : InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [nontrivialE : Nontrivial E]



def reciprocalKernelScale {r : ℕ} (κ : Kernel (Fin r → E) E) (s : E)
    (A : Fin r → E) : ℝ≥0∞ := ∫⁻ t, ENNReal.ofReal (‖t-s‖⁻¹) ∂κ A

end KernelTilt





def negativeLogAbs (x : ℝ) : ℝ := max (-Real.log |x|) 0

def regularizedCauchyCross (r e x y : ℝ) : ℝ :=
  Real.log Real.pi + Real.log ((r*x)^2+(r*y)^2+e^2) -
    (1/2:ℝ)*Real.log ((r*x)^2+e^2)

abbrev standardNormalPair : Measure (ℝ×ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

def cauchyTiltConstant : ℝ := Real.log Real.pi + 2 +
  ∫ x, negativeLogAbs x ∂gaussianReal 0 1



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Reference
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory




def conditionalReferenceKL {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (A×B)) (ν : Measure B) : ℝ≥0∞ := klDiv P (P.fst.prod ν)



def gaussianLabels (k : ℕ) : Measure (Fin k → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)

instance gaussianLabels_probability (k : ℕ) : IsProbabilityMeasure (gaussianLabels k) := by
  unfold gaussianLabels
  infer_instance

def regularizedReciprocal {d : ℕ} (e : ℝ) (s t : Sphere d) : ℝ :=
  (max (dist s t) e)⁻¹

def regularizedScale {d : ℕ} (μ : Measure (Sphere d)) (e : ℝ) (s : Sphere d) : ℝ :=
  ∫ t, regularizedReciprocal e s t ∂μ



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Mixture
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


abbrev gaussianVectorPair (d : ℕ) := (stdGaussian (Vector d)).prod (stdGaussian (Vector d))

def sphereCauchyCross {d : ℕ} (e : ℝ) (s t : Sphere d) (x : Vector d×Vector d) : ℝ :=
  regularizedCauchyCross 1 e ⟪(s:Vector d)-(t:Vector d),x.1⟫ ⟪(s:Vector d)-(t:Vector d),x.2⟫

def ownCauchyMixture {d : ℕ} (μ : Measure (Sphere d)) (e : ℝ) (s : Sphere d)
    (x : Vector d×Vector d) : ℝ := ∫ t, Real.exp (-sphereCauchyCross e s t x) ∂μ



def regularizedCauchyPDF (e a b : ℝ) : ℝ := Real.exp (-regularizedCauchyCross 1 e a b)

def cauchyMixture {d : ℕ} (μ : Measure (Sphere d)) (e : ℝ) (x : Vector d×Vector d)
    (b : ℝ×ℝ) : ℝ :=
  ∫ t, regularizedCauchyPDF e (b.1-⟪(t:Vector d),x.1⟫) (b.2-⟪(t:Vector d),x.2⟫) ∂μ



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.FreshRows
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def cauchyObservation {d : ℕ} {C : Type*} (z : (C×Sphere d)×(Vector d×Vector d)) :
    ((C×(Vector d×Vector d))×ℝ)×ℝ :=
  (((z.1.1,z.2),⟪(z.1.2:Vector d),z.2.1⟫),⟪(z.1.2:Vector d),z.2.2⟫)

def cauchyObservationLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) : Measure (((C×(Vector d×Vector d))×ℝ)×ℝ) :=
  (Γ.prod (gaussianVectorPair d)).map cauchyObservation

def standardGaussianEntropy : ℝ := Real.log (Real.sqrt (2*Real.pi))+1/2



def reciprocalScale {d : ℕ} (μ : Measure (Sphere d)) (s : Sphere d) : ℝ≥0∞ :=
  ∫⁻ t, (ENNReal.ofReal (dist s t))⁻¹ ∂μ

def reciprocalCutoff (n : ℕ) : ℝ := 1/((n:ℝ)+1)

def logScaleExtended (a : ℝ≥0∞) : ℝ≥0∞ := (ENNReal.log (2*a)).toENNReal



def residualObservation {d r : ℕ} {C : Type*} (z : (C×Sphere d)×Rows r d) :
    (C×(Rows r d×(Fin r→ℝ)))×Sphere d :=
  ((z.1.1,(z.2,label z.2 (z.1.2:Vector d))),z.1.2)

lemma measurable_residualObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (residualObservation (d:=d) (r:=r) (C:=C)) := by
  unfold residualObservation label
  fun_prop

def residualLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : Measure ((C×(Rows r d×(Fin r→ℝ)))×Sphere d) :=
  (Γ.prod (gaussianRows r d)).map residualObservation

instance residualLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    IsProbabilityMeasure (residualLaw Γ r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_residualObservation.aemeasurable).mpr inferInstance



def fixedTargetPosterior {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (c : C) (s : Sphere d) :
    Kernel (Rows r d) (Vector d) :=
  ((residualLaw Γ r).condKernel.comap (fun A => (c,(A,label A (s:Vector d))))
    (by unfold label; fun_prop)).map Subtype.val

instance fixedTargetPosterior_markov {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (c : C) (s : Sphere d) :
    IsMarkovKernel (fixedTargetPosterior (r:=r) Γ c s) := by
  unfold fixedTargetPosterior
  exact Kernel.IsMarkovKernel.map _ measurable_subtype_coe



def residualScale {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (z : C×Sphere d) (A : Rows r d) : ℝ≥0∞ :=
  reciprocalScale ((residualLaw Γ r).condKernel (z.1,(A,label A (z.2:Vector d)))) z.2

def residualCube {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ)
    (w : ((C×Sphere d)×Vector d)×Rows r d) : ℝ≥0∞ :=
  (∫⁻ t : Sphere d, cubeKernel δ ⟪(t:Vector d)-(w.1.1.2:Vector d),w.1.2⟫
    ∂(residualLaw Γ r).condKernel (w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d)))) /
      residualScale Γ w.1.1 w.2




def scalarCube (μ : Measure ℝ) (y δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, cubeKernel δ (t-y) ∂μ

def scalarExtended (μ : Measure ℝ) (y : ℝ) : ℝ≥0∞ :=
  liminf (fun n : ℕ => scalarCube μ y (1/(n:ℝ))) atTop

def scalarDensity (μ : Measure ℝ) (y : ℝ) : ℝ≥0∞ :=
  if scalarExtended μ y = ∞ then 0 else scalarExtended μ y



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ConditionalLaw
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def scalarProjectionKernel {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) : Kernel (C×Vector d) ℝ :=
  dependentMapKernel (κ.comap Prod.fst measurable_fst)
    (fun z : (C×Vector d)×Sphere d => ⟪(z.2:Vector d),z.1.2⟫)

def scalarObservation {d : ℕ} {C : Type*} (z : (C×Sphere d)×Vector d) : (C×Vector d)×ℝ :=
  ((z.1.1,z.2),⟪(z.1.2:Vector d),z.2⟫)

def scalarObservationLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) : Measure ((C×Vector d)×ℝ) :=
  (Γ.prod (stdGaussian (Vector d))).map scalarObservation



def residualLabelObservation {d r : ℕ} {C : Type*}
    (w : ((C×Sphere d)×Vector d)×Rows r d) : ((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ :=
  (((w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d))),w.1.2),⟪(w.1.1.2:Vector d),w.1.2⟫)

def residualLabelLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) (r : ℕ) :
    Measure (((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ) :=
  (P.prod (gaussianRows r d)).map residualLabelObservation

def residualExact {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (w : ((C×Sphere d)×Vector d)×Rows r d) : ℝ≥0∞ :=
  scalarDensity (scalarProjectionKernel (residualLaw Γ r).condKernel
    (residualLabelObservation w).1) (residualLabelObservation w).2 /
    residualScale Γ w.1.1 w.2

def hybridRowConstant : ℝ := cauchyTiltConstant+Real.log (1+5*kernelSmallBallConstant)



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Observation
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def appendEquiv (E : Type*) [MeasurableSpace E] (m r : ℕ) :
    ((Fin m→E)×(Fin r→E)) ≃ᵐ (Fin (m+r)→E) where
  toFun z := Fin.append z.1 z.2
  invFun z := ((fun i => z (Fin.castAdd r i)),fun i => z (Fin.natAdd m i))
  left_inv z := by ext i <;> simp
  right_inv z := by ext i; induction i using Fin.addCases <;> simp
  measurable_toFun := measurable_append m r
  measurable_invFun := by
    change Measurable (fun z : Fin (m+r) → E =>
      ((fun i => z (Fin.castAdd r i)),fun i => z (Fin.natAdd m i)))
    fun_prop

abbrev Observations (k d : ℕ) := Fin k → (Vector d×ℝ)

def pairObservation {d k : ℕ} (z : Rows k d×(Fin k→ℝ)) : Observations k d :=
  fun j => (z.1 j,z.2 j)

def observationEquiv (k d : ℕ) : (Rows k d×(Fin k→ℝ)) ≃ᵐ Observations k d :=
  (MeasurableEquiv.arrowProdEquivProdArrow (Vector d) ℝ (Fin k)).symm

def gaussianObservation (d : ℕ) : Measure (Vector d×ℝ) :=
  (stdGaussian (Vector d)).prod (gaussianReal 0 1)

instance gaussianObservation_probability (d : ℕ) : IsProbabilityMeasure (gaussianObservation d) := by
  unfold gaussianObservation; infer_instance

def gaussianObservations (k d : ℕ) : Measure (Observations k d) :=
  Measure.pi (fun _ => gaussianObservation d)

instance gaussianObservations_probability (k d : ℕ) : IsProbabilityMeasure (gaussianObservations k d) := by
  unfold gaussianObservations Observations; infer_instance

def ownObservations {k d : ℕ} (G : Rows k d) (s : Sphere d) : Observations k d :=
  pairObservation (G,label G (s:Vector d))

lemma measurable_ownObservations {k d : ℕ} :
    Measurable (fun z : Rows k d×Sphere d => ownObservations z.1 z.2) := by
  unfold ownObservations pairObservation label
  fun_prop


def observationReferenceKL {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : ℝ≥0∞ :=
  klDiv (observedMessage P) (((gaussianRows k d).prod (gaussianLabels k)).prod P.fst.snd)



def snocEquiv (E : Type*) [MeasurableSpace E] (r : ℕ) :
    ((Fin r→E)×E) ≃ᵐ (Fin (r+1)→E) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => E) (Fin.last r)).symm

def arrayResidualObservation {d r : ℕ} {C : Type*} (z : (C×Sphere d)×Rows r d) :
    (C×Observations r d)×Sphere d := ((z.1.1,ownObservations z.2 z.1.2),z.1.2)

def arrayResidualLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : Measure ((C×Observations r d)×Sphere d) :=
  (Γ.prod (gaussianRows r d)).map arrayResidualObservation

def freshArrayLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : Measure (C×Observations r d) := (arrayResidualLaw Γ r).fst

def freshReference {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : ℝ≥0∞ :=
  conditionalReferenceKL (freshArrayLaw Γ r) (gaussianObservations r d)

def freshSlope {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : ℝ≥0∞ :=
  conditionalReferenceKL (scalarObservationLaw (arrayResidualLaw Γ r)) (gaussianReal 0 1)



def singleResidualObservation {d : ℕ} {C : Type*} (z : (C×Sphere d)×Vector d) :
    (C×(Vector d×ℝ))×Sphere d := ((z.1.1,(z.2,⟪(z.1.2:Vector d),z.2⟫)),z.1.2)

def singleSignalLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) : Measure ((C×(Vector d×ℝ))×Sphere d) :=
  P.map singleResidualObservation

def singleObservationLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) : Measure (C×(Vector d×ℝ)) := (singleSignalLaw P).fst

def singleReference {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) : ℝ≥0∞ :=
  conditionalReferenceKL (singleObservationLaw P) (gaussianObservation d)



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.RowOrder
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def exchangeMiddle (C A B D : Type*) [MeasurableSpace C] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace D] :
    ((C×(A×B))×D) ≃ᵐ ((C×(A×D))×B) where
  toFun z := ((z.1.1,(z.1.2.1,z.2)),z.1.2.2)
  invFun z := ((z.1.1,(z.1.2.1,z.2)),z.1.2.2)
  left_inv z := by rcases z with ⟨⟨c,a,b⟩,d⟩; rfl
  right_inv z := by rcases z with ⟨⟨c,a,d⟩,b⟩; rfl
  measurable_toFun := (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)).prodMk measurable_fst.snd.snd
  measurable_invFun := (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)).prodMk measurable_fst.snd.snd

def liftActualObservation {d r : ℕ} {C : Type*} (w : ((C×Sphere d)×Vector d)×Rows r d) :
    (((C×Observations r d)×Sphere d)×Vector d) :=
  (((w.1.1.1,ownObservations w.2 w.1.1.2),w.1.1.2),w.1.2)

def liftActualLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) (r : ℕ) : Measure (((C×Observations r d)×Sphere d)×Vector d) :=
  (P.prod (gaussianRows r d)).map liftActualObservation

def actualFreshArrayLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) (r : ℕ) :
    Measure (C×((Vector d×ℝ)×Observations r d)) :=
  (P.prod (gaussianRows r d)).map (fun w =>
    (w.1.1.1,((w.1.2,⟪(w.1.1.2:Vector d),w.1.2⟫),ownObservations w.2 w.1.1.2)))

attribute [fun_prop] measurable_ownObservations




def initialArray {E : Type*} {i m : ℕ} (hi : i ≤ m) (X : Fin m → E) : Fin i → E :=
  fun j => X (Fin.castLE hi j)

lemma measurable_initialArray {E : Type*} [MeasurableSpace E] {i m : ℕ} (hi : i ≤ m) :
    Measurable (initialArray (E:=E) hi) := by
  unfold initialArray; fun_prop

def prefixLaw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i ≤ m) :
    Measure ((Sphere d×W)×Rows i d) := P.map (Prod.map id (initialArray hi))

instance prefixLaw_probability {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i ≤ m) :
    IsProbabilityMeasure (prefixLaw P i hi) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_id.prodMap (measurable_initialArray hi)).aemeasurable).mpr inferInstance

def observationSignalMap {d k : ℕ} {W : Type*} (z : (Sphere d×W)×Rows k d) :
    (W×Observations k d)×Sphere d := ((z.1.2,ownObservations z.2 z.1.1),z.1.1)

def observationSignalLaw {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : Measure ((W×Observations k d)×Sphere d) :=
  P.map observationSignalMap

def nextActualRowLaw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    Measure (((W×Observations i d)×Sphere d)×Vector d) :=
  P.map (fun z => (((z.1.2,ownObservations (initialArray (Nat.le_of_lt hi) z.2) z.1.1),z.1.1),z.2 ⟨i,hi⟩))



def rawNextRowLaw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    Measure (((Sphere d×W)×Rows i d)×Vector d) :=
  P.map (fun z => ((z.1,initialArray (Nat.le_of_lt hi) z.2),z.2 ⟨i,hi⟩))



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ArrayBounds
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def arrayReference {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : ℝ≥0∞ :=
  conditionalReferenceKL (observationSignalLaw P).fst (gaussianObservations k d)



def baselineCost (d k : ℕ) : ℝ≥0∞ :=
  klDiv (projectionJoint (uniformSphere d) (gaussianRows k d))
    ((gaussianRows k d).prod (gaussianLabels k))

def hybridBaselineConstant : ℝ := 20 + |Real.log (normalizer 1)+1/2|



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Telescopes
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



def processedKernel {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B))
    (η : Kernel (Z×B) C) : Kernel Z (A×C) :=
  (α ⊗ₖ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map
    (fun z => (z.1.1,z.2))

instance processedKernel_markov {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] : IsMarkovKernel (processedKernel α η) := by
  unfold processedKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_fst.fst.prodMk measurable_snd)

def processedLaw {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (P : Measure (Z×(A×B)))
    (η : Kernel (Z×B) C) : Measure (Z×(A×C)) :=
  (P ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map
    (fun z => (z.1.1,(z.1.2.1,z.2)))

instance processedLaw_probability {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (P : Measure (Z×(A×B))) [IsProbabilityMeasure P]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] : IsProbabilityMeasure (processedLaw P η) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)).aemeasurable).mpr
    inferInstance




def endingRowLaw {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U))
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) : Measure ((Sphere d×V)×Rows m d) :=
  (blockLaw P κ).map (fun z => ((z.1.1.1,z.2),z.1.2))

lemma measurable_endingRowMap {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V] :
    Measurable (fun z : (((Sphere d×U)×Rows m d)×V) => ((z.1.1.1,z.2),z.1.2)) :=
  (measurable_fst.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

instance endingRowLaw_probability {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ] : IsProbabilityMeasure (endingRowLaw P κ) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_endingRowMap.aemeasurable).mpr inferInstance

def blockObservedInput {d m r : ℕ} {U : Type*}
    (z : (Rows (m+r) d×(Fin (m+r)→ℝ))×U) : U×(Rows m d×(Fin m→ℝ)) :=
  (z.2, (fun j => z.1.1 (Fin.castAdd r j)), (fun j => z.1.2 (Fin.castAdd r j)))

lemma measurable_blockObservedInput {d m r : ℕ} {U : Type*} [MeasurableSpace U] :
    Measurable (blockObservedInput (d:=d) (m:=m) (r:=r) (U:=U)) := by
  unfold blockObservedInput
  fun_prop

def blockExposedBaseMap {d m r : ℕ} {U : Type*}
    (z : ((Sphere d×U)×Rows m d)×Rows r d) :
    (Rows (m+r) d×(Fin (m+r)→ℝ))×(Sphere d×U) :=
  exposedJointMap (z.1.1,Fin.append z.1.2 z.2)



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.FiberGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



section GaussianDirection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

def directionComplement (u : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ u).smulRight u

end GaussianDirection

section GaussianSlab
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

def gaussianReconstruct (u : E) {k : ℕ} (zG : (Fin k→ℝ)×(Fin k→E)) : Fin k→E :=
  fun i => zG.1 i • u + directionComplement u (zG.2 i)

end GaussianSlab




def fiberEnergyBound (d : ℕ) : ℝ≥0∞ := momentConstant 9 d (3*4^d) (3*4^d)



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Slab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



def fiberPairInverse {d : ℕ} (k : ℕ) (z : Sphere d×Sphere d) : ℝ≥0∞ :=
  ENNReal.ofReal (‖(z.2:Vector d)-(z.1:Vector d)‖⁻¹ ^ k)

def fiberSlab {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (δ : ℝ)
    (z : Sphere d×Sphere d) : ℝ≥0∞ :=
  ∫⁻ C, (H C : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C ∂gaussianRows k d

def fiberPerpendicularTest {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (z : Sphere d×Sphere d) : ℝ≥0∞ :=
  ∫⁻ C : Rows k d, (H (fun i => perpendicularRow ((z.2:Vector d)-(z.1:Vector d)) (C i)) : ℝ≥0∞)
    ∂gaussianRows k d



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.FiberConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def sphericalPosteriorWeight (d k : ℕ) [Nonempty (Sphere d)] (b : Sphere d→ℝ≥0∞)
    (o : Rows k d×(Fin k→ℝ)) : ℝ≥0∞ := ∫⁻ s, b s ∂sphericalFiberKernel d k o



def fiberBilinearTest {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (z : Rows k d×(Sphere d×Sphere d)) : ℝ≥0∞ :=
  (H z.1 : ℝ≥0∞)*b z.2.1*a z.2.2



end CurrentProjection

end

end OAI
end


