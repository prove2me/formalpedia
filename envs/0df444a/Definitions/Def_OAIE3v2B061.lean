-- Prove2me | Definitions.Def_OAIE3v2B061
-- name    : OAIE3v2B061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:14:20.020735+00:00
-- url     : https://prove2.me/theorems/b8998ab5-7eb3-4df9-bcf2-566899e70578
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 62 of 311
-- statement:
--   Definitions bundle 62 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B013`, `OAIE3v2B015`, `OAIE3v2B017`, `OAIE3v2B018`, `OAIE3v2B021`, `OAIE3v2B028`, `OAIE3v2B030` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateNativeMajorBudget.lean`, `Dynamics/AllocatedCandidateStageScalarBudget.lean`, `Dynamics/CandidatePhysicalOrdinaryBudget.lean`, `Dynamics/CoefficientFrontBudget.lean`, `Dynamics/JointPivotProfileBudget.lean`, `Dynamics/PrecenterNativeSelectionBudget.lean`, `Dynamics/UniformExternalNetScalarBudget.lean`, `Estimates/ActiveProfileNoise.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/BooleanMinorDimension.lean`, `Estimates/CoefficientJetScalar.lean`, `Estimates/CoefficientNormalization.lean`, `Estimates/CubeTranslation.lean`, `Estimates/DependentPatchValue.lean`, `Estimates/FourSlicedProductSmoothing.lean`, `Estimates/InactiveShortLogBounds.lean`, `Estimates/JointBooleanGoodWeight.lean`, `Estimates/MarginalTailModeling.lean`, `Estimates/NormalizedJetColumns.lean`, `Estimates/PreparedFiniteScheduleUniversalMaskProductiveGood.lean`, `Estimates/ScalarDominatedSlack.lean`, `Estimates/SelectedCoefficientEvaluation.lean`, `Estimates/SlicedPairAmplitude.lean`, `Fourier/CrossRowCharacterDifference.lean`, `Geometry/BlockCubeCoordinates.lean`, `Geometry/JetAxisCoordinates.lean`, `Geometry/NarrowSpatialSiteVariation.lean`, `Geometry/PivotCoordinateChange.lean`, `Geometry/SignedSplitCoordinates.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Geometry/UnitBoxAmplitude.lean`, `Lattices/BooleanAffineInput.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/IntegerFiberUniformBound.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PrincipalResidueMixture.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Linear/AllocatedKernelScaleWithCutoff.lean`, `Linear/BasisSurjectionSection.lean`, `Linear/ContainedKernelPhysicalDisplacement.lean`, `Linear/KernelCoefficientLogBudget.lean`, `Linear/PivotNormalizedMatrix.lean`, `Linear/WeightedDualVector.lean`, `Polynomial/CRTPolynomialInputAffineLaw.lean`, `Polynomial/FrozenPolynomialAffineRange.lean`, `Polynomial/JointPolynomialDilationGrid.lean`, `Polynomial/PolynomialDeterminantDerivativeBound.lean`, `Polynomial/PolynomialParameterContinuity.lean`, `Probability/CanonicalConstantDensityBound.lean`, `Probability/DiagonalDensityTransport.lean`, `Probability/DiagonalImageDensity.lean`, `Probability/FiniteProbabilityLipschitz.lean`, `Probability/FullFrozenChartMass.lean`, `Probability/NormalizedJetDensitySupport.lean`, `Probability/PositiveDensityNormalization.lean`, `Probability/ScalarCubeBoundaryMass.lean`, `Probability/ScaledCubeProductMeasure.lean`, `Probability/ShiftedProductCoordinateLaw.lean`, `Probability/SlicedRemainderDensityFamily.lean`, `Probability/SpatialProductDensity.lean`, `Probability/TranslatedMixtureL1.lean`, `Sampling/AveragedNormalizedTwistForecastJointModel.lean`, `Sampling/BooleanProductSampler.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B005
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B017
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B021
import Definitions.Def_OAIE3v2B028
import Definitions.Def_OAIE3v2B030

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3.TriangularSlots

variable {D E d : ℕ}

def dropPrefix (A : TriangularSlots (D + E)) (b : Fin D → ℝ) : TriangularSlots E where
  center x i := A.center (Fin.append b x) (i.natAdd D)
  lower i x y hxy := by
    apply A.lower
    intro j
    refine Fin.addCases (fun k hj => ?_) (fun k hj => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      apply hxy
      simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hj

end Erdos3.TriangularSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem integerResidueMap_mulVec {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) (x : J → ℤ) :
    integerResidueMap I m (A *ᵥ x) = integerResidueMatrix A m *ᵥ integerResidueMap J m x := by
  funext i
  exact (Int.castRingHom (ZMod m)).map_mulVec A x i

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem reducedIntegerMatrix_residue {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (M : ℕ) (x : J → ℤ) :
    integerResidueMap I M (A *ᵥ x) =
      integerResidueMatrix (reducedIntegerMatrix A M) M *ᵥ integerResidueMap J M x := by
  rw [integerResidueMatrix_reduced]
  exact integerResidueMap_mulVec A M x

theorem exists_bounded_integerMap_residue_matrix {I J : Type*} [Fintype J] [DecidableEq J]
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (M : ℕ) [NeZero M] :
    ∃ A : Matrix I J ℤ,
      (∀ i j, 0 ≤ A i j ∧ A i j < M) ∧
      ∀ x, integerResidueMap I M (f x) = integerResidueMatrix A M *ᵥ integerResidueMap J M x := by
  refine ⟨reducedIntegerMatrix (LinearMap.toMatrix' f) M, reducedIntegerMatrix_bounds _ M, ?_⟩
  intro x
  rw [← LinearMap.toMatrix'_mulVec f x]
  exact reducedIntegerMatrix_residue _ M x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (law : C → FiniteProbabilityWeights Ω)

noncomputable def centeredFiniteWeightDensity (z : C × Ω) : ℝ :=
  (law z.1).weight z.2

omit [MeasurableSpace C] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFiniteWeightDensity_le_one (z : C × Ω) :
    centeredFiniteWeightDensity law z ≤ 1 := by
  change (law z.1).weight z.2 ≤ 1
  rw [← (law z.1).total]
  exact Finset.single_le_sum (fun x _ => (law z.1).nonneg x) (Finset.mem_univ z.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

theorem inverseJacobian_pos (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : 0 < inverseJacobian A :=
  abs_pos.mpr A.symm.toLinearEquiv.isUnit_det'.ne_zero

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def linearBoxDensityCap (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : ℝ≥0 :=
  ⟨inverseJacobian A * ∏ i, 1 / ℓ i,
    mul_nonneg (inverseJacobian_pos A).le
      (Finset.prod_nonneg (fun i _ => div_nonneg zero_le_one (hℓ i).le))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

instance unitBoxMeasure_probability : IsProbabilityMeasure (unitBoxMeasure ι) := by
  constructor
  simp only [unitBoxMeasure, Measure.restrict_apply_univ, positiveUnitBox, Real.volume_pi_Ioc,
    sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal Classical

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

noncomputable def fixedSpatialBlockDensityCap
    (B : (X → ℝ) ≃L[ℝ] (X → ℝ)) : ℝ≥0 :=
  linearBoxDensityCap (fun _ => 1) (fun _ => zero_lt_one) B

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PivotCoordinateChange
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def pivotDensityPullback (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (p : (J → ℝ) × (I → ℝ)) : ℝ :=
  inverseJacobian A * f ((pivotCoordinateChange A B).symm p)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def pivotOutputDensity (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (v : I → ℝ) : ℝ := ∫ y, pivotDensityPullback A B f (y, v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotNormalizedMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem normalizedIntegerPivot_det_ne_zero (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedIntegerPivot A S P).det ≠ 0 := by
  apply abs_pos.mp
  rw [normalizedIntegerPivot_abs_det A S P hS hP]
  have hq : (0 : ℝ) < A.det.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hA
  exact div_pos (mul_pos hq (Finset.prod_pos fun i _ => hS i))
    (Finset.prod_pos fun i _ => hP i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def normalizedPivotEquiv (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (I → ℝ) ≃L[ℝ] (I → ℝ) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem map_cubeShift (φ : A →+ B) {j : ℕ} (hs : Fin j → A) (ω : Fin j → Bool) :
    φ (cubeShift hs ω) = cubeShift (fun i ↦ φ (hs i)) ω := by
  simp only [cubeShift, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

def SupportedCube.map (φ : A →+ B) {j : ℕ} {Q : Set A} (p : SupportedCube j Q) :
    SupportedCube j (φ '' Q) :=
  ⟨(fun i ↦ φ (p.val.1 i), φ p.val.2), fun ω ↦
    ⟨p.val.2 + cubeShift p.val.1 ω, p.property ω, by rw [map_add, map_cubeShift]⟩⟩

theorem SupportedCube.map_injective {φ : A →+ B} {Q : Set A}
    (hφ : Set.InjOn φ Q) (j : ℕ) :
    Function.Injective (SupportedCube.map φ : SupportedCube j Q → _) := by
  intro p q he
  have hb : φ p.val.2 = φ q.val.2 := congrArg (fun r ↦ r.val.2) he
  have hx : p.val.2 = q.val.2 := hφ p.base_mem q.base_mem hb
  have hh (i : Fin j) : φ (p.val.1 i) = φ (q.val.1 i) :=
    congrArg (fun r ↦ r.val.1 i) he
  have hi (i : Fin j) : p.val.1 i = q.val.1 i := by
    have hv := hφ (p.axis_mem i) (q.axis_mem i) (by simp only [map_add, hb, hh])
    rw [hx] at hv
    exact add_left_cancel hv
  apply Subtype.ext
  exact Prod.ext (funext hi) hx

theorem exists_lift_cube {φ : A →+ B} {Q : Set A} (hφ : ReflectsPairSums φ Q)
    (j : ℕ) (x : B) (hs : Fin j → B)
    (hQ : ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ φ '' Q) :
    ∃ a : A, ∃ ds : Fin j → A,
      (∀ ω : Fin j → Bool, a + cubeShift ds ω ∈ Q) ∧ φ a = x ∧ ∀ i, φ (ds i) = hs i := by
  induction j generalizing x with
  | zero =>
    obtain ⟨a, ha, he⟩ := hQ (fun _ ↦ false)
    refine ⟨a, (fun i ↦ Fin.elim0 i), ?_, ?_, fun i ↦ Fin.elim0 i⟩
    · intro ω
      simpa [cubeShift] using ha
    · simpa using he
  | succ j ih =>
    have hface : ∀ ω : Fin j → Bool, x + cubeShift (Fin.tail hs) ω ∈ φ '' Q := by
      intro ω
      have hv := hQ (Fin.cons false ω)
      rw [← Fin.cons_self_tail hs, cubeShift_cons_false] at hv
      exact hv
    obtain ⟨a, ds, hds, ha, hmap⟩ := ih x (Fin.tail hs) hface
    obtain ⟨b, hb, hbmap⟩ := hQ (Fin.cons true (fun _ ↦ false))
    rw [← Fin.cons_self_tail hs, cubeShift_cons_true, cubeShift_false, add_zero] at hbmap
    have hamem : a ∈ Q := by simpa using hds (fun _ ↦ false)
    have hdmap : φ (b - a) = hs 0 := by rw [map_sub, hbmap, ha]; abel
    refine ⟨a, Fin.cons (b - a) ds, ?_, ha, ?_⟩
    · intro ω
      rw [← Fin.cons_self_tail ω]
      cases hω : ω 0 with
      | false => simpa only [cubeShift_cons_false] using hds (Fin.tail ω)
      | true =>
        rw [cubeShift_cons_true]
        obtain ⟨c, hc, hcmap⟩ := hQ (Fin.cons true (Fin.tail ω))
        rw [← Fin.cons_self_tail hs, cubeShift_cons_true] at hcmap
        have hpair : (a + cubeShift ds (Fin.tail ω)) + b = c + a := by
          apply hφ _ (hds (Fin.tail ω)) b hb c hc a hamem
          simp only [map_add, map_cubeShift, hmap, hbmap, hcmap, ha]
          abel
        have he : a + (b - a + cubeShift ds (Fin.tail ω)) = c := by
          apply add_right_cancel (b := a)
          calc
            (a + (b - a + cubeShift ds (Fin.tail ω))) + a =
                (a + cubeShift ds (Fin.tail ω)) + b := by abel
            _ = c + a := hpair
        rwa [he]
    · intro i
      refine Fin.cases ?_ (fun k ↦ ?_) i
      · exact hdmap
      · exact hmap k

theorem SupportedCube.map_surjective {φ : A →+ B} {Q : Set A}
    (hφ : ReflectsPairSums φ Q) (j : ℕ) :
    Function.Surjective (SupportedCube.map φ : SupportedCube j Q → _) := by
  intro p
  obtain ⟨a, ds, hds, ha, hmap⟩ := exists_lift_cube hφ j p.val.2 p.val.1 p.property
  refine ⟨⟨(ds, a), hds⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext (funext hmap) ha

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem SupportedCube.first_mem_difference {j : ℕ} {Q : Finset A}
    (p : SupportedCube (j + 1) (Q : Set A)) : p.val.1 0 ∈ cubeDifferenceSupport Q :=
  Finset.mem_image.mpr ⟨(p.val.2, p.val.2 + p.val.1 0),
    Finset.mem_product.mpr ⟨p.base_mem, p.axis_mem 0⟩, by simp⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeTranslation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [DecidableEq A]

theorem ReflectsPairSums.translate {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (a : A) :
    ReflectsPairSums φ (translateSupport a Q : Set A) := by
  intro b hb c hc d hd e he hrel
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
  simp only [map_add] at hrel
  have hr : φ x + φ y = φ z + φ w := by
    apply add_left_cancel (a := φ a + φ a)
    calc
      _ = (φ a + φ x) + (φ a + φ y) := by abel
      _ = (φ a + φ z) + (φ a + φ w) := hrel
      _ = _ := by abel
  have hsum := hφ x hx y hy z hz w hw hr
  calc
    (a + x) + (a + y) = (a + a) + (x + y) := by abel
    _ = (a + a) + (z + w) := by rw [hsum]
    _ = _ := by abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanAffinePolynomial {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) : MvPolynomial (BlockParameter B F α) ℝ :=
  ∑ r : Option α, MvPolynomial.C (booleanFeature r t : ℝ) * MvPolynomial.X (b, v, r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BooleanProductSampler
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

noncomputable def booleanBlockPolynomial (b : B) (t : Finset α) :
    MvPolynomial (BlockParameter B F α) ℝ :=
  ∏ v : F, booleanAffinePolynomial b v t

noncomputable def booleanSamplerPolynomial (c : B → ℝ) (s : Finset α) :
    MvPolynomial (BlockParameter B F α) ℝ :=
  booleanCoefficient (fun t => ∑ b : B, MvPolynomial.C (c b) * booleanBlockPolynomial b t) s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

noncomputable def booleanSamplerMap (c : B → ℝ) (sets : O → Finset α)
    (a : BlockParameter B F α → ℝ) (o : O) : ℝ :=
  MvPolynomial.eval a (booleanSamplerPolynomial c (sets o))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def scalarCubeMeasure (α : Type*) [Fintype α] [DecidableEq α] :
    Measure (Option α → ℝ) :=
  (volume (scalarCubeDomain α))⁻¹ • volume.restrict (scalarCubeDomain α)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeProductMeasure (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] : Measure (ι → Option α → ℝ) :=
  Measure.pi (fun _ : ι => scalarCubeMeasure α)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def polynomialColumns {P I J : Type*} [Fintype I] [Fintype J]
    (p : I → J → MvPolynomial P ℝ) (x : P → ℝ) : (J → ℝ) →L[ℝ] (I → ℝ) :=
  matrixSupCLM (fun i j => MvPolynomial.eval x (p i j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BlockCubeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def blockCubeFlatten (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] :
    ((B × F) → Option α → ℝ) ≃L[ℝ] (BlockParameter B F α → ℝ) where
  toLinearEquiv :=
    { toFun := fun x z => x (z.1, z.2.1) z.2.2
      invFun := fun a bf r => a (bf.1, bf.2, r)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BooleanAffineInput
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanAffineInput {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) : MvPolynomial I ℝ :=
  ∑ r, MvPolynomial.C (booleanFeature r t : ℝ) * a r

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def booleanJetColumnPolynomial {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α) : MvPolynomial P ℝ :=
  booleanCoefficient (fun t => polynomialMonomial (fun k => booleanAffineInput (input k) t) e) s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def blockCubeMeasure (B F α : Type*) [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] : Measure (BlockParameter B F α → ℝ) :=
  Measure.map (blockCubeFlatten B F α) (scalarCubeProductMeasure (B × F) α)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPairAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace SlicedProductBlock

variable {ι : Type*} [Fintype ι]

structure Admissible (B : SlicedProductBlock ι) : Prop where
  coefficient_ne_zero : B.coefficient ≠ 0
  lower_nonneg : ∀ i, 0 ≤ B.lower i
  width_pos : ∀ i, 0 < B.width i
  lastWidth_pos : 0 < B.lastWidth

noncomputable def value (B : SlicedProductBlock ι) (x : ι → ℝ) (u : ℝ) : ℝ :=
  B.coefficient * B.prefixProduct x * (B.lastLower + B.lastWidth * u)

noncomputable def volumeScale (B : SlicedProductBlock ι) : ℝ :=
  |B.coefficient| * B.lastWidth * ∏ i, B.width i

theorem volumeScale_pos {B : SlicedProductBlock ι} (hB : B.Admissible) : 0 < B.volumeScale :=
  mul_pos (mul_pos (abs_pos.mpr hB.coefficient_ne_zero) hB.lastWidth_pos)
    (Finset.prod_pos (fun i _ => hB.width_pos i))

end SlicedProductBlock

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def pairScale (A B : SlicedProductBlock ι) : ℝ := min A.volumeScale B.volumeScale

noncomputable def pairWidth (A B : SlicedProductBlock ι) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  max |A.slope p.1| |B.slope p.2|

theorem pairScale_pos {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    0 < pairScale A B := lt_min (volumeScale_pos hA) (volumeScale_pos hB)

noncomputable def pairCap (A B : SlicedProductBlock ι) : ℝ :=
  (pairScale A B)⁻¹ * 4 ^ Fintype.card ι

theorem pairCap_pos {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    0 < pairCap A B := mul_pos (inv_pos.mpr (pairScale_pos hA hB)) (by positivity)

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourSlicedProductSmoothing
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def pairCapNN {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) : ℝ≥0 := ⟨pairCap A B, (pairCap_pos hA hB).le⟩

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SpatialProductDensity
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def pairSource (ι : Type*) [Fintype ι] : Measure (PairInput ι) :=
  ((unitBoxMeasure ι).prod (unitBoxMeasure ι)).prod
    (unitScalarMeasure.prod unitScalarMeasure)

noncomputable def pairValue (A B : SlicedProductBlock ι) (p : PairInput ι) : ℝ :=
  A.value p.1.1 p.2.1 + B.value p.1.2 p.2.2

noncomputable def fourSource (ι : Type*) [Fintype ι] : Measure (FourInput ι) :=
  (pairSource ι).prod (pairSource ι)

noncomputable def fourValue (A B C D : SlicedProductBlock ι) (p : FourInput ι) : ℝ :=
  pairValue A B p.2 + pairValue C D p.1

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def fourBoxValue (B : Fin 4 → SlicedProductBlock ι)
    (x : Fin 4 × Option ι → ℝ) : ℝ :=
  ∑ b, (B b).value (fun i => x (b, some i)) (x (b, none))

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

noncomputable def splitFreeColumns (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) : (J ⊕ N → ℝ) →L[ℝ] (I → ℝ) :=
  B.comp (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (.inl j)) +
    C.comp (ContinuousLinearMap.pi fun n => ContinuousLinearMap.proj (.inr n))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

open scoped BigOperators

theorem integerScalarCube_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} {x : Option I → ℤ} (hx : IntegerScalarCube L x) (i : Option I) :
    -(L : ℤ) < x i ∧ x i < L := by
  have h0 := hx ∅
  simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h0
  cases i with
  | none => omega
  | some i =>
    have h1 := hx {i}
    simp only [integerScalarCubeValue, Finset.sum_singleton] at h1
    omega

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def normalizedJetColumn {Z P K α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (s : Finset α) : MvPolynomial P ℝ :=
  booleanJetColumnPolynomial e (fun k r => frozenTupleCoordinate z (input k r)) s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def normalizedJetDensity {Z P K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : I → Finset α)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (x : P → ℝ) : (I → ℝ) → ℝ :=
  pivotOutputDensity A
    (splitFreeColumns F (polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x))
    (splitFreeProfile f g)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open scoped Matrix

noncomputable def coefficientWeightSum {J : Type*} (f : (J → ℝ) → ℝ) (S : J → ℝ) : ℝ :=
  ∑' z : J → ℤ, coefficientWeight f S z

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid
namespace OAI


namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

theorem abs_eval_sub_eval_unit_mass_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (x y : σ → ℝ) {δ : ℝ} {m : ℕ}
    (hδ : 0 ≤ δ) (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    (hxy : ∀ i, |x i - y i| ≤ δ) (hdegree : P.totalDegree ≤ m) :
    |eval x P - eval y P| ≤ (m : ℝ) * realPolynomialMass P * δ := by
  classical
  have hmonomial (α : σ →₀ ℕ) (hα : α ∈ P.support) :
      |(∏ i, x i ^ α i) - ∏ i, y i ^ α i| ≤ (m : ℝ) * δ := by
    have he (i : σ) : |x i ^ α i - y i ^ α i| ≤ δ * α i := by
      simpa only [one_pow, mul_one] using abs_pow_sub_pow_box_bound
        (B := (1 : ℝ)) le_rfl hδ (hx i) (hy i) (hxy i) (le_refl (α i))
    have hp := abs_prod_sub_prod_unit_sum Finset.univ
      (fun i => x i ^ α i) (fun i => y i ^ α i) (fun i => δ * α i)
      (fun _ _ => by positivity)
      (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hx i))
      (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hy i))
      (fun i _ => he i)
    have hsum : (∑ i, (α i : ℝ)) ≤ (m : ℝ) := by
      exact_mod_cast (show (∑ i, α i) ≤ m by
        have hs : α.sum (fun (_ : σ) (n : ℕ) => n) = ∑ i, α i :=
          Finsupp.sum_fintype α (fun _ n => n) (fun _ => rfl)
        rw [← hs]
        exact (MvPolynomial.le_totalDegree hα).trans hdegree)
    apply hp.trans
    rw [← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hsum hδ]
  change |P.eval₂ (RingHom.id ℝ) x - P.eval₂ (RingHom.id ℝ) y| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ α ∈ P.support, |P.coeff α| * ((m : ℝ) * δ) := by
      apply Finset.sum_le_sum
      intro α hα
      change |P.coeff α * ∏ i, x i ^ α i - P.coeff α * ∏ i, y i ^ α i| ≤ _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hmonomial α hα) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold realPolynomialMass; ring

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateNativeMajorBudget
namespace OAI

section

namespace Erdos3

def allocatedCandidateNativeMajorBudget (pNative v : ℝ) : ℝ :=
  productNiltestBudget pNative + pNative + v + 2

theorem allocatedCandidateNativeMajorBudget_mono {pNative qNative v w : ℝ}
    (hpNative : 0 ≤ pNative) (hNative : pNative ≤ qNative) (hvw : v ≤ w) :
    allocatedCandidateNativeMajorBudget pNative v ≤
      allocatedCandidateNativeMajorBudget qNative w := by
  unfold allocatedCandidateNativeMajorBudget productNiltestBudget productObservableLipBudget
  gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UniformExternalNetScalarBudget
namespace OAI

section

namespace Erdos3

theorem exists_uniformExternalNetScalarBudget (netExponent localExponent : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p ε : ℝ, 0 ≤ p → 0 < ε → ε ≤ 1 →
      ∃ q : ℝ, 0 ≤ q ∧ p ≤ q ∧ Real.log (1 / ε) ≤ q ∧
        (p + Real.log (1 / (ε / 3)) + netExponent) ^ netExponent ≤ q ∧
        (q + localExponent) ^ localExponent ≤ (p + Real.log (1 / ε) + C) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C netExponent + 3) ^ netExponent +
      3 + Polynomial.C localExponent) ^ localExponent
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p ε hp hε hε1
  have hlog : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div hε).2 hε1)
  have hlogThree : Real.log (1 / (ε / 3)) = Real.log (1 / ε) + Real.log 3 := by
    rw [show (1 : ℝ) / (ε / 3) = (1 / ε) * 3 by field_simp]
    exact Real.log_mul (by positivity) (by norm_num)
  have hthree : Real.log (3 : ℝ) ≤ 3 := Real.log_le_self (by norm_num)
  have hthree0 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  let x := p + Real.log (1 / ε)
  have hx : 0 ≤ x := add_nonneg hp hlog
  let q := x + (x + netExponent + 3) ^ netExponent + 3
  have hpower : 0 ≤ (x + netExponent + 3) ^ netExponent := by positivity
  refine ⟨q, by dsimp [q]; positivity, ?_, ?_, ?_, ?_⟩
  · dsimp [q, x]
    linarith only [hlog, hpower]
  · dsimp [q, x]
    linarith only [hp, hpower]
  · have hbase0 : 0 ≤ p + Real.log (1 / (ε / 3)) + netExponent := by
      rw [hlogThree]
      positivity
    have hbase : p + Real.log (1 / (ε / 3)) + netExponent ≤
        x + netExponent + 3 := by
      rw [hlogThree]
      dsimp [x]
      linarith only [hthree]
    exact (pow_le_pow_left₀ hbase0 hbase netExponent).trans (by dsimp [q]; linarith)
  · simpa [P, q, x, Polynomial.eval₂_pow] using hbudget x hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def weightedDualVector (p : FiniteProbabilityWeights Ω)
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) : ℂ :=
  star (f (Pi.single x 1)) / (p.weight x : ℂ)

theorem weightedDualVector_norm (p : FiniteProbabilityWeights Ω)
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) :
    ‖weightedDualVector p f x‖ = ‖f (Pi.single x 1)‖ / p.weight x := by
  rw [weightedDualVector, norm_div, norm_star, Complex.norm_real,
    Real.norm_of_nonneg (p.nonneg x)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SignedSplitCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {R E F I J : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [Fintype I] [Fintype J]

noncomputable def signedSplitCoordinates (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (bK : Basis I R (LinearMap.ker q)) (bI : Basis J R F) :
    E ≃ₗ[R] (J → R) × (I → R) :=
  (splitSurjectionEquiv q s hs).symm.trans
    ((bK.equivFun.prodCongr bI.equivFun).trans
      ((LinearEquiv.prodComm R (I → R) (J → R)).trans
        ((LinearEquiv.neg R : (J → R) ≃ₗ[R] (J → R)).prodCongr
          (LinearEquiv.refl R (I → R)))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisSurjectionSection
namespace OAI

section

namespace Erdos3

open Module

variable {R E F I : Type*} [CommSemiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F]

theorem basisSurjectionSection_rightInverse (q : E →ₗ[R] F) (hq : Function.Surjective q)
    (b : Basis I R F) (x : F) : q (basisSurjectionSection q hq b x) = x := by
  have he : q.comp (basisSurjectionSection q hq b) = LinearMap.id := by
    apply b.ext
    intro i
    change q (b.constr R (fun j => (hq (b j)).choose) (b i)) = b i
    rw [b.constr_basis]
    exact (hq (b i)).choose_spec
  exact LinearMap.congr_fun he x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def standardEuclideanLinearEquiv (J : Type*) [Fintype J] :
    (J → ℤ) ≃ₗ[ℤ] standardEuclideanLattice J :=
  ((EuclideanSpace.basisFun J ℝ).toBasis.restrictScalars ℤ).equivFun.symm

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalSectionKernelEquiv (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    latticeSection Λ W ≃ₗ[ℤ] LinearMap.ker (orthogonalLatticeProjection Λ Wᗮ) where
  toFun x := ⟨⟨x.val.val, x.property⟩,
    Subtype.ext (W.orthogonalProjectionOnto_orthogonal_apply_eq_zero x.val.property)⟩
  invFun x := ⟨⟨x.val.val, by
    have h := Wᗮ.orthogonalProjectionOnto_eq_zero_iff.mp
      (congrArg Subtype.val (show orthogonalLatticeProjection Λ Wᗮ x.val = 0 from x.property))
    change x.val.val ∈ Wᗮᗮ at h
    rwa [W.orthogonal_orthogonal] at h⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def affineProductProfileLip (I : Type*) [Fintype I] (δ : ℝ≥0) : ℝ≥0 :=
  Fintype.card I * probabilityProfileLipschitz * δ⁻¹ ^ (Fintype.card I + 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalConstantDensityBound
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

noncomputable def earlyConstantDensityCap (a n : ℕ) (R V : ℝ) : ℝ :=
  V * (R / 4)⁻¹ ^ a * (8 * (probabilityProfileLipschitz : ℝ) / (R / 4)) ^ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

noncomputable def integerMappedCubeTuple {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z : Z → ℤ) (x : X → ℤ) : Finset α → K → ℤ :=
  integerAffineCube (fun k => Sum.elim z x (input k none))
    (fun i k => Sum.elim z x (input k (some i)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_linear_model_partner {V I : Type*}
    [AddCommGroup V] [Module ℂ V] [Fintype I]
    (test : V →ₗ[ℂ] ℂ) (v e : V) (Q : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • Q i) + e) {delta M : ℝ}
    (hdelta : 0 < delta) (hM : 0 < M) (hc : (∑ i, ‖c i‖) ≤ M)
    (herr : ‖test e‖ ≤ delta / 2) (hscore : delta ≤ ‖test v‖) :
    ∃ i, delta / (2 * M) ≤ ‖test (Q i)‖ := by
  have hid : test v = (∑ i, c i * test (Q i)) + test e := by
    rw [hmodel, map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hsum : delta / 2 ≤ ‖∑ i, c i * test (Q i)‖ := by
    have ht := norm_add_le (∑ i, c i * test (Q i)) (test e)
    rw [← hid] at ht
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c (fun i => test (Q i))
    (by positivity : 0 < delta / 2) hM hc hsum
  refine ⟨i, ?_⟩
  convert hi using 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

noncomputable def allocatedWidthFloor (R σ : ℝ) (L s a : ℕ) : ℝ :=
  min (R / 4) (min (principalProfileSize R a / 2) (tailProfileSize R σ a)) / (L : ℝ)^s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarginalTailModeling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] [DecidableEq Ω] in

theorem model_error_norm_le {ι : Type*} [Fintype ι]
    {b e : Ω → ℂ} {Q : ι → (Ω → ℂ)} {c : ι → ℝ} {M R : ℝ}
    (hb : ∀ x, ‖b x‖ ≤ M) (hQ : ∀ i x, ‖Q i x‖ ≤ 1)
    (hdecomp : b = (∑ i, c i • Q i) + e) (hc : (∑ i, |c i|) ≤ R) :
    ∀ x, ‖e x‖ ≤ M + R := by
  intro x
  have hsum : ‖(∑ i, c i • Q i) x‖ ≤ R := by
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _ => ?_)).trans hc
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hQ i x)
  have he : e x = b x - (∑ i, c i • Q i) x := by
    have h := congrFun hdecomp x
    simp only [Pi.add_apply] at h
    exact eq_sub_of_add_eq' h.symm
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (hb x) hsum)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def affineProfileLogBound (n : ℕ) (t : ℝ) : ℝ :=
  n + (probabilityProfileLipschitz : ℝ) + (n + 1) * t

noncomputable def affineCoefficientCommonBudget (n d : ℕ) (b t : ℝ) : ℝ :=
  b + d + affineProfileLogBound n t

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {K : Type*} (oldKeep keep : K → Prop)

@[simp] theorem axisInsertion_kept (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (u : {i // keep i} → ℤ) (i : {i // keep i}) :
    axisInsertion oldKeep keep fixed u (axisInclusion oldKeep keep hsub i) = u i := by
  simp [axisInsertion, axisInclusion, i.property]

theorem axisInsertion_injective (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ) :
    Function.Injective (axisInsertion oldKeep keep fixed) := by
  intro x y h
  funext i
  simpa only [axisInsertion_kept] using
    congrFun h (axisInclusion oldKeep keep hsub i)

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

def CoefficientAxisRow (K : Type*) {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ} :
    LayerSamplerAxis I n → Type _
  | ⟨j, .inl _⟩ => BoundedCoefficientExponent K (j.val+1) → ℝ
  | ⟨j, .inr _⟩ => BoundedCoefficientExponent K (j.val+1) → ℤ

instance coefficientAxisRowMeasurable (K : Type*) {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    (a : LayerSamplerAxis I n) : MeasurableSpace (CoefficientAxisRow K a) :=
  match a with
  | ⟨j, .inl _⟩ => inferInstanceAs (MeasurableSpace (BoundedCoefficientExponent K (j.val+1) → ℝ))
  | ⟨j, .inr _⟩ => inferInstanceAs (MeasurableSpace (BoundedCoefficientExponent K (j.val+1) → ℤ))

abbrev CoefficientAxisArrays (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ) :=
  ∀ a : LayerSamplerAxis I n, CoefficientAxisRow K a

def coefficientAxisEquiv (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ) :
    CoefficientSamplerArrays (K := K) I n ≃ᵐ CoefficientAxisArrays K I n :=
  (MeasurableEquiv.piCongrRight (fun j =>
    (MeasurableEquiv.sumPiEquivProdPi (fun a : I j ⊕ Fin (n j) => CoefficientAxisRow K ⟨j, a⟩)).symm)).trans
      (MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientAxisRow K ⟨j, a⟩)).symm

variable {K : Type*} {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val+1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val+1) → PMF ℤ)

def coefficientAxisSplitEquiv (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ)
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    CoefficientSamplerArrays (K := K) I n ≃ᵐ
      (∀ a : {a // P a}, CoefficientAxisRow K a.val) ×
        (∀ a : {a // ¬P a}, CoefficientAxisRow K a.val) :=
  (coefficientAxisEquiv K I n).trans (MeasurableEquiv.piEquivPiSubtypeProd (CoefficientAxisRow K) P)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

def CoefficientJetAxisRow (O : Fin m → Type*) : LayerSamplerAxis I n → Type _
  | ⟨j, .inl _⟩ => O j → ℝ
  | ⟨j, .inr _⟩ => O j → ℤ

instance coefficientJetAxisRowMeasurable (O : Fin m → Type*) (a : LayerSamplerAxis I n) :
    MeasurableSpace (CoefficientJetAxisRow O a) :=
  match a with
  | ⟨j, .inl _⟩ => inferInstanceAs (MeasurableSpace (O j → ℝ))
  | ⟨j, .inr _⟩ => inferInstanceAs (MeasurableSpace (O j → ℤ))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.JetAxisCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)

def coefficientJetAxisEquiv :
    (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ≃ᵐ
      (∀ a : LayerSamplerAxis I n, CoefficientJetAxisRow O a) :=
  (MeasurableEquiv.piCongrRight (fun j =>
    (MeasurableEquiv.sumPiEquivProdPi (fun a : I j ⊕ Fin (n j) => CoefficientJetAxisRow O ⟨j, a⟩)).symm)).trans
      (MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

noncomputable def unitProfilePrincipalSize (d : D) : ℝ :=
  principalProfileSize 1 (Fintype.card (B d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

theorem positiveProjectionAccuracy_mass_bound {p : ℝ} (hp : 0 ≤ p) :
    3 * positiveProjectionAccuracy p ≤ Real.exp (-p) ∧
      3 * positiveProjectionAccuracy p ≤ 1 / 2 := by
  have hfour : (3 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have htwo : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hnine : (9 : ℝ) ≤ Real.exp 4 := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (2 : ℝ)]
  have hsix : (6 : ℝ) ≤ Real.exp (2 * p + 4) :=
    (by linarith : (6 : ℝ) ≤ Real.exp 4).trans (Real.exp_le_exp.mpr (by linarith))
  constructor
  · calc
      _ ≤ Real.exp 4 * Real.exp (-(2 * p + 4)) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = Real.exp (-(2 * p)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-p) := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ = 3 / Real.exp (2 * p + 4) := by
        simp only [positiveProjectionAccuracy, Real.exp_neg, div_eq_mul_inv]
      _ ≤ 3 / (6 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsix
      _ = 1 / 2 := by norm_num

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientFrontBudget
namespace OAI

section

namespace Erdos3

noncomputable def coefficientFrontLog (i j : ℕ) (b t e : ℝ) : ℝ :=
  coefficientLogAllowance i j (affineCoefficientCommonBudget j j b t) + e + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

noncomputable def allocatedUnitProfileWidth (R σ : ℝ) (a : ℕ) : ℝ :=
  allocatedWidthFloor R σ 1 0 a

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def kernelRowOutputLog (q n j k u d : ℕ) (p : ℝ) : ℝ :=
  let P := kernelGeometryLog q n j k d p
  (j : ℝ)^2 + (j + 1) * P + affineProfileLogBound k p + k * (P + 1) +
    jetOutputRadiusLog q u d P + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CrossRowCharacterDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem characterCrossRow_norm (f g : G → ℂ) (χ : G → AddChar G ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (h n : G) :
    ‖characterCrossRow f g χ h n‖ ≤ 1 := by
  simp only [characterCrossRow, norm_mul, norm_star, AddChar.norm_apply, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))

theorem characterCrossRow_derivative (f g : G → ℂ) (χ : G → AddChar G ℂ) (h k n : G) :
    multiplicativeDerivative (characterCrossRow f g χ h) k n =
      (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) * χ h k := by
  have hcancel : χ h n * star (χ h n) = 1 := by
    change χ h n * (starRingEnd ℂ) (χ h n) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, AddChar.norm_apply]
    norm_num
  have hshift : n + k + h = n + h + k := by abel
  simp only [characterCrossRow, multiplicativeDerivative, star_mul, star_star,
    (χ h).map_add_eq_mul, hshift]
  calc
    _ = (((f n * star (f (n + k))) * (star (g (n + h)) * g (n + h + k))) * χ h k) *
        (χ h n * star (χ h n)) := by ring
    _ = _ := by rw [hcancel, mul_one]; ring

theorem characterCrossRow_derivative_correlation_norm (f g : G → ℂ)
    (χ : G → AddChar G ℂ) (h k : G) (K : G → ℂ) :
    ‖𝔼 n, multiplicativeDerivative (characterCrossRow f g χ h) k n * star (K n)‖ =
      ‖𝔼 n, (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (K n)‖ := by
  have heq : (𝔼 n, multiplicativeDerivative (characterCrossRow f g χ h) k n * star (K n)) =
      χ h k * (𝔼 n, (multiplicativeDerivative f k n *
        star (multiplicativeDerivative g k (n + h))) * star (K n)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    rw [characterCrossRow_derivative]
    ring
  rw [heq, norm_mul, AddChar.norm_apply, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3

theorem forecastAugmentedUnitThreshold_bounds {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    0 < forecastAugmentedUnitThreshold u p K C Fcap ∧
      forecastAugmentedUnitThreshold u p K C Fcap ≤ 1 ∧
      Real.exp (-(2 * u + 4 * p + 8)) ≤ forecastAugmentedUnitThreshold u p K C Fcap := by
  let τ := Real.exp (-(u + 3))
  let D := max 1 ((2 * K * C + Fcap) / τ)
  have hτ : 0 < τ := Real.exp_pos _
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hτ1 : τ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hep : 1 ≤ Real.exp p := Real.one_le_exp hp
  have hnum : τ / Real.exp p ^ 2 ≤ 1 :=
    (div_le_iff₀ (sq_pos_of_pos (Real.exp_pos p))).mpr (by nlinarith)
  have hKC : K * C ≤ Real.exp p * Real.exp p := mul_le_mul hKp hCp hC (Real.exp_nonneg p)
  have hbound : D ≤ 3 * Real.exp (2 * p + u + 3) := by
    apply max_le
    · have he := Real.one_le_exp (show 0 ≤ 2 * p + u + 3 by positivity)
      linarith
    · calc
        _ ≤ (3 * (Real.exp p * Real.exp p)) / τ := by
          apply div_le_div_of_nonneg_right _ hτ.le
          nlinarith
        _ = 3 * Real.exp (2 * p + u + 3) := by
          dsimp only [τ]
          rw [show 2 * p + u + 3 = p + p + (u + 3) by ring]
          simp only [Real.exp_add, Real.exp_neg, div_eq_mul_inv, inv_inv]
          ring
  refine ⟨div_pos (div_pos hτ (sq_pos_of_pos (Real.exp_pos p))) hD,
    (div_le_iff₀ hD).mpr (by nlinarith [le_max_left 1 ((2 * K * C + Fcap) / τ)]), ?_⟩
  change _ ≤ (τ / Real.exp p ^ 2) / D
  calc
    _ ≤ Real.exp (-(2 * u + 4 * p + 6)) / 3 := by
      rw [show -(2 * u + 4 * p + 8) = -(2 * u + 4 * p + 6) - 2 by ring, Real.exp_sub]
      exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
        (by linarith [Real.add_one_le_exp (2 : ℝ)])
    _ = (τ / Real.exp p ^ 2) / (3 * Real.exp (2 * p + u + 3)) := by
      dsimp only [τ]
      rw [show -(2 * u + 4 * p + 6) = -(u + 3) - (p + p) - (2 * p + u + 3) by ring,
        Real.exp_sub, Real.exp_sub, Real.exp_add]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hD hbound

theorem forecastAugmentedUnitThreshold_atom_gain {u p q K C Fcap M : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p)
    (hM : 0 ≤ M) (hMq : M ≤ Real.exp q) :
    Real.exp (-(2 * u + 4 * p + q + 20)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / (8 * (M + 1)) := by
  have hα := (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2
  have hden : 8 * (M + 1) ≤ Real.exp (q + 12) := by
    rw [Real.exp_add]
    have heq := Real.one_le_exp hq
    have he12 : (16 : ℝ) ≤ Real.exp 12 := by
      have h6 := Real.add_one_le_exp (6 : ℝ)
      have h12 : Real.exp (12 : ℝ) = Real.exp 6 * Real.exp 6 := by
        rw [← Real.exp_add]; norm_num
      rw [h12]
      nlinarith
    nlinarith [Real.exp_pos q]
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp (q + 12) := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / (8 * (M + 1)) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hden
    _ ≤ _ := div_le_div_of_nonneg_right hα (by positivity)

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_approximation_precision {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    Real.exp (-(2 * u + 4 * p + 12)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / 8 := by
  have h8 : (8 : ℝ) ≤ Real.exp 4 := by
    have h2 := Real.add_one_le_exp (2 : ℝ)
    have he : Real.exp (4 : ℝ) = Real.exp 2 * Real.exp 2 := by
      rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 4 := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / 8 :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) h8
    _ ≤ _ := div_le_div_of_nonneg_right
      (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2
      (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtPrimePowerIntegerPolynomialOutput {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) : ℤ :=
  eval (fun v => ((crtInput (fun l => p l ^ A l) hq
    (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v) v).val : ℤ))
      (F j.1 j.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]

variable {T : Type*} [Fintype X]

omit [Fintype X] in
theorem fixedSpatialKernelBlock_slice (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (second : Bool) :
    fixedSpatialKernelBlock e W L (fixedSpatialKernelSliceFrame W L z lower width) second =
      fun x i => fixedSpatialKernelBlock e W L z second x i *
        width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)) := by
  funext x i
  simp only [fixedSpatialKernelBlock, fixedSpatialKernelSliceFrame_some]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NarrowSpatialSiteVariation
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

theorem jointIntegerPhysicalSite_normalized_dist_of_slope_sum
    {K X : Type*} [Fintype K] [Fintype X]
    (N : X → ℕ) (T : K → ℝ) (a : X → ℤ) (frame : Option K × X → ℤ)
    (u v : K → ℤ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hslope : ∀ x, (∑ k, |(frame (some k, x) : ℝ) / N x| * T k) ≤ C)
    (hcell : ∀ k, |(u k : ℝ) - (v k : ℝ)| ≤ T k * δ) :
    dist (fun x => (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x)
      (fun x => (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x) ≤ C * δ := by
  apply (dist_pi_le_iff (mul_nonneg hC hδ)).mpr
  intro x
  rw [Real.dist_eq]
  have hraw : (jointIntegerPhysicalSite u (a, frame) x : ℝ) -
      (jointIntegerPhysicalSite v (a, frame) x : ℝ) =
      ∑ k, ((u k : ℝ) - (v k : ℝ)) * (frame (some k, x) : ℝ) := by
    calc
      _ = (∑ k, (u k : ℝ) * (frame (some k, x) : ℝ)) -
          ∑ k, (v k : ℝ) * (frame (some k, x) : ℝ) := by
        simp only [jointIntegerPhysicalSite, Pi.add_apply, integerPhysicalSite,
          Int.cast_add, Int.cast_sum, Int.cast_mul]
        ring
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have heq : (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x -
      (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x =
      ∑ k, ((u k : ℝ) - (v k : ℝ)) * ((frame (some k, x) : ℝ) / N x) := by
    rw [← sub_div, hraw, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  calc
    _ ≤ ∑ k, |((u k : ℝ) - (v k : ℝ)) * ((frame (some k, x) : ℝ) / N x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (T k * δ) * |(frame (some k, x) : ℝ) / N x| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcell k) (abs_nonneg _)
    _ = (∑ k, |(frame (some k, x) : ℝ) / N x| * T k) * δ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hslope x) hδ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FrozenPolynomialAffineRange
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

theorem freezePolynomial_monomial_eq_C_of_no_keep (keep : I → Prop)
    (fixed : {i // ¬keep i} → R) (d : I →₀ ℕ)
    (hd : ¬∃ i, keep i ∧ d i ≠ 0) (c : R) :
    freezePolynomial keep fixed (monomial d c) =
      C (eval (finiteSplitPoint keep (0 : {i // keep i} → R) fixed) (monomial d c)) := by
  classical
  simp only [freezePolynomial, aeval_monomial, eval_monomial,
    map_mul, map_finsuppProd, map_pow]
  congr 1
  apply Finsupp.prod_congr
  intro i hi
  have hkeep : ¬keep i := fun h => hd ⟨i, h, Finsupp.mem_support_iff.mp hi⟩
  simp [frozenCoordinate, finiteSplitPoint, hkeep]

theorem freezePolynomial_monomial_coeff_eq_zero_of_no_keep (keep : I → Prop)
    (fixed : {i // ¬keep i} → R) (d : I →₀ ℕ)
    (hd : ¬∃ i, keep i ∧ d i ≠ 0) (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    (freezePolynomial keep fixed (monomial d (1 : R))).coeff α = 0 := by
  rw [freezePolynomial_monomial_eq_C_of_no_keep keep fixed d hd]
  exact coeff_C_of_ne_zero hα _

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem polynomialFamily_freeze_coeff_mem {I J R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial I R) (keep : I → Prop)
    (fixed : {i // ¬ keep i} → R) (K : Submodule R (J → R))
    (hP : ∀ d, (∃ i, keep i ∧ d i ≠ 0) → (fun j => (P j).coeff d) ∈ K)
    (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    (fun j => (freezePolynomial keep fixed (P j)).coeff α) ∈ K := by
  classical
  let S : Finset (I →₀ ℕ) := Finset.univ.biUnion (fun j => (P j).support)
  let c (d : I →₀ ℕ) : R := (freezePolynomial keep fixed (monomial d 1)).coeff α
  have hm (d : I →₀ ℕ) (r : R) :
      (freezePolynomial keep fixed (monomial d r)).coeff α = c d * r := by
    have hr : monomial d r = r • monomial d (1 : R) := by
      simp only [smul_monomial, smul_eq_mul, mul_one]
    rw [hr, map_smul, coeff_smul]
    exact mul_comm r (c d)
  have he (j : J) : (freezePolynomial keep fixed (P j)).coeff α =
      ∑ d ∈ S, c d * (P j).coeff d := by
    conv_lhs => rw [← (P j).support_sum_monomial_coeff, map_sum, coeff_sum]
    simp only [hm]
    apply Finset.sum_subset
    · intro d hd
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hd⟩
    · intro d _ hd
      have hz : (P j).coeff d = 0 := by
        simpa only [mem_support_iff, not_not] using hd
      rw [hz, mul_zero]
  have he' : (fun j => (freezePolynomial keep fixed (P j)).coeff α) =
      ∑ d ∈ S, c d • (fun j => (P j).coeff d) := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he j
  rw [he']
  apply K.sum_mem
  intro d _
  by_cases hd : ∃ i, keep i ∧ d i ≠ 0
  · exact K.smul_mem _ (hP d hd)
  · have hc : c d = 0 :=
      freezePolynomial_monomial_coeff_eq_zero_of_no_keep keep fixed d hd α hα
    rw [hc, zero_smul]
    exact K.zero_mem

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomialFamily_eval_sub_zero_mem {J I R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial I R) (K : Submodule R (J → R))
    (hP : ∀ d, d ≠ 0 → (fun j => (P j).coeff d) ∈ K) (x : I → R) :
    (fun j => eval x (P j) - eval (0 : I → R) (P j)) ∈ K := by
  classical
  have h := polynomialFamily_eval_mem
    (fun j => P j - C (constantCoeff (P j))) K (fun d => ?_) x
  · simpa only [map_sub, eval_C, eval_zero] using h
  · by_cases hd : d = 0
    · subst d
      simp only [coeff_sub, coeff_C, ↓reduceIte, constantCoeff_eq, sub_self]
      exact K.zero_mem
    · simpa [coeff_C, Ne.symm hd] using hP d hd

theorem frozenPolynomialFamily_coeff_mem {J Full : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (keep : Full → Prop)
    (fixed : {i // ¬ keep i} → ℤ) (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ d, (∃ i, keep i ∧ d i ≠ 0) →
      (fun j => (((β j).coeff d : ℤ) : ℝ)) ∈ K)
    (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    (fun j =>
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))).coeff α) ∈ K := by
  have hreal : ∀ d, (∃ i, keep i ∧ d i ≠ 0) →
      (fun j => (MvPolynomial.map (Int.castRingHom ℝ) (β j)).coeff d) ∈ K := by
    intro d hd
    simpa only [coeff_map, Int.coe_castRingHom] using hcoeff d hd
  have h := polynomialFamily_freeze_coeff_mem
    (fun j => MvPolynomial.map (Int.castRingHom ℝ) (β j)) keep
    (fun i => (fixed i : ℝ)) K hreal α hα
  simpa only [freezePolynomial_map, Int.coe_castRingHom] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateStageScalarBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration

theorem allocatedCandidateStage_reset_lower (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    v + (v + 2) ^ 4 ≤ allocatedCandidateStageResetInput s m v := by
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hrest : 0 ≤ ((s : ℝ) + 1) + s * (v + 1) +
      s * (((m : ℝ) + 1) + m * (v + 1)) := by positivity
  unfold allocatedCandidateStageResetInput
  linarith only [hrest]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FullFrozenChartMass
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial

theorem aeval_frozen_integer_chart {σ K : Type*}
    (β : σ → MvPolynomial K ℤ)
    (keep : K → Prop) (fixed : {i // ¬keep i} → ℤ)
    (p : MvPolynomial σ ℝ) :
    aeval (integerSampledRealChart (fun z => freezePolynomial keep fixed (β z))) p =
      freezePolynomial keep (fun i => (fixed i : ℝ))
        (aeval (integerSampledRealChart β) p) := by
  have hchart : integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) =
      fun z => freezePolynomial keep (fun i => (fixed i : ℝ)) (integerSampledRealChart β z) := by
    funext z
    exact integerSampledRealChart_freeze β keep fixed z
  rw [hchart]
  exact (comp_aeval_apply (integerSampledRealChart β)
    (freezePolynomial keep (fun i => (fixed i : ℝ))) p).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidatePhysicalOrdinaryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCandidateTerminalFullInput
    (s m Cprimitive : ℕ) (x work cumulative : ℝ) : ℝ :=
  (x + Cprimitive) ^ Cprimitive + x + work +
    s * m * certifiedAffineCenterBudget cumulative +
    certifiedAffineCenterBudget cumulative + s + m + 10

attribute [local irreducible] certifiedAffineCenterBudget

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PrecenterNativeSelectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem precenter_native_selection_correlation_budget
    {Bin : Type*} [Fintype Bin] [Nonempty Bin] {rFreq b c : ℝ}
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp b) :
    Real.exp (-(rFreq + b + c + 4)) ≤
      (Real.exp (-rFreq) / (2 * (Fintype.card Bin : ℝ))) / (2 * Real.exp c) := by
  have hcardpos : (0 : ℝ) < Fintype.card Bin := by
    exact_mod_cast Fintype.card_pos
  have hfour : Real.log (4 : ℝ) ≤ 4 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)).trans (by norm_num)
  calc
    _ ≤ Real.exp (-(rFreq + b + c)) / 4 :=
      precenter_exp_add_le_div (rFreq + b + c) 4 (by norm_num) hfour
    _ = (Real.exp (-rFreq) / (2 * Real.exp b)) / (2 * Real.exp c) := by
      rw [show -(rFreq + b + c) = -rFreq - b - c by ring,
        Real.exp_sub, Real.exp_sub]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
        (mul_le_mul_of_nonneg_left hcard (by norm_num))) (by positivity)

theorem precenter_native_selection_residual_budget
    {Bin : Type*} [Fintype Bin] [Nonempty Bin] {pLocal Eres rFreq b : ℝ}
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp b)
    (hres : pLocal + rFreq + b + 4 ≤ Eres) :
    Real.exp (pLocal - Eres) ≤
      (Real.exp (-rFreq) / (2 * (Fintype.card Bin : ℝ))) / 2 := by
  calc
    _ ≤ Real.exp (-(rFreq + b + 0 + 4)) := Real.exp_le_exp.mpr (by linarith only [hres])
    _ ≤ _ := by simpa using (precenter_native_selection_correlation_budget (c := 0) hcard)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleUniversalMaskProductiveGood
namespace OAI

section

namespace Erdos3

attribute [instance] FinitePrecenterInputFamily.branchFintype

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem externalNetMaskFamily_norm_le
    {Freq X Y I : Type*} (F : Freq → X → Y → ℂ)
    (centers : Freq → I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ f x, ∃ i, ∀ y, ‖F f x y - centers f i y‖ ≤ ε)
    (input : X → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hinput : ∀ x, ‖input x‖ ≤ B) (b : Freq × I) (x : X) :
    ‖externalNetMaskFamily F centers hnet input b x‖ ≤ B := by
  unfold externalNetMaskFamily
  split_ifs
  · exact hinput x
  · simpa only [norm_zero] using hB

end Erdos3

end

end OAI
end


