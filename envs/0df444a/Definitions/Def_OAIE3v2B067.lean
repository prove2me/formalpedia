-- Prove2me | Definitions.Def_OAIE3v2B067
-- name    : OAIE3v2B067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:16:18.785561+00:00
-- url     : https://prove2.me/theorems/f1d3f7c0-af93-4866-8c9b-99134640bd79
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 68 of 311
-- statement:
--   Definitions bundle 68 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B012`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B017`, `OAIE3v2B029`, `OAIE3v2B030`, `OAIE3v2B032`, `OAIE3v2B033`, `OAIE3v2B035`, `OAIE3v2B036`, `OAIE3v2B037` of this split.
--
--   Modules: `Dynamics/FixedListPowerBudget.lean`, `Dynamics/InitialBudgetJointReplacement.lean`, `Dynamics/JointPivotProfileBudget.lean`, `Dynamics/SmallRatioPotential.lean`, `Estimates/AmplificationFinalCostGrowth.lean`, `Estimates/AxisCompression.lean`, `Estimates/BooleanMinorDimension.lean`, `Estimates/GroupedSiteTensor.lean`, `Estimates/IndexedComparableScalarGeometryData.lean`, `Estimates/InteriorIntervalCutoff.lean`, `Estimates/JointBooleanRegularization.lean`, `Estimates/JointBooleanStability.lean`, `Estimates/LayeredCoverSiteExtension.lean`, `Estimates/NativeBoundedVariablePatchExpansion.lean`, `Estimates/NormalizedImageMask.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/PhysicalPairAccuracyLogBounds.lean`, `Estimates/PivotStageBoundary.lean`, `Estimates/ProductMeanPullback.lean`, `Estimates/ProductTensorGroupedBound.lean`, `Estimates/RepresentativeWindowPatch.lean`, `Estimates/ResidualErrorAllocation.lean`, `Estimates/ScalarCubeBoundaryCost.lean`, `Estimates/ScalarCubeFaceSlab.lean`, `Estimates/SecondaryMeshGeometry.lean`, `Estimates/SelectedCoefficientEvaluation.lean`, `Estimates/SelectedOutputL1.lean`, `Estimates/SelectedSplitUnitSource.lean`, `Estimates/ShiftedSmoothSelectedMarginal.lean`, `Estimates/SigmaAxisOperator.lean`, `Estimates/SlicedPrincipalInverse.lean`, `Estimates/SmoothPairErrorLogBounds.lean`, `Estimates/SplitSmoothProductProfile.lean`, `Estimates/WeightedPlateauSiteApproximation.lean`, `Fourier/CharacterCoordinateScale.lean`, `Fourier/LatticeTorusFourierCoefficient.lean`, `Fourier/PlateauFourierMode.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/PhysicalBoxPartition.lean`, `Geometry/PrincipalSpatialSiteComparison.lean`, `Geometry/ProductSectionSupport.lean`, `Geometry/SigmaAxisCoordinates.lean`, `Geometry/SortedLayerCoordinateEnumeration.lean`, `Geometry/SpatialPivotNormalization.lean`, `Geometry/UnitBoxInteriorCutoff.lean`, `Lattices/AffineSampleAlphabet.lean`, `Lattices/AllocatedSupportedAffineAccurateSource.lean`, `Lattices/AllocatedSupportedSlicedResidue.lean`, `Lattices/BoxResiduePartition.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/IntegerBoxCutoffLogBounds.lean`, `Lattices/LatticeHyperplaneBasis.lean`, `Lattices/LatticeSheetHaar.lean`, `Lattices/NormalizedIntegerBoxZeroCube.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Lattices/ResidueSliceUpperFailure.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Lattices/SmoothAffinePairLaw.lean`, `Lattices/SmoothIntegerTranslation.lean`, `Linear/AllocatedKernelPrimitiveBudget.lean`, `Linear/KernelCoefficientLogBudget.lean`, `Linear/RealKernelJetInverse.lean`, `Polynomial/CRTPolynomialInputStepLaw.lean`, `Polynomial/JointBooleanPolynomialPerturbation.lean`, `Polynomial/PolynomialGridCover.lean`, `Polynomial/PolynomialParameterContinuity.lean`, `Polynomial/RestrictedDegreeSupports.lean`, `Polynomial/ScalarCubeMinorPolynomial.lean`, `Polynomial/SchmidtGaussianMean.lean`, `Polynomial/SlicedPolynomialPerturbation.lean`, `Probability/AllocatedAnisotropicSpatialLaw.lean`, `Probability/AnisotropicSmoothPairLaw.lean`, `Probability/CanonicalPairPointLaw.lean`, `Probability/CoefficientDensitySplit.lean`, `Probability/LargeCokernelProbability.lean`, `Probability/ScalarCubeHistogramMeasure.lean`, `Probability/SelectedDensityNormalization.lean`, `Probability/ShiftedProductCoordinateLaw.lean`, `Probability/SmoothSelectedSpatialLaw.lean`, `Probability/UniformSelectedCoefficientProductLaw.lean`, `Sampling/MixedOutputGrid.lean`, `Sampling/RationalGridMajorSet.lean`, `Sampling/ScalarCubeGridCoordinates.lean`, `Sampling/SmoothPairPhysicalGrid.lean`.
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
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B012
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B017
import Definitions.Def_OAIE3v2B029
import Definitions.Def_OAIE3v2B030
import Definitions.Def_OAIE3v2B032
import Definitions.Def_OAIE3v2B033
import Definitions.Def_OAIE3v2B035
import Definitions.Def_OAIE3v2B036
import Definitions.Def_OAIE3v2B037

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem pivotFreeAdmissible_coset {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ)
    {y₀ : J → ℤ} (hy₀ : pivotFreeAdmissible A B v y₀) (y : J → ℤ) :
    pivotFreeAdmissible A B v y ↔ y - y₀ ∈ pivotFreeLattice A B := by
  change v - B *ᵥ y ∈ A.mulVecLin.range ↔ B *ᵥ (y - y₀) ∈ A.mulVecLin.range
  rw [Matrix.mulVec_sub]
  constructor
  · intro hy
    convert A.mulVecLin.range.sub_mem hy₀ hy using 1
    abel
  · intro hy
    convert A.mulVecLin.range.sub_mem hy₀ hy using 1
    abel

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem integerScalarLattice_index {J : Type*} [Fintype J] [DecidableEq J]
    {m : ℤ} (hm : m ≠ 0) :
    (integerScalarLattice J m).toAddSubgroup.index = m.natAbs ^ Fintype.card J := by
  have hM : (m • (1 : Matrix J J ℤ)).det ≠ 0 := by
    simp only [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hm
  have hi := integerMatrixImage_index (m • (1 : Matrix J J ℤ)) hM
  have he : (m • (1 : Matrix J J ℤ)).mulVecLin = m • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (m • (1 : Matrix J J ℤ)) *ᵥ x = m • x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [he, Matrix.det_smul, Matrix.det_one, mul_one, Int.natAbs_pow] at hi
  exact hi

theorem integerScalarLattice_le_pivotFreeLattice {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) {m : ℤ} (hm : A.det ∣ m) :
    integerScalarLattice J m ≤ pivotFreeLattice A B := by
  rintro y ⟨z, rfl⟩
  change B *ᵥ (m • z) ∈ A.mulVecLin.range
  rw [Matrix.mulVec_smul]
  exact integerMatrixImage_multiple_smul A hm (B *ᵥ z)

end Erdos3

end

section

namespace Erdos3

def integerLatticeResidue {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) (m : ℤ) :=
  L.toAddSubgroup ⧸ (integerScalarLattice J m).toAddSubgroup.addSubgroupOf L.toAddSubgroup

@[instance_reducible] noncomputable def integerLatticeResidueFintype {J : Type*}
    [Fintype J] [DecidableEq J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0) :
    Fintype (integerLatticeResidue L m) := by
  let : (integerScalarLattice J m).toAddSubgroup.FiniteIndex :=
    ⟨by rw [integerScalarLattice_index hm]; exact pow_ne_zero _ (Int.natAbs_ne_zero.mpr hm)⟩
  unfold integerLatticeResidue
  exact Fintype.ofFinite _

noncomputable def integerScalarPeriodEquiv {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hL : integerScalarLattice J m ≤ L) :
    (J → ℤ) ≃ (integerScalarLattice J m).toAddSubgroup.addSubgroupOf L.toAddSubgroup where
  toFun z := ⟨⟨m • z, hL ⟨z, rfl⟩⟩, ⟨z, rfl⟩⟩
  invFun z := z.property.choose
  left_inv z := by
    funext j
    apply mul_left_cancel₀ hm
    exact congrFun (Exists.choose_spec (show ∃ w : J → ℤ, m • w = m • z from ⟨z, rfl⟩)) j
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact z.property.choose_spec

noncomputable def integerLatticeResidueEquiv {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hL : integerScalarLattice J m ≤ L) :
    L ≃ integerLatticeResidue L m × (J → ℤ) :=
  (additiveResidueEquiv _).trans
    (Equiv.prodCongr (Equiv.refl _) (integerScalarPeriodEquiv L hm hL).symm)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

def pivotAdmissibleLatticeEquiv {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀) :
    {y : J → ℤ // pivotFreeAdmissible A B v y} ≃ pivotFreeLattice A B where
  toFun y := ⟨y.val - y₀, (pivotFreeAdmissible_coset A B v hy₀ y.val).mp y.property⟩
  invFun z := ⟨y₀ + z.val, (pivotFreeAdmissible_coset A B v hy₀ _).mpr (by
    simpa only [add_sub_cancel_left] using z.property)⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

noncomputable def pivotFiberGridEquiv {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m) :
    {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} ≃
      integerLatticeResidue (pivotFreeLattice A B) m × (J → ℤ) :=
  (pivotIntegerFiberEquiv A hA B v).trans ((pivotAdmissibleLatticeEquiv A B v y₀ hy₀).trans
    (integerLatticeResidueEquiv (pivotFreeLattice A B) hm
      (integerScalarLattice_le_pivotFreeLattice A B hdiv)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
namespace OAI

section

namespace Erdos3

noncomputable def torsionCharacterCoordinates {I : Type*} [DecidableEq I] {a : ℕ} [NeZero a]
    (χ : TorsionLatticeCharacter I a) (i : I) : rootsOfUnity a ℂ :=
  rootsOfUnity.mkOfPowEq (latticeCharacterCoordinates χ.val i)
    (congrArg (fun ψ : AddChar (I → ℤ) ℂ => ψ (Pi.single i 1)) χ.property)

theorem torsionCharacterCoordinates_injective {I : Type*} [Fintype I] [DecidableEq I]
    {a : ℕ} [NeZero a] :
    Function.Injective (torsionCharacterCoordinates (I := I) (a := a)) := by
  intro χ ψ h
  apply Subtype.ext
  apply latticeCharacterCoordinates_injective
  funext i
  exact congrArg (fun z : rootsOfUnity a ℂ => (z.val : ℂ)) (congrFun h i)

noncomputable instance torsionLatticeCharacterFintype (I : Type*) [Fintype I] (a : ℕ) [NeZero a] :
    Fintype (TorsionLatticeCharacter I a) := by
  classical
  let _ : Fintype (rootsOfUnity a ℂ) := Fintype.ofFinite _
  exact Fintype.ofInjective torsionCharacterCoordinates torsionCharacterCoordinates_injective

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.LargeCokernelProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def largeCokernelEvent {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {Ω : J → Type*} (column : ∀ j, Ω j → I → ℤ) (B R : ℕ) (x : ∀ j, Ω j) : Prop :=
  ∃ A : Matrix I I ℤ, A.det ≠ 0 ∧
    A.mulVecLin.range ≤ (sampledColumnMatrix column x).mulVecLin.range ∧
    A.det.natAbs ≤ R ∧ B < integerCokernelExponent (sampledColumnMatrix column x).mulVecLin.range

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealKernelJetInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def realKernelInterpolant {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (s : Finset α) : MvPolynomial K ℝ :=
  realBooleanInterpolant (fun r => realAffineDualPolynomial root selection
    (fun j => (realDifferencePivot difference selection)⁻¹ j r)) s

end Erdos3

end

section

namespace Erdos3

noncomputable def realKernelJetRightInverse {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (h : ℕ) (rows : O → Finset α) : Matrix (BoundedIntegerExponent K h) O ℝ :=
  fun e o => (realKernelInterpolant root difference selection (rows o)).coeff e.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

omit [Fintype J] in
theorem rectangularLatticePoint_scaled (c T : J → ℝ) {m : ℝ} (hm : m ≠ 0) (z : J → ℤ) :
    rectangularLatticePoint (fun j => -c j / m) (fun j => T j / m) z =
      fun j => (c j + m * z j) / T j := by
  funext j
  unfold rectangularLatticePoint
  field_simp
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

theorem sigmaAxisProjection_norm_apply_le (d : D) (x : (Σ d, I d) → ℝ) :
    ‖sigmaAxisProjection I d x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact norm_le_pi_norm x ⟨d, i⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
theorem splitInputProfile_sample_sum (f : (J → ℝ) × (I → ℝ) → ℝ) (S : I → ℝ) (T : J → ℝ) :
    (∑' z : J ⊕ I → ℤ, splitInputProfile f (fun k => (z k : ℝ) / Sum.elim T S k)) =
      ∑' p : (I → ℤ) × (J → ℤ), scaledIntegerWeight f S T p := by
  let e : (J ⊕ I → ℤ) ≃ (I → ℤ) × (J → ℤ) :=
    (Equiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℤ)).trans (Equiv.prodComm _ _)
  exact e.tsum_eq (scaledIntegerWeight f S T)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def rectangularResidueCount {I : Type*} [Fintype I] (a b r v : I → ℤ) : ℕ :=
  ∏ i, integerResidueCount (a i) (b i) (r i) (v i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def restrictBlockParameters {B O F α : Type*} (block : O → B)
    (a : BlockParameter B F α → ℝ) (j : BlockParameter O F α) : ℝ :=
  a (block j.1, j.2.1, j.2.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeBoundaryCost
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def scalarCubeLinearMap {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    (Option α → ℝ) →L[ℝ] ℝ :=
  ∑ r : Option α, (booleanFeature r t : ℝ) • ContinuousLinearMap.proj r

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeFaceSlab
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

def halfOpenScalarCubeDomain (I : Type*) [Fintype I] [DecidableEq I] : Set (Option I → ℝ) :=
  {x | ∀ t : Finset I, scalarCubeValue x t ∈ Set.Ico (0 : ℝ) 1}

noncomputable def scalarCubeIndicator (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) : ℝ := if x ∈ halfOpenScalarCubeDomain I then 1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

theorem replacementAccuracy_inverse_le_exp {B epsilon P : ℝ}
    (hB0 : 0 ≤ B) (hepsilon : 0 < epsilon) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (replacementAccuracy B epsilon)⁻¹ ≤ Real.exp (2 * P + 2) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold replacementAccuracy
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by linarith : 0 ≤ 2 * P + 2)
  · rw [inv_div, div_eq_mul_inv]
    calc
      (1 + B) * epsilon⁻¹ ≤ (1 + Real.exp P) * Real.exp P :=
        mul_le_mul (by linarith) heps (inv_nonneg.mpr hepsilon.le) (by positivity)
      _ ≤ 2 * (Real.exp P) ^ 2 := by nlinarith
      _ ≤ Real.exp 2 * (Real.exp P) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem replacementScaleThreshold_conditions {C delta rho J Q R U L H : ℝ} {N e : ℕ}
    (hC : 0 ≤ C) (hd : 0 < delta) (hr : 0 < rho) (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (hR : 0 < R) (hU : 0 ≤ U) (hL : 1 ≤ L) (he : 2 ≤ e)
    (hscale : replacementScaleThreshold C delta rho J Q R U * L ^ e ≤ H)
    (hupper : H ≤ R * N) (hrR : rho * R ≤ 2) :
    0 < H ∧ 2 * C * L ^ 2 / H ≤ delta ∧ 4 ≤ rho * H ∧
      J ≤ rho * H / 4 ∧ Q ≤ N ∧ U ≤ H / L ∧ rho * H ≤ 2 * N := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hn2 : 0 ≤ 2 * C / delta := by positivity
  have hnJ : 0 ≤ 4 * J / rho := by positivity
  have hn4 : 0 ≤ 4 / rho := by positivity
  have hnRQ : 0 ≤ R * Q := by positivity
  have hT1 : 1 ≤ replacementScaleThreshold C delta rho J Q R U := by
    unfold replacementScaleThreshold
    linarith
  have hT0 := zero_le_one.trans hT1
  have hpow : 1 ≤ L ^ e := one_le_pow₀ hL
  have hT : replacementScaleThreshold C delta rho J Q R U ≤ H :=
    (le_mul_of_one_le_right hT0 hpow).trans hscale
  have hH : 0 < H := zero_lt_one.trans_le (hT1.trans hT)
  have hcoef : 2 * C / delta ≤ replacementScaleThreshold C delta rho J Q R U := by
    unfold replacementScaleThreshold
    linarith
  have hpow2 : L ^ 2 ≤ L ^ e := pow_le_pow_right₀ hL he
  have hmesh : (2 * C / delta) * L ^ 2 ≤ H :=
    (mul_le_mul hcoef hpow2 (sq_nonneg L) hT0).trans hscale
  have hfour : 4 / rho ≤ H := by unfold replacementScaleThreshold at hT; linarith
  have hcell : 4 * J / rho ≤ H := by unfold replacementScaleThreshold at hT; linarith
  have hRQ : R * Q ≤ H := by unfold replacementScaleThreshold at hT; linarith
  have hUT : U ≤ replacementScaleThreshold C delta rho J Q R U := by
    unfold replacementScaleThreshold
    linarith
  have hpowL : L ≤ L ^ e := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ e by omega)
  refine ⟨hH, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hH).mpr
    have hh := mul_le_mul_of_nonneg_left hmesh hd.le
    have hid : delta * ((2 * C / delta) * L ^ 2) = 2 * C * L ^ 2 := by field_simp
    rw [hid] at hh
    nlinarith
  · have hh := (div_le_iff₀ hr).mp hfour
    nlinarith
  · have hh := (div_le_iff₀ hr).mp hcell
    nlinarith
  · nlinarith [hRQ.trans hupper]
  · apply (le_div_iff₀ hLp).mpr
    exact (mul_le_mul hUT hpowL hLp.le hT0).trans hscale
  · have hh := mul_le_mul_of_nonneg_left hupper hr.le
    have hn := mul_le_mul_of_nonneg_right hrR (Nat.cast_nonneg N)
    nlinarith

theorem replacementScaleThreshold_le_exp {C delta rho J Q R U P : ℝ}
    (hC0 : 0 ≤ C) (hd : 0 < delta) (hr : 0 < rho) (hQ0 : 0 ≤ Q)
    (hP : 0 ≤ P)
    (hC : C ≤ Real.exp P) (hdinv : delta⁻¹ ≤ Real.exp P) (hrinv : rho⁻¹ ≤ Real.exp P)
    (hJ : J ≤ Real.exp P) (hQ : Q ≤ Real.exp P) (hR : R ≤ Real.exp P) (hU : U ≤ Real.exp P) :
    replacementScaleThreshold C delta rho J Q R U ≤ Real.exp (2 * P + 16) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have he2 : Real.exp P ≤ (Real.exp P) ^ 2 := by nlinarith
  have hcd : C * delta⁻¹ ≤ (Real.exp P) ^ 2 := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hC hdinv (inv_nonneg.mpr hd.le) (Real.exp_nonneg _)
      _ = _ := by ring
  have hjr : J * rho⁻¹ ≤ (Real.exp P) ^ 2 := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hJ hrinv (inv_nonneg.mpr hr.le) (Real.exp_nonneg _)
      _ = _ := by ring
  have hrq : R * Q ≤ (Real.exp P) ^ 2 := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hR hQ hQ0 (Real.exp_nonneg _)
      _ = _ := by ring
  have h13 : (13 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  calc
    _ ≤ 13 * (Real.exp P) ^ 2 := by
      unfold replacementScaleThreshold
      simp only [div_eq_mul_inv]
      nlinarith
    _ ≤ Real.exp 16 * (Real.exp P) ^ 2 := mul_le_mul_of_nonneg_right h13 (sq_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped ContDiff

def polynomialParameterPoint {Z I : Type*} (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    PolynomialParameter Z I → ℝ := fun s => match s with
  | none => t
  | some (.inl j) => z j
  | some (.inr i) => x i

noncomputable def polynomialParameterInjection (Z I : Type*) [Fintype I] :
    (I → ℝ) →L[ℝ] (PolynomialParameter Z I → ℝ) :=
  ContinuousLinearMap.pi (fun s => match s with
    | none => 0
    | some (.inl _) => 0
    | some (.inr i) => ContinuousLinearMap.proj i)

noncomputable def parameterPolynomialMap {Z I O : Type*} [Fintype Z] [Fintype I] [Fintype O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) (t : ℝ) (z : Z → ℝ) (x : I → ℝ) : O → ℝ :=
  polynomialVectorMap p (polynomialParameterPoint t z x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaAxisOperator
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O P : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] [∀ d, Fintype (P d)]

noncomputable def sigmaAxisOperator (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) :
    ((Σ d, I d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ) :=
  ContinuousLinearMap.pi (fun s => (ContinuousLinearMap.proj s.2).comp
    ((A s.1).comp (sigmaAxisProjection I s.1)))

omit [Fintype D] [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] in
theorem sigmaAxisOperator_apply (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    (x : (Σ d, I d) → ℝ) (s : Σ d, O d) :
    sigmaAxisOperator A x s = A s.1 (sigmaAxisProjection I s.1 x) s.2 := rfl

theorem sigmaAxisOperator_norm_le (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ d, ‖A d‖ ≤ K) : ‖sigmaAxisOperator A‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg x))).mpr
  intro s
  calc
    ‖sigmaAxisOperator A x s‖ ≤ ‖A s.1 (sigmaAxisProjection I s.1 x)‖ := norm_le_pi_norm _ s.2
    _ ≤ ‖A s.1‖ * ‖sigmaAxisProjection I s.1 x‖ := (A s.1).le_opNorm _
    _ ≤ K * ‖x‖ := mul_le_mul (hA s.1) (sigmaAxisProjection_norm_apply_le I s.1 x)
      (norm_nonneg _) hK

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxInteriorCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def unitBoxInteriorCutoff (r : ℝ) : (ι → ℝ) → ℝ :=
  inequalityBoundaryCutoff (fun _ : Bool × ι => r) unitBoxFace

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialPerturbation
namespace OAI

section

namespace Erdos3

noncomputable def scalePerturbedPolynomial {Z I : Type*}
    (p : MvPolynomial I ℝ) (r : MvPolynomial (PolynomialParameter Z I) ℝ) :
    MvPolynomial (PolynomialParameter Z I) ℝ :=
  MvPolynomial.rename (fun i => some (Sum.inr i)) p + MvPolynomial.X none * r

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix

noncomputable def selectedSpatialColumnEquiv {I J : Type*} [Fintype I] (s : I ↪ J) :
    (Unit ⊕ I) ⊕ UnselectedColumn s ≃ Unit ⊕ J :=
  (Equiv.sumAssoc Unit I (UnselectedColumn s)).trans
    (Equiv.sumCongr (Equiv.refl Unit) (selectedColumnEquiv s))

end Erdos3

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

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_nonneg {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ n, 0 ≤ g n) (p) :
    0 ≤ splitFreeProfile f g p := mul_nonneg (hf _) (hg _)

theorem splitFreeProfile_zero_outside {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} {R S : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (hg : ∀ n, S < ‖n‖ → g n = 0)
    (p : (J ⊕ N → ℝ) × (I → ℝ)) (hp : max R S < ‖p‖) :
    splitFreeProfile f g p = 0 := by
  let y : J → ℝ := fun j => p.1 (.inl j)
  let n : N → ℝ := fun n => p.1 (.inr n)
  by_cases hy : R < ‖(y, p.2)‖
  · exact mul_eq_zero_of_left (hf _ hy) _
  · have hn : S < ‖n‖ := by
      by_contra! hn
      have hy' : ‖(y, p.2)‖ ≤ R := le_of_not_gt hy
      have hnorm : ‖p‖ ≤ max R S := by
        rw [Prod.norm_def]
        apply max_le
        · rw [← splitCoordinates_norm p.1, Prod.norm_def]
          exact max_le ((norm_fst_le (y, p.2)).trans (hy'.trans (le_max_left _ _)))
            (hn.trans (le_max_right _ _))
        · exact (norm_snd_le (y, p.2)).trans (hy'.trans (le_max_left _ _))
      exact (not_le_of_gt hp) hnorm
    exact mul_eq_zero_of_right _ (hg _ hn)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem sumElim_norm {J I : Type*} [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ‖Sum.elim p.1 p.2‖ = ‖p‖ :=
  (splitCoordinates_norm (Sum.elim p.1 p.2)).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedCoefficientEquiv_apply {I J R : Type*} [Fintype I]
    (s : I ↪ J) (p : (UnselectedColumn s → R) × (I → R)) (j : J) :
    selectedCoefficientEquiv s R p j =
      Sum.elim p.1 p.2 ((selectedFreeFirstEquiv s).symm j) := rfl

theorem selectedCoefficientEquiv_norm {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (p : (UnselectedColumn s → ℝ) × (I → ℝ)) :
    ‖selectedCoefficientEquiv s ℝ p‖ = ‖p‖ := by
  change ‖(Sum.elim p.1 p.2) ∘ (selectedFreeFirstEquiv s).symm‖ = _
  exact ((selectedFreeFirstEquiv s).symm.surjective.pi_norm_comp (Sum.elim p.1 p.2)).trans
    (sumElim_norm p)

theorem selectedCoefficientEquiv_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) : LipschitzWith 1 (selectedCoefficientEquiv s ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have he : selectedCoefficientEquiv s ℝ p - selectedCoefficientEquiv s ℝ q =
      selectedCoefficientEquiv s ℝ (p - q) := by
    funext j
    simp only [Pi.sub_apply, selectedCoefficientEquiv_apply]
    cases (selectedFreeFirstEquiv s).symm j <;> rfl
  rw [he, selectedCoefficientEquiv_norm]

theorem selectedCoefficientProfile_nonneg {I J : Type*} [Fintype I]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ p, 0 ≤ selectedCoefficientProfile s f p := fun p => hf (selectedCoefficientEquiv s ℝ p)

theorem selectedCoefficientProfile_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ x, R < ‖x‖ → f x = 0) :
    ∀ p, R < ‖p‖ → selectedCoefficientProfile s f p = 0 := by
  intro p hp
  exact hf _ (by rwa [selectedCoefficientEquiv_norm])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def selectedCoefficientComplementFill {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X) : J → X :=
  Function.extend Subtype.val tail (fun _ => x0)

noncomputable def selectedCoefficientJoin {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X)
    (selected : A → X) : J → X :=
  Function.extend e selected (selectedCoefficientComplementFill e x0 tail)

@[simp] theorem selectedCoefficientJoin_selected {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X)
    (selected : A → X) (a : A) :
    selectedCoefficientJoin e x0 tail selected (e a) = selected a :=
  e.injective.extend_apply _ _ _

@[simp] theorem selectedCoefficientJoin_complement {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X)
    (selected : A → X) (k : SelectedCoefficientComplement e) :
    selectedCoefficientJoin e x0 tail selected k.val = tail k := by
  rw [selectedCoefficientJoin, Function.extend_apply' _ _ _ k.property]
  exact Subtype.val_injective.extend_apply _ _ k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def smoothInputJoin {I J D X : Type*} (e : (I ⊕ J) ≃ D) (p : (I → X) × (J → X)) : D → X :=
  fun d => Sum.elim p.1 p.2 (e.symm d)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3


theorem integerScalarCube_iff_supported (q L : ℕ) (x : Option (Fin q) → ℤ) :
    IntegerScalarCube L x ↔ ∀ ω : Fin q → Bool,
      x none + cubeShift (fun i => x (some i)) ω ∈ Set.Ico (0 : ℤ) (L : ℤ) := by
  classical
  constructor
  · intro h ω
    have hx := h (Finset.univ.filter (fun i => ω i))
    simpa only [integerScalarCubeValue, Finset.sum_filter, cubeShift, Set.mem_Ico] using hx
  · intro h t
    have hx := h (fun i => decide (i ∈ t))
    simpa [integerScalarCubeValue, cubeShift] using hx


open scoped BigOperators Classical

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ScalarCubeGridCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def scalarCubeGrid {I J : Type*} {N L : ℕ} (e : J × Option I ≃ Fin N)
    (x : J → IntegerScalarCubeBox I L) : Fin N → ℤ :=
  fun i => (x (e.symm i).1 (e.symm i).2 : ℤ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial
namespace OAI

section

namespace Erdos3

noncomputable def scalarCubeMinorPolynomial {I J : Type*} [Fintype I] [DecidableEq I]
    {N : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) : MvPolynomial (Fin N) ℝ :=
  (coordinateMatrixPolynomial (fun i j => e (s j, some i))).det

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3


noncomputable def normalizedScalarCubePivot {I J : Type*} {L : ℕ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) : Matrix I I ℝ :=
  fun i j => (x (s j) (some i) : ℤ) / (L : ℝ)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedImageMask
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

noncomputable def maskedIntegerImageDensity {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ)
    (v : I → ℤ) : ℝ := by
  classical
  exact if v ∈ pivotFullImage A B then
    ((pivotFullImage A B).toAddSubgroup.index : ℝ) * f (fun i => (v i : ℝ) / P i) else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped NNReal Matrix

noncomputable def smoothPairRowLipschitz {J : Type*} [Fintype J] [DecidableEq J] (k : J) : ℝ≥0 :=
  ((Fintype.card {j : J // j ≠ k} + 2 : ℕ) : ℝ≥0) * probabilityProfileLipschitz

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem selectedCoefficientEquiv_normalize {I J : Type*} [Fintype I]
    (s : I ↪ J) (S : J → ℝ) (p : (UnselectedColumn s → ℤ) × (I → ℤ)) :
    selectedCoefficientEquiv s ℝ
      ((fun j => (p.1 j : ℝ) / S j.val), (fun i => (p.2 i : ℝ) / S (s i))) =
      fun j => (selectedCoefficientEquiv s ℤ p j : ℝ) / S j := by
  funext j
  obtain ⟨k, rfl⟩ := (selectedFreeFirstEquiv s).surjective j
  simp only [selectedCoefficientEquiv_apply, Equiv.symm_apply_apply]
  cases k <;> rfl

noncomputable def selectedIntegerCoefficientEquiv {I J : Type*} [Fintype I]
    (s : I ↪ J) : (I → ℤ) × (UnselectedColumn s → ℤ) ≃ (J → ℤ) :=
  (Equiv.prodComm _ _).trans (selectedCoefficientEquiv s ℤ)

theorem selectedIntegerCoefficient_weight {I J : Type*} [Fintype I]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) (S : J → ℝ)
    (p : (I → ℤ) × (UnselectedColumn s → ℤ)) :
    coefficientWeight f S (selectedIntegerCoefficientEquiv s p) =
      scaledIntegerWeight (selectedCoefficientProfile s f)
        (fun i => S (s i)) (fun j => S j.val) p := by
  exact (congrArg f (selectedCoefficientEquiv_normalize s S (p.2, p.1))).symm

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def interiorIntervalCutoff (eta : ℝ≥0) (x : ℝ) : ℝ :=
  linearCutoff (1 / 2 - 2 * eta) eta |x - 1 / 2|

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def representativeWindowCount : ℕ := intervalSiteCount 1 (1 / 16)

noncomputable def representativeWindowPartitionLip : ℝ≥0 :=
  (2 * representativeWindowCount + 1) / (1 / 16)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedListPowerBudget
namespace OAI

section

namespace Erdos3

def fixedListRequiredBudget (B c : ℕ) (p : ℝ) : ℝ :=
  fixedListComparisonBudget B c p +
    productNiltestBudget (raisedNiltestBudget (fixedListComparisonBudget B c p))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SelectedDensityNormalization
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def selectedCoefficientMeasurableEquiv {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) : (UnselectedColumn s → ℝ) × (I → ℝ) ≃ᵐ (J → ℝ) where
  toEquiv := selectedCoefficientEquiv s ℝ
  measurable_toFun := (selectedCoefficientEquiv_lipschitz s).continuous.measurable
  measurable_invFun := by
    change Measurable (fun x : J → ℝ => ((fun j : UnselectedColumn s => x j.val), fun i => x (s i)))
    fun_prop

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedOutputL1
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def selectedOutputSlice {I J : Type*} [Fintype J]
    (s : J ↪ I) (f : (I → ℝ) → ℝ) (x : UnselectedColumn s → ℝ) (y : J → ℝ) : ℝ :=
  f (selectedCoefficientEquiv s ℝ (x, y))

noncomputable def retainedSelectedOutputEquiv {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) :
    (W × (UnselectedColumn s → ℝ)) × (J → ℝ) ≃ᵐ W × (I → ℝ) :=
  MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl W).prodCongr (selectedCoefficientMeasurableEquiv s))

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

theorem normalizedFiberErrorConstant_le_exp (j d : ℕ) {G U V R H b : ℝ} (K : ℝ≥0)
    (hb : 0 ≤ b) (_hG0 : 0 ≤ G) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hR0 : 0 ≤ R) (hH0 : 0 ≤ H)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hV : V ≤ Real.exp b)
    (hR : R ≤ Real.exp b) (hH : H ≤ Real.exp b) (hK : (K : ℝ) ≤ Real.exp b) :
    normalizedFiberErrorConstant j d G U V R H K ≤
      Real.exp ((j : ℝ)^2 + (j + 4) * b + (j + 2*d) * (b + 4) + 4) := by
  have hone : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbox : 2 * R + 2 ≤ Real.exp (b + 4) := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left hfour (Real.exp_pos b).le]
  have htwor : 2 * R ≤ Real.exp (b + 4) := by linarith
  have hmax : max 1 (U * V) ≤ Real.exp (2*b) := by
    apply max_le
    · exact Real.one_le_exp_iff.mpr (by positivity)
    · calc
        _ ≤ Real.exp b * Real.exp b := mul_le_mul hU hV hV0 (Real.exp_pos b).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
  let F := (j : ℝ)^2 + (j + 4) * b + (j + 2*d) * (b + 4)
  have hfirst : integerFiberErrorConstant j d G U V R K ≤ Real.exp F := by
    unfold integerFiberErrorConstant
    calc
      _ ≤ Real.exp b * (Real.exp ((j : ℝ)^2) * (Real.exp b)^j) *
          (Real.exp (b + 4))^d * Real.exp b * Real.exp (2*b) := by
        gcongr
        exact factorial_le_exp_sq j
      _ = Real.exp ((j : ℝ)^2 + (j + 4)*b + d*(b+4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        simp only [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp F := Real.exp_le_exp.mpr (by dsimp [F]; nlinarith [Nat.cast_nonneg j (α := ℝ), Nat.cast_nonneg d (α := ℝ)])
  have hsecond : (G * (j.factorial * U ^ j) * H * (2*R)^d) *
      ((2*R+2)^(j+d) * K) ≤ Real.exp F := by
    calc
      _ ≤ (Real.exp b * (Real.exp ((j : ℝ)^2) * (Real.exp b)^j) * Real.exp b *
          (Real.exp (b+4))^d) * ((Real.exp (b+4))^(j+d) * Real.exp b) := by
        gcongr
        exact factorial_le_exp_sq j
      _ = Real.exp ((j : ℝ)^2 + (j+3)*b + (j+2*d)*(b+4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        simp only [← Real.exp_add]
        push_cast
        congr 1
        ring
      _ ≤ Real.exp F := Real.exp_le_exp.mpr (by dsimp [F]; nlinarith)
  change 2 * integerFiberErrorConstant j d G U V R K +
    2 * (G * (j.factorial * U ^ j) * H * (2*R)^d) * ((2*R+2)^(j+d) * K) ≤ _
  calc
    _ ≤ 4 * Real.exp F := by linarith
    _ ≤ Real.exp F * Real.exp 4 := by nlinarith [Real.exp_pos F]
    _ = _ := by rw [← Real.exp_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem productCoordinateMix_swap (S : Finset I) (x y : ∀ i, X i) :
    productCoordinateMix S (productCoordinateMix S x y) (productCoordinateMix S y x) = x := by
  funext i
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi]

def productCoordinateSwap (S : Finset I) : ((∀ i, X i) × (∀ i, X i)) ≃
    ((∀ i, X i) × (∀ i, X i)) where
  toFun p := (productCoordinateMix S p.1 p.2, productCoordinateMix S p.2 p.1)
  invFun p := (productCoordinateMix S p.1 p.2, productCoordinateMix S p.2 p.1)
  left_inv p := by simp [productCoordinateMix_swap]
  right_inv p := by simp [productCoordinateMix_swap]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def physicalBoxUnitResidueEquiv (lo : I → ℤ) (N : I → ℕ) :
    translatedIntegerBox lo N ≃ IntegerResidueBox lo (fun i => lo i + N i) (fun _ => 1) (fun _ => 0) where
  toFun x i := ⟨x.val i, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ((mem_translatedIntegerBox lo N x.val).mp x.property i), Int.modEq_one⟩⟩
  invFun x := ⟨fun i => (x i).val, (mem_translatedIntegerBox lo N _).mpr
    (fun i => Finset.mem_Ico.mp (Finset.mem_filter.mp (x i).property).1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def smoothAffinePairRows {K I : Type*} [Fintype K]
    (t u : K → ℤ) (z : Option K × I → ℤ) : I → Fin 2 → ℤ :=
  fun i => affinePairMatrix t u *ᵥ independentArrayRows z i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth
namespace OAI

section

namespace Erdos3

noncomputable def potentialExponent (K : ℝ) : ℝ := 1 - gainExponent K / 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem smoothPairCoefficientScale_pos {J : Type*} {H L : ℝ} (hH : 0 < H) (hL : 0 < L) :
    ∀ c : Option J, 0 < smoothPairCoefficientScale H L c := by
  intro c
  cases c
  · exact hH
  · exact div_pos hH hL

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

noncomputable def smoothPairProbabilityError {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) : ℝ :=
  normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
    (4 * C / κ) ((Fintype.card J : ℝ) * C) 1 1 (smoothPairRowLipschitz k) * δ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem smoothPairProbabilityError_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ smoothPairProbabilityError k Q C κ δ := by
  unfold smoothPairProbabilityError normalizedFiberErrorConstant integerFiberErrorConstant
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalPairPointLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def fullSmoothPairError {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ δ : ℝ) : ℝ :=
  n * smoothPairProbabilityError k Q C κ δ *
    (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ δ) ^ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothPairPhysicalGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def smoothPairKernelBaseLip {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (C κ : ℝ) : ℝ≥0 :=
  Real.toNNReal (2 * (4 * C / κ) ^ 3 * (smoothPairRowLipschitz k : ℝ) *
    2 ^ Fintype.card {j : J // j ≠ k})

noncomputable def smoothPairKernelLip {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) : ℝ≥0 :=
  n * smoothPairKernelBaseLip k C κ * smoothPairKernelCap n k C κ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem fullSmoothPairError_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ fullSmoothPairError n k Q C κ δ := by
  have he := smoothPairProbabilityError_nonneg k Q C κ δ hδ
  have hc : 0 ≤ smoothPairProbabilityCap k Q C κ := by
    unfold smoothPairProbabilityCap
    positivity
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) he)
    (pow_nonneg (add_nonneg hc he) _)

end Erdos3

end

section

namespace Erdos3

noncomputable def smoothPairErrorCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) : ℝ := fullSmoothPairError n k Q C κ 1

theorem smoothPairErrorCoefficient_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) : 0 ≤ smoothPairErrorCoefficient n k Q C κ :=
  fullSmoothPairError_nonneg n k Q C κ 1 zero_le_one

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem smoothPairRowLipschitz_le_exp (k : J) {P : ℝ} (hP : 0 ≤ P)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    (smoothPairRowLipschitz k : ℝ) ≤ Real.exp (2 * P + 3) := by
  have hd : (Fintype.card {j : J // j ≠ k} : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_subtype_le (fun j : J => j ≠ k)
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hsum : (Fintype.card {j : J // j ≠ k} : ℝ) + 2 ≤ Real.exp (P + 3) := by
    rw [Real.exp_add]
    nlinarith
  simp only [smoothPairRowLipschitz, NNReal.coe_mul, Nat.cast_add, Nat.cast_ofNat]
  calc
    _ ≤ Real.exp (P + 3) * Real.exp P := mul_le_mul hsum hprofile (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem smoothPairProbabilityCap_le_exp (k : J) (Q : ℕ) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hQ : (Q : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    smoothPairProbabilityCap k Q C κ ≤ Real.exp (6 * P + 11) := by
  have hfactor := smoothPairQuadraticFactor_le_exp k hC0 hκ0 hC hκ hpow
  have hproduct : (Q : ℝ) * (2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k}) ≤
      Real.exp (6 * P + 10) := by
    calc
      _ ≤ Real.exp P * Real.exp (5 * P + 10) := mul_le_mul hQ hfactor (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp ((6 * P + 10) + 1) := one_add_le_exp_succ (by linarith) hproduct
    _ = _ := by congr 1; ring

theorem smoothPairKernelBaseCap_le_exp (k : J) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelBaseCap k C κ : ℝ) ≤ Real.exp (5 * P + 11) := by
  apply coe_toNNReal_le_exp
  calc
    _ ≤ Real.exp ((5 * P + 10) + 1) := one_add_le_exp_succ (by linarith)
      (smoothPairQuadraticFactor_le_exp k hC0 hκ0 hC hκ hpow)
    _ = _ := by congr 1; ring

theorem smoothPairKernelBaseLip_le_exp (k : J) {C κ P : ℝ}
    (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelBaseLip k C κ : ℝ) ≤ Real.exp (8 * P + 14) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hU := smoothPairScaleRatio_le_exp hC0 hκ0 hC hκ
  apply coe_toNNReal_le_exp
  calc
    _ ≤ Real.exp 2 * (Real.exp (2 * P + 4)) ^ 3 * Real.exp P * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring

theorem smoothPairKernelCap_le_exp (n : ℕ) (k : J) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelCap n k C κ : ℝ) ≤ Real.exp ((n : ℝ) * (5 * P + 11)) := by
  simpa only [smoothPairKernelCap, NNReal.coe_pow, Real.exp_nat_mul] using
    pow_le_pow_left₀ (NNReal.coe_nonneg (smoothPairKernelBaseCap k C κ))
      (smoothPairKernelBaseCap_le_exp k hP hC0 hκ0 hC hκ hpow) n

theorem smoothPairKernelLip_le_exp (n : ℕ) (k : J) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hn : (n : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelLip n k C κ : ℝ) ≤ Real.exp ((n : ℝ) * (5 * P + 11) + 9 * P + 14) := by
  have hbase := smoothPairKernelBaseLip_le_exp k hC0 hκ0 hC hκ hrow hpow
  have hcap := smoothPairKernelCap_le_exp n k hP hC0 hκ0 hC hκ hpow
  simp only [smoothPairKernelLip, NNReal.coe_mul, NNReal.coe_natCast]
  calc
    _ ≤ Real.exp P * Real.exp (8 * P + 14) * Real.exp ((n : ℝ) * (5 * P + 11)) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem smoothPairProbabilityError_one_le_exp (k : J) (Q : ℕ) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hQ : (Q : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P) :
    smoothPairProbabilityError k Q C κ 1 ≤
      Real.exp (smoothPairRowErrorLog (Fintype.card {j : J // j ≠ k}) P) := by
  have hlift : Real.exp P ≤ Real.exp (2 * P + 4) := Real.exp_le_exp.mpr (by linarith)
  have hV : (Fintype.card J : ℝ) * C ≤ Real.exp (2 * P + 4) := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hcard hC hC0 (Real.exp_nonneg _)
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have h1 : (1 : ℝ) ≤ Real.exp (2 * P + 4) := Real.one_le_exp_iff.mpr (by linarith)
  have h := normalizedFiberErrorConstant_le_exp 2 (Fintype.card {j : J // j ≠ k})
    (smoothPairRowLipschitz k) (by linarith : 0 ≤ 2 * P + 4)
    (Nat.cast_nonneg Q) (by positivity) (by positivity) (by norm_num) (by norm_num)
    (hQ.trans hlift) (smoothPairScaleRatio_le_exp hC0 hκ0 hC hκ) hV h1 h1 (hrow.trans hlift)
  simp only [smoothPairProbabilityError, mul_one]
  apply h.trans_eq
  congr 1
  unfold smoothPairRowErrorLog
  ring

theorem smoothPairErrorCoefficient_le_exp (n : ℕ) (k : J) (Q : ℕ) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hn : (n : ℝ) ≤ Real.exp P) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    smoothPairErrorCoefficient n k Q C κ ≤
      Real.exp (smoothPairErrorLog n (Fintype.card {j : J // j ≠ k}) P) := by
  let d := Fintype.card {j : J // j ≠ k}
  have hr := smoothPairProbabilityError_one_le_exp k Q hP hC0 hκ0 hQ hC hκ hcard hrow
  have hc := smoothPairProbabilityCap_le_exp k Q hP hC0 hκ0 hQ hC hκ hpow
  have hsum : smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ 1 ≤
      Real.exp (smoothPairRowErrorLog d P + 6 * P + 12) := by
    have hh := add_le_exp_add_one (by linarith : 0 ≤ 6 * P + 11)
      (smoothPairRowErrorLog_nonneg d hP) hc hr
    apply hh.trans_eq
    congr 1
    ring
  have hr0 := smoothPairProbabilityError_nonneg k Q C κ 1 zero_le_one
  have hc0 : 0 ≤ smoothPairProbabilityCap k Q C κ := by unfold smoothPairProbabilityCap; positivity
  unfold smoothPairErrorCoefficient fullSmoothPairError
  calc
    _ ≤ Real.exp P * Real.exp (smoothPairRowErrorLog d P) *
        (Real.exp (smoothPairRowErrorLog d P + 6 * P + 12)) ^ n := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1

theorem smoothPairMeshCoefficient_le_exp (k : J) {P : ℝ}
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P) :
    (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k ≤
      Real.exp (4 * (2 + (Fintype.card {j : J // j ≠ k} : ℝ)) + P) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ (Real.exp 4) ^ (2 + Fintype.card {j : J // j ≠ k}) * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalGridMajorSet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def rationalGridMajorSet (M Q H : ℕ) : Finset (Fin M) :=
  (Finset.range (Q + 1)).biUnion fun d =>
    (Finset.Icc (-(Q * (H + 1) : ℤ)) (Q * (H + 1) : ℤ)).biUnion fun a =>
      frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H

noncomputable def rationalGridMajorBox (J : Type*) [Fintype J] [DecidableEq J]
    (M Q H : ℕ) : Finset (J → Fin M) :=
  Fintype.piFinset (fun _ => rationalGridMajorSet M Q H)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridCover
namespace OAI

section

namespace Erdos3

noncomputable def polynomialGridCover (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) (C : ℝ) (r : ℕ) (ζ : ℝ) : Finset (J → Fin M) :=
  rationalGridMajorBox J M ⌈C / ζ ^ r⌉₊ ⌈C / ζ ^ r⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_add_lattice (Λ : Submodule ℤ E) (t : ℝ) (x : E) (v : Λ) :
    latticeGaussianMass Λ t (x + (v : E)) = latticeGaussianMass Λ t x := by
  have h := (Equiv.addRight v).tsum_eq (fun m : Λ => Real.exp (-Real.pi * t * ‖x + (v : E) - (m : E)‖ ^ 2))
  simpa only [latticeGaussianMass, Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub] using h.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

theorem standardEuclideanPoint_bijective : Function.Bijective (standardEuclideanPoint ι) := by
  constructor
  · intro z w h
    funext i
    have hi := congrArg (fun x : standardEuclideanLattice ι => (x : EuclideanSpace ℝ ι) i) h
    exact Int.cast_injective (α := ℝ) hi
  · intro x
    choose z hz using (mem_standardEuclideanLattice ι (x : EuclideanSpace ℝ ι)).mp x.property
    refine ⟨z, ?_⟩
    apply Subtype.ext
    ext i
    exact hz i

noncomputable def standardEuclideanEquiv : (ι → ℤ) ≃ standardEuclideanLattice ι :=
  Equiv.ofBijective (standardEuclideanPoint ι) (standardEuclideanPoint_bijective ι)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def normalizedLatticeGaussian (Λ : Submodule ℤ E) (t : ℝ) (x : E) : ℝ :=
  latticeGaussianNormalizer Λ t * latticeGaussianMass Λ t x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def orthonormalMixedChartHom (o : OrthonormalBasis I ℝ W) :
    ((I → ℝ) × (Fin n → ℤ)) →+ (W × (Fin n → ℤ)) where
  toFun := orthonormalMixedChart o
  map_zero' := by
    change (orthonormalChart o 0, (0 : Fin n → ℤ)) = 0
    simp
  map_add' x y := by
    change (orthonormalChart o (x.1 + y.1), x.2 + y.2) =
      (orthonormalChart o x.1, x.2) + (orthonormalChart o y.1, y.2)
    simp only [map_add, Prod.mk_add_mk]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem scalarResidueGrid_normalized {I : Type*} [Fintype I] {L : ℕ} (hL : 0 < L)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i) (k : Option I → ℤ) :
    rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k =
      fun i => (scalarResidueGridPoint m r k i : ℝ) / L := by
  funext i
  have hmi : (m i : ℝ) ≠ 0 := by exact_mod_cast (hm i).ne'
  simp only [rectangularLatticePoint, scalarResidueGridOffset, scalarResidueGridScale,
    scalarResidueGridPoint, Int.cast_add, Int.cast_natCast, Int.cast_mul]
  field_simp
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeHistogramMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def scalarCubeProbabilityDensity (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) : ℝ := scalarCubeIndicator I x / volume.real (scalarCubeDomain I)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PlateauFourierMode
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {J : Type*} [Fintype J]

noncomputable def realLinearCharacter (ω x : J → ℝ) : ℂ :=
  CircleFourier.character ((∑ j, ω j * x j : ℝ) : CircleFourier.Circle)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

noncomputable def productTuplePoint (a : J → I) (ha : Function.Injective a)
    (v : ∀ j, X (a j)) (base : ∀ i, X i) : ∀ i, X i :=
  productSubtypePoint (Finset.univ.image a)
    (Equiv.piCongrLeft (fun i : ↥(Finset.univ.image a) => X i)
      (productTupleIndexEquiv a ha) v) base

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MixedOutputGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def gridDensityTest {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (a S : J → ℝ) (s : Finset (J → ℤ))
    (mask : (J → ℤ) → ℝ) (φ : (J → ℤ) → ℂ) : ℂ :=
  (∑ k ∈ s, ((mask k*f (rectangularLatticePoint a S k) : ℝ) : ℂ)*φ k) / ((∏ j, S j : ℝ) : ℂ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanRegularization
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

noncomputable def sigmaAxisOperatorMap :
    (∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) →L[ℝ]
      (((Σ d, I d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ)) :=
  ({ toFun := sigmaAxisOperator
     map_add' := by
       intro A B
       ext x s
       simp only [sigmaAxisOperator_apply, Pi.add_apply, add_apply]
     map_smul' := by
       intro t A
       ext x s
       simp only [sigmaAxisOperator_apply, Pi.smul_apply, smul_apply, RingHom.id_apply] } :
    (∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) →ₗ[ℝ]
      (((Σ d, I d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ))).mkContinuous 1 (fun A => by
        rw [one_mul]
        exact sigmaAxisOperator_norm_le A (norm_nonneg A) (norm_le_pi_norm A))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPrincipalInverse
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

section Joint

variable {D : Type*} [Fintype D]
variable {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

noncomputable def jointSlicedInjection (b : ∀ d, B d) (i : ∀ d, F d) :=
  sigmaAxisOperator (fun d => coordinateInjection (fun _ : Unit => (b d, i d)))

end Joint

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def slicedPrincipalC2Tolerance (N O m : ℕ) (C a δ A η : ℝ) : ℝ :=
  let r := slicedPrincipalBoundaryRadius N η
  let κ := a * δ * (δ * r) ^ m
  polynomialPerturbationScale κ⁻¹ 1 (slicedPrincipalComparisonBudget N m C A r κ) (η / 2) O

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedPolynomialPerturbation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def slicedPolynomialScale (N O Z m d : ℕ) (C M a δ A η : ℝ) : ℝ :=
  slicedPrincipalC2Tolerance N O m C a δ A η / (1 + polynomialMassC2Budget Z d M)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDensitySplit
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

noncomputable def selectedSplitCoefficients {I J N : Type*} [Fintype I]
    (s : I ↪ J) (p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) : J ⊕ N → ℝ :=
  Sum.elim (selectedCoefficientEquiv s ℝ ((fun j => p.1 (.inl j)), p.2))
    (fun n => p.1 (.inr n))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

theorem lowDegreeCoordinateSets_card (b : ℕ) :
    (lowDegreeCoordinateSets I b).card = ∑ j ∈ Finset.range (b + 1), (Fintype.card I).choose j := by
  rw [lowDegreeCoordinateSets, Finset.card_biUnion]
  · simp only [Finset.card_powersetCard, Finset.card_univ]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro S hSi hSj
    exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans (Finset.mem_powersetCard.mp hSj).2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def intervalTensorWeight {S : Type*} [Fintype S] (B r : ℝ)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : ℝ :=
  ∏ i, intervalSiteWeight B r (k i) (x i)

noncomputable def intervalTensorApprox {S : Type*} [Fintype S] [DecidableEq S]
    (B r : ℝ) (F : (S → ℝ) → ℂ) (x : S → ℝ) : ℂ :=
  ∑ k : S → Fin (intervalSiteCount B r),
    (intervalTensorWeight B r k x : ℂ) * F (fun i => intervalSiteCenter B r (k i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

noncomputable def residueColumnAverage (V : J → G) (f : G → ℂ) (x : G) : ℂ :=
  𝔼 t : J → ZMod q, f (x + residueColumnMap (q := q) V t)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorGroupedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)]

noncomputable def orderedFamilyTensor (k : ℕ) (base : ∀ i, X i)
    (F : Finset I → (∀ i, X i) → ℝ) (z : Fin k → Sigma X) : ℝ := by
  classical
  exact if h : StrictMono (fun j => (z j).1) then
    F (Finset.univ.image (fun j => (z j).1))
      (productTuplePoint (fun j => (z j).1) h.injective (fun j => (z j).2) base)
    else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinate_constraints_lcm {ι σ : Type*} [DecidableEq ι]
    (M : ℕ) (a u z : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (huM : ∀ j, u j ≡ a j [ZMOD (M : ℤ)])
    (hux : ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i) :
    ((∀ j, z j ≡ a j [ZMOD (M : ℤ)]) ∧
      (∀ i ∈ I, (fun j => (z j : ZMod (q i))) = x i)) ↔
    ∀ j, z j ≡ u j [ZMOD (M.lcm (∏ i ∈ I, q i) : ℤ)] := by
  constructor
  · rintro ⟨hzM, hzx⟩ j
    apply (modEq_nat_lcm_iff M (∏ i ∈ I, q i) (z j) (u j)).mpr
    refine ⟨(hzM j).trans (huM j).symm, ?_⟩
    apply (modEq_selected_prod_iff q hcop I (z j) (u j)).mpr
    intro i hi
    apply (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mp
    exact congrFun ((hzx i hi).trans (hux i hi).symm) j
  · intro hz
    have hparts := fun j => (modEq_nat_lcm_iff M (∏ i ∈ I, q i) (z j) (u j)).mp (hz j)
    refine ⟨fun j => (hparts j).1.trans (huM j), ?_⟩
    intro i hi
    calc
      (fun j => (z j : ZMod (q i))) = (fun j => (u j : ZMod (q i))) := by
        funext j
        exact (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mpr
          ((modEq_selected_prod_iff q hcop I (z j) (u j)).mp (hparts j).2 i hi)
      _ = x i := hux i hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

theorem residualPointAccuracy_inverse_le_exp {M S F mesh epsilon P : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hF : 0 ≤ F) (hmesh : 0 ≤ mesh)
    (heps : 0 < epsilon) (hP : 0 ≤ P)
    (hcoef : 6 * M * S * F ≤ Real.exp P) (hmeshcoef : 2 * mesh ≤ Real.exp P)
    (hepsinv : epsilon⁻¹ ≤ Real.exp P) :
    (residualPointAccuracy M S F mesh epsilon)⁻¹ ≤ Real.exp (2 * P + 2) := by
  unfold residualPointAccuracy
  apply inv_min_le_of_inv_le
  · exact replacementAccuracy_inverse_le_exp (by positivity) heps hP hcoef hepsinv
  · exact replacementAccuracy_inverse_le_exp (by positivity) (by norm_num) hP hmeshcoef
      (by simpa only [inv_one] using Real.one_le_exp_iff.mpr hP)

theorem residualGridAccuracy_inverse_le_exp {M S K epsilon P : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hK : 0 ≤ K) (heps : 0 < epsilon) (hP : 0 ≤ P)
    (hcoef : 6 * M * S * K ≤ Real.exp P) (hepsinv : epsilon⁻¹ ≤ Real.exp P) :
    (residualGridAccuracy M S K epsilon)⁻¹ ≤ Real.exp (2 * P + 2) :=
  replacementAccuracy_inverse_le_exp (by positivity) heps hP hcoef hepsinv

theorem residualMeanAccuracy_inverse_le_exp {M K V epsilon P : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (heps : 0 < epsilon) (hP : 0 ≤ P)
    (hcoef : V ^ 2 * (1 + 3 * M * K) ≤ Real.exp P) (hepsinv : epsilon⁻¹ ≤ Real.exp P) :
    (residualMeanAccuracy M K V epsilon)⁻¹ ≤ Real.exp (2 * P + 2) := by
  apply replacementAccuracy_inverse_le_exp (by positivity) (lt_min zero_lt_one heps) hP hcoef
  exact inv_min_le_of_inv_le (by simpa only [inv_one] using Real.one_le_exp_iff.mpr hP) hepsinv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem lowDegreeCoordinateSets_card_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : ℝ} (hP : 0 ≤ P) (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) (j : ℕ) :
    ((lowDegreeCoordinateSets ι j).card : ℝ) ≤ Real.exp ((j : ℝ) * (P + 1)) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (j + 1)) :
      ((Fintype.card ι).choose k : ℝ) ≤ Real.exp ((j : ℝ) * P) := by
    have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
    calc
      _ ≤ (Fintype.card ι : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow (Fintype.card ι) k
      _ ≤ (Real.exp P) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount k
      _ = Real.exp ((k : ℝ) * P) := (Real.exp_nat_mul P k).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) hP)
  rw [lowDegreeCoordinateSets_card, Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ Finset.range (j + 1), Real.exp ((j : ℝ) * P) := Finset.sum_le_sum hterm
    _ = ((j : ℝ) + 1) * Real.exp ((j : ℝ) * P) := by simp
    _ ≤ Real.exp j * Real.exp ((j : ℝ) * P) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

noncomputable def residualCapEnvelope (ι : Type*) [Fintype ι] [DecidableEq ι] (degree : ℕ) : ℝ :=
  1 + 2 * ((lowDegreeCoordinateSets ι degree).card : ℝ) * 2 ^ degree

theorem residualCapEnvelope_one_le (ι : Type*) [Fintype ι] [DecidableEq ι] (degree : ℕ) :
    1 ≤ residualCapEnvelope ι degree := by
  unfold residualCapEnvelope
  exact le_add_of_nonneg_right (by positivity)

theorem residualCapEnvelope_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degree : ℕ) {P : ℝ} (hP : 0 ≤ P) (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) :
    residualCapEnvelope ι degree ≤ Real.exp ((degree : ℝ) * (P + 2) + 2) := by
  have hs := lowDegreeCoordinateSets_card_le_exp hP hcount degree
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ degree ≤ Real.exp (degree : ℝ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo degree
    simpa only [← Real.exp_nat_mul, mul_one] using h
  have hprod : ((lowDegreeCoordinateSets ι degree).card : ℝ) * 2 ^ degree ≤
      Real.exp ((degree : ℝ) * (P + 2)) := by
    apply (mul_le_mul hs hp (by positivity) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : 1 ≤ Real.exp ((degree : ℝ) * (P + 2)) := Real.one_le_exp_iff.mpr (by positivity)
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold residualCapEnvelope
  calc
    _ ≤ 3 * Real.exp ((degree : ℝ) * (P + 2)) := by nlinarith
    _ ≤ Real.exp 2 * Real.exp ((degree : ℝ) * (P + 2)) := mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

noncomputable def physicalPairPointAccuracy {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A epsilon : ℝ) : ℝ :=
  residualPointAccuracy (A ^ (2 * n)) (2 ^ n) (smoothPairErrorCoefficient n k Q C κ)
    ((4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k) epsilon

noncomputable def physicalPairGridAccuracy {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ A epsilon : ℝ) : ℝ :=
  residualGridAccuracy (A ^ (2 * n)) (2 ^ n) (smoothPairKernelLip n k C κ) epsilon

noncomputable def physicalPairMeanAccuracy {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A : ℝ) (degree : ℕ) (epsilon : ℝ) : ℝ :=
  residualMeanAccuracy (A ^ (2 * n)) (smoothPairKernelCap n k C κ)
    (residualCapEnvelope (BoundedPrime Q) degree) epsilon

theorem physicalPairPointAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let delta := physicalPairPointAccuracy n k Q C κ A epsilon
    0 < delta ∧ delta ≤ 1 ∧
      6 * A ^ (2 * n) * (2 : ℝ) ^ n * smoothPairErrorCoefficient n k Q C κ * delta ≤ epsilon ∧
      ((4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k) * delta ≤ 1 / 2 :=
  residualPointAccuracy_spec (by positivity) (by positivity) (smoothPairErrorCoefficient_nonneg n k Q C κ)
    (by positivity) heps

theorem physicalPairGridAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let rho := physicalPairGridAccuracy n k C κ A epsilon
    0 < rho ∧ rho ≤ 1 ∧
      6 * A ^ (2 * n) * (2 : ℝ) ^ n * (smoothPairKernelLip n k C κ : ℝ) * rho ≤ epsilon :=
  residualGridAccuracy_spec (by positivity) (by positivity) (NNReal.coe_nonneg _) heps

theorem physicalPairMeanAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) (degree : ℕ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let eta := physicalPairMeanAccuracy n k Q C κ A degree epsilon
    let V := residualCapEnvelope (BoundedPrime Q) degree
    0 < eta ∧ eta ≤ 1 ∧ eta * V ^ 2 ≤ 1 ∧
      3 * A ^ (2 * n) * (smoothPairKernelCap n k C κ : ℝ) * eta * V ^ 2 ≤ epsilon :=
  residualMeanAccuracy_spec (by positivity) (NNReal.coe_nonneg _) heps

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physicalPairPointGridAccuracy_inverse_le_exp (n : ℕ) (k : J) (Q : ℕ)
    {C κ A epsilon P : ℝ} (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hA0 : 0 ≤ A) (heps0 : 0 < epsilon)
    (hn : (n : ℝ) ≤ Real.exp P) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (heps : epsilon⁻¹ ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (physicalPairPointAccuracy n k Q C κ A epsilon)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) P + 2) ∧
    (physicalPairGridAccuracy n k C κ A epsilon)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) P + 2) := by
  let d := Fintype.card {j : J // j ≠ k}
  have hlogs := physicalPairCoefficientLog_bounds n d hP
  obtain ⟨hM, hS⟩ := physicalPairPowerBounds n hA0 hA
  have hF := smoothPairErrorCoefficient_le_exp n k Q hP hC0 hκ0 hn hQ hC hκ hcard hrow hpow
  have hK := smoothPairKernelLip_le_exp n k hP hC0 hκ0 hn hC hκ hrow hpow
  have hm := smoothPairMeshCoefficient_le_exp k hrow
  have h6 : (6 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hF0 := smoothPairErrorCoefficient_nonneg n k Q C κ
  have heps' : epsilon⁻¹ ≤ Real.exp (physicalPairCoefficientLog n d P) :=
    heps.trans (Real.exp_le_exp.mpr hlogs.2.1)
  constructor
  · apply residualPointAccuracy_inverse_le_exp (by positivity) (by positivity) hF0 (by positivity)
      heps0 hlogs.1
    · calc
        _ ≤ Real.exp 6 * Real.exp (2 * n * P) * Real.exp (2 * n) *
            Real.exp (smoothPairErrorLog n d P) := by gcongr
        _ = Real.exp (6 + 2 * n * P + 2 * n + smoothPairErrorLog n d P) := by
          simp only [← Real.exp_add]
        _ ≤ _ := Real.exp_le_exp.mpr hlogs.2.2.1
    · calc
        _ ≤ Real.exp 2 * Real.exp (4 * (2 + (d : ℝ)) + P) := by gcongr
        _ = Real.exp (2 + 4 * (2 + (d : ℝ)) + P) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr hlogs.2.2.2.1
    · exact heps'
  · apply residualGridAccuracy_inverse_le_exp (by positivity) (by positivity) (by positivity)
      heps0 hlogs.1
    · calc
        _ ≤ Real.exp 6 * Real.exp (2 * n * P) * Real.exp (2 * n) *
            Real.exp ((n : ℝ) * (5 * P + 11) + 9 * P + 14) := by gcongr
        _ = Real.exp (20 + 2 * n * P + 2 * n + n * (5 * P + 11) + 9 * P) := by
          simp only [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := Real.exp_le_exp.mpr hlogs.2.2.2.2
    · exact heps'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCutoffLogBounds
namespace OAI

section

namespace Erdos3

theorem integerBoxGcdCutoff_le_exp (d : ℕ) {C epsilon P : ℝ}
    (hC0 : 0 ≤ C) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : (2 : ℝ) ^ (d - 1) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (integerBoxGcdCutoff d C epsilon : ℝ) ≤ Real.exp (3 * P + 6) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hsum := one_add_le_exp_succ hP hC
  have hx : 2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon ≤ Real.exp (3 * P + 3) := by
    calc
      _ = 2 * (2 : ℝ) ^ (d - 1) * (1 + C) * epsilon⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ Real.exp 2 * Real.exp P * Real.exp (P + 1) * Real.exp P := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hceil := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon)).le
  have hbase : 1 ≤ Real.exp (3 * P + 3) := Real.one_le_exp_iff.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    (integerBoxGcdCutoff d C epsilon : ℝ) ≤ Real.exp (3 * P + 3) + 2 := by
      unfold integerBoxGcdCutoff
      push_cast
      linarith
    _ ≤ 3 * Real.exp (3 * P + 3) := by linarith
    _ ≤ Real.exp 3 * Real.exp (3 * P + 3) :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem integerBoxNearRatio_inverse_le_exp (d : ℕ) {epsilon P : ℝ}
    (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : 2 * (3 : ℝ) ^ d ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (integerBoxNearRatio d epsilon)⁻¹ ≤ Real.exp (2 * P + 2) :=
  replacementAccuracy_inverse_le_exp (by positivity) heps0 hP hpow heps

theorem integerBoxPairScale_le_exp (d : ℕ) {C epsilon P : ℝ}
    (hC0 : 0 ≤ C) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow2 : (2 : ℝ) ^ (d - 1) ≤ Real.exp P)
    (hpow3 : 2 * (3 : ℝ) ^ d ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    integerBoxPairScale d C epsilon ≤ Real.exp (3 * P + 6) := by
  apply max_le (integerBoxGcdCutoff_le_exp d hC0 heps0 hP hpow2 hC heps)
  rw [one_div]
  exact (integerBoxNearRatio_inverse_le_exp d heps0 hP hpow3 heps).trans
    (Real.exp_le_exp.mpr (by linarith))

theorem integerBoxRetainedGap_inverse_le_exp (d D : ℕ) {c epsilon P : ℝ}
    (hD : 0 < D) (hc0 : 0 < c) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : 2 * (3 : ℝ) ^ d ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (integerBoxRetainedGap d D c epsilon)⁻¹ ≤ Real.exp (3 * P + 2) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDinv : (D : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hD1
  have hnu0 := (integerBoxNearRatio_spec d heps0).1
  have hnu := integerBoxNearRatio_inverse_le_exp d heps0 hP hpow heps
  calc
    _ = (D : ℝ)⁻¹ * (integerBoxNearRatio d epsilon)⁻¹ * c⁻¹ := by
      simp only [integerBoxRetainedGap, mul_inv_rev]
      ring
    _ ≤ 1 * Real.exp (2 * P + 2) * Real.exp P := by gcongr
    _ = _ := by rw [one_mul, ← Real.exp_add]; congr 1; ring

theorem integerBoxGcdModulus_le_exp (d D : ℕ) {C epsilon P : ℝ}
    (hC0 : 0 ≤ C) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : (2 : ℝ) ^ (d - 1) ≤ Real.exp P)
    (hD : (D : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    ((D * integerBoxGcdCutoff d C epsilon : ℕ) : ℝ) ≤ Real.exp (4 * P + 6) := by
  rw [Nat.cast_mul]
  calc
    _ ≤ Real.exp P * Real.exp (3 * P + 6) :=
      mul_le_mul hD (integerBoxGcdCutoff_le_exp d hC0 heps0 hP hpow hC heps)
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement
namespace OAI

section

namespace Erdos3

noncomputable def replacementCutoffInputLog (m n d : ℕ) (P : ℝ) : ℝ :=
  6 * physicalReplacementInputLog m n P + P + 3 * d + 10

noncomputable def replacementCommonInputLog (m n d : ℕ) (P : ℝ) : ℝ :=
  4 * replacementCutoffInputLog m n d P + 2 * P + 10

theorem replacementCutoffInputLog_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ replacementCutoffInputLog m n d P ∧
    P ≤ replacementCutoffInputLog m n d P ∧
    6 * physicalReplacementInputLog m n P + 6 ≤ replacementCutoffInputLog m n d P ∧
    3 * (d : ℝ) + 2 ≤ replacementCutoffInputLog m n d P ∧
    2 * (d : ℝ) ≤ replacementCutoffInputLog m n d P := by
  have hW := physicalReplacementInputLog_nonneg m n hP
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  unfold replacementCutoffInputLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem replacementCommonInputLog_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ replacementCommonInputLog m n d P ∧
    P ≤ replacementCommonInputLog m n d P ∧
    replacementCutoffInputLog m n d P ≤ replacementCommonInputLog m n d P ∧
    4 * replacementCutoffInputLog m n d P + 6 ≤ replacementCommonInputLog m n d P ∧
    3 * replacementCutoffInputLog m n d P + 6 ≤ replacementCommonInputLog m n d P ∧
    2 * P + 3 ≤ replacementCommonInputLog m n d P := by
  have hb := replacementCutoffInputLog_bounds m n d hP
  unfold replacementCommonInputLog
  constructor
  · linarith [hb.1]
  constructor
  · linarith [hb.1]
  constructor
  · linarith [hb.1]
  constructor
  · linarith
  constructor <;> linarith [hb.1]

theorem replacementCutoffInputLog_power_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (2 : ℝ) ^ (d - 1) ≤ Real.exp (replacementCutoffInputLog m n d P) ∧
    2 * (3 : ℝ) ^ d ≤ Real.exp (replacementCutoffInputLog m n d P) := by
  have hb := replacementCutoffInputLog_bounds m n d hP
  constructor
  · apply (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le d 1)).trans
    exact (replacement_binary_power_le_exp d).trans (Real.exp_le_exp.mpr hb.2.2.2.2)
  · exact (replacement_ternary_power_le_exp d).trans (Real.exp_le_exp.mpr hb.2.2.2.1)

end Erdos3

end

section

namespace Erdos3

theorem replacement_common_geometric_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (m n : ℕ) (k : J) {C A P : ℝ} (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    (n : ℝ) ≤ Real.exp Z ∧ (Fintype.card J : ℝ) ≤ Real.exp Z ∧
    C ≤ Real.exp Z ∧ A ≤ Real.exp Z ∧ (probabilityProfileLipschitz : ℝ) ≤ Real.exp Z ∧
    (smoothPairRowLipschitz k : ℝ) ≤ Real.exp Z ∧
    (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp Z := by
  intro Z
  have hz := replacementCommonInputLog_bounds m n (Fintype.card J) hP
  have ht := replacementCutoffInputLog_bounds m n (Fintype.card J) hP
  have hexp : Real.exp P ≤ Real.exp Z := Real.exp_le_exp.mpr hz.2.1
  refine ⟨hn.trans hexp, hcard.trans hexp, hC.trans hexp, hA.trans hexp, hprofile.trans hexp, ?_, ?_⟩
  · exact (smoothPairRowLipschitz_le_exp k hP hcard hprofile).trans (Real.exp_le_exp.mpr hz.2.2.2.2.2)
  · apply (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Fintype.card_subtype_le (fun j : J => j ≠ k))).trans
    apply (replacement_binary_power_le_exp (Fintype.card J)).trans
    exact Real.exp_le_exp.mpr (ht.2.2.2.2.trans hz.2.2.1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SmallRatioPotential
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def smallRatioCenterPotential (L : Finset G) (f g : G → ℝ)
    (u v c₀ : ℝ) (x y : G) : ℝ := by
  classical
  exact if cellAverage L f x < c₀ * u ∨ cellAverage L g y < c₀ * v then
    (cellAverage L f x * cellAverage L g y) ^ (1 / 4 : ℝ) else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedAxisProduct {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (c : ℝ) (y : G) : ℝ := axisProduct f t y / c ^ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupedSiteTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {S D : Type*} [Fintype S] [Fintype D]

noncomputable def groupedSiteCoefficient (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    (k : S × D → Fin (intervalSiteCount B r)) : ℂ :=
  F (fun s d => intervalSiteCenter B r (k (s, d)))

noncomputable def groupedSiteFactor (B r : ℝ)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) (x : D → ℝ) : ℂ :=
  vectorIntervalSiteWeight B r (fun d => k (s, d)) x

noncomputable def groupedSiteApprox [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    (x : S → D → ℝ) : ℂ :=
  ∑ k : S × D → Fin (intervalSiteCount B r),
    groupedSiteCoefficient B r F k * ∏ s, groupedSiteFactor B r k s (x s)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

noncomputable def scalarInitialReferenceInput (m n d : ℕ) (p P0 : ℝ) : ℝ :=
  let Z := replacementCommonInputLog m n d P0
  let G := 2 * physicalPairCoefficientLog n d Z + 2
  G + Z + P0 + m + n + d + scalarTransferTail (3 * p) + p + 20

end Erdos3

end

section

namespace Erdos3

noncomputable def scalarCombinedLogThreshold (n d b : ℕ)
    (p P0 Z G refCost cellLog meshLog : ℝ) : ℝ :=
  refCost + p + scalarTransferTail (3 * p) + 2 * physicalReplacementThresholdLog n d b Z +
    G + P0 + 4 * meshLog + 2 * cellLog + 2 * Z + 100

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LayeredCoverSiteExtension
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable (q : ℕ) [NeZero q]

noncomputable def quarterCoverPoint {D : Type*} (a : D → ZMod q) (x : D → ℝ) :
    D → UnitAddCircle := fun i => circleQuarterCover q (a i) (x i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotStageBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def pivotKernelFactor {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (a b : R) (parameter : ℝ) (f g : R → ℝ)
    (z : Fin l → Fin q → R) (x d : R) : ℝ :=
  ∏ beta : Fin l → Fin q, countingKernel parameter
    (f (pivotCellForm v a z x d beta)) (g (pivotCellForm v b z x d beta))

noncomputable def pivotStageIntegrand {I R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin l → Fin q → R) (x d : R) : ℝ :=
  (∏ i ∈ S, pivotGridFactor v (slopes i) (mu i) z x d) *
    pivotKernelFactor v a b parameter f g z x d

noncomputable def pivotStageCount {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) : ℝ :=
  𝔼 z : Fin l → Fin q → R, 𝔼 x, 𝔼 d, pivotStageIntegrand v S slopes mu a b parameter f g z x d

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SecondaryMeshGeometry
namespace OAI

section

namespace Erdos3

noncomputable def secondaryBoundaryMargin (boundary beta : ℝ) : ℝ := replacementAccuracy boundary beta

noncomputable def secondaryMeshDelta (boundary movement beta : ℝ) : ℝ :=
  replacementAccuracy movement (secondaryBoundaryMargin boundary beta)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedSplitUnitSource
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def selectedSplitMeasurableEquiv {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) :
    ((UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) ≃ᵐ (J ⊕ N → ℝ) :=
  (splitFreeCoordinates I (UnselectedColumn s) N).trans
    (((selectedCoefficientMeasurableEquiv s).prodCongr (MeasurableEquiv.refl (N → ℝ))).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).symm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerBoxZeroCube
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def integerBoxCubeProductEquiv {I : Type*} [Fintype I] [DecidableEq I] (N : I → ℕ) (q : ℕ) :
    SupportedCube q (integerBox N : Set (I → ℤ)) ≃
      (∀ i, SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ))) where
  toFun c i := ⟨(fun j => c.val.1 j i, c.val.2 i), by
    intro ω
    have h := (mem_integerBox N _).mp (c.property ω) i
    simpa only [Set.mem_Ico, Pi.add_apply, cubeShift, Finset.sum_apply, ite_apply, Pi.zero_apply] using h⟩
  invFun c := ⟨(fun j i => (c i).val.1 j, fun i => (c i).val.2), by
    intro ω
    apply (mem_integerBox N _).mpr
    intro i
    have h := (c i).property ω
    simpa only [Set.mem_Ico, Pi.add_apply, cubeShift, Finset.sum_apply, ite_apply, Pi.zero_apply] using h⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by funext i; apply Subtype.ext; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SmoothSelectedSpatialLaw
namespace OAI

section

namespace Erdos3

noncomputable def selectedFullSpatialColumnEquiv {I J : Type*} [Fintype I]
    (s : I ↪ J) (N : Type*) :
    (Unit ⊕ I) ⊕ (UnselectedColumn s ⊕ N) ≃ (Unit ⊕ J) ⊕ N :=
  (Equiv.sumAssoc (Unit ⊕ I) (UnselectedColumn s) N).symm.trans
    (Equiv.sumCongr (selectedSpatialColumnEquiv s) (Equiv.refl N))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

def scalarTupleSpatialColumns {I N : Type*} (T : N → ℕ) (c : N → ℤ)
    (x : ∀ j, IntegerScalarCubeBox I (T j)) : Matrix (Unit ⊕ I) N ℤ :=
  tupleColumnMatrix (fun j x => scalarTupleColumn (c j) (fun i => (x i : ℤ))) x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A] [DecidableEq A]

noncomputable def selectedBooleanSiteRows (axis : A) (rows : Finset (Finset α))
    (x : Finset α → A → ℝ) : rows → ℝ :=
  fun t => booleanCoefficient (fun s => x s axis) t

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LatticeTorusFourierCoefficient
namespace OAI

section

namespace Erdos3

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeBasis_integerCoordinates (b : Module.Basis ι ℤ Λ) (n : ι → ℤ) :
    (b.ofZLatticeBasis ℝ Λ).equivFun.symm (fun i => (n i : ℝ)) = (b.equivFun.symm n : E) := by
  apply (b.ofZLatticeBasis ℝ Λ).equivFun.injective
  ext i
  rw [LinearEquiv.apply_symm_apply]
  change (n i : ℝ) = (b.ofZLatticeBasis ℝ Λ).repr (b.equivFun.symm n : E) i
  rw [Module.Basis.ofZLatticeBasis_repr_apply]
  exact (congrArg (fun z : ℤ => (z : ℝ)) (congrFun (b.equivFun.apply_symm_apply n) i)).symm

theorem latticeGaussian_integer_periodic (b : Module.Basis ι ℤ Λ) (t : ℝ)
    (x : ι → ℝ) (n : ι → ℤ) :
    latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm (fun i => x i + (n i : ℝ))) =
      latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) := by
  change latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm (x + (fun i => (n i : ℝ)))) = _
  rw [map_add, latticeBasis_integerCoordinates]
  exact latticeGaussianMass_add_lattice Λ t _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SortedLayerCoordinateEnumeration
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {m : ℕ} (E : Fin m → Type) [∀ j, Fintype (E j)]

noncomputable def sortedLayerCoordinateWeight (i : Fin (Fintype.card (Σ j, E j))) : ℕ :=
  (sortedLayerCoordinateEquiv E i).1.val + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedAnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

def physicalSpatialSplitEquiv (G N : Type*) : ((Unit ⊕ G) ⊕ N) ≃ Option (G ⊕ N) :=
  (Equiv.sumAssoc Unit G N).trans (physicalCubeOptionEquiv (G ⊕ N))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

def zeroScalarFinPoint (L : ℕ) (t : Fin L) : IntegerScalarCubeBox Empty L :=
  fun _ => ⟨t.val, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast t.isLt⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

instance kernelPeriodCandidate_neZero {B : ℕ} (degree : ℕ) (a : Fin B) :
    NeZero (kernelPeriodCandidate degree a) :=
  ⟨(kernelPeriodCandidate_pos degree a).ne'⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedAffineAccurateSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite

noncomputable def affineSourceSum {ι : Type*} [Finite ι] (f : ι → ℝ) : ℝ :=
  @Finset.sum ι ℝ _ (@Finset.univ ι (Fintype.ofFinite ι)) f

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputStepLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem padicStepQuotient_coprime {p step : ℕ} (hp : p.Prime)
    (hstep : step ≠ 0) (A : ℕ) :
    (step / p ^ padicValNat p step).Coprime (p ^ A) := by
  let : Fact p.Prime := ⟨hp⟩
  apply Nat.Coprime.pow_right A
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  have hm := Nat.mul_dvd_mul_left (p ^ padicValNat p step) h
  rw [← pow_succ, Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := step))] at hm
  exact pow_succ_padicValNat_not_dvd hstep hm

def padicStepQuotientUnit (p A step : ℕ) (hp : p.Prime) (hstep : step ≠ 0) :
    (ZMod (p ^ A))ˣ :=
  ZMod.unitOfCoprime (step / p ^ padicValNat p step)
    (padicStepQuotient_coprime hp hstep A)

@[simp] theorem padicStepQuotientUnit_coe (p A step : ℕ)
    (hp : p.Prime) (hstep : step ≠ 0) :
    (padicStepQuotientUnit p A step hp hstep : ZMod (p ^ A)) =
      (step / p ^ padicValNat p step : ℕ) := rfl

variable {L V : Type*} [Fintype L]

def prescribedCRTArbitraryStepEquiv (p A : L → ℕ) (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0) :
    (∀ l, V → ZMod (p l ^ A l)) ≃+ (∀ l, V → ZMod (p l ^ A l)) where
  toFun x l v := padicStepQuotientUnit (p l) (A l) step (hp l) hstep * x l v
  invFun x l v := ↑(padicStepQuotientUnit (p l) (A l) step (hp l) hstep)⁻¹ * x l v
  left_inv x := by
    funext l v
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    funext l v
    simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := by
    funext l v
    exact mul_add _ _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtGaussianMean
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def latticeGaussianMean (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), normalizedLatticeGaussian Λ t ((n : ℝ) ^ k • α)) /
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ)

end Erdos3

end

end OAI
end


