-- Prove2me | Definitions.Def_OAIE3v2B086
-- name    : OAIE3v2B086
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:22:45.880944+00:00
-- url     : https://prove2.me/theorems/94d99ce1-4714-4e59-a4d6-ffa49f5a5e7d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 87 of 311
-- statement:
--   Definitions bundle 87 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B042`, `OAIE3v2B044`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B059`, `OAIE3v2B060`, `OAIE3v2B061`, `OAIE3v2B063`, `OAIE3v2B064`, `OAIE3v2B065`, `OAIE3v2B066`, `OAIE3v2B067` of this split.
--
--   Modules: `Dynamics/InitialBudgetJointReplacement.lean`, `Dynamics/PreparedEarlyStructuralPowerBudget.lean`, `Dynamics/ScalarCubeBoundaryLogBudget.lean`, `Dynamics/SharedWidthNormalizedTupleSideBudget.lean`, `Estimates/GroupedSiteTensor.lean`, `Estimates/PhysicalBoundaryLabels.lean`, `Estimates/PhysicalPairAccuracyLogBounds.lean`, `Estimates/PositiveShiftTestingGowers.lean`, `Estimates/ScalarCubeBoundaryVolume.lean`, `Estimates/ScalarCubeFaceSlab.lean`, `Estimates/ScalarInitialThreshold.lean`, `Estimates/SitePlateauCutoff.lean`, `Estimates/SmallWeightedPhysicalReplacement.lean`, `Estimates/SplitSmoothProductProfile.lean`, `Estimates/WeightedPlateauSiteApproximation.lean`, `Fourier/PlateauFourierMode.lean`, `Fourier/RationalCharacterIndividualModulus.lean`, `Fourier/UniformScaledRetainedCharacters.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/PhysicalBoxPartition.lean`, `Geometry/PrincipalSpatialSiteComparison.lean`, `Geometry/SpatialNumericEnvelopeFunctoriality.lean`, `Lattices/AffineSampleAlphabet.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/PrincipalResidueMixture.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Lattices/TriangularAffineReset.lean`, `Linear/KernelScaleIndependence.lean`, `Linear/PivotKernelAllowances.lean`, `Polynomial/PrependPolynomialVariable.lean`, `Polynomial/RawAffinePolynomialJet.lean`, `Polynomial/ScalarThresholdPolynomial.lean`, `Probability/ShiftedProductCoordinateLaw.lean`, `Probability/WeightedPlateauMixture.lean`, `Probability/WeightedSliceFamilyLaw.lean`, `Sampling/PositiveGridFamily.lean`, `Sampling/PrecenterForecastNativeAtomDictionary.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B059
import Definitions.Def_OAIE3v2B060
import Definitions.Def_OAIE3v2B061
import Definitions.Def_OAIE3v2B063
import Definitions.Def_OAIE3v2B064
import Definitions.Def_OAIE3v2B065
import Definitions.Def_OAIE3v2B066
import Definitions.Def_OAIE3v2B067

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothProductProfile_sum (I J : Type*) [Fintype I] [Fintype J]
    (x : I → ℝ) (y : J → ℝ) :
    smoothProductProfile (I ⊕ J) (Sum.elim x y) =
      smoothProductProfile I x * smoothProductProfile J y := by
  simp [smoothProductProfile, Fintype.prod_sum_type]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def splitSmoothProductProfile (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ℝ :=
  smoothProductProfile J p.1 * smoothProductProfile I p.2

theorem splitSmoothProductProfile_range (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) :
    0 ≤ splitSmoothProductProfile J I p ∧ splitSmoothProductProfile J I p ≤ 1 := by
  have hJ := smoothProductProfile_range J p.1
  have hI := smoothProductProfile_range I p.2
  exact ⟨mul_nonneg hJ.1 hI.1, (mul_le_mul hJ.2 hI.2 hI.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem splitSmoothProductProfile_zero_outside (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) (hp : 1 < ‖p‖) : splitSmoothProductProfile J I p = 0 := by
  change 1 < max ‖p.1‖ ‖p.2‖ at hp
  rcases lt_max_iff.mp hp with h | h
  · exact mul_eq_zero_of_left (smoothProductProfile_zero_outside J p.1 h) _
  · exact mul_eq_zero_of_right _ (smoothProductProfile_zero_outside I p.2 h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeBoundaryVolume
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def scalarCubeFaceStrip {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) : Set (Option α → ℝ) :=
  scalarCubeDomain α ∩ {a | scalarCubeFace i a < u}

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
open scoped BigOperators

def scalarCubeFaceSlab {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) (u : ℝ) : Set (Option I → ℝ) :=
  Metric.closedBall 0 2 ∩ {x | |scalarCubeFace i x| ≤ u}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeBoundaryLogBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def scalarCubeProductDerivativeConstant (α : Type*) [Fintype α]
    [DecidableEq α] (A : ℝ≥0) : ℝ :=
  ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A *
    scalarCubeBoundaryConstant α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

def scalarCubeLargeCokernelEvent {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {L : ℕ} (B : ℕ) (x : J → IntegerScalarCubeBox I L) : Prop :=
  (∃ s : I → J, ((scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0) ∧
    B < integerCokernelExponent (scalarCubeDifferenceMatrix x).mulVecLin.range


open scoped BigOperators

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotKernelAllowances
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def pivotKernelCap {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R H : ℝ≥0) : ℝ≥0 :=
  ⟨inverseJacobian A, (inverseJacobian_pos A).le⟩ * H * (2*R)^Fintype.card J

noncomputable def pivotKernelLip {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R K : ℝ≥0) : ℝ≥0 :=
  pivotKernelCap J A R K * ‖A.symm.toContinuousLinearMap‖₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3

noncomputable def normalizedScalarKernelJet {I J O : Type*}
    [DecidableEq I] {L : ℕ} (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) : Matrix O (BoundedIntegerExponent J h) ℝ :=
  boundedDegreeRealJetMatrix (fun j => (x j none : ℝ) / L)
    (fun i j => (x j (some i) : ℝ) / L) h rows

noncomputable def scalarKernelFixedFree {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree) :
    (UnselectedColumn s → ℝ) →L[ℝ] (O → ℝ) :=
  matrixSupCLM (remainingMatrixColumns (normalizedScalarKernelJet x degree rows) s)

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem selectedCoefficient_weight_sum {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) (S : J → ℝ) :
    scaledInputWeightSum (selectedCoefficientProfile s f)
      (fun i => S (s i)) (fun j => S j.val) = coefficientWeightSum f S := by
  rw [scaledInputWeightSum, coefficientWeightSum]
  simp only [← selectedIntegerCoefficient_weight]
  exact (selectedIntegerCoefficientEquiv s).tsum_eq _

theorem selectedCoefficient_weight_sum_pos {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hM : 0 < scaledInputMass (selectedCoefficientProfile s f)
      (fun i => S (s i)) (fun j => S j.val)) : 0 < coefficientWeightSum f S := by
  rw [← selectedCoefficient_weight_sum s]
  exact scaledInputWeightSum_pos _ _ _ (fun i => hS (s i)) (fun j => hS j.val) hM

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem physicalBoxCell_nonempty (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) :
    Nonempty (IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
      (fun _ => 1) (fun _ => 0)) := by
  refine ⟨fun i => ⟨intervalCellLower (lo i) (P i) (c i), Finset.mem_filter.mpr ⟨?_, Int.modEq_one⟩⟩⟩
  exact Finset.mem_Ico.mpr ⟨le_rfl, lt_add_of_pos_right _ (by exact_mod_cast hpos i (c i))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalBoundaryLabels
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

def physicalBoundaryNear (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) (x : I → ℤ) : Prop :=
  ∃ i c, |x i - intervalCellLower (lo i) (P i) c| ≤ (r i : ℤ) ∨
    |x i - intervalCellUpper (lo i) (P i) c| ≤ (r i : ℤ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def uniformBlockSpectrumCover (J : Type*) [Fintype J] [DecidableEq J]
    (M n : ℕ) (U V L ζ : ℝ) : Finset (J → Fin M) :=
  lengthAwareSpectrumCover (majorArcLengthConstant n U) L (majorArcLengthExponent n)
    (polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
      (majorArcCoverExponent n (Fintype.card J))) ζ

noncomputable def uniformBlockSpectrumCardBudget (n j t : ℕ) (U V W ζ : ℝ) : ℝ :=
  majorArcSpectrumConstant n j U V / ζ ^ majorArcSpectrumExponent n j +
    W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t)

end Erdos3

end

section

namespace Erdos3

noncomputable def uniformCharacterDenominatorBound (n j t : ℕ) (U V W ζ : ℝ) : ℝ :=
  1 + (3 * majorArcCoverConstant n j U V) ^ j / ζ ^ (majorArcCoverExponent n j * j) +
    W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t)

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

noncomputable def normalizedLatticePointHom :
    W × (Fin n → ℤ) →+ EuclideanSpace ℝ D where
  toFun := normalizedLatticePoint W b
  map_zero' := by
    simp [normalizedLatticePoint]
    rfl
  map_add' x y := by
    unfold normalizedLatticePoint
    rw [← map_add]
    congr 1
    ext i
    · rfl
    · simp [add_div]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

def principalTupleResidues {D α : Type*} {B : D → Type*} {h : D → ℕ} {m : ℕ}
    (r : PrincipalTupleIndex B h → Option α → ZMod m) : JointBlockParameter B h α → ZMod m :=
  fun a => r ⟨a.1, a.2.1, a.2.2.1⟩ a.2.2.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

noncomputable def paddedResidueDensityFactor (I : Type*) [Fintype I] (L P : ℕ)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) : ℝ :=
  (P : ℝ) ^ (Fintype.card I + 1) /
    ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrependPolynomialVariable
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def prependPolynomialVariable {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n+1)) ℝ := MvPolynomial.X 0 * MvPolynomial.rename Fin.succ P

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

noncomputable def plateauFourierMode (H : ℝ) (ω x : J → ℝ) : ℂ :=
  (normalizedSupportPlateau H x : ℂ) * realLinearCharacter ω x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedPlateauMixture
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {T J : Type*} [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable [Fintype J]

noncomputable def plateauModeMixture (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (x : J → ℝ) : ℂ :=
  ∫ t, rationalGridPhase D a (integerGridResidue D (shift t)) *
    plateauFourierMode H (fun j => -ω j) (x - fun j => (shift t j : ℝ) / K) ∂p.toMeasure

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def zeroScalarCubeIntervalEquiv (α : Type*) [Fintype α]
    [DecidableEq α] [IsEmpty α] (L : ℕ) :
    ↥(integerScalarCubeSet α L) ≃ ↥(Finset.Ico (0 : ℤ) (L : ℤ)) where
  toFun x := by
    have h0 := ((mem_integerScalarCubeSet L x.val).mp x.property) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h0
    exact ⟨x.val none, Finset.mem_Ico.mpr h0⟩
  invFun z := by
    have hz := Finset.mem_Ico.mp z.property
    let x : IntegerScalarCubeBox α L := fun _ =>
      ⟨z.val, Finset.mem_Ico.mpr ⟨by omega, hz.2⟩⟩
    refine ⟨x, (mem_integerScalarCubeSet L x).mpr ?_⟩
    intro t
    have ht : t = ∅ := Subsingleton.elim _ _
    simpa only [ht, integerScalarCubeValue, Finset.sum_empty, add_zero] using hz
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    cases i with
    | none => rfl
    | some a => exact isEmptyElim a
  right_inv z := by apply Subtype.ext; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateCell_subtypeEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateCell lo N q I x ≃
      {z : translatedIntegerBox lo N // ∀ i ∈ I, (fun j => (z.val j : ZMod (q i))) = x i} where
  toFun z := ⟨⟨z.val, ((mem_primeCoordinateCell lo N q I x z.val).mp z.property).1⟩,
    ((mem_primeCoordinateCell lo N q I x z.val).mp z.property).2⟩
  invFun z := ⟨z.val.val, (mem_primeCoordinateCell lo N q I x z.val.val).mpr ⟨z.val.property, z.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def physicalResidualPairBudget {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (k : J) (Q : ℕ)
    (C κ δ : ℝ) (degree : ℕ) (eta ρ : ℝ) : ℝ :=
  ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) *
    ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap (BoundedPrime Q) degree eta) ^ 2 +
      (fullSmoothPairError (Fintype.card I) k Q C κ δ + (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
        (2 : ℝ) ^ Fintype.card I * (1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2))

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physicalPairMeanAccuracy_inverse_le_exp (n degree : ℕ) (k : J) (Q : ℕ)
    {C κ A epsilon P : ℝ} (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hA0 : 0 ≤ A) (heps0 : 0 < epsilon) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (heps : epsilon⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (physicalPairMeanAccuracy n k Q C κ A degree epsilon)⁻¹ ≤
      Real.exp (2 * physicalPairMeanLog n degree P + 2) := by
  have hlogs := physicalPairMeanLog_bounds n degree hP
  have hpower := (physicalPairPowerBounds n hA0 hA).1
  have hK := smoothPairKernelCap_le_exp n k hP hC0 hκ0 hC hκ hpow
  have hcount : (Fintype.card (BoundedPrime Q) : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (boundedPrime_card_le Q)).trans hQ
  have hV := residualCapEnvelope_le_exp degree hP hcount
  have hV0 := zero_le_one.trans (residualCapEnvelope_one_le (BoundedPrime Q) degree)
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hprod : 3 * A ^ (2 * n) * (smoothPairKernelCap n k C κ : ℝ) ≤
      Real.exp (3 + 2 * n * P + n * (5 * P + 11)) := by
    calc
      _ ≤ Real.exp 3 * Real.exp (2 * n * P) * Real.exp ((n : ℝ) * (5 * P + 11)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]
  have hsum := one_add_le_exp_succ (by positivity : 0 ≤ 3 + 2 * n * P + n * (5 * P + 11)) hprod
  apply residualMeanAccuracy_inverse_le_exp (by positivity) (by positivity) heps0 hlogs.1
  · calc
      _ ≤ (Real.exp ((degree : ℝ) * (P + 2) + 2)) ^ 2 *
          Real.exp ((3 + 2 * n * P + n * (5 * P + 11)) + 1) := by gcongr
      _ = Real.exp (2 * ((degree : ℝ) * (P + 2) + 2) + 4 + 2 * n * P + n * (5 * P + 11)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold physicalPairMeanLog; linarith)
  · exact heps.trans (Real.exp_le_exp.mpr hlogs.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

theorem weightedReplacementTolerance_pos {F E epsilon : ℝ}
    (hE : 0 ≤ E) (heps : 0 < epsilon) :
    0 < weightedReplacementTolerance F E epsilon :=
  (replacementAccuracy_spec (mul_nonneg (sq_nonneg F) (by linarith)) (sq_pos_of_pos heps)).1

end Erdos3

end

section

namespace Erdos3

theorem weightedReplacementTolerance_inverse_le_exp {F E epsilon P : ℝ}
    (hF0 : 0 ≤ F) (hE0 : 0 ≤ E) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hF : F ≤ Real.exp P) (hE : E ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (weightedReplacementTolerance F E epsilon)⁻¹ ≤ Real.exp (6 * P + 6) := by
  have hcoef : F ^ 2 * (1 + E) ≤ Real.exp (3 * P + 2) := by
    calc
      _ ≤ (Real.exp P) ^ 2 * Real.exp (P + 1) :=
        mul_le_mul (pow_le_pow_left₀ hF0 hF 2) (one_add_le_exp_succ hP hE)
          (by linarith) (by positivity)
      _ = Real.exp (3 * P + 1) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have heps2 : (epsilon ^ 2)⁻¹ ≤ Real.exp (3 * P + 2) := by
    calc
      _ = (epsilon⁻¹) ^ 2 := by rw [inv_pow]
      _ ≤ (Real.exp P) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr heps0.le) heps 2
      _ = Real.exp (2 * P) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp (2 * (3 * P + 2) + 2) :=
      replacementAccuracy_inverse_le_exp (by positivity) (sq_pos_of_pos heps0)
        (by linarith) hcoef heps2
    _ = _ := by congr 1; ring

theorem physicalReplacementTolerance_inverse_le_exp (m n : ℕ) {K A epsilon P : ℝ}
    (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon)⁻¹ ≤
      Real.exp (6 * physicalReplacementInputLog m n P + 6) := by
  apply weightedReplacementTolerance_inverse_le_exp (by positivity) (by positivity) heps0
    (physicalReplacementInputLog_nonneg m n hP)
  · apply (replacementWindowFactor_le_exp m hK0 hK).trans
    apply Real.exp_le_exp.mpr
    unfold physicalReplacementInputLog
    nlinarith [mul_nonneg (Nat.cast_nonneg n (α := ℝ)) hP]
  · apply (replacementSampledEnergy_le_exp n hA0 hA).trans
    apply Real.exp_le_exp.mpr
    unfold physicalReplacementInputLog
    nlinarith [mul_nonneg (Nat.cast_nonneg m (α := ℝ)) (by linarith : 0 ≤ P + 3)]
  · apply heps.trans
    apply Real.exp_le_exp.mpr
    unfold physicalReplacementInputLog
    nlinarith [mul_nonneg (Nat.cast_nonneg m (α := ℝ)) (by linarith : 0 ≤ P + 3),
      mul_nonneg (Nat.cast_nonneg n (α := ℝ)) hP]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement
namespace OAI

section

namespace Erdos3

theorem replacement_selected_parameter_bounds (m n d D : ℕ) {K A Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hCwidth : Cwidth ≤ Real.exp P) (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let Z := replacementCommonInputLog m n d P
    0 < tol ∧ tol⁻¹ ≤ Real.exp Z ∧
    0 < integerBoxRetainedGap d D c tol ∧ (integerBoxRetainedGap d D c tol)⁻¹ ≤ Real.exp Z ∧
    ((D * integerBoxGcdCutoff d Cwidth tol : ℕ) : ℝ) ≤ Real.exp Z ∧
    integerBoxPairScale d Cwidth tol ≤ Real.exp Z := by
  intro tol Z
  let T := replacementCutoffInputLog m n d P
  have hb := replacementCutoffInputLog_bounds m n d hP
  have hz := replacementCommonInputLog_bounds m n d hP
  have hpows := replacementCutoffInputLog_power_bounds m n d hP
  have ht : 0 < tol := weightedReplacementTolerance_pos (by positivity) heps0
  have hti : tol⁻¹ ≤ Real.exp T :=
    (physicalReplacementTolerance_inverse_le_exp m n hK0 hA0 heps0 hP hK hA heps).trans
      (Real.exp_le_exp.mpr hb.2.2.1)
  have hexp : Real.exp P ≤ Real.exp T := Real.exp_le_exp.mpr hb.2.1
  have hq := integerBoxGcdModulus_le_exp d D hCwidth0 ht hb.1 hpows.1
    (hDlog.trans hexp) (hCwidth.trans hexp) hti
  have hk := integerBoxRetainedGap_inverse_le_exp d D hD hc0 ht hb.1 hpows.2 (hc.trans hexp) hti
  have hs := integerBoxPairScale_le_exp d hCwidth0 ht hb.1 hpows.1 hpows.2 (hCwidth.trans hexp) hti
  refine ⟨ht, hti.trans (Real.exp_le_exp.mpr hz.2.2.1), ?_, ?_, ?_, ?_⟩
  · unfold integerBoxRetainedGap
    exact mul_pos (mul_pos (by exact_mod_cast hD) (integerBoxNearRatio_spec d ht).1) hc0
  · exact hk.trans (Real.exp_le_exp.mpr (by linarith [hz.2.2.2.2.1]))
  · exact hq.trans (Real.exp_le_exp.mpr hz.2.2.2.1)
  · exact hs.trans (Real.exp_le_exp.mpr hz.2.2.2.2.1)

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

noncomputable def vectorResidueSiteWeight {D : Type*} [Fintype D] (b r : ℝ) (H : D → ℝ)
    {m : ℕ} (a : D → ZMod m) (k : D → Fin (intervalSiteCount b r)) (u : D → ℤ) : ℂ :=
  ∏ d, (residueIntervalSiteWeight b r (H d) (a d) (k d) (u d) : ℂ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def principalSpatialColumns {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (y : PrincipalIntegerTuples B h α L) : Matrix (Unit ⊕ α) N ℤ :=
  scalarTupleSpatialColumns (fun n => L (index n)) c (fun n => y (index n))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RawAffinePolynomialJet
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def originalMonomialJetMap {C Z X K α O : Type*}
    [Fintype C] [Fintype α] [DecidableEq α]
    (e : C → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : O → Finset α) (c w : C → ℝ) (x : X → ℝ) (r : C → ℝ) (o : O) : ℝ :=
  booleanCoefficient (fun t => MvPolynomial.eval (normalizedCubeTuple input z x t)
    (monomialArrayPolynomial e (fun j => c j + w j * r j))) (rows o)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftTestingGowers
namespace OAI

section

namespace Erdos3

noncomputable def shiftDetectionPolynomial (s C : ℕ) : Polynomial ℕ :=
  Polynomial.C 6 * Polynomial.X + Polynomial.C (2 ^ (s + 1)) *
    (Polynomial.C 6 * Polynomial.X + Polynomial.C C) ^ C

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveGridFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveGridFiber {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*} [Add G]
    (f : PositiveGridVertex a → G → ℝ) (t : Fin (a 0) → G) (c : ℝ)
    (b : PositiveGridVertex (fun i => a i.succ)) : G → ℝ :=
  normalizedAxisProduct (fun i => f (Fin.cons i b)) t c

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

noncomputable def rationalBooleanSitePhase (D : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (s : Finset α) (v : ZMod D) : ℂ :=
  rationalGridPhase D a (fun t => booleanCoefficient (Pi.single s v) t)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SitePlateauCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def scalarSupportPlateau (H x : ℝ) : ℂ :=
  normalizedSupportPlateau H (fun _ : Unit => x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

noncomputable def normalizedTupleRadius (X : Type*) [Fintype X]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E W : ℝ) : ℝ :=
  twoTermErrorWidth (Real.exp (p ^ 3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W)))
    (normalizedTupleTolerance X p E)

noncomputable def normalizedTupleResolution (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ)
    (p E C₀ W Cg Centry : ℝ) : ℝ :=
  twoTermErrorResolution
    (anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
      2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry))
    (anisotropicSpatialDiscretizationCost N s M C₀) (normalizedTupleTolerance X p E) +
    (Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X))) /
      (normalizedSpatialShare E / 2) +
    (Fintype.card N * (2 * Centry)) / normalizedTupleRadius X s M p E W

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedWidthNormalizedTupleSideBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def sharedWidthNormalizedTupleSideLog (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E l Bξ : ℝ) : ℝ :=
  3 * normalizedTupleLateBudget X N s p E l + Bξ + 3 * l + 17

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalCharacterIndividualModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {O : Type*} {N : ℕ}

variable [NeZero N] (qW : ℕ) [NeZero qW] (χ : AddChar (O → ZMod N) ℂ)

variable (hW : qW ∣ N)

omit [NeZero qW] in
theorem exists_rationalCharacterIndividualReduction [NeZero qW] :
    ∃ ψ : AddChar (O → ZMod (rationalCharacterIndividualModulus qW χ)) ℂ,
      characterPullback (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW)) ψ = χ ∧
        orderOf ψ = orderOf χ := by
  apply exists_zmodPiReduction_character (rationalCharacterIndividualModulus_dvd qW χ hW) χ
  exact orderOf_dvd_iff_pow_eq_one.mp (rationalCharacterIndividualModulus_order_dvd qW χ)

noncomputable def rationalCharacterIndividualReduction :
    AddChar (O → ZMod (rationalCharacterIndividualModulus qW χ)) ℂ :=
  (exists_rationalCharacterIndividualReduction qW χ hW).choose

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

noncomputable def preparationModulusCap (s M R : ℕ) (p : ℝ) : ℕ :=
  R * preparationHeight p s ^ M

noncomputable def preparationOscillationCap (s n R : ℕ) (p : ℝ) : ℕ :=
  (s + 1) * (n + 1) ^ s * R * n * s * preparationHeight p s

noncomputable def preparationShrink (s n M R : ℕ) (p δ : ℝ) : ℝ :=
  4 * preparationModulusCap s M R p /
    min 1 (δ / (preparationOscillationCap s n R p + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarThresholdPolynomial
namespace OAI

section

namespace Erdos3

noncomputable def scalarThresholdPolynomial : Polynomial ℕ :=
  let X := Polynomial.X
  let b := 1024 * (X + 3) ^ 3
  let row := (16 + 4 * X) * X + 16 * X + 48
  let error := X + row + X * (row + 6 * X + 12)
  let coeff := 30 + 2 * X * X + 2 * X + error + X * (5 * X + 11) + 10 * X + 4 * (2 + X)
  let mean := 2 * (b * (X + 2) + 2) + 4 + 2 * X * X + X * (5 * X + 11) + X
  let replacement := 2 * coeff + 2 * mean + (2 * b + 2) * X + 20
  let accuracy := 3 * X + (b * (X + 2) + 1) + 10
  let cell := 65536 * (X + 3) ^ 4 + X * b + accuracy + X + 1
  let mesh := X + 3 * (X + 1) + accuracy + 50
  X + X + 2 * (3 * X + 10) + 2 * replacement + X + X + 4 * mesh + 2 * cell + 2 * X + 100

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarInitialThreshold
namespace OAI

section

namespace Erdos3

noncomputable def scalarInitialThreshold (E m n d : ℕ) (epsilon p P0 : ℝ) : ℝ :=
  let Z := replacementCommonInputLog m n d P0
  let G := 2 * physicalPairCoefficientLog n d Z + 2
  let U := scalarInitialReferenceInput m n d p P0
  let pref := affineReferenceInput epsilon U
  let common := affineCommonReferenceBudget E epsilon U
  let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
    (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
  scalarCombinedLogThreshold n d b p P0 Z G ((pref + 2) ^ E)
    (scalarTransferCellLog common b p Z U)
    (scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.TriangularAffineReset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d : ℕ}

noncomputable def reducedTriangularMatrix (T : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  T * (triangularReductionMatrix T).map (Int.castRingHom ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrecenterForecastNativeAtomDictionary
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable instance precenterForecastNativeAtomLabelFintype
    {X Branch : Type*} [Fintype Branch] (models : Branch → CenteredForecastModel X) :
    Fintype (PrecenterForecastNativeAtomLabel models) := by
  unfold PrecenterForecastNativeAtomLabel
  infer_instance

end Erdos3

end

end OAI
end


