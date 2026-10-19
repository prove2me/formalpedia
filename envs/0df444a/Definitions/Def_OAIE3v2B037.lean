-- Prove2me | Definitions.Def_OAIE3v2B037
-- name    : OAIE3v2B037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:51.352441+00:00
-- url     : https://prove2.me/theorems/5996d12e-ab7a-489f-aa7b-a617b842dc5d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 38 of 311
-- statement:
--   Definitions bundle 38 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CanonicalZeroLayerBudgetedInitialization.lean`, `Dynamics/InitialBudgetJointReplacement.lean`, `Dynamics/PivotNativeIteration.lean`, `Dynamics/ScalarMeshCoefficientBudget.lean`, `Estimates/AllocatedExternalCandidateTaggedPairFamily.lean`, `Estimates/BooleanSelectedDerivativeBound.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/ComplexFiniteMeans.lean`, `Estimates/FixedPartnerPower.lean`, `Estimates/IndexedComparableScalarGeometryData.lean`, `Estimates/InteriorIntervalCutoff.lean`, `Estimates/InverseSqrtMoment.lean`, `Estimates/JointBooleanStability.lean`, `Estimates/PhysicalPairAccuracyLogBounds.lean`, `Estimates/PivotJacobianBound.lean`, `Estimates/PivotStageBoundary.lean`, `Estimates/PositiveShiftTestingGowers.lean`, `Estimates/PreparedCanonicalRelativeEndpointBounds.lean`, `Estimates/RealBooleanInterpolation.lean`, `Estimates/RelativeScalarPassageDiscount.lean`, `Estimates/ResidualErrorAllocation.lean`, `Estimates/RetainedPatchCutoffChoice.lean`, `Estimates/SecondaryMeshGeometry.lean`, `Estimates/ShiftDifferenceCount.lean`, `Estimates/ShiftedSmoothSelectedMarginal.lean`, `Estimates/SigmaProductPeriodization.lean`, `Estimates/SlicedPrincipalInverse.lean`, `Estimates/SmallWeightedPhysicalReplacement.lean`, `Estimates/SubsetAlternatingInversion.lean`, `Estimates/TaggedZModOrderBounds.lean`, `Fourier/ConfigurationCharacters.lean`, `Fourier/FiniteSpectrumCutoff.lean`, `Fourier/PrimePowerCharacterScaling.lean`, `Fourier/RationalCharacterIndividualModulus.lean`, `Geometry/ActualFixedSpatialRetainedPatchEndpoint.lean`, `Geometry/OneDimensionalBox.lean`, `Geometry/PrincipalSpatialSiteComparison.lean`, `Geometry/QuotientCoordinateRadius.lean`, `Geometry/ScalarCubeCoordinates.lean`, `Geometry/SplitFreeCoordinates.lean`, `Geometry/UnitBoxInteriorCutoff.lean`, `Lattices/AffineCubeMinorGoodMass.lean`, `Lattices/AffineLowestLayer.lean`, `Lattices/AffineResidualRecovery.lean`, `Lattices/AllocatedSupportedSlicedResidue.lean`, `Lattices/CRTProgressionVanishing.lean`, `Lattices/FiniteAffineClassAverage.lean`, `Lattices/FullAffineCoefficientBound.lean`, `Lattices/IntegerAffineResidues.lean`, `Lattices/RecoveredLatticeMatrixInvariance.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Lattices/StrideSelectedResidueBadProduct.lean`, `Lattices/TupleResidueConditioning.lean`, `Lattices/WeightedScalarResidueCell.lean`, `Linear/CountingKernelOuter.lean`, `Linear/ProductANOVATensorChoices.lean`, `Linear/ProductKernelPairing.lean`, `Linear/RecoveredKernelScalarBudget.lean`, `Linear/SmoothCoefficientRankBadProduct.lean`, `Linear/WeightedDualVector.lean`, `Nilpotent/UnconditionedScalarScaleNiltestBase.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/CRTPolynomialImage.lean`, `Polynomial/CRTPolynomialInputAffineLaw.lean`, `Polynomial/EmbeddedMatrixDeterminantPolynomial.lean`, `Polynomial/PolynomialCoordinatePartition.lean`, `Polynomial/PolynomialDifferencePermanentCombinatorics.lean`, `Polynomial/PolynomialParameterContinuity.lean`, `Polynomial/PolynomialPatchProductBudget.lean`, `Polynomial/RationalPolynomialForecastBoxError.lean`, `Polynomial/RestrictedDegreeSupports.lean`, `Polynomial/ScalarCubeMinorPolynomial.lean`, `Polynomial/SchmidtShortDualVector.lean`, `Polynomial/WeylStepScales.lean`, `Probability/AllocatedNarrowSpatialLaw.lean`, `Probability/RegularizedSigmaDensity.lean`, `Probability/ShiftedProductCoordinateLaw.lean`, `Probability/SlicedRemainderDensityFamily.lean`, `Results/Reciprocal.lean`, `Sampling/AllocatedPeriodicGridQuadrature.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def realShiftCorrelation (a J : G → ℝ) (h : G) : ℝ :=
  𝔼 n, a n * J (n + h)

noncomputable def realBilinearAverage (a H W : G → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, H x * W y * a (x + y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineLowestLayer
namespace OAI

section

namespace Erdos3

def shiftedIntegerBlock {T : Type*} {D : ℕ} (I : T → Fin D → ℤ)
    (t₀ : T) (b₀ : Fin D → ℤ) (t : T) : Fin D → ℤ := b₀ + I t - I t₀

@[simp] theorem shiftedIntegerBlock_at_base {T : Type*} {D : ℕ}
    (I : T → Fin D → ℤ) (t₀ : T) (b₀ : Fin D → ℤ) :
    shiftedIntegerBlock I t₀ b₀ t₀ = b₀ := by simp [shiftedIntegerBlock]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

noncomputable def shiftedParameterPolynomials {σ : Type*} {D : ℕ}
    (I : Fin D → MvPolynomial σ ℝ) (t₀ : σ → ℝ) (b₀ : Fin D → ℤ) :
    Fin D → MvPolynomial σ ℝ := fun i => C (b₀ i : ℝ) + I i - C (aeval t₀ (I i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling
namespace OAI

section

namespace Erdos3

theorem zmod_character_order_dvd {I : Type*} {N : ℕ}
    (χ : AddChar (I → ZMod N) ℂ) : orderOf χ ∣ N := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow]
  have hx : N • x = 0 := by
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  rw [hx, AddChar.map_zero_eq_one, AddChar.one_apply]

theorem zmod_character_order_pos {I : Type*} {N : ℕ} [NeZero N]
    (χ : AddChar (I → ZMod N) ℂ) : 0 < orderOf χ := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hdvd := zmod_character_order_dvd χ
  rw [hz, zero_dvd_iff] at hdvd
  exact NeZero.ne N hdvd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

def pivotFreeAdmissible {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ) (y : J → ℤ) : Prop :=
  v - B *ᵥ y ∈ A.mulVecLin.range

theorem pivotFreeAdmissible_iff {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ) (y : J → ℤ) :
    pivotFreeAdmissible A B v y ↔ ∃ x : I → ℤ, A *ᵥ x + B *ᵥ y = v := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (eq_sub_iff_add_eq).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (eq_sub_iff_add_eq).mpr hx⟩

noncomputable def pivotIntegerFiberEquiv {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ) :
    {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} ≃
      {y : J → ℤ // pivotFreeAdmissible A B v y} where
  toFun p := ⟨p.val.2, (pivotFreeAdmissible_iff A B v p.val.2).mpr ⟨p.val.1, p.property⟩⟩
  invFun y := ⟨⟨(pivotFreeAdmissible_iff A B v y.val).mp y.property |>.choose, y.val⟩,
    (pivotFreeAdmissible_iff A B v y.val).mp y.property |>.choose_spec⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Matrix.mulVec_injective_of_det_ne_zero hA
      have h := (pivotFreeAdmissible_iff A B v p.val.2).mp
        ((pivotFreeAdmissible_iff A B v p.val.2).mpr ⟨p.val.1, p.property⟩) |>.choose_spec
      exact add_right_cancel (h.trans p.property.symm)
    · rfl
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def realAffineDualPolynomial {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ) : MvPolynomial K ℝ :=
  ∑ j, MvPolynomial.C (n j) *
    (MvPolynomial.X (selection j) - MvPolynomial.C (root (selection j)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealBooleanInterpolation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def realBooleanInterpolant {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α) : MvPolynomial K ℝ := ∏ r ∈ s, q r

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InverseSqrtMoment
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def unitInverseSqrt (x : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun x => (Real.sqrt x)⁻¹) x

variable {ι : Type*} [Fintype ι]

noncomputable def unitBoxInverseSqrt (x : ι → ℝ) : ℝ := ∏ i, unitInverseSqrt (x i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotJacobianBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def pivotSliceProfile (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (v : I → ℝ) (y : J → ℝ) : ℝ := f (y, A.symm (v - B y))

noncomputable def pivotGraphLipschitz (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) : ℝ≥0 :=
  max 1 (‖A.symm.toContinuousLinearMap‖₊ * ‖B‖₊)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedPartnerPower
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def weightedModelError {G I : Type*} [Fintype I]
    (c : I → ℂ) (ea : G → ℝ) (eb : I → G → ℝ) (h : G) : ℝ :=
  ea h + ∑ i, ‖c i‖ * eb i h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def spectrumTail {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (f : K → ℝ) : ℝ := ∑ k, if k ∈ S then 0 else f k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def reindexPolynomialMatrix {I J O : Type*} (e : I ≃ J)
    (M : Matrix O O (MvPolynomial I ℝ)) : Matrix O O (MvPolynomial J ℝ) :=
  M.map (MvPolynomial.rename e)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeJoin {α : Type*} (z : (α → ℝ) × ℝ) : Option α → ℝ :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

noncomputable def regularizationRadius (L ε : ℝ) : ℝ := min 1 (ε/(2*(1+L)))

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

noncomputable def polynomialBoxLip (n d : ℕ) (C : ℝ≥0) : ℝ≥0 :=
  n * ((d+1 : ℝ≥0)^n * (d*C))

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators ContDiff

noncomputable def polynomialMassC2Budget (N d : ℕ) (C : ℝ) : ℝ :=
  (1 + (N : ℝ) * d) ^ 2 * C

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Topology NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

noncomputable def selectedDerivative (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : κ → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (fderiv ℝ U x).comp J

noncomputable def selectedInverseField (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (i : ι) (j : κ) (x : κ → ℝ) : ℝ :=
  J ((selectedDerivative U J x).inverse (Pi.single i 1)) j

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

def unitBoxFace (j : Bool × ι) (x : ι → ℝ) : ℝ :=
  if j.1 then 1 - x j.2 else x j.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]

def principalSumBoxSplit (x : (Fin 4 ⊕ J) × Option ι → ℝ) :
    (Fin 4 × Option ι → ℝ) × (J × Option ι → ℝ) :=
  ((fun p => x (.inl p.1, p.2)), (fun p => x (.inr p.1, p.2)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuotientCoordinateRadius
namespace OAI

section

namespace Erdos3

noncomputable def quotientCoordinateRadius (δ K : ℝ) (d : ℕ) : ℝ :=
  δ / (δ + 4 * K ^ 2 * (d + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TaggedZModOrderBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def taggedIntegerResidue {Tag : Type*} (J : Tag → Type*) (N : ℕ) :
    ((Sigma J) → ℤ) →+ (∀ h : Tag, J h → ZMod N) where
  toFun x h j := (x ⟨h, j⟩ : ZMod N)
  map_zero' := by ext h j; simp
  map_add' := by intro x y; ext h j; simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FiniteAffineClassAverage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
    [Fintype H] [Fintype K]

def scalarTupleHom {I R : Type*} [CommRing R] (c : R) : (I → R) →+ (I → R) where
  toFun x i := c * x i
  map_zero' := by ext i; simp
  map_add' := by intro x y; ext i; simp [mul_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L Tag V : Type*} [Fintype L]

noncomputable def taggedOutputCRTEquiv (J : Tag → Type*) (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (∀ h : Tag, J h → ZMod (∏ l, q l)) ≃+
      (∀ l : L, ∀ h : Tag, J h → ZMod (q l)) where
  toFun y l h j := ZMod.prodEquivPi q hq (y h j) l
  invFun y h j := (ZMod.prodEquivPi q hq).symm (fun l => y l h j)
  left_inv y := by
    funext h j
    exact (ZMod.prodEquivPi q hq).symm_apply_apply (y h j)
  right_inv y := by
    funext l h j
    exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun l => y l h j)) l
  map_add' x y := by
    funext l h j
    exact congrFun (map_add (ZMod.prodEquivPi q hq) (x h j) (y h j)) l

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

def smoothInputSplit {I J D X : Type*} (e : (I ⊕ J) ≃ D) (z : D → X) :
    (I → X) × (J → X) := (fun i => z (e (.inl i)), fun j => z (e (.inr j)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial
namespace OAI

section

namespace Erdos3

noncomputable def scalarCubeMinorTestPoint {I J : Type*} [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) : Fin N → ℝ := fun k =>
  match (e.symm k).2 with
  | none => 0
  | some i => if (e.symm k).1 = s i then 1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped BigOperators

def spatialCoordinateArrayEquiv (K X : Type*) : (K × X → ℤ) ≃ (X → K → ℤ) where
  toFun z x k := z (k, x)
  invFun z p := z p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

noncomputable def polynomialCommonScale (c : R) :
    MvPolynomial I R →ₐ[R] MvPolynomial I R :=
  aeval (fun i => C c * X i)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def positiveCellParameter {A X Ξ : Type*}
    (w : A → X → ℝ) (E : Set X) (xi : X → Ξ) (a : A) : Option Ξ := by
  classical
  exact if h : ∃ x, x ∉ E ∧ 0 < w a x then some (xi h.choose) else none

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FullAffineCoefficientBound
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

noncomputable def realAxisAffinePolynomial {σ : Type*} (h r : σ → ℝ) (i : σ) : MvPolynomial σ ℝ :=
  C (h i) + C (r i) * X i

noncomputable def realAxisAffinePullback {σ : Type*} (h r : σ → ℝ) :
    MvPolynomial σ ℝ →+* MvPolynomial σ ℝ :=
  eval₂Hom C (realAxisAffinePolynomial h r)

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

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

noncomputable def uniformDualVector (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) : ℂ :=
  (Fintype.card Ω : ℂ) * star (f (Pi.single x 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTProgressionVanishing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def residueBoxIntegerPoint {J : Type*} (N : J → ℕ)
    (u : (j : J) → ZMod (N j)) : J → ℤ := fun j => (u j).val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialForecastBoxError
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def tupleResidueReduction {A : Type*} {q N : ℕ} (hq : q ∣ N) :
    (A → ZMod N) →+ (A → ZMod q) where
  toFun x a := ZMod.castHom hq (ZMod q) (x a)
  map_zero' := by ext a; simp
  map_add' := by
    intro x y
    ext a
    exact map_add (ZMod.castHom hq (ZMod q)) (x a) (y a)

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

def scalarResidueGridPoint {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (k : Option I → ℤ) : Option I → ℤ := fun i => (r i).val + (m i : ℤ)*k i

noncomputable def scalarResidueGridOffset {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) : Option I → ℝ :=
  fun i => -((r i).val : ℝ) / m i

noncomputable def scalarResidueGridScale {I : Type*} (L : ℕ) (m : Option I → ℕ) : Option I → ℝ :=
  fun i => (L : ℝ) / m i

theorem scalarResidueGridScale_pos {I : Type*} {L : ℕ} (hL : 0 < L)
    (m : Option I → ℕ) (hm : ∀ i, 0 < m i) (i : Option I) : 0 < scalarResidueGridScale L m i := by
  unfold scalarResidueGridScale
  exact div_pos (by exact_mod_cast hL) (by exact_mod_cast hm i)

theorem scalarResidueGridPoint_residue {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (k : Option I → ℤ) (i : Option I) :
    (scalarResidueGridPoint m r k i : ZMod (m i)) = r i := by
  let : NeZero (m i) := ⟨(hm i).ne'⟩
  simp [scalarResidueGridPoint]

theorem scalarResidueGridPoint_injective {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) : Function.Injective (scalarResidueGridPoint m r) := by
  intro k l h
  funext i
  have hh := congrFun h i
  have hmi : (m i : ℤ) ≠ 0 := by exact_mod_cast (hm i).ne'
  exact mul_left_cancel₀ hmi (add_left_cancel hh)

theorem scalarResidueGridPoint_surjective {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (z : Option I → ℤ)
    (hz : ∀ i, (z i : ZMod (m i)) = r i) : ∃ k, scalarResidueGridPoint m r k = z := by
  have hi (i : Option I) : ∃ k : ℤ, z i = (r i).val + (m i : ℤ)*k := by
    let : NeZero (m i) := ⟨(hm i).ne'⟩
    have he : (((r i).val : ℤ) : ZMod (m i)) = (z i : ZMod (m i)) := by simpa using (hz i).symm
    obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ((r i).val : ℤ) (z i) (m i)).mp he
    exact ⟨k, by linarith⟩
  choose k hk using hi
  exact ⟨k, funext (fun i => (hk i).symm)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedScalarResidueCell
namespace OAI

section

namespace Erdos3

def residueCellIntegerPoint {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N) : Option I → ℤ :=
  scalarResidueGridPoint m res (fun i => (N : ℤ) * (k i).val + (t i).val - L)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaProductPeriodization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A : Type*} [Fintype A] {D : A → Type*}

noncomputable def sigmaProductKernel (H : ∀ a, (D a → ℝ) → ℝ)
    (x : (Σ a, D a) → ℝ) : ℝ :=
  ∏ a, H a (fun i => x ⟨a, i⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

def prescribedDeepBad {Ω : Type*} (b : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p a : ℕ) (x : Ω) : Prop := b p < a ∧ bad p a x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RegularizedSigmaDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

def regularizedImageMap {Ω I : Type*} (δ : ℝ≥0) (U : Ω → I → ℝ)
    (p : Ω × (I → ℝ)) : I → ℝ := U p.1 + (δ : ℝ) • p.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPrincipalInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

noncomputable def principalSliceSlope (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) : ℝ :=
  c b * width (b, i) * ∏ j ∈ Finset.univ.erase i,
    (lower (b, j) + width (b, j) * x (b, j))

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

noncomputable def slicedPrincipalComparisonBudget (N m : ℕ) (C A r κ : ℝ) : ℝ :=
  1 + 2 * κ⁻¹ * (2 * (N : ℝ) ^ 2 * A / r) +
    N * ((2 * κ⁻¹) ^ 2 * (N * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def slicedPrincipalBoundaryRadius (N : ℕ) (η : ℝ) : ℝ :=
  min (1 / 4) (η / (16 * ((N : ℝ) + 1)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SplitFreeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def splitFreeCoordinates (I J N : Type*) [Fintype I] [Fintype J] [Fintype N] :
    ((J ⊕ N → ℝ) × (I → ℝ)) ≃ᵐ (((J → ℝ) × (I → ℝ)) × (N → ℝ)) :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).prodCongr
    (MeasurableEquiv.refl (I → ℝ))).trans
    (MeasurableEquiv.prodAssoc.trans
      (((MeasurableEquiv.refl (J → ℝ)).prodCongr MeasurableEquiv.prodComm).trans
        MeasurableEquiv.prodAssoc.symm))

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

variable {ι : Type*} [DecidableEq ι]

def restrictedDegreeSupports (J : Finset ι) (b : ℕ) : Finset (Finset ι) :=
  J.powerset.filter (fun S => S.card ≤ b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.TupleResidueConditioning
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def tupleColumnMatrix {I J : Type*} {Ω : J → Type*}
    (c : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) : Matrix I J ℤ :=
  Matrix.of (fun i j => c j (x j) i)

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

def scalarTupleColumn {I : Type*} (c : ℤ) (x : Option I → ℤ) : (Unit ⊕ I) → ℤ :=
  Sum.elim (fun _ => c + x none) (fun i => x (some i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CountingKernelOuter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveCountingKernel (b u v : ℝ) : ℝ := 1 - b + b * u * v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveKernelGram {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (b : ℝ) (f : I → X → ℝ) : ℝ := 𝔼 x, 𝔼 y, ∏ i, positiveCountingKernel b (f i x) (f i y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OneDimensionalBox
namespace OAI

section

namespace Erdos3

def scalarPiOneEquiv (A : Type*) [AddCommGroup A] : A ≃+ (Fin 1 → A) where
  toFun a _ := a
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by
    funext i
    exact congrArg f (Subsingleton.elim _ _)
  map_add' _ _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftTestingGowers
namespace OAI

section

namespace Erdos3

def shiftDetectionLoss (s C : ℕ) (p : ℝ) : ℝ :=
  6 * p + (2 ^ (s + 1) : ℕ) * (6 * p + C) ^ C

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

noncomputable def pivotCellForm {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (z : Fin l → Fin q → R) (x d : R) (beta : Fin l → Fin q) : R :=
  x + slope * d + ∑ a, (slope - v a) * z a (beta a)

noncomputable def pivotGridFactor {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (x d : R) : ℝ :=
  ∏ beta : Fin l → Fin q, f (pivotCellForm v slope z x d beta)

noncomputable def pivotRootFactor {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (w : R) : ℝ :=
  ∏ beta : Fin l → Fin q, f (w + ∑ a, (slope - v a) * z a (beta a))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PivotNativeIteration
namespace OAI

section

namespace Erdos3

noncomputable def pivotIterationBound (q r m : ℕ) (p B : ℝ) : ℝ :=
  Real.exp ((r : ℝ) * p * m / q) * B ^ ((r + 2) * m)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ConfigurationCharacters
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def twoSlopeAddHom {R : Type*} [CommRing R] (a b : R) : (R × R) →+ (R × R) where
  toFun z := (z.1 + a * z.2, z.1 + b * z.2)
  map_zero' := by simp
  map_add' x y := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedNarrowSpatialLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def splitPhysicalSpatialInputScale (G N : Type*)
    (H T : ℝ) (Q : N → ℝ) : Option (G ⊕ N) → ℝ
  | none => H
  | some (.inl _) => T
  | some (.inr j) => Q j

theorem splitPhysicalSpatialInputScale_pos (G N : Type*)
    {H T : ℝ} {Q : N → ℝ} (hH : 0 < H) (hT : 0 < T) (hQ : ∀ j, 0 < Q j) :
    ∀ k, 0 < splitPhysicalSpatialInputScale G N H T Q k := by
  rintro (_ | (g | j))
  · exact hH
  · exact hT
  · exact hQ j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidualRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

def recoveredIntegerLift {d m : ℕ} (M : Fin m → Fin d → ℤ) (c : Fin m → ℤ)
    (k : Fin d → ℤ) : Fin m → ℤ := fun i => c i + ∑ j, M i j * k j

noncomputable def realIntegerMatrix {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (x : Fin d → ℝ) : Fin m → ℝ := fun i => ∑ j, (M i j : ℝ) * x j

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

def finIntegerIntervalEquiv (L : ℕ) :
    Fin L ≃ ↥(Finset.Ico (0 : ℤ) (L : ℤ)) where
  toFun t := ⟨t.val, Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast t.isLt⟩⟩
  invFun z := ⟨z.val.toNat, by have hz := Finset.mem_Ico.mp z.property; omega⟩
  left_inv t := by apply Fin.ext; simp
  right_inv z := by
    apply Subtype.ext
    change (z.val.toNat : ℤ) = z.val
    exact Int.toNat_of_nonneg (Finset.mem_Ico.mp z.property).1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def unconditionedResidueSiteBound {K : Type*} [Fintype K] (P : K → ℕ) : ℝ :=
  ∑ k, (P k : ℝ)

noncomputable def unconditionedCollisionWidth {K : Type*} [Fintype K] [DecidableEq K]
    (P : K → ℕ) [∀ k, NeZero (P k)] (σ : ℝ) : ℝ :=
  32 * (Fintype.card (∀ k, ZMod (P k)) : ℝ) ^ 2 / σ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeMinorGoodMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def reindexedAffineSource {I : Type*} {N : ℕ} (e : I ≃ Fin N)
    (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) (a : I → ℝ) : I → ℝ :=
  (b + L (a ∘ e.symm)) ∘ e

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

def taggedPolynomialOutputCurry {s : ℕ} (J : Fin s → Type*) (N : ℕ) :
    (Sigma J → ZMod N) ≃+ (∀ j, J j → ZMod N) :=
  { Equiv.piCurry (fun _ (_ : J _) => ZMod N) with map_add' := fun _ _ => rfl }

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem retainedPrimePowerModulus_dvd {L : Type*} [Fintype L]
    (p A : L → ℕ) (retained : Finset L) :
    (∏ l : retained, p l.val ^ A l.val) ∣ ∏ l, p l ^ A l := by
  rw [Finset.prod_coe_sort (f := fun l => p l ^ A l)]
  exact Finset.prod_dvd_prod_of_subset retained Finset.univ (fun l => p l ^ A l)
    (Finset.subset_univ _)

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

noncomputable def rationalCharacterIndividualModulus (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) : ℕ := Nat.lcm qW (orderOf χ)

theorem rationalCharacterIndividualModulus_dvd (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) (hW : qW ∣ N) :
    rationalCharacterIndividualModulus qW χ ∣ N :=
  Nat.lcm_dvd hW (zmod_character_order_dvd χ)

theorem rationalCharacterIndividualModulus_test_dvd (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) :
    qW ∣ rationalCharacterIndividualModulus qW χ := Nat.dvd_lcm_left _ _

theorem rationalCharacterIndividualModulus_order_dvd (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) :
    orderOf χ ∣ rationalCharacterIndividualModulus qW χ := Nat.dvd_lcm_right _ _

variable [NeZero N] (qW : ℕ) [NeZero qW] (χ : AddChar (O → ZMod N) ℂ)

theorem rationalCharacterIndividualModulus_pos :
    0 < rationalCharacterIndividualModulus qW χ :=
  Nat.lcm_pos (NeZero.pos qW) (zmod_character_order_pos χ)

noncomputable instance rationalCharacterIndividualModulus_neZero :
    NeZero (rationalCharacterIndividualModulus qW χ) :=
  ⟨(rationalCharacterIndividualModulus_pos qW χ).ne'⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedPeriodicGridQuadrature
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal
variable {J : Type*} [Fintype J]

noncomputable def translatedGridMass (g : (J → ℝ) → ℝ) (center T : J → ℝ) : ℝ :=
  (∑' k : J → ℤ, g (fun j => ((k j : ℝ) - center j) / T j)) / (∏ j, T j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentCombinatorics
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I R : Type*} [DecidableEq I] [CommSemiring R]

noncomputable def squarefreePermanent :
    (n : ℕ) → Finset I → (Fin n → I → R) → R
  | 0, S, _ => if S = ∅ then 1 else 0
  | n + 1, S, u => ∑ j ∈ S, u 0 j * squarefreePermanent n (S.erase j) (Fin.tail u)

noncomputable def squarefreeEmbeddingHeadEquiv (n : ℕ) (S : Finset I) :
    (Fin (n + 1) ↪ S) ≃ Σ j : S, Fin n ↪ (S.erase j.val) where
  toFun f := ⟨f 0, ⟨fun i => ⟨(f i.succ).val,
    Finset.mem_erase.mpr ⟨fun h => Fin.succ_ne_zero i (f.injective (Subtype.ext h)),
      (f i.succ).property⟩⟩,
    fun i j h => Fin.succ_injective _ (f.injective (Subtype.ext (congrArg (fun z : S.erase (f 0).val => z.val) h)))⟩⟩
  invFun p := ⟨Fin.cons p.1 (fun i => ⟨(p.2 i).val, (Finset.mem_erase.mp (p.2 i).property).2⟩), by
    intro i j h
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        exact False.elim ((Finset.mem_erase.mp (p.2 j).property).1 (congrArg Subtype.val h).symm)
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        exact False.elim ((Finset.mem_erase.mp (p.2 i).property).1 (congrArg Subtype.val h))
      | succ j => exact congrArg Fin.succ (p.2.injective (Subtype.ext (congrArg (fun z : S => z.val) h)))⟩
  left_inv f := by
    ext i
    cases i using Fin.cases <;> rfl
  right_inv p := by
    cases p with
    | mk j f =>
      congr 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SmoothCoefficientRankBadProduct
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

def scalarCoefficientTupleEquiv {T D V : Type*} {B : T → Type*} [AddCommGroup V] :
    ((Σ t, B t × D) → V) ≃+ (∀ t, B t → D → V) where
  toFun x t b d := x ⟨t, (b,d)⟩
  invFun c j := c j.1 j.2.1 j.2.2
  left_inv x := by
    funext j
    rcases j with ⟨t,b,d⟩
    rfl
  right_inv c := rfl
  map_add' x y := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftDifferenceCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def shiftCorrelation (Q : Finset G) (f : G → ℂ) (h : G) : ℂ :=
  ∑ x ∈ Q, f x * star (f (x + h))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeylStepScales
namespace OAI

section

namespace Erdos3

def weylNextBudget (k B K : ℕ) : ℕ :=
  2 * K + 32 * B ^ 2 + 128 * B ^ 2 * K +
    65536 * 2 ^ k * B ^ 4 * K ^ 3 +
    128 * (k + 1) * B ^ 2 * K ^ 2 + 98304 * 2 ^ k * B ^ 4 * K ^ 3

def weylBudget : ℕ → ℕ → ℕ
  | 0, B => B
  | j + 1, B => weylNextBudget (j + 1) B (weylBudget j (8 * B ^ 2))

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped BigOperators

noncomputable def weylBudgetPolynomial : ℕ → Polynomial ℕ
  | 0 => X
  | j + 1 =>
    let R := (weylBudgetPolynomial j).comp (C 8 * X ^ 2)
    C 2 * R + C 32 * X ^ 2 + C 128 * X ^ 2 * R +
      C (65536 * 2 ^ (j + 1)) * X ^ 4 * R ^ 3 +
      C (128 * (j + 2)) * X ^ 2 * R ^ 2 + C (98304 * 2 ^ (j + 1)) * X ^ 4 * R ^ 3

end Erdos3

end

section

namespace Erdos3

def weylShiftDenom (B K : ℕ) : ℕ := 128 * B ^ 2 * K

noncomputable def weylShiftDensity (B K : ℕ) : ℝ := 1 / (32 * (B : ℝ) ^ 2 * K)

noncomputable def weylShiftError (k N K : ℕ) : ℝ := (2 : ℝ) ^ k * K / (N : ℝ) ^ k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open Polynomial

noncomputable def polynomialShiftDifference (P : Polynomial ℝ) (h : ℝ) : Polynomial ℝ :=
  P - P.comp (X + C h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
namespace OAI

section

namespace Erdos3

noncomputable def schmidtDegreeConstant (C e : ℕ) : ℝ :=
  (10 + 8 * Real.exp (4 * Real.pi + 1)) *
    (1 + 2 * Real.exp Real.pi * (C : ℝ) * (8 : ℝ) ^ e)

end Erdos3

end

section

namespace Erdos3

def schmidtRecurrenceExponent (e : ℕ) : ℕ := 15 * (e + 1) + 23

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtRecurrenceBase (C e : ℕ) : ℝ :=
  2 + 121 * Real.exp 10 + schmidtDegreeConstant C e + schmidtRecurrenceExponent e

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
namespace OAI

universe u

section

namespace Erdos3

open scoped TensorProduct NNReal

variable {X : Type*} {J : Fin 0 → Type*}

def zeroLayerPhysicalPoint (x : X → ℤ) : X ⊕ Sigma J → ℤ :=
  Sum.elim x (fun a => Fin.elim0 a.1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RecoveredLatticeMatrixInvariance
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {m d a : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

def recoveredLayeredIntegerLift (e : Fin d ≃ Sigma J)
    (M : Fin d → Fin a → ℤ) (β : Sigma J → ℤ) (k : Fin a → ℤ) : Sigma J → ℤ :=
  fun i => recoveredIntegerLift M (fun i => β (e i)) k (e.symm i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedPatchEndpoint
namespace OAI

section

namespace Erdos3

noncomputable def spatialPatchExtractionCost (L : ℝ) : ℝ := 20 * (L + 1) ^ 2

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def spatialPatchExtractionMesh (L : ℝ) : ℕ :=
  ⌈Real.exp (5 * L)⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RecoveredKernelScalarBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

def recoveredKernelScalarBudget (B : ℝ) : ℝ := 8 * (B + 1) ^ 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UnconditionedScalarScaleNiltestBase
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct

noncomputable def unconditionedScalarPrimeRatio (n : ℕ) : ℕ :=
  ⌈Real.exp ((n : ℝ) + 2)⌉₊ + 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeScalarPassageDiscount
namespace OAI

section

namespace Erdos3

noncomputable def relativeScalarPassageSlack (τ : ℝ) : ℝ := τ / (2 * (1 - τ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubsetAlternatingInversion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

noncomputable def subsetAlternatingTransform (F : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * F (S \ U)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductKernelPairing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def productMatrixApply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (Y i)] (A : ∀ i, X i → Y i → ℝ)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) : ℝ := ∑ y, (∏ i, A i (x i) (y i)) * f y

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def productPairCoordinates {ι : Type*} (X Y : ι → Type*) :
    (∀ i, X i × Y i) ≃ (∀ i, X i) × (∀ i, Y i) where
  toFun z := (fun i => (z i).1, fun i => (z i).2)
  invFun z := fun i => (z.1 i, z.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVATensorChoices
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

noncomputable def productANOVATensorChoices (k q : ℕ) : Finset ((Fin q × Fin k) → I) := by
  classical
  exact Finset.univ.filter (fun a => (∀ j, StrictMono (fun l => a (j, l))) ∧
    ∀ i, (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card ≠ 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

noncomputable def scalarTransferBaseAccuracy (targetLog : ℝ) : ℝ := Real.exp (-(targetLog + 10))

noncomputable def scalarTransferMarginalAccuracy (targetLog capLog : ℝ) : ℝ :=
  Real.exp (-(targetLog + capLog + 10))

noncomputable def scalarTransferTail (targetLog : ℝ) : ℝ := 2 * (targetLog + 10)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

theorem replacementWindowFactor_le_exp (m : ℕ) {K P : ℝ}
    (hK0 : 0 ≤ K) (hK : K ≤ Real.exp P) :
    (3 * K) ^ m ≤ Real.exp ((m : ℝ) * (P + 3)) := by
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hbase : 3 * K ≤ Real.exp (P + 3) := by
    calc
      _ ≤ Real.exp 3 * Real.exp P := mul_le_mul h3 hK hK0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ 3 * K) hbase m

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement
namespace OAI

section

namespace Erdos3

theorem replacement_binary_power_le_exp (d : ℕ) : (2 : ℝ) ^ d ≤ Real.exp (2 * d) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  apply (pow_le_pow_left₀ (by norm_num) h2 d).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem replacement_ternary_power_le_exp (d : ℕ) : 2 * (3 : ℝ) ^ d ≤ Real.exp (3 * d + 2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ Real.exp 2 * (Real.exp 3) ^ d := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

noncomputable def scalarTransferCapLog (b : ℕ) (Z : ℝ) : ℝ := (b : ℝ) * (Z + 2) + 1

noncomputable def scalarTransferAccuracyLog (b : ℕ) (p Z : ℝ) : ℝ :=
  3 * p + scalarTransferCapLog b Z + 10

noncomputable def scalarTransferCellLog (common : ℝ) (b : ℕ) (p Z U : ℝ) : ℝ :=
  65536 * (common + 3) ^ 4 + Z * b + scalarTransferAccuracyLog b p Z + U + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarMeshCoefficientBudget
namespace OAI

section

namespace Erdos3

noncomputable def scalarMeshLog (gridLog inputLog accuracyLog : ℝ) : ℝ :=
  gridLog + 3 * inputLog + accuracyLog + 50

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SecondaryMeshGeometry
namespace OAI

section

namespace Erdos3

noncomputable def secondaryMovementBudget (movement sourceRatio parameterRatio : ℝ) : ℝ :=
  movement + sourceRatio + parameterRatio

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalZeroLayerBudgetedInitialization
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def unconditionedCommonSide {n : ℕ} (P : Fin n → ℕ) : ℕ := 1 + ∑ i, P i

@[simp] theorem unconditionedCommonSide_cast {n : ℕ} (P : Fin n → ℕ) :
    (unconditionedCommonSide P : ℝ) = 1 + unconditionedResidueSiteBound P := by
  simp [unconditionedCommonSide, unconditionedResidueSiteBound]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def unconditionedCommonSideScalarRatio (n : ℕ) : ℕ :=
  1 + n * unconditionedScalarPrimeRatio n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalRelativeEndpointBounds
namespace OAI

section

namespace Erdos3
open scoped BigOperators

noncomputable def preparedRelativeLateHeight
    (Bstruct p : ℝ) (preparationPower requiredPower : ℕ) : ℝ :=
  max Bstruct (max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedPatchCutoffChoice
namespace OAI

section

namespace Erdos3

noncomputable def retainedPatchCutoff (ε : ℝ) : ℕ := ⌈16 / ε⌉₊

noncomputable def retainedPatchRelativeError (ε : ℝ) : ℝ := ε / 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Reciprocal
namespace OAI

section

open scoped BigOperators

namespace Erdos3

@[simp] theorem reciprocalTerm_zero (A : Set ℕ) : reciprocalTerm A 0 = 0 := by
  classical
  simp [reciprocalTerm]

end Erdos3

end

end OAI
end


