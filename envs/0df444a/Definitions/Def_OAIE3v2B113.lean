-- Prove2me | Definitions.Def_OAIE3v2B113
-- name    : OAIE3v2B113
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:40:16.85716+00:00
-- url     : https://prove2.me/theorems/ab9afdbb-84ca-467a-b737-1c0f70662578
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 115 of 311
-- statement:
--   Definitions bundle 115 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B088`, `OAIE3v2B090`, `OAIE3v2B092`, `OAIE3v2B093`, `OAIE3v2B096`, `OAIE3v2B097`, `OAIE3v2B099`, `OAIE3v2B100` of this split.
--
--   Modules: `Dynamics/ConstructLayerResetScales.lean`, `Estimates/ActiveProfileNoise.lean`, `Estimates/AllocatedDetectedCanonicalPeriod.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedSlicedEndpointIdentity.lean`, `Estimates/FiniteProductCellMean.lean`, `Estimates/JointBooleanGoodWeight.lean`, `Estimates/MixedCoveredRowReindex.lean`, `Estimates/RowRestrictedDeckSiteMask.lean`, `Estimates/SmoothWindowChange.lean`, `Estimates/UnconditionedTrimmedSliceFamily.lean`, `Geometry/AnisotropicSpatialCapBudget.lean`, `Geometry/MixedCoveredChart.lean`, `Lattices/AffineBlockScale.lean`, `Lattices/AffineModeratePlateauModel.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Lattices/SmoothBadPrimeProduct.lean`, `Lattices/SmoothIntegerImage.lean`, `Linear/FiniteCenteredKernel.lean`, `Linear/KernelSupportContraction.lean`, `Linear/ModularVectorCoefficientRank.lean`, `Linear/ProductANOVATensorChoices.lean`, `Linear/SmoothCoefficientRankBadProduct.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Probability/AnisotropicSpatialLaw.lean`, `Probability/ScalarCubeBoundaryMass.lean`, `Probability/ScaledCubeProductMeasure.lean`, `Probability/SlicedRemainderDensityFamily.lean`, `Sampling/ActualForecastModelPrecision.lean`, `Sampling/AllocatedProbabilityGrid.lean`, `Sampling/FixedPathSlicedGridMeshBudget.lean`, `Sampling/ForecastPreparedScaleBudget.lean`, `Sampling/PreparedConcreteComparisonGridBudget.lean`, `Sampling/PreparedSlicedForecastComparisonLogs.lean`, `Sampling/SmoothSplitSampling.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B093
import Definitions.Def_OAIE3v2B096
import Definitions.Def_OAIE3v2B097
import Definitions.Def_OAIE3v2B099
import Definitions.Def_OAIE3v2B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

instance scalarCubeMeasure_probability (α : Type*) [Fintype α] [DecidableEq α] :
    IsProbabilityMeasure (scalarCubeMeasure α) := by
  constructor
  simp only [scalarCubeMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (scalarCubeDomain_volume_pos α).ne' (scalarCubeDomain_volume_lt_top α).ne

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

instance scalarCubeProductMeasure_probability (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] : IsProbabilityMeasure (scalarCubeProductMeasure ι α) := by
  unfold scalarCubeProductMeasure
  infer_instance

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

instance blockCubeMeasure_probability (B F α : Type*) [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] : IsProbabilityMeasure (blockCubeMeasure B F α) := by
  constructor
  rw [blockCubeMeasure, Measure.map_apply (blockCubeFlatten B F α).continuous.measurable
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

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

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

instance jointBooleanSource_probability (h : D → ℕ) :
    IsProbabilityMeasure (jointBooleanSource (B := B) (α := α) h) := by
  unfold jointBooleanSource
  infer_instance

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductSamples_sum {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    (∑' z : I → ℤ, smoothProductProfile I (fun i => (z i : ℝ) / S i)) =
      ∏ i, smoothSampleSum (S i) := by
  classical
  have h := rectangularWeightSum_eq_tsum (smoothProductProfile I) (fun _ => 0) S hS
    (smoothProductProfile_zero_outside I)
  change rectangularWeightSum (smoothProductProfile I) (fun _ => 0) S 1 =
    ∑' z : I → ℤ, smoothProductProfile I (fun i => ((z i : ℝ) - 0) / S i) at h
  simp only [sub_zero] at h
  rw [← h]
  simp only [rectangularWeightSum, rectangularWeightIndices, rectangularWeight,
    rectangularLatticePoint, sub_zero, smoothProductProfile]
  rw [← Finset.prod_univ_sum (fun i => sampledWeightIndices 0 (S i) 1)
    (fun i k => smoothProbabilityProfile ((k : ℝ) / S i))]
  apply Finset.prod_congr rfl
  intro i _
  have hi := sampledWeightSum_eq_tsum smoothProbabilityProfile (a := 0) (hS i)
    smoothProbabilityProfile_zero_outside
  simpa only [sampledWeightSum, sampledWeight, sub_zero, smoothSampleSum] using hi

theorem smoothProductSamples_sum_pos {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    0 < ∑' z : I → ℤ, smoothProductProfile I (fun i => (z i : ℝ) / S i) := by
  rw [smoothProductSamples_sum S hS]
  exact Finset.prod_pos (fun i _ => smoothSampleSum_pos (hS i))

noncomputable def smoothProductPMF {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) : PMF (I → ℤ) :=
  realWeightPMF (fun z => smoothProductProfile I (fun i => (z i : ℝ) / S i))
    (fun _ => (smoothProductProfile_range I _).1)
    (smoothProductSamples_summable S hS) (smoothProductSamples_sum_pos S hS)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSplit_weight_sum {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    scaledInputWeightSum (smoothSplitProfile J I) S T =
      (∏ i, smoothSampleSum (S i)) * (∏ j, smoothSampleSum (T j)) := by
  have hST : ∀ k, 0 < Sum.elim T S k := by
    intro k
    cases k with
    | inl j => exact hT j
    | inr i => exact hS i
  unfold scaledInputWeightSum
  rw [← splitInputProfile_sample_sum, splitInputProfile_smooth,
    smoothProductSamples_sum _ hST]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mul_comm]

theorem smoothSplit_mass_pos {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    0 < scaledInputMass (smoothSplitProfile J I) S T := by
  rw [scaledInputMass, smoothSplit_weight_sum S T hS hT]
  exact div_pos
    (mul_pos (Finset.prod_pos (fun i _ => smoothSampleSum_pos (hS i)))
      (Finset.prod_pos (fun j _ => smoothSampleSum_pos (hT j))))
    (mul_pos (Finset.prod_pos (fun i _ => hS i)) (Finset.prod_pos (fun j _ => hT j)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerImage
namespace OAI

section

namespace Erdos3

open scoped Matrix

noncomputable def smoothMatrixImagePMF {O J : Type*} [Fintype J]
    (A : Matrix O J ℤ) (S : J → ℝ) (hS : ∀ j, 0 < S j) : PMF (O → ℤ) :=
  (smoothProductPMF S hS).map (fun z => A *ᵥ z)

noncomputable def smoothIntegerImagePMF {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) : PMF (I → ℤ) :=
  integerImagePMF A B (smoothSplitProfile J I)
    (fun p => (smoothSplitProfile_range J I p).1) S T hS hT
    (smoothSplitProfile_zero_outside J I) (smoothSplit_mass_pos S T hS hT)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def primePowerHomogeneousRankProbability
    {V J : Type*} [Fintype V] [Fintype J]
    (p A B n : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : J → MvPolynomial V (ZMod (p ^ A))) (row : J → ZMod (p ^ B)) : ℝ :=
  𝔼 u : Fin n → V → ZMod (p ^ B),
    if polynomialLinearRow (polynomialIterDifference n
      (polynomialCharacterRow row (fun i =>
        map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
          (homogeneousComponent (n + 1) (F i)))) u) = 0 then 1 else 0

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def integerPolynomialRankProbability
    {V J : Type*} [Fintype V] [Fintype J]
    (p B n : ℕ) [NeZero p]
    (F : J → MvPolynomial V ℤ) (row : J → ZMod (p ^ B)) : ℝ :=
  𝔼 u : Fin n → V → ZMod (p ^ B),
    if polynomialLinearRow (polynomialIterDifference n
      (polynomialCharacterRow row (fun i =>
        map (Int.castRingHom (ZMod (p ^ B)))
          (homogeneousComponent (n + 1) (F i)))) u) = 0 then 1 else 0

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3

noncomputable def bchLatticeSeparationRadius (s d H l : ℕ) : ℝ :=
  1 / ((l : ℝ) + 1) / (bchLogMetricConstant s d H 1 : ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothWindowChange
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def smoothSourceFiniteWeights {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S) :
    FiniteProbabilityWeights (rectangularWeightIndices a S 1) where
  weight z := (shiftedSmoothProductPMF a S hS hZ z.val).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
      (fun z => (shiftedSmoothProductPMF a S hS hZ z).toReal)]
    have h : (∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal) =
        ∑ z ∈ rectangularWeightIndices a S 1, (shiftedSmoothProductPMF a S hS hZ z).toReal :=
      (hasSum_sum_of_ne_finset_zero (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)).tsum_eq
    rw [← h]
    exact shiftedSmoothProductPMF_toReal_sum a S hS hZ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

noncomputable def scalarCubeGridSet (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : Finset (Option I → ℤ) :=
  (rectangularWeightIndices a S 1).filter (fun k =>
    rectangularLatticePoint a S k ∈ halfOpenScalarCubeDomain I)

theorem mem_scalarCubeGridSet {I : Type*} [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (k : Option I → ℤ) :
    k ∈ scalarCubeGridSet I a S ↔ rectangularLatticePoint a S k ∈ halfOpenScalarCubeDomain I := by
  rw [scalarCubeGridSet, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hk
    refine ⟨?_, hk⟩
    by_contra hn
    have h := rectangularWeight_zero_off_indices (scalarCubeIndicator I) a S hS
      (scalarCubeIndicator_zero_outside I) k hn
    change scalarCubeIndicator I (rectangularLatticePoint a S k) = 0 at h
    simp only [scalarCubeIndicator, hk, ite_true] at h
    exact one_ne_zero h

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

noncomputable def scalarCubeResidueGridEquiv (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i) :
    ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) ≃
      ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) := by
  let F : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) →
      ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) := fun k => by
    have hk := (mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm) k.val).mp k.property
    rw [scalarResidueGrid_normalized hL m r hm] at hk
    have hc := (integerScalarCube_iff_normalized hL _).mpr hk
    let z : IntegerScalarCubeBox I L := fun i => ⟨scalarResidueGridPoint m r k.val i,
      Finset.mem_Ico.mpr ⟨(integerScalarCube_coordinates hc i).1.le, (integerScalarCube_coordinates hc i).2⟩⟩
    exact ⟨z, Finset.mem_inter.mpr ⟨(mem_integerScalarCubeSet L z).mpr hc,
      (mem_scalarCubeResidueSet L m r z).mpr (scalarResidueGridPoint_residue m r hm k.val)⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro k l h
    apply Subtype.ext
    apply scalarResidueGridPoint_injective m r hm
    exact funext (fun i => congrArg (fun z : ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) =>
      (z.val i : ℤ)) h)
  · intro z
    obtain ⟨k,hk⟩ := scalarResidueGridPoint_surjective m r hm (fun i => (z.val i : ℤ))
      ((mem_scalarCubeResidueSet L m r z.val).mp (Finset.mem_inter.mp z.property).2)
    have hc := (mem_integerScalarCubeSet L z.val).mp (Finset.mem_inter.mp z.property).1
    have hmem : k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m) := by
      rw [mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm), scalarResidueGrid_normalized hL m r hm, hk]
      exact (integerScalarCube_iff_normalized hL _).mp hc
    refine ⟨⟨k,hmem⟩, ?_⟩
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun hk i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBlockScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def affineWeightedCubeIntegerBlock {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I) (u : Fin (n + 1) → Option I → ℤ)
    (v : Fin (n + 1) → Option I → ℕ) (J : Finset (Finset I))
    (x : ∀ j, IntegerScalarCubeBox I (s j).length) : J → ℤ :=
  fun S => integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u j) (v j) (fun i => (x j i : ℤ))) S

noncomputable def affineWeightedCubeIntegerSum {B : Type*} [Fintype B] {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (J : Finset (Finset I)) (shift : J → ℤ)
    (x : ∀ b j, IntegerScalarCubeBox I (s b j).length) : J → ℤ :=
  shift + ∑ b, affineWeightedCubeIntegerBlock (s b) (u b) (v b) J (x b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteCenteredKernel
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def centeredKernelMatrix (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y) (x : X) (y : Y) : ℝ := (K x).weight y - ν.weight y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

theorem principalAxisRestrict_join_left (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    principalAxisRestrict P (principalAxisJoin P u v) = u := by
  funext j
  rcases j with ⟨⟨d, hd⟩, bv⟩
  simp only [principalAxisRestrict, principalAxisJoin, hd, ↓reduceDIte]

theorem principalAxisRestrict_join_right (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    principalAxisRestrict (fun d => ¬P d) (principalAxisJoin P u v) = v := by
  funext j
  rcases j with ⟨⟨d, hd⟩, bv⟩
  simp only [principalAxisRestrict, principalAxisJoin, hd, ↓reduceDIte]

theorem principalAxisJoin_restrict (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ} (y : PrincipalIntegerTuples B h α L) :
    principalAxisJoin P (principalAxisRestrict P y) (principalAxisRestrict (fun d => ¬P d) y) = y := by
  funext j
  simp only [principalAxisJoin, principalAxisRestrict]
  split <;> rfl

def principalAxisPartitionEquiv (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) :
    PrincipalIntegerTuples B h α L ≃
      PrincipalAxisTuples (α := α) P L × PrincipalAxisTuples (α := α) (fun d => ¬P d) L where
  toFun y := (principalAxisRestrict P y, principalAxisRestrict (fun d => ¬P d) y)
  invFun y := principalAxisJoin P y.1 y.2
  left_inv := principalAxisJoin_restrict P
  right_inv y := Prod.ext (principalAxisRestrict_join_left P y.1 y.2)
    (principalAxisRestrict_join_right P y.1 y.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

def partitionedProfileInput {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    PartitionedProfileNoiseIndex G Z α B h P ⊕
      PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) :=
  Sum.map Sum.inl id (partitionedPrincipalInput P extra k a)

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

noncomputable def partitionedProfileTerms (d : {d // ¬P d}) :
    Finset (SamplerCoefficientSlot G B h d.val) :=
  nonprincipalCoefficientSlots Subtype.val (canonicalPrincipalExponent h d.val)

noncomputable def partitionedProfileJet (ρ γ ε : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (o : Σ d, O d) : ℝ :=
  booleanCoefficient (fun s => MvPolynomial.eval
    (normalizedCubeTuple (partitionedProfileInput P extra) y x s)
    (monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B h o.1.val =>
      coefficientProfileCenter (principalCoefficientSlots h o.1.val) (γ o.1.val) e +
        coefficientProfileWidth (principalCoefficientSlots h o.1.val) (constantCoefficientSlot _ _)
          (ρ o.1.val) (γ o.1.val) (t * ε o.1.val) e * y (.inr ⟨o.1.val, e⟩)))) (sets o.1 o.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

noncomputable def unitProfileTailSize (d : D) : ℝ :=
  tailProfileSize 1 1 (Fintype.card (SamplerCoefficientSlot G B h d))

noncomputable def partitionedAllocatedProfileJet (R : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    (Σ d, O d) → ℝ :=
  partitionedProfileJet h P extra sets (fun d => R d / 4)
    (fun d => principalProfileSize (R d) (Fintype.card (B d)))
    (fun d => tailProfileSize (R d) 1 (Fintype.card (SamplerCoefficientSlot G B h d))) t y x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedCoveredJetCoordinatesEquiv (d : ℕ) :
    MixedCoveredJetSource I O E n d ≃ CoveredJetChartSource U O E n d where
  toFun := mixedCoveredJetCoordinates U o d
  invFun z := (fun j => (mixedArrayRegroup (I j) (Fin (n j)) (O j)).symm
    (fun t => (orthonormalMixedChart (o j)).symm (z j t).1), fun j t => (z j t).2)
  left_inv z := by
    apply Prod.ext
    · funext j
      simp only [mixedCoveredJetCoordinates, MeasurableEquiv.symm_apply_apply]
    · rfl
  right_inv z := by
    funext j t
    simp only [mixedCoveredJetCoordinates, MeasurableEquiv.apply_symm_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredBooleanSiteValue
    (y : EuclideanJetLayers U jets) (s : Finset α) : EuclideanJetLayers U (fun _ => Unit) :=
  fun j _ => ∑ r, boundedBooleanReconstructionMatrix α (j.val + 1) s r • y j r

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def anisotropicSpatialOutputLaw {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (C : Matrix (Unit ⊕ I) N ℤ)
    (A R : ℝ) (Q : N → ℝ) (hA : 0 < A) (hR : 0 < R) (hQ : ∀ j, 0 < Q j) :
    PMF ((Unit ⊕ I) → ℤ) :=
  smoothMatrixImagePMF (Matrix.fromCols (rootDifferenceMatrix root D) C)
    (Sum.elim (anisotropicSpatialScale J A R) Q)
    (fun j => Sum.rec (anisotropicSpatialScale_pos J hA hR) hQ j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AnisotropicSpatialCapBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem anisotropicSpatialPivot_control {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    (selectedSpatialPivot root D s).det ≠ 0 ∧
      ‖(matrixSupCLM (normalizedIntegerPivot (selectedSpatialPivot root D s)
        (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L))).inverse‖ ≤
          physicalSpatialInverseBound I κ := by
  have h := physicalCube_pivot_control root D s hA hR hL hκ hr hD hminor
  simpa only [physicalCubeCoefficient_pivot, anisotropicSpatialScale_physicalPivot,
    physicalSpatialInverseBound] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoveredRowReindex
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem coveredJetArrayScale_pos : 0 < coveredJetArrayScale (O := O) U :=
  Finset.prod_pos (fun _ _ => pow_pos (inv_pos.mpr (ZLattice.covolume_pos _ volume)) _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

noncomputable def weightedAffineModerateIntegerBlock {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℤ) (v : Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : ℤ)
    (x : IntegerScalarCubeBox Empty c.length × (∀ j, IntegerScalarCubeBox I (s j).length)) : J → ℤ :=
  fun S => (offset + (x.1 none : ℤ)) * integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u j) (v j) (fun r => (x.2 j r : ℤ))) S

noncomputable def weightedAffineModerateIntegerJetSum {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length)) : J → ℤ :=
  shift + ∑ b, weightedAffineModerateIntegerBlock (c b) (s b) (u b) (v b) J (offset b) (x b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedJetAmbientPoint
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : JetAmbientIndex O J → ℝ :=
  fun a => normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
    (orthonormalMixedChart (o a.1) (mixedArrayRegroup _ _ _ (z a.1) a.2.1)) a.2.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedEndpointIdentity
namespace OAI

section

namespace Erdos3

open MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

variable {D G E : Type*} [Fintype D] [Fintype G] [Fintype E]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (axis : E → D)

local notation "Input" => (Σ e, B (axis e) × Fin (h (axis e)))
local notation "Output" => (Σ _e : E, Unit)

noncomputable def jointSlicedProfileValue
    (ρ γ ε : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ)
    (t : ℝ) (x : Input → ℝ) (o : Output) : ℝ :=
  MvPolynomial.eval (fun k => MvPolynomial.eval x (ξ o.1 k))
    (monomialArrayPolynomial Subtype.val (fun j : SamplerCoefficientSlot G B h (axis o.1) =>
      coefficientProfileCenter (principalCoefficientSlots h (axis o.1)) (γ (axis o.1)) j +
        coefficientProfileWidth (principalCoefficientSlots h (axis o.1)) (constantCoefficientSlot _ _)
          (ρ (axis o.1)) (γ (axis o.1)) (t * ε (axis o.1)) j * r o.1 j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

noncomputable def canonicalSlicedModulus (x : G → IntegerScalarCubeBox α L) : ℕ :=
  if hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x then
    residueRefinedPeriod (kernelPeriodCandidate (height + 1)
      (goodKernelUniformCandidate selection x hx height)) stride
  else 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

noncomputable def smoothCoefficientResidueWeights (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (M : ℕ) [NeZero M] :
    FiniteProbabilityWeights (ZMod M) :=
  ofPMF ((shiftedSmoothCoefficientPMF a S hS hZ).map (fun k : ℤ => (k : ZMod M)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def slicedFixedUniformSitePolynomial (m : ℕ) (p E : Polynomial ℕ) : Polynomial ℕ :=
  p + E + 1 + ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem preparedSamplerBlockCount_positive (m dim : ℕ) (j : Fin m) :
    0 < preparedSamplerBlockCount m dim j := by dsimp only [preparedSamplerBlockCount]; omega

theorem preparedSamplerBlockCount_spectrum (m dim : ℕ) (j : Fin m) :
    let rows := boundedBooleanJetRows (Fin dim) (j.val + 1)
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card)) ≤
        preparedSamplerBlockCount m dim j := by dsimp only [preparedSamplerBlockCount]; omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem preparedCommonBlockCount_ge (m : ℕ) (j : Fin m) (s : Fin (m + 1)) :
    preparedSamplerBlockCount m (s.val + 1) j ≤ preparedCommonBlockCount m j := by
  exact Finset.single_le_sum
    (f := fun r : Fin (m + 1) => preparedSamplerBlockCount m (r.val + 1) j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)

theorem preparedCommonBlockCount_positive (m : ℕ) (j : Fin m) :
    0 < preparedCommonBlockCount m j :=
  (preparedSamplerBlockCount_positive m 1 j).trans_le (preparedCommonBlockCount_ge m j 0)

theorem preparedCommonBlockCount_spectrum (m : ℕ) (j : Fin m) (s : Fin (m + 1)) :
    let rows := boundedBooleanJetRows (Fin (s.val + 1)) (j.val + 1)
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card)) ≤
        preparedCommonBlockCount m j :=
  (preparedSamplerBlockCount_spectrum m (s.val + 1) j).trans (preparedCommonBlockCount_ge m j s)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ConstructLayerResetScales
namespace OAI

section

namespace Erdos3

noncomputable def powerLayerResetScales {s r T p : ℕ} {K L σ : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hL : 0 ≤ L) (hT : 0 < T) (hσ : 0 < σ)
    (hpartition : ∀ h ≤ s, PolynomialCoordinatePartitionBound.{0} h K p)
    (hscale : K * ((r : ℝ) + 1) ≤ T)
    (hlift : (2 : ℝ) ^ (s + 1) * s < T)
    (hfreeze : 24 * (r : ℝ) * s < T)
    (hroom : 8 * L * r * s * (2 : ℝ) ^ s ≤ σ * T)
    (hlength : (2 : ℝ) ^ (2 * s + 3) ≤ σ * T) : LayerResetScales s r L := by
  let B := p * (r + 1) ^ (2 * s)
  have hB : 0 < B := Nat.mul_pos hp (pow_pos (by omega) _)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hge (h : ℕ) : (T : ℝ) ≤ layerResetCellScale s B T h := by
    exact_mod_cast layerResetCellScale_ge (h := h) hB hT
  have hcell (h : ℕ) : (0 : ℝ) < layerResetCellScale s B T h := hT0.trans_le (hge h)
  have hprod (h : ℕ) (hh : h ≤ s) (x : ℝ) (hx : (T : ℝ) ≤ x) :
      σ * T / (2 : ℝ) ^ s ≤ (σ / (2 : ℝ) ^ h) * x := by
    have hdiv : σ / (2 : ℝ) ^ s ≤ σ / (2 : ℝ) ^ h :=
      div_le_div_of_nonneg_left hσ.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) hh)
    calc
      _ = (σ / (2 : ℝ) ^ s) * T := by ring
      _ ≤ _ := mul_le_mul hdiv hx hT0.le (by positivity)
  refine {
    threshold := layerResetThreshold s B T
    cellScale := layerResetCellScale s B T
    score := fun h => σ / (2 : ℝ) ^ h
    constant := fun _ => K
    exponent := fun _ => p
    score_pos := fun h _ => div_pos hσ (by positivity)
    constant_nonneg := fun _ _ => hK
    partition := hpartition
    cell_pos := fun h _ => hT.trans_le (layerResetCellScale_ge hB hT)
    scale_bound := fun h _ => hscale.trans (hge h)
    power_bound := ?_
    lift_error := ?_
    freeze_error := ?_
    score_error := ?_
    score_next := ?_
    length_bound := ?_
  }
  · intro h hh
    have he : p * (r + 1) ^ (2 * h) ≤ B :=
      Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by omega) (by omega))
    exact (Nat.pow_le_pow_right (hT.trans_le (layerResetCellScale_ge hB hT)) he).trans_eq
      (layerResetCellScale_power hh)
  · intro h hh
    rw [← mul_div_assoc]
    apply (div_lt_one (hcell h)).mpr
    calc
      _ ≤ (2 : ℝ) ^ (s + 1) * s := mul_le_mul
        (pow_le_pow_right₀ (by norm_num) (by omega)) (by exact_mod_cast hh)
        (by positivity) (by positivity)
      _ < T := hlift
      _ ≤ _ := hge h
  · intro h hh
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 12)).mpr
    rw [show (r : ℝ) * (2 * ((h : ℝ) / layerResetCellScale s B T h)) * 12 =
      (24 * r * h) / layerResetCellScale s B T h by ring]
    apply (div_lt_one (hcell h)).mpr
    calc
      _ ≤ 24 * (r : ℝ) * s := mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (by positivity)
      _ < T := hfreeze
      _ ≤ _ := hge h
  · intro h hh
    calc
      _ ≤ 8 * L * r * s := mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (by positivity)
      _ ≤ σ * T / (2 : ℝ) ^ s := (le_div_iff₀ (by positivity)).mpr hroom
      _ ≤ _ := hprod h hh _ (hge h)
  · intro h _
    simp only [pow_succ, div_div]
    exact le_rfl
  · intro h hh
    let A := layerResetThreshold s B T (h + 1)
    have hA : (T : ℝ) ≤ A := by exact_mod_cast layerResetThreshold_ge (h := h + 1) hB hT
    have hc : (2 : ℝ) ^ (h + 3) ≤ (σ / (2 : ℝ) ^ h) * A := by
      calc
        _ ≤ (2 : ℝ) ^ (s + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ σ * T / (2 : ℝ) ^ s := by
          apply (le_div_iff₀ (by positivity)).mpr
          simpa only [← pow_add, show s + 3 + s = 2 * s + 3 by omega] using hlength
        _ ≤ _ := hprod h hh _ hA
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (h + 3))).mpr
    rw [layerResetCellScale_sq, Nat.cast_pow]
    change (A : ℝ) * 2 ^ (h + 3) ≤ (σ / 2 ^ h) * A ^ 2
    nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) A)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteCellMean {X A : Type*} [Fintype X] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (f : X → ℝ) (a : A) : ℝ :=
  p.mean (fun x => if C x = a then f x else 0)

noncomputable def finiteCellResidueMean {X A R : Type*}
    [Fintype X] [DecidableEq A] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (C : X → A) (F : X → R) (e : X → ℝ) (a : A) (r : R) : ℝ :=
  p.mean (fun x => if C x = a ∧ F x = r then e x else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelSupportContraction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

noncomputable def productKernelApply (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (FiniteProbabilityWeights.pi (fun i => K i (x i))).mean f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

noncomputable def anovaKernelMatrix (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (i : ι) (x : X i) (y : Y i) : ℝ :=
  if i ∈ S then centeredKernelMatrix (ν i) (K i) x y else (ν i).weight y

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

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def coordinateUnionWeight (z : Sigma X) : ℝ := (μ z.1).weight z.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedTrimmedSliceFamily
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def rectangularScalarDiscrepancy {I J : Type*}
    [Fintype I] [Fintype J] (parent : I → ℤ) (H : I → ℕ)
    (h g : (I → ℤ) → ℂ) (epsilon level : ℝ) (D : ℕ)
    (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (z : Option J × I → ℤ) : ℝ :=
  (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
    realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (h x).re)
      (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z) -
    (1 + epsilon) * level *
      realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (g x).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ModularVectorCoefficientRank
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def vectorDesignatedRankFailureProbability {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (N n : ℕ) [NeZero N]
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod N))
    (w : B → ZMod N) (c : B → A → ZMod N) : ℝ :=
  𝔼 u : Fin n → I → ZMod N,
    if polynomialLinearRow (polynomialIterDifference n
      (∑ b, w b • designatedVectorComponent S Q c b) u) = 0 then 1 else 0

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

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

def scalarCoefficientBad (n : T → ℕ) (S : ∀ t, B t → D → Finset I)
    (Q : ∀ t, B t → MvPolynomial I ℤ) (C : ℝ) (M : ℕ) [NeZero M]
    (x : (Σ t, B t × D) → ZMod M) : Prop :=
  ∃ t, ∃ w : B t → ZMod M, (∃ b, IsUnit (w b)) ∧
    (M : ℝ) ^ (-C) < vectorDesignatedRankFailureProbability M (n t) (S t)
      (fun b => (Q t b).map (Int.castRingHom (ZMod M))) w
      (fun b d => x ⟨t,(b,d)⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]
variable {Y : Type*} [PseudoMetricSpace Y]

local notation "single" => (fun _ : Fin m => Unit)

noncomputable def forecastBufferedFullResidue (w : MixedCoveredJetSource I single E n d) :
    ∀ j, Fin (n j) ⊕ E j → ZMod period :=
  fun j => Sum.elim (fun i => ((w.1 j).2 i () : ZMod period))
    (fun i => ((w.2 j () i).val : ZMod period))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastComparisonLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedSlicedForecastSourceLog (m M Jalloc : ℕ) (Ptest : ℝ) : ℝ :=
  2 + (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)) ^ 2 +
    preparedSlicedForecastPrimitiveCap + max 0 Ptest

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteComparisonGridBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedSlicedForecastPerturbationLog (m M Jalloc : ℕ)
    (cost Ptest E : ℝ) : ℝ :=
  let D := allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
  let Pu := preparedSlicedForecastSourceLog m M Jalloc Ptest
  fixedPathSlicedPerturbationLog D (D + Pu + 4) (cost + 1) (2 * Pu + (E + 4) + 14) m

end Erdos3.VectorPolynomial

end

end OAI
end


