-- Prove2me | Definitions.Def_OAIE3v2B074
-- name    : OAIE3v2B074
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:18:47.524785+00:00
-- url     : https://prove2.me/theorems/99ee0bfe-e593-45f9-b27f-a3f7ad37df2c
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 75 of 311
-- statement:
--   Definitions bundle 75 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B042`, `OAIE3v2B043`, `OAIE3v2B044`, `OAIE3v2B045`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049` of this split.
--
--   Modules: `Dynamics/ArbitraryStepPrescribedBudget.lean`, `Dynamics/PreparedFiniteStageNativeBudget.lean`, `Estimates/AllocatedExternalCandidateTaggedPairFamily.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/CoefficientRowEvaluation.lean`, `Estimates/CommonDependentIntegralModel.lean`, `Estimates/CubeSignalAlgebra.lean`, `Estimates/FreeLieTreeCoefficientBounds.lean`, `Estimates/FreePrimitiveCriterion.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/MixedRealPoint.lean`, `Estimates/NativeSeparatedSumIntervals.lean`, `Estimates/NormalizedCoefficientRemainder.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/SquarefreeSplitCount.lean`, `Estimates/UniformPhysicalVisitBounds.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Geometry/AllocatedSpatialProxyCap.lean`, `Geometry/CommonStrideCoordinates.lean`, `Geometry/CoveredJetChart.lean`, `Geometry/CubeSignalCoordinates.lean`, `Geometry/EmptyLayerChartBounds.lean`, `Geometry/MixedAntisymmetricBox.lean`, `Geometry/MixedArraySourceSupport.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/MixedProfileCoordinates.lean`, `Geometry/NormalizedCoveredChart.lean`, `Lattices/AffineCoefficientLaw.lean`, `Lattices/AlgebraicMajorWeightedAffineTopPullback.lean`, `Lattices/CoefficientDeckResidueMask.lean`, `Lattices/CoefficientIntegerFloorRemainder.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/IntegerAxisPrincipalLaw.lean`, `Lattices/IntegerAxisTailLaw.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/IntegerVectorFreimanEmbedding.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/SpatialAffineFullMass.lean`, `Lattices/StrideSelectedResidueBadProduct.lean`, `Linear/AllocatedKernelPrimitiveBudget.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/BasisAxisNormalization.lean`, `Linear/FixedSpatialKernelSliceDensity.lean`, `Linear/HomogeneousLieSpan.lean`, `Linear/LieWordProjection.lean`, `Linear/WeightedParameterPatchRankPadding.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/CurrentBracketInductionStep.lean`, `Nilpotent/SquarefreeBracketHeight.lean`, `Nilpotent/WordTruncationBracket.lean`, `Polynomial/CoefficientPolynomialLift.lean`, `Polynomial/ContinuousPolynomialSupport.lean`, `Polynomial/IntegerPolynomialActiveProfileSupport.lean`, `Polynomial/IntegerPolynomialSupport.lean`, `Polynomial/PolynomialRationalApproximationMono.lean`, `Polynomial/PrincipalMonomialScale.lean`, `Polynomial/ScalarCubeMinorPolynomial.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Probability/DiagonalImageDensity.lean`, `Probability/EmptyCoefficientDensity.lean`, `Probability/MixedDensityInterpolation.lean`, `Probability/OrthonormalMixedLaw.lean`, `Probability/PerturbationCoefficientLaw.lean`, `Probability/PrincipalCoefficientLaw.lean`, `Probability/ScaledCoefficientLaw.lean`, `Sampling/LayerSamplerWitnessScale.lean`, `Sampling/SamplingRankProjectedContainment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B043
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

theorem mixedCubeProduct_cons {j : ℕ} (F : (Fin (j + 1) → Bool) → H → ℂ)
    (h : H) (hs : Fin j → H) (x : H) :
    mixedCubeProduct F (Fin.cons h hs) x =
      mixedCubeProduct (fun ω ↦ F (Fin.cons false ω)) hs x *
        star (mixedCubeProduct (fun ω ↦ F (Fin.cons true ω)) hs (x + h)) := by
  simp only [mixedCubeProduct]
  rw [prod_bool_tuple_succ]
  simp only [booleanWeight_cons_false, booleanWeight_cons_true,
    cubeShift_cons_false, cubeShift_cons_true, conjugationPower, RingHom.comp_apply,
    starRingEnd_apply, ← add_assoc]
  change _ = _ * (starRingEnd ℂ) _
  rw [map_prod]
  simp only [starRingEnd_apply]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem cubeProduct_eq_mixedCubeProduct {H : Type*} [AddCommGroup H]
    (f : H → ℂ) {d : ℕ} (k : Fin d → H) (x : H) :
    cubeProduct f (List.ofFn k) x = mixedCubeProduct (fun _ => f) k x := by
  induction d generalizing x with
  | zero => simp only [List.ofFn_zero, cubeProduct_nil, mixedCubeProduct_zero]
  | succ d ih =>
    rw [← Fin.cons_self_tail k, List.ofFn_cons, cubeProduct_cons, mixedCubeProduct_cons]
    rw [ih, ih]

theorem cubeProduct_eq_boolean_product {H : Type*} [AddCommGroup H]
    (f : H → ℂ) {d : ℕ} (k : Fin d → H) (x : H) :
    cubeProduct f (List.ofFn k) x =
      ∏ ω : Fin d → Bool, conjugationPower (booleanWeight ω) (f (x + cubeShift k ω)) :=
  cubeProduct_eq_mixedCubeProduct f k x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem dynkinProjection_freeLieWordExpansion (x : FreeLieAlgebra ℚ X) :
    dynkinProjection (FreeLieAlgebra.of ℚ) (freeLieWordExpansion x) = x := by
  apply freeLie_linear_induction (fun x =>
    dynkinProjection (FreeLieAlgebra.of ℚ) (freeLieWordExpansion x) = x)
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    simp only [map_smul, hx]
  · intro t
    rw [freeLieWordExpansion_tree, dynkinProjection_commutatorTree]

theorem freeLieWordExpansion_injective :
    Function.Injective (freeLieWordExpansion (X := X)) :=
  Function.LeftInverse.injective dynkinProjection_freeLieWordExpansion

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LieWordProjection
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem lieWordProjection_eq_self_iff (p : WordPolynomial X) :
    lieWordProjection p = p ↔ p ∈ lieWordSubalgebra := by
  rw [← freeLieWordExpansion_range]
  constructor
  · intro h
    exact (LieHom.mem_range _ _).mpr ⟨dynkinProjection (FreeLieAlgebra.of ℚ) p, h⟩
  · intro h
    obtain ⟨x, rfl⟩ := (LieHom.mem_range _ _).mp h
    simp only [lieWordProjection_apply, dynkinProjection_freeLieWordExpansion]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem wordTruncation_freeLie_mem (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    wordTruncation s (freeLieWordExpansion p) ∈ lieWordSubalgebra := by
  apply freeLie_linear_induction (fun p =>
    wordTruncation s (freeLieWordExpansion p) ∈ lieWordSubalgebra)
  · simpa only [map_zero] using lieWordSubalgebra.zero_mem
  · intro p q hp hq
    rw [map_add, map_add]
    exact lieWordSubalgebra.add_mem hp hq
  · intro r p hp
    rw [map_smul, map_smul]
    exact lieWordSubalgebra.smul_mem r hp
  · intro t
    rw [freeLieWordExpansion_tree, wordTruncation_homogeneous s (commutatorTree_homogeneous t)]
    split_ifs
    · exact commutatorTree_mem_lieWordSubalgebra t
    · exact lieWordSubalgebra.zero_mem

theorem freeLieTruncation_expansion (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieWordExpansion (freeLieTruncation s p) = wordTruncation s (freeLieWordExpansion p) :=
  (lieWordProjection_eq_self_iff _).mpr (wordTruncation_freeLie_mem s p)

theorem lift_freeLieTruncation {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : X → L) {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (p : FreeLieAlgebra ℚ X) :
    FreeLieAlgebra.lift ℚ f (freeLieTruncation s p) = FreeLieAlgebra.lift ℚ f p := by
  rw [← dynkinProjection_lift, freeLieTruncation_expansion,
    dynkinProjection_wordTruncation f hnil, dynkinProjection_lift]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

noncomputable def lieBCHList (s : ℕ) (f : X → L) : List X → L
  | [] => 0
  | x :: xs => lieBCH s (f x) (lieBCHList s f xs)

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

noncomputable def fixedSpatialBlockDensity
    (μ : Measure T) (center : X → ℝ) (rest : T → X → ℝ)
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) : (X → ℝ) → ℝ :=
  haarShiftDensity μ (fun t => center + rest t)
    (twoBoxDifferenceDensity (fun _ => 1) (fun _ => 1)
      (A.trans (ContinuousLinearEquiv.neg ℝ)) B)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrincipalMonomialScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialScale_canonicalPrincipal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (T : SamplerTupleIndex G B h → ℝ) (d : D) (b : B d) :
    monomialScale T (canonicalPrincipalExponent h d b) = ∏ v, T (.inr ⟨d, b, v⟩) :=
  monomialScale_productBlockExponent _ T

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ]

@[simp] theorem blockExponent_zero (π : ι → σ) : blockExponent π 0 = 0 := by
  ext i
  simp only [blockExponent_apply, blockDegree_zero, Pi.zero_apply, Finsupp.zero_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3


noncomputable def integerScalarCubeReference (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform _


open scoped BigOperators Classical

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial
namespace OAI

section

namespace Erdos3

noncomputable def normalizedScalarCubeMinor {I J : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} (s : I → J) (x : J → IntegerScalarCubeBox I L) : ℝ :=
  (((scalarCubeDifferenceMatrix x).submatrix id s).det : ℝ) / (L : ℝ) ^ Fintype.card I

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3

def GoodScalarKernelTuple {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {L : ℕ} (s : I → J) (κ : ℝ) (B : ℕ) (x : J → IntegerScalarCubeBox I L) : Prop :=
  κ < |normalizedScalarCubeMinor s x| ∧
    HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range B

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selected_factorization_product_dvd (S : Finset ℕ) (n : ℕ) :
    (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  have he : (∏ p ∈ S ∩ n.factorization.support, p ^ n.factorization p) =
      ∏ p ∈ S, p ^ n.factorization p := by
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hp hnot
    have hzero : n.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      exact fun hs => hnot (Finset.mem_inter.mpr ⟨hp, hs⟩)
    simp [hzero]
  rw [← he]
  exact (Finset.prod_dvd_prod_of_subset (S ∩ n.factorization.support)
    n.factorization.support (fun p => p ^ n.factorization p) Finset.inter_subset_right).trans
      (dvd_of_eq (Nat.prod_factorization_pow_eq_self hn))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ArbitraryStepPrescribedBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem arbitraryStep_prescribed_product_dvd (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) (step : ℕ) :
    (∏ p : Pr, p.val ^ padicValNat p.val step) ∣ step := by
  rw [Finset.prod_coe_sort Pr (fun p : ℕ => p ^ padicValNat p step)]
  have hprod : (∏ p ∈ Pr, p ^ padicValNat p step) =
      ∏ p ∈ Pr, p ^ step.factorization p := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_def step (hprime p hp)]
  rw [hprod]
  exact selected_factorization_product_dvd Pr step

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

theorem affineProbabilityProfile_nonneg (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ) :
    0 ≤ affineProbabilityProfile c w x :=
  mul_nonneg (inv_nonneg.mpr hw.le) (smoothProbabilityProfile_range _).1

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_nonneg {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) (x : I → ℝ) : 0 ≤ affineProductProfile c w x :=
  Finset.prod_nonneg (fun i _ => affineProbabilityProfile_nonneg (c i) (hw i) (x i))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem affineProbabilityProfile_support (c : ℝ) {w : ℝ} (hw : 0 < w) {x : ℝ}
    (hx : affineProbabilityProfile c w x ≠ 0) : |x - c| < 3 * w / 4 := by
  by_contra! h
  have hz : smoothProbabilityProfile ((x-c)/w) = 0 := by
    apply smoothProbabilityProfile_zero
    rw [abs_div, abs_of_pos hw]
    apply (le_div_iff₀ hw).mpr
    linarith
  exact hx (by simp only [affineProbabilityProfile, hz, mul_zero])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

theorem constantIntegerPMF_support (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) {k : ℤ}
    (hk : k ∈ (constantIntegerPMF K δ hK hδ).support) :
    |(k : ℝ) / K| < 3 * δ / 4 := by
  by_cases hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K
  · rw [constantIntegerPMF_large K δ hK hδ hlarge] at hk
    simpa only [sub_zero] using normalizedIntegerPMF_support K 0 δ hK hδ hlarge hk
  · rw [(constantIntegerPMF_small K δ hK hδ (lt_of_not_ge hlarge)).1] at hk
    have hk0 : k = 0 := by simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk
    subst k
    simp only [Int.cast_zero, zero_div, abs_zero]
    positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PrincipalCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem principalIntegerPMF_support {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
    {k : ℤ} (hk : k ∈ (principalIntegerPMF K T γ hK hT hγ hlarge).support) :
    γ < T * (k : ℝ) / K ∧ T * (k : ℝ) / K < 2 * γ := by
  have hb := normalizedIntegerPMF_support (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge hk
  have he : (k : ℝ) / (K / T) = T * (k : ℝ) / K := by field_simp
  rw [he] at hb
  constructor <;> nlinarith [(abs_lt.mp hb).1, (abs_lt.mp hb).2]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAxisPrincipalLaw
namespace OAI

section

namespace Erdos3

theorem integerAxisPrincipalPMF_active {h K L : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K) (ha : L ^ h < K)
    {k : ℤ} (hk : k ∈ (integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap).support) :
    γ < (L : ℝ) ^ h * (k : ℝ) / K ∧ (L : ℝ) ^ h * (k : ℝ) / K < 2 * γ := by
  simp only [integerAxisPrincipalPMF, ha, ↓reduceDIte] at hk
  exact principalIntegerPMF_support (by exact_mod_cast hK)
    (pow_pos (by exact_mod_cast hL) _) hγ (integerAxisPrincipal_width hh hL hγ (hgap ha)) hk

theorem integerAxisPrincipalPMF_bound {h K L : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
    {k : ℤ} (hk : k ∈ (integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap).support) :
    |(k : ℝ) / K| * (integerAxisSideLength h K L γ : ℝ) ^ h ≤ 2 * γ := by
  by_cases ha : L ^ h < K
  · have hb := integerAxisPrincipalPMF_active hh hK hL hγ hgap ha hk
    have he : |(k : ℝ) / K| * (L : ℝ) ^ h = |(L : ℝ) ^ h * (k : ℝ) / K| := by
      calc
        _ = |((k : ℝ) / K) * (L : ℝ) ^ h| := by
          rw [abs_mul, abs_of_pos (pow_pos (show (0 : ℝ) < L by exact_mod_cast hL) h)]
        _ = _ := by congr 1; ring
    simp only [integerAxisSideLength, ha, ↓reduceIte]
    rw [he, abs_of_pos (hγ.trans hb.1)]
    exact hb.2.le
  · rw [integerAxisPrincipalPMF_inactive hh hK hL hγ hgap (Nat.le_of_not_gt ha)] at hk
    rw [inactivePrincipalPMF_support hk]
    simp only [integerAxisSideLength, ha, ↓reduceIte, abs_div,
      abs_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)]
    calc
      _ = |(inactivePrincipalCoefficient K (inactiveDenominator γ) : ℝ)| *
          (inactiveSideLength h K (inactiveDenominator γ) : ℝ) ^ h / K := by ring
      _ ≤ 1 / (inactiveDenominator γ : ℝ) :=
        inactivePrincipal_scaled_upper hh hK (inactiveDenominator_pos γ)
      _ ≤ γ := inactiveDenominator_bound hγ
      _ ≤ 2 * γ := by linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PerturbationCoefficientLaw
namespace OAI

section

namespace Erdos3

theorem integerPerturbation_scaled_support {K ε S : ℝ} (hK : 0 < K) (hε : 0 < ε) (hS : 0 < S)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (ε / S) * K) {k : ℤ}
    (hk : k ∈ (normalizedIntegerPMF K 0 (ε / S) hK (div_pos hε hS) hlarge).support) :
    |(k : ℝ) / K| * S < 3 * ε / 4 := by
  have hb := normalizedIntegerPMF_support K 0 (ε / S) hK (div_pos hε hS) hlarge hk
  simp only [sub_zero] at hb
  have he := mul_lt_mul_of_pos_right hb hS
  have hs : 3 * (ε / S) / 4 * S = 3 * ε / 4 := by field_simp
  rwa [hs] at he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAxisTailLaw
namespace OAI

section

namespace Erdos3

theorem integerAxisTailPMF_small {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {K L s : ℕ} (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) (ha : K ≤ L ^ (s + 1)) :
    integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL e he = PMF.pure 0 := by
  simp [integerAxisTailPMF, Nat.not_lt.mpr ha]

theorem integerAxisTailPMF_support {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {K L s : ℕ} (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) {k : ℤ}
    (hk : k ∈ (integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL e he).support) :
    |(k : ℝ) / K| * monomialScale T e < 3 * ε / 4 := by
  by_cases ha : L ^ (s + 1) < K
  · simp only [integerAxisTailPMF, ha, ↓reduceDIte] at hk
    exact integerPerturbation_scaled_support (by exact_mod_cast hK) hε
      (monomialScale_pos T hT e) (integerAxisTail_width T hT hL hTL hε hεL e he ha) hk
  · rw [integerAxisTailPMF_small T hT hK hL hTL hε hεL e he (Nat.le_of_not_gt ha)] at hk
    have hk0 : k = 0 := by simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk
    subst k
    simp only [Int.cast_zero, zero_div, abs_zero, zero_mul]
    positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomial_abs_le_scale {K : Type*} (T x : K → ℝ) (hx : ∀ k, |x k| ≤ T k)
    (e : K →₀ ℕ) : |∏ k ∈ e.support, x k ^ e k| ≤ monomialScale T e := by
  classical
  rw [Finset.abs_prod]
  change (∏ k ∈ e.support, |x k ^ e k|) ≤ ∏ k ∈ e.support, T k ^ e k
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro k _
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _

theorem monomialArrayPolynomial_box_bound {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (T x : K → ℝ) (hx : ∀ k, |x k| ≤ T k) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤
      ∑ j, |a j| * monomialScale T (e j) := by
  rw [monomialArrayPolynomial_eval]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (monomial_abs_le_scale T x hx (e j)) (abs_nonneg _)

theorem monomialArrayPolynomial_box_budget {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a B : J → ℝ) (T x : K → ℝ) (hx : ∀ k, |x k| ≤ T k)
    (ha : ∀ j, |a j| * monomialScale T (e j) ≤ B j) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ ∑ j, B j :=
  (monomialArrayPolynomial_box_bound e a T x hx).trans (Finset.sum_le_sum (fun j _ => ha j))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

local notation "laws" => integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
  ρ γ ε hρ hγ hε hgap hεL

omit [Fintype J] in
theorem integerPolynomialCoordinatePMF_bound (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (j : J) {k : ℤ} (hk : k ∈ (laws j).support) :
    |(k : ℝ) / K| * monomialScale T (e j) ≤
      |coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  by_cases hj : j = j₀
  · subst j
    simp only [integerPolynomialCoordinatePMF, ↓reduceIte] at hk
    have hb := constantIntegerPMF_support K ρ (by exact_mod_cast hK) hρ hk
    simp only [coefficientProfileCenter, coefficientProfileWidth, hj₀, ↓reduceIte,
      he₀, monomialScale_zero, mul_one, abs_zero, zero_add]
    linarith
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisPrincipalPMF_bound hh hK hL hγ hgap hk
      rw [hprincipal j hp]
      have hpos : 0 ≤ 3 * γ / 2 := by positivity
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp,
        ↓reduceIte, abs_of_nonneg hpos]
      linarith
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisTailPMF_support T hT hK hL hTL hε hεL (e j) (he j) hk
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp,
        ↓reduceIte, abs_zero, zero_add]
      linarith

theorem integerPolynomialCoordinatePMF_box (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (a : J → ℤ) (ha : ∀ j, a j ∈ (laws j).support) (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a j : ℝ) / K))| ≤
      ρ + 2 * γ * P.card + ε * Fintype.card J := by
  apply (monomialArrayPolynomial_box_budget e (fun j => (a j : ℝ) / K)
    (fun j => |coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j) T x hx
    (fun j => integerPolynomialCoordinatePMF_bound P j₀ h K L s hh hK hL T hT hTL e he
      ρ γ ε hρ hγ hε hgap hεL hj₀ he₀ hprincipal j (ha j))).trans
  exact coefficientProfile_budget P j₀ hj₀ hγ.le hε.le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem affineProbabilityProfile_scaled_support {c w S x : ℝ} (hw : 0 < w) (hS : 0 < S)
    (hx : affineProbabilityProfile (c / S) (w / S) x ≠ 0) :
    |x * S - c| < 3 * w / 4 := by
  have hb := mul_lt_mul_of_pos_right
    (affineProbabilityProfile_support (c / S) (div_pos hw hS) hx) hS
  have hl : |x - c / S| * S = |x * S - c| := by
    calc
      _ = |(x - c / S) * S| := by rw [abs_mul, abs_of_pos hS]
      _ = _ := by rw [sub_mul, div_mul_cancel₀ _ hS.ne']
  have hr : 3 * (w / S) / 4 * S = 3 * w / 4 := by field_simp
  rwa [hl, hr] at hb

noncomputable def scaledCoefficientDensity {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (c w : J → ℝ) : (J → ℝ) → ℝ :=
  affineProductProfile (fun j => c j / monomialScale T (e j))
    (fun j => w j / monomialScale T (e j))

theorem scaledCoefficientDensity_support {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) {a : J → ℝ} (ha : scaledCoefficientDensity e T c w a ≠ 0) (j : J) :
    |a j * monomialScale T (e j) - c j| < 3 * w j / 4 := by
  classical
  apply affineProbabilityProfile_scaled_support (hw j) (monomialScale_pos T hT (e j))
  exact (Finset.prod_ne_zero_iff.mp ha) j (Finset.mem_univ j)

theorem scaledCoefficientDensity_coefficient_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) {a : J → ℝ} (ha : scaledCoefficientDensity e T c w a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ |c j| + w j := by
  have hb := scaledCoefficientDensity_support e T hT c w hw ha j
  have ht := abs_add_le (a j * monomialScale T (e j) - c j) (c j)
  rw [sub_add_cancel, abs_mul, abs_of_pos (monomialScale_pos T hT (e j))] at ht
  linarith [hw j]

theorem scaledCoefficientDensity_box_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) {a : J → ℝ} (ha : scaledCoefficientDensity e T c w a ≠ 0)
    (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ ∑ j, (|c j| + w j) :=
  monomialArrayPolynomial_box_budget e a _ T x hx
    (scaledCoefficientDensity_coefficient_bound e T hT c w hw ha)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ContinuousPolynomialSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def continuousPolynomialDensity {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (P : Finset J) (j₀ : J) (R σ : ℝ) : (J → ℝ) → ℝ :=
  scaledCoefficientDensity e T (coefficientProfileCenter P (principalProfileSize R P.card))
    (coefficientProfileWidth P j₀ (R / 4) (principalProfileSize R P.card)
      (tailProfileSize R σ (Fintype.card J)))

theorem continuousPolynomialDensity_width_pos {J : Type*} [Fintype J]
    (P : Finset J) (j₀ : J) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (j : J) :
    0 < coefficientProfileWidth P j₀ (R / 4) (principalProfileSize R P.card)
      (tailProfileSize R σ (Fintype.card J)) j :=
  coefficientProfileWidth_pos P j₀ (by positivity) (principalProfileSize_pos hR _)
    (tailProfileSize_pos hR hσ _) j

theorem continuousPolynomialDensity_box {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0)
    (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ 3 * R / 4 := by
  have hb := scaledCoefficientDensity_box_bound e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha x hx
  exact hb.trans ((coefficientProfile_budget P j₀ hj₀ (principalProfileSize_pos hR _).le
    (tailProfileSize_pos hR hσ _).le).trans (allocatedProfile_budget hR.le hσ1 _ _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)

variable (hgap : L ^ h < K → (principalSamplingGapRatio (principalProfileSize R P.card) * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ (tailProfileSize R σ (Fintype.card J)) * L)

local notation "laws" => allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL
  e he R σ hR hσ hgap hεL

theorem allocatedIntegerPolynomial_box (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h)
    (a : J → ℤ) (ha : ∀ j, a j ∈ (laws j).support) (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a j : ℝ) / K))| ≤ 3 * R / 4 := by
  have hb := integerPolynomialCoordinatePMF_box P j₀ h K L s hh hK hL T hT hTL e he
    (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J)) (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hgap hεL hj₀ he₀ hprincipal a ha x hx
  exact hb.trans (allocatedProfile_budget hR.le hσ1 _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedParameterPatchRankPadding
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def localTentKernel (d q : ℕ) (hq : 8 ≤ q) : PatchKernel d where
  value x := max 0 (1 - (q : ℝ) / 2 * dist x 0)
  nonneg x := le_max_left _ _
  le_one x := max_le zero_le_one (by
    have h : 0 ≤ (q : ℝ) / 2 * dist x 0 := by positivity
    linarith)
  support x hx i := by
    have hqR : (8 : ℝ) ≤ q := by exact_mod_cast hq
    have hsmall : (q : ℝ) / 2 * dist x 0 < 1 := by
      by_contra h
      exact hx (max_eq_left (by linarith))
    have hcoord : |x i| ≤ dist x 0 := by
      simpa only [Real.dist_eq, Pi.zero_apply, sub_zero] using dist_le_pi_dist x 0 i
    have hdist : 0 ≤ dist x 0 := dist_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hqR hdist]
  lip := (q : ℝ≥0) / 2
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |max 0 (1 - (q : ℝ) / 2 * dist x 0) - max 0 (1 - (q : ℝ) / 2 * dist y 0)| ≤
      (q : ℝ) / 2 * dist x y
    calc
      _ ≤ |(1 - (q : ℝ) / 2 * dist x 0) - (1 - (q : ℝ) / 2 * dist y 0)| := by
        rw [max_comm 0 _, max_comm 0 _]
        exact abs_max_sub_max_le_abs _ _ _
      _ = (q : ℝ) / 2 * |dist x 0 - dist y 0| := by
        rw [show (1 - (q : ℝ) / 2 * dist x 0) - (1 - (q : ℝ) / 2 * dist y 0) =
          -((q : ℝ) / 2) * (dist x 0 - dist y 0) by ring,
          abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (q : ℝ) / 2)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_dist_sub_le x y 0) (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {U X : Type*}

noncomputable def residueAffinePolynomial (q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) : MvPolynomial U ℝ :=
  eval₂Hom C (fun i => C (r i : ℝ) + C (q : ℝ) * MvPolynomial.X i) P

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable (I : Type*) [Fintype I]

theorem mem_finiteLieTrees_of_length_le (a : FreeMagma I) {n : ℕ} (hn : a.length ≤ n) :
    a ∈ finiteLieTrees I n := by
  classical
  induction a using FreeMagma.rec generalizing n with
  | of i =>
    cases n with
    | zero => simp only [FreeMagma.length] at hn; omega
    | succ n =>
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  | mul a b ha hb =>
    have hapos := a.length_pos
    have hbpos := b.length_pos
    change a.length + b.length ≤ n at hn
    cases n with
    | zero => omega
    | succ n =>
      apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_image.mpr ⟨(a, b),
        Finset.mem_product.mpr ⟨ha (n := n) (by omega), hb (n := n) (by omega)⟩, rfl⟩

variable {I} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def finiteWeightedLieValues (v : I → L) (w : I → ℕ) (d r : ℕ) : Finset L := by
  classical
  exact ((finiteLieTrees I d).filter (fun a => lieTreeWeight w a = d ∧ r ≤ a.length)).image
    (lieTreeEval v)

omit [LieAlgebra ℚ L] in
theorem finiteWeightedLieValues_card_le (v : I → L) (w : I → ℕ) (d r : ℕ) :
    (finiteWeightedLieValues v w d r).card ≤ (Fintype.card I + 2) ^ (3 ^ d) := by
  classical
  exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans (finiteLieTrees_card_le I d)

end Erdos3

end

section

namespace Erdos3

variable {I σ : Type*}

theorem lieTreeMultidegree_apply (g : I → σ →₀ ℕ) (a : FreeMagma I) (j : σ) :
    lieTreeMultidegree g a j = lieTreeWeight (fun i => g i j) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb => exact congrArg₂ (· + ·) ha hb

theorem markedTreeGrade_weight (w : I → ℕ) (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMultidegree (markedGeneratorGrade w marked) a 0 = lieTreeWeight w a := by
  rw [lieTreeMultidegree_apply]
  simp [markedGeneratorGrade]

theorem markedTreeGrade_count (w : I → ℕ) (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMultidegree (markedGeneratorGrade w marked) a 1 = lieTreeMarkedCount marked a := by
  rw [lieTreeMultidegree_apply]
  simp [markedGeneratorGrade, lieTreeMarkedCount]

theorem markedTreeGrade_length (w : I → ℕ) (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMultidegree (markedGeneratorGrade w marked) a 2 = a.length := by
  induction a using FreeMagma.rec with
  | of i => simp [markedGeneratorGrade, FreeMagma.length]
  | mul a b ha hb => exact congrArg₂ (· + ·) ha hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

theorem lie_bracket_coordinate_height {α : Type*} [Fintype α] (b : Basis α ℚ L)
    {H A B : ℕ} (hbr : ∀ i j n, RationalHeightLE (lieStructureConstants b i j n) H)
    (x y : L) (hx : ∀ i, RationalHeightLE (b.repr x i) A)
    (hy : ∀ i, RationalHeightLE (b.repr y i) B) (n : α) :
    RationalHeightLE (b.repr ⁅x, y⁆ n)
      ((Fintype.card α ^ 2 + 1) * (H * A * B) ^ (Fintype.card α ^ 2)) := by
  classical
  rw [lie_coordinate_formula]
  have h := rationalHeightLE_sum
    (fun ij : α × α => lieStructureConstants b ij.1 ij.2 n * b.repr x ij.1 * b.repr y ij.2)
    (fun ij => ((hbr ij.1 ij.2 n).mul (hx ij.1)).mul (hy ij.2))
  simpa only [Fintype.card_prod, ← pow_two] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module

theorem finiteLieTrees_coordinate_height {I ι L : Type*} [Fintype I] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] (e : Basis ι ℚ L) (v : I → L) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v i) j) H) (n : ℕ)
    (a : FreeMagma I) (ha : a ∈ finiteLieTrees I n) (k : ι) :
    RationalHeightLE (e.repr (lieTreeEval v a) k) (lieTreeHeight (Fintype.card ι) H n) := by
  classical
  induction n generalizing a k with
  | zero => simp only [finiteLieTrees, Finset.notMem_empty] at ha
  | succ n ih =>
    rcases Finset.mem_union.mp ha with h | h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact (hv i k).mono (lieTreeHeight_ge_input _ _ _)
    · obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hb, hc'⟩ := Finset.mem_product.mp hbc
      exact (lie_bracket_coordinate_height e hc (lieTreeEval v b) (lieTreeEval v c)
        (fun j => ih b hb j) (fun j => ih c hc' j) k).mono (lieTreeHeight_step _ _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AlgebraicMajorWeightedAffineTopPullback
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U R : Type*} [CommRing R]

theorem polynomial_dilation_monomial (a c : R) (α : U →₀ ℕ) :
    aeval (fun i => C a * X i) (monomial α c) = monomial α (a ^ α.degree * c) := by
  classical
  rw [aeval_monomial]
  simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum, prod_X_pow_eq_monomial]
  rw [monomial_eq, monomial_eq]
  simp only [map_one, one_mul, map_mul]
  have hd : (∑ i ∈ α.support, α i) = α.degree := rfl
  rw [hd]
  ring

theorem coeff_polynomial_dilation (a : R) (P : MvPolynomial U R) (α : U →₀ ℕ) :
    (aeval (fun i => C a * X i) P).coeff α = a ^ α.degree * P.coeff α := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, polynomial_dilation_monomial, coeff_sum, coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β hβ hβα
      simp [hβα]
    · exact fun h => (h hα).elim
  · rw [Finset.sum_eq_zero]
    · have hz : P.coeff α = 0 := not_ne_iff.mp (fun h => hα (mem_support_iff.mpr h))
      simp only [hz, mul_zero]
    · intro β hβ
      have hβα : β ≠ α := by rintro rfl; exact hα hβ
      simp [hβα]

theorem homogeneousComponent_polynomial_dilation (h : ℕ) (a : R)
    (P : MvPolynomial U R) :
    homogeneousComponent h (aeval (fun i => C a * X i) P) =
      C (a ^ h) * homogeneousComponent h P := by
  classical
  ext α
  rw [coeff_homogeneousComponent, coeff_polynomial_dilation, coeff_C_mul,
    coeff_homogeneousComponent]
  by_cases hα : α.degree = h
  · simp only [hα, ite_true]
  · simp only [hα, ite_false, mul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialRationalApproximationMono
namespace OAI

section

namespace Erdos3

theorem PolynomialRationalApproximation.mono {I : Type*}
    {T : I → ℝ} {R S : ℝ} {P : MvPolynomial I ℝ}
    (h : PolynomialRationalApproximation T R P) (hRS : R ≤ S)
    (hT : ∀ i, 0 < T i) : PolynomialRationalApproximation T S P := by
  obtain ⟨D, hD, hDR, Q, hQ⟩ := h
  exact ⟨D, hD, hDR.trans hRS, Q, fun α =>
    (hQ α).trans (div_le_div_of_nonneg_right hRS (monomialScale_pos T hT α).le)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {I J : Type*} [Fintype J]

@[simp] theorem samplingRankProjection_apply (a : J → ℤ) (e v : J → ℝ) :
    samplingRankProjection a e v = v - integerRowLinear a v • e := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisAxisNormalization
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [Fintype I]

theorem normalizedAxisBasis_coordinates (b : Basis I ℝ E) (x : E) (i : I) :
    (normalizedAxisBasis b).equivFun x i = b.equivFun x i / (basisAxisScale b i : ℝ) := by
  simp only [normalizedAxisBasis, Basis.equivFun_apply, Basis.repr_unitsSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, div_eq_mul_inv]
  exact mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmptyLayerChartBounds
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem normalizedOrthogonalChart_apply (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) (x : E) :
    normalizedOrthogonalChart W b x = (W.orthogonalProjectionOnto x,
      fun i => b.equivFun (Wᗮ.orthogonalProjectionOnto x) i / (basisAxisScale b i : ℝ)) := by
  rw [normalizedOrthogonalChart, orthogonalBasisChart_apply]
  refine Prod.ext rfl ?_
  funext i
  exact normalizedAxisBasis_coordinates b _ i

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
open MeasureTheory

theorem normalizedLatticeSheet_point {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Submodule ℝ E) (Λ : Submodule ℤ Wᗮ) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = Λ) (z : Fin n → ℤ) (u : W) :
    latticeSheetPoint W (latticeBasisEquiv Λ b hb z).val u =
      (normalizedOrthogonalChart W b).symm (u, fun i => (z i : ℝ) / (basisAxisScale b i : ℝ)) := by
  apply (normalizedOrthogonalChart W b).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, normalizedOrthogonalChart_apply,
    latticeSheetPoint_projection, latticeSheetPoint_projection_orthogonal]
  refine Prod.ext rfl ?_
  funext i
  change b.equivFun (latticeBasisEquiv Λ b hb z).val i / (basisAxisScale b i : ℝ) =
    (z i : ℝ) / (basisAxisScale b i : ℝ)
  rw [latticeBasisEquiv_coordinates]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))

theorem euclideanSubspaceTorusEquiv_mk (x : euclideanSubspace U) :
    euclideanSubspaceTorusEquiv U (QuotientAddGroup.mk' _ x) =
      QuotientAddGroup.mk' _ (euclideanSubspaceArrayEquiv U x) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedDensityInterpolation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem mixedCoefficientDensity_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) (x : (I → ℝ) × (J → ℤ)) :
    0 ≤ mixedCoefficientDensity c w p x :=
  mul_nonneg (affineProductProfile_nonneg c w hw x.1)
    (Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))

theorem mixedCoefficientDensity_support {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (p : J → PMF ℤ) (x : (I → ℝ) × (J → ℤ)) :
    mixedCoefficientDensity c w p x ≠ 0 ↔
      (∀ i, affineProbabilityProfile (c i) (w i) (x.1 i) ≠ 0) ∧
      (∀ j, x.2 j ∈ (p j).support) := by
  classical
  simp only [mixedCoefficientDensity, affineProductProfile, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]
  refine and_congr Iff.rfl (forall_congr' fun j => ?_)
  constructor
  · intro h hz
    exact h (by rw [hz]; exact ENNReal.toReal_zero)
  · intro h
    exact (ENNReal.toReal_pos h ((p j).apply_ne_top _)).ne'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.OrthonormalMixedLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I] [Fintype J]

omit [FiniteDimensional ℝ E] in
theorem orthonormalMixedDensity_nonneg (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) (x) :
    0 ≤ orthonormalMixedDensity b c w p x := mixedCoefficientDensity_nonneg c w hw p _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

theorem normalizedLatticePoint_continuous (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) : Continuous (normalizedLatticePoint W b) := by
  unfold normalizedLatticePoint
  fun_prop

theorem normalizedLatticePoint_eq_sheet (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (x : W × (Fin n → ℤ)) : normalizedLatticePoint W b x =
      latticeSheetPoint W (latticeBasisEquiv (projectedIntegerLattice W) b hb x.2).val x.1 :=
  (normalizedLatticeSheet_point W (projectedIntegerLattice W) b hb x.2 x.1).symm

theorem normalizedLatticeQuotient_injOn (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedLatticeQuotient W b hb) (normalizedLatticePoint W b ⁻¹' Ω) := by
  intro x hx y hy he
  have hx' : latticeSheetPoint W (latticeBasisEquiv (projectedIntegerLattice W) b hb x.2).val x.1 ∈ Ω := by
    rw [← normalizedLatticePoint_eq_sheet W b hb]
    exact hx
  have hy' : latticeSheetPoint W (latticeBasisEquiv (projectedIntegerLattice W) b hb y.2).val y.1 ∈ Ω := by
    rw [← normalizedLatticePoint_eq_sheet W b hb]
    exact hy
  have h := latticeSheetQuotient_injective_on_region (standardEuclideanLattice D) W
    (fun a ha c hc hac => standardLatticeSmallBox_separates D (hΩ ha) (hΩ hc) hac) hx' hy' he
  exact Prod.ext h.2 ((latticeBasisEquiv (projectedIntegerLattice W) b hb).injective h.1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedArraySourceSupport
namespace OAI

section

namespace Erdos3

open Module Submodule _root_.Set
open scoped BigOperators

def mixedArraySupported {I Z J : Type*} [Fintype I] [Fintype Z]
    (c w : I → J → ℝ) (p : Z → J → PMF ℤ) (x : (I → J → ℝ) × (Z → J → ℤ)) : Prop :=
  ∀ j, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun z => p z j)
    (mixedArrayRegroup I Z J x j) ≠ 0

theorem mixedArraySupported_iff_rows {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (p : Z → J → PMF ℤ) (x : (I → J → ℝ) × (Z → J → ℤ)) :
    mixedArraySupported c w p x ↔
      (∀ i, affineProductProfile (c i) (w i) (x.1 i) ≠ 0) ∧
      (∀ z j, x.2 z j ∈ (p z j).support) := by
  classical
  constructor
  · intro hx
    have hs (j) := (mixedCoefficientDensity_support (fun i => c i j) (fun i => w i j)
      (fun z => p z j) (mixedArrayRegroup I Z J x j)).mp (hx j)
    refine ⟨?_, fun z j => (hs j).2 z⟩
    intro i
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact (hs j).1 i
  · rintro ⟨hc, hp⟩ j
    apply (mixedCoefficientDensity_support _ _ _ _).mpr
    refine ⟨?_, fun z => hp z j⟩
    intro i
    exact (Finset.prod_ne_zero_iff.mp (hc i)) j (Finset.mem_univ j)

def mixedArrayInChart {D I J : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (o : OrthonormalBasis I ℝ W) (x : (I → J → ℝ) × (Fin n → J → ℤ)) : Prop :=
  ∀ j, normalizedLatticePoint W b (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) ∈
    standardLatticeSmallBox D

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def canonicalCoefficientSample (a : CoefficientSamplerArrays (K := K) I n) :
    CoefficientTorus (K := K) U :=
  (euclideanCoefficientEquiv U).symm
    (fun j => mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (a j))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3

theorem heterogeneousSamplerSides_integer_principal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : D → ℝ) (d : D) [Fintype (B d)]
    {k : ℕ} (hk : K d = some k) (e) (he : e ∈ principalCoefficientSlots (G := G) (B := B) h d) :
    monomialScale (fun v : SamplerTupleIndex G B h => (heterogeneousSamplerSides h K L γ v : ℝ)) e.val =
      (integerAxisSideLength (h d) k L (γ d) : ℝ) ^ h d := by
  obtain ⟨b, rfl⟩ := (mem_principalCoefficientSlots h d e).mp he
  change monomialScale _ (canonicalPrincipalExponent h d b) = _
  rw [monomialScale_canonicalPrincipal]
  simp only [heterogeneousSamplerSides, hk, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ}

variable {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem layerSamplerSides_integer_principal (R : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : Fin (n j)) (e) (he : e ∈ layerIntegerPrincipalSlots (G := G) B j i) :
    monomialScale (fun v : LayerSamplerVariables G I n B => (layerSamplerSides B U b R L v : ℝ)) e.val =
      (integerAxisSideLength (j.val + 1) (basisAxisScale (b j) i) L
        (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) : ℝ) ^ (j.val + 1) := by
  rw [layerIntegerPrincipalSlots_card]
  exact heterogeneousSamplerSides_integer_principal _ _ L (layerSamplerWidths B R)
    ⟨j, Sum.inr i⟩ rfl e he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem allocatedArrayWidths_pos {I J V : Type*} [Fintype J] (e : J → V →₀ ℕ) (T : V → ℝ)
    (hT : ∀ v, 0 < T v) (Pc : I → Finset J) (j₀ : J) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    (i : I) (j : J) : 0 < allocatedArrayWidths e T Pc j₀ R σ i j :=
  div_pos (continuousPolynomialDensity_width_pos (Pc i) j₀ hR hσ j) (monomialScale_pos T hT (e j))

theorem allocatedArraySupported_iff_rows {I Z J V : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (Pc : I → Finset J) (j₀ : J) (R σ : ℝ)
    (p : Z → J → PMF ℤ) (x : (I → J → ℝ) × (Z → J → ℤ)) :
    mixedArraySupported (allocatedArrayCenters e T Pc R) (allocatedArrayWidths e T Pc j₀ R σ) p x ↔
      (∀ i, continuousPolynomialDensity e T (Pc i) j₀ R σ (x.1 i) ≠ 0) ∧
      (∀ z j, x.2 z j ∈ (p z j).support) :=
  mixedArraySupported_iff_rows _ _ _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR hσ in
theorem allocatedLayerWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedLayerWidths B U b S j i d :=
  allocatedArrayWidths_pos _ _ (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v))
    _ _ (hR j) (hσ j) i d

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRealPoint
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedRealPoint : ((I → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] EuclideanSpace ℝ D :=
  (normalizedOrthogonalChart W b).symm.toLinearMap.comp
    ((orthonormalChart o).toLinearMap.prodMap (LinearMap.id))

theorem mixedRealPoint_norm_le {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (u : I → ℝ) (z : Fin n → ℝ) (hu : ∀ i, |u i| ≤ R) (hz : ∀ i, |z i| ≤ R) :
    ‖mixedRealPoint W b o (u, z)‖ ≤ C * (((Fintype.card I : ℝ) + 1) * R) := by
  have hu' : ‖u‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hu)
  have hz' : ‖z‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hz)
  have ho := (orthonormalChart_norm_le o u).trans (mul_le_mul_of_nonneg_left hu' (Nat.cast_nonneg _))
  have hp : ‖(orthonormalChart o u, z)‖ ≤ ((Fintype.card I : ℝ) + 1) * R := by
    rw [Prod.norm_def]
    apply max_le <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  exact (hchart _).trans (mul_le_mul_of_nonneg_left hp hC)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCoefficientRemainder
namespace OAI

section

namespace Erdos3

open Module Submodule

theorem normalizedLatticePoint_sub_mem_of_mk_eq {D : Type*} [Fintype D] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (u : W) (x : W × (Fin n → ℤ))
    (hx : QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u =
      normalizedLatticeQuotient W b hb x) :
    u.val - normalizedLatticePoint W b x ∈ standardEuclideanLattice D := by
  let z := latticeBasisEquiv (projectedIntegerLattice W) b hb x.2
  have hm : (u - (x.1 - projectedLatticeShift (standardEuclideanLattice D) W z)).val ∈
      standardEuclideanLattice D := QuotientAddGroup.eq_iff_sub_mem.mp hx
  rw [normalizedLatticePoint_eq_sheet W b hb]
  change u.val - latticeSheetPoint W z.val x.1 ∈ standardEuclideanLattice D
  rw [latticeSheetPoint_reconstruction (standardEuclideanLattice D) W z x.1]
  convert (standardEuclideanLattice D).sub_mem hm
    (projectedLatticeLift (standardEuclideanLattice D) W z).property using 1
  simp only [Submodule.coe_sub]
  abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CoefficientPolynomialLift
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedLiftCoefficient (a : (I → J → ℝ) × (Fin n → J → ℤ)) (j : J) :
    EuclideanSpace ℝ D :=
  mixedRealPoint W b o (fun i => a.1 i j, fun i => (a.2 i j : ℝ) / basisAxisScale b i)

omit [Fintype J] in
theorem mixedLiftCoefficient_eq (a : (I → J → ℝ) × (Fin n → J → ℤ)) (j : J) :
    mixedLiftCoefficient W b o a j = normalizedLatticePoint W b
      (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J a j)) := rfl

noncomputable def mixedLiftPolynomial (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (d : D) : MvPolynomial V ℝ :=
  monomialArrayPolynomial e (fun j => mixedLiftCoefficient W b o a j d)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientRowPolynomial_constant (z : ∀ j, U j) (j : Fin m) (i : J j) :
    coefficientRowPolynomial U (constantCoefficientArray (K := K) U (fun s => z s.1)) j i =
      MvPolynomial.C ((z j).val i) := by
  classical
  unfold coefficientRowPolynomial monomialArrayPolynomial
  rw [Finset.sum_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp [constantCoefficientArray, zeroCoefficientExponent]
  · intro d _ hd
    have hzero : d.val ≠ 0 := fun h => hd (Subtype.ext h)
    simp [constantCoefficientArray, hzero]
  · simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

noncomputable def normalizedCoveredChart (p : (W × (Fin n → ℤ)) × (R → ZMod d)) :
    W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  normalizedCoverLift W b hb d p.1 +
    (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
      bW d (Nat.pos_of_ne_zero (NeZero.ne d)) p.2).val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

noncomputable def coveredJetChart : CoveredJetChartSource U O B n d → EuclideanJetLayers U O :=
  fun x j t => normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d (x j t)

def coveredJetSourceRegion (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    Set (CoveredJetChartSource U O B n d) :=
  Set.univ.pi (fun j => Set.univ.pi (fun t =>
    (normalizedLatticePoint (euclideanSubspace (U j)) (b j) ⁻¹' Ω j t) ×ˢ Set.univ))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

theorem single_direction_derivative [DecidableEq σ] (i : σ)
    (P : MvPolynomial σ ℚ) : scalarDirectionalDerivative (Pi.single i 1) P = pderiv i P := by
  classical
  simp [scalarDirectionalDerivative_apply, Pi.single_apply]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonStrideCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem commonStrideBox_card {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) {m : ℕ} (hm : 0 < m) (H : I → ℕ) :
    (commonStrideBox c m H).card = ∏ i, H i := by
  simp only [commonStrideBox, Fintype.card_piFinset, card_integerProgressionSupport _ _ _ hm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WordTruncationBracket
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem freeLieTruncation_zero (p : FreeLieAlgebra ℚ X) : freeLieTruncation 0 p = 0 := by
  apply freeLieWordExpansion_injective
  rw [freeLieTruncation_expansion, map_zero]
  apply (wordTruncation_eq_zero_iff _ _).mpr
  intro w hw
  have : 0 < w.length := by change 0 < w.tail.length + 1; omega
  omega

theorem freeLie_lowerCentralSeries_truncation_zero (s : ℕ) (p : FreeLieAlgebra ℚ X)
    (hp : p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s) :
    freeLieTruncation s p = 0 := by
  induction s generalizing p with
  | zero => exact freeLieTruncation_zero p
  | succ s ih =>
    have hsub : (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) (s + 1)).toSubmodule ≤
        LinearMap.ker (freeLieTruncation (X := X) (s + 1)) := by
      rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
      apply Submodule.span_le.mpr
      rintro z ⟨x, y, rfl⟩
      change freeLieTruncation (s + 1) ⁅x.val, y.val⁆ = 0
      apply freeLieWordExpansion_injective
      rw [freeLieTruncation_expansion, map_zero, LieHom.map_lie]
      apply wordTruncation_succ_lie_eq_zero
      rw [← freeLieTruncation_expansion, ih y.val y.property, map_zero]
    exact hsub hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem narrowTrimmedSpatialWidths_pos {G J X : Type*}
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (z : Option (G ⊕ J) × X) :
    0 < narrowTrimmedSpatialWidths W τ ξ N z := by
  rcases z with ⟨_ | (g | j), x⟩
  · exact trimmedSpatialWidths_pos hW hτ N hN _
  · exact trimmedSpatialWidths_pos hW hτ N hN _
  · exact mul_pos hξ (trimmedSpatialWidths_pos hW hτ N hN _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerVectorFreimanEmbedding
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped BigOperators Pointwise

theorem exists_integer_freiman_embedding {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) (s : ℕ) :
    ∃ f : (I → ℤ) →+ ℤ, IsAddFreimanIso s (A : Set _)
      (A.image f : Set ℤ) f := by
  classical
  obtain ⟨f, hf⟩ := exists_integer_vector_embedding (A ∪ s • A)
  refine ⟨f, isAddFreimanIso_of_injOn_iterated_sums f A s ?_ ?_⟩
  · exact hf.mono (fun _ hx => Finset.mem_union_left _ hx)
  · exact hf.mono (fun _ hx => Finset.mem_union_right _ hx)

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedAntisymmetricBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_mixed_tuple {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin (n + 2) → X) → ℂ) :
    (𝔼 x, F x) = 𝔼 u : Fin n → X, 𝔼 h, 𝔼 m, F (Fin.cons h (Fin.cons m u)) := by
  simp_rw [expect_dependent_fin_cons]
  calc
    _ = 𝔼 h, 𝔼 u : Fin n → X, 𝔼 m, F (Fin.cons h (Fin.cons m u)) :=
      Finset.expect_congr rfl (fun _ _ => Finset.expect_comm _ _ _)
    _ = _ := Finset.expect_comm _ _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeSignalAlgebra
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedCubeInput {d : ℕ} (ω : Fin d → Bool) (x : Fin (d + 2) → ℤ) : Fin 2 → ℤ :=
  correlationInput (x 0) (x 1 + cubeShift (fun j => x j.succ.succ) ω)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedCubeObservable {J : Type*} {d : ℕ} (f : J → (Fin 2 → ℤ) → ℂ)
    (a : (Fin d → Bool) → J) (x : Fin (d + 2) → ℤ) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (f (a ω) (mixedCubeInput ω x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.HomogeneousLieSpan
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

def homogeneousLieSpan (v : I → L) (g : I → σ →₀ ℕ) (S : Set (σ →₀ ℕ)) : Submodule ℚ L :=
  Submodule.span ℚ {x | ∃ a : FreeMagma I, lieTreeMultidegree g a ∈ S ∧ lieTreeEval v a = x}

theorem homogeneousLieSpan_mono (v : I → L) (g : I → σ →₀ ℕ)
    {S T : Set (σ →₀ ℕ)} (hST : S ⊆ T) : homogeneousLieSpan v g S ≤ homogeneousLieSpan v g T := by
  apply Submodule.span_mono
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, hST ha, rfl⟩

@[simp] theorem homogeneousLieSpan_empty (v : I → L) (g : I → σ →₀ ℕ) :
    homogeneousLieSpan v g ∅ = ⊥ := by
  simp [homogeneousLieSpan]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentIntegralModel
namespace OAI

section

namespace Erdos3

open Module

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L]

noncomputable def finiteMarkedLieValues (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) : Finset L := by
  classical
  exact ((finiteLieTrees I s).filter (fun a => d ≤ lieTreeWeight w a ∧
    k ≤ lieTreeMarkedCount marked a ∧ l ≤ a.length)).image (lieTreeEval v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CubeSignalCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanWeight_true (d : ℕ) : booleanWeight (fun _ : Fin d => true) = d := by
  simp [booleanWeight]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSeparatedSumIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_fullCube_proper_factors {G : Type*} [AddCommGroup G] {d : ℕ}
    (f : G → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    ∃ A : Fin (d + 3) → (Fin (d + 3) → G) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, fullCubeSignal f x = conjugationPower (d + 2) (f (∑ i, x i)) * ∏ i, A i x := by
  classical
  let S : Finset (Fin (d + 2) → Bool) := Finset.univ.erase (fun _ => true)
  let F (ω : S) (x : Fin (d + 3) → G) := conjugationPower (booleanWeight ω.val)
    (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω.val))
  have hF : ∀ ω x, ‖F ω x‖ ≤ 1 := by
    intro ω x
    exact (conjugationPower_norm _ _).trans_le (hf _)
  have hFi : ∀ ω, ∃ i, ∀ x y, (∀ k, k ≠ i → x k = y k) → F ω x = F ω y := by
    intro ω
    obtain ⟨j, hj⟩ := exists_false_of_ne_true (Finset.mem_erase.mp ω.property).1
    refine ⟨(1 : Fin (d + 3)).succAbove j, ?_⟩
    intro x y hxy
    exact congrArg (fun z => conjugationPower (booleanWeight ω.val) (f z))
      (fullCube_input_independent ω.val j hj x y hxy)
  obtain ⟨A, hA, hAi, hprod⟩ := exists_missing_coordinate_product_factors F hF hFi
  refine ⟨A, hA, hAi, ?_⟩
  intro x
  have hsum : x 1 + (∑ j : Fin (d + 2), x ((1 : Fin (d + 3)).succAbove j)) = ∑ i, x i :=
    (Fin.sum_univ_succAbove x 1).symm
  calc
    fullCubeSignal f x = conjugationPower (d + 2) (f (∑ i, x i)) *
        ∏ ω ∈ S, conjugationPower (booleanWeight ω)
          (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω)) := by
      unfold fullCubeSignal
      rw [cubeProduct_eq_boolean_product]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun ω => conjugationPower (booleanWeight ω)
          (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω)))
        (Finset.mem_univ (fun _ : Fin (d + 2) => true))]
      rw [booleanWeight_true, cubeShift_true, hsum]
    _ = _ := by
      rw [hprod]
      congr 1
      exact (Finset.prod_coe_sort S (fun ω => conjugationPower (booleanWeight ω)
        (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω)))).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedProfileCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedProfileFromCoordinates {d : ℕ} {α : Type*} (x : Fin (d + 3) → α) :
    (Fin (d + 1) → α) × α :=
  (Fin.cons (x 0) (fun j => x j.succ.succ.succ), x 2)

def mixedProfileEquiv (d : ℕ) (α : Type*) :
    (((Fin (d + 1) → α) × α) × α) ≃ (Fin (d + 3) → α) where
  toFun t := Fin.cons (t.1.1 0) (Fin.cons t.2 (Fin.cons t.1.2 (Fin.tail t.1.1)))
  invFun x := (mixedProfileFromCoordinates x, x 1)
  left_inv := by
    rintro ⟨⟨t, u⟩, n⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        exact Fin.cases rfl (fun _ => rfl) i
      · rfl
    · rfl
  right_inv := by
    intro x
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun _ => rfl) k

theorem mixedProfileFromCoordinates_independent {d : ℕ} {α : Type*}
    (x y : Fin (d + 3) → α) (h : ∀ k, k ≠ 1 → x k = y k) :
    mixedProfileFromCoordinates x = mixedProfileFromCoordinates y := by
  have h1 : (1 : Fin (d + 3)).val = 1 := Fin.val_one (d + 1)
  have h2 : (2 : Fin (d + 3)).val = 2 := by
    change 2 % (d + 3) = 2
    exact Nat.mod_eq_of_lt (by omega)
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h 0 (by
        intro e
        have he := congrArg Fin.val e
        norm_num only [Fin.val_zero, h1] at he)
    · exact h j.succ.succ.succ (by
        intro e
        have he := congrArg Fin.val e
        simp only [Fin.val_succ, h1] at he
        omega)
  · exact h 2 (by
      intro e
      have he := congrArg Fin.val e
      norm_num only [h2, h1] at he)

theorem mixedProfile_average {d : ℕ} {α : Type*} [Fintype α]
    (F : (Fin (d + 3) → α) → ℂ) :
    (𝔼 x, F x) = 𝔼 t : (Fin (d + 1) → α) × α, 𝔼 n : α,
      F (mixedProfileEquiv d α (t, n)) := by
  calc
    _ = 𝔼 t : ((Fin (d + 1) → α) × α) × α, F (mixedProfileEquiv d α t) :=
      (Fintype.expect_equiv (mixedProfileEquiv d α) _ F (fun _ => rfl)).symm
    _ = _ := expect_prod_split _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardParameterPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | n + 1 =>
    let P := preparedFiniteForwardParameterPolynomial A stageCountConstant n
    let work := (P + Polynomial.C A) ^ A
    let cap := (4 * P + 4 * work + 16 + Polynomial.C A) ^ A
    let count := P + cap
    let branch := Polynomial.X * cap + (count + 8) ^ 8 +
      (count + Polynomial.C (stageCountConstant n)) ^ stageCountConstant n
    P + cap + branch + 1

@[simp] theorem preparedFiniteForwardParameterPolynomial_zero (A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    preparedFiniteForwardParameterPolynomial A stageCountConstant 0 = Polynomial.X := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R : Type*} [CommRing R]

noncomputable def lowTaggedRestrictionVariables (k : ℕ) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R := by
  classical
  exact Sum.elim (fun x => MvPolynomial.X (Sum.inl x))
    (fun a => if h : a.1.val + 1 ≤ k then
      MvPolynomial.X (Sum.inr (lowTaggedSlot J k a.1 h a.2)) else 0)

noncomputable def lowTaggedRestrict (k : ℕ) :
    MvPolynomial (X ⊕ (Σ j, J j)) R →ₐ[R]
      MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R :=
  aeval (lowTaggedRestrictionVariables (X := X) (R := R) J k)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientIntegerFloorRemainder
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientIntegerFloorPolynomial
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (j : Fin m) (i : J j) : MvPolynomial K ℤ :=
  integerMonomialArrayPolynomial Subtype.val
    (fun d : BoundedCoefficientExponent K (j.val + 1) =>
      ⌊(c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i⌋)

theorem coefficientIntegerFloorPolynomial_degree
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (j : Fin m) (i : J j) :
    (coefficientIntegerFloorPolynomial U b o a c j i).totalDegree ≤ j.val + 1 :=
  integerMonomialArrayPolynomial_degree Subtype.val _ (fun d => d.property)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X R : Type*} [Fintype K] [CommRing R] [Nontrivial R]

noncomputable def affineFramePolynomial (frame : Option K → X → R) (i : X) : MvPolynomial K R :=
  MvPolynomial.C (frame none i) + ∑ k, MvPolynomial.C (frame (some k) i) * MvPolynomial.X k

theorem affineFramePolynomial_degree (frame : Option K → X → R) (i : X) :
    (affineFramePolynomial frame i).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl])

omit [Nontrivial R] in
@[simp] theorem affineFramePolynomial_eval (frame : Option K → X → R) (y : K → R) (i : X) :
    MvPolynomial.aeval y (affineFramePolynomial frame i) =
      frame none i + ∑ k, frame (some k) i * y k := by
  simp [affineFramePolynomial]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientDeckResidueMask
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

abbrev CoefficientChartResidues (K : Type*) {m : ℕ} (n : Fin m → ℕ) (E : Fin m → Type*) (q : ℕ) :=
  ∀ j, BoundedCoefficientExponent K (j.val + 1) → (Fin (n j) ⊕ E j) → ZMod q

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K A : Type*} {m : ℕ} {E : Fin m → Type*} {N : ℕ}

abbrev CoefficientDeckScalarIndex (K : Type*) (E : Fin m → Type*) :=
  Σ j : Fin m, BoundedCoefficientExponent K (j.val + 1) × E j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
namespace OAI

universe u

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct NNReal

variable {X : Type*} {J : Fin 0 → Type*}

noncomputable def zeroLayerSpatialChart : X ⊕ Sigma J → MvPolynomial X ℝ :=
  Sum.elim MvPolynomial.X (fun a => Fin.elim0 a.1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformPhysicalVisitBounds
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def physicalResidueMean {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ) : ℂ :=
  𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u,
    f (fun i => (x i).val)

universe u v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedSpatialKernelSliceDensity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)

variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

noncomputable def fixedSpatialKernelDensity : (X → ℝ) → ℝ :=
  fixedSpatialBlockDensity (unitBoxMeasure T) (fun x => z (none,x))
    (fixedSpatialKernelRest e W L z)
    (fixedSpatialKernelBlockEquiv e W L z false h0)
    (fixedSpatialKernelBlockEquiv e W L z true h1)

end Erdos3

end

end OAI
end


