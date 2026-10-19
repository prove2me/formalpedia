-- Prove2me | Definitions.Def_OAIE3v2B117
-- name    : OAIE3v2B117
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:36:19.612791+00:00
-- url     : https://prove2.me/theorems/233c389c-d808-47eb-9417-17c80062101c
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 119 of 311
-- statement:
--   Definitions bundle 119 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B103`, `OAIE3v2B104`, `OAIE3v2B105` of this split.
--
--   Modules: `Estimates/CoefficientRowEvaluation.lean`, `Estimates/ControlledProductReconstruction.lean`, `Estimates/FreeWeightedLayerBounds.lean`, `Estimates/FreeWeightedModelBounds.lean`, `Estimates/IndexedComparableScalarGeometryData.lean`, `Estimates/PolarizedCoefficientPermutation.lean`, `Estimates/RationalTagConstraintSpaces.lean`, `Estimates/RealProjectedCoefficientLift.lean`, `Estimates/RealSymbolRepresentativeSplitting.lean`, `Estimates/ScalarDominatedSlack.lean`, `FixedDensity/AdaptiveCoarseTargetRegularity.lean`, `FixedDensity/BoundaryBernoulli.lean`, `FixedDensity/CoarseAtomBridge.lean`, `FixedDensity/CoarseOrderedRemoval.lean`, `FixedDensity/CoarseTargetRegularity.lean`, `FixedDensity/Conclusions.lean`, `FixedDensity/ConfigurationWeightedDefect.lean`, `FixedDensity/GeneratorCells.lean`, `FixedDensity/HypergraphBundleFrozenUniformity.lean`, `FixedDensity/HypergraphBundleSourceGoodnessBridge.lean`, `FixedDensity/OrderedAtomEnergy.lean`, `FixedDensity/OrderedBoundaryPartition.lean`, `FixedDensity/OrderedConfigurationCounting.lean`, `FixedDensity/OrderedFullBoundary.lean`, `FixedDensity/OrderedGoodAtoms.lean`, `FixedDensity/OrderedPatternPartition.lean`, `FixedDensity/OrderedRemovalAssembly.lean`, `FixedDensity/SourceFullBundleRemovalParameters.lean`, `FixedDensity/SourceFullCoarseTargetRegularity.lean`, `FixedDensity/SourceFullOrderedRemoval.lean`, `FixedDensity/StrongOrderedComplexRegularity.lean`, `Fourier/ProductFrequencyKernel.lean`, `Fourier/UnbalancedBohrShape.lean`, `Geometry/EmbeddingCoordinateHeight.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Lattices/AlgebraicMajorWeightedAffineTopPullback.lean`, `Lattices/CenteredAffineCoefficient.lean`, `Linear/CommonFreeSpanBounds.lean`, `Linear/FreeLieTruncationKernel.lean`, `Linear/FreeWeightedRankGenerators.lean`, `Linear/HomogeneousLieSpan.lean`, `Linear/RankPreparationSizes.lean`, `Nilpotent/FreeNilpotentLieAlgebra.lean`, `Nilpotent/FreeNilpotentSourceBounds.lean`, `Nilpotent/FreeWeightedNilpotentLieAlgebra.lean`, `Polynomial/CRTPolynomialInputAffineLaw.lean`, `Polynomial/RealAdaptedPolynomialGroup.lean`, `Probability/IntervalDivisorProbability.lean`, `Probability/NormalizedExpectationWeights.lean`, `Probability/RelativeFullSliceLaw.lean`, `Probability/ScalarCubeHistogramMeasure.lean`, `Sampling/AllocatedExternalCandidateSamplerFamily.lean`, `Sampling/SamplingRankProjectedContainment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102
import Definitions.Def_OAIE3v2B103
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B105

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3

theorem HasLayerSamplingRank.mono {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R S : ℝ} {W : Submodule ℝ (J → ℝ)}
    {P : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h T S W P) (hRS : R ≤ S)
    (hT : ∀ i, 0 < T i) : HasLayerSamplingRank h T R W P := by
  intro a ha hw happ
  exact hrank a (fun j => (ha j).trans hRS) hw (happ.mono hRS hT)

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

theorem homogeneousComponent_polynomialTranslate (h : ℕ) (r : U → R)
    (P : MvPolynomial U R) (hP : P.totalDegree ≤ h) :
    homogeneousComponent h (polynomialTranslate r P) = homogeneousComponent h P := by
  have hp : VectorPolynomial.DegreeLE (1 : U → ℕ) h (P ⊗ₜ[R] (1 : R)) := by
    intro α hα
    have hz : P.coeff α = 0 := coeff_eq_zero_of_totalDegree_lt (hP.trans_lt (by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply,
        smul_eq_mul, mul_one] using hα))
    simp only [VectorPolynomial.coefficients_tmul, hz, zero_smul]
  have ht := VectorPolynomial.homogeneousPart_translate r (P ⊗ₜ[R] (1 : R)) hp
  ext α
  have hc := congrArg (fun p => VectorPolynomial.coefficients p α) ht
  simpa only [VectorPolynomial.translate_tmul, VectorPolynomial.homogeneousPart_tmul,
    VectorPolynomial.coefficients_tmul, smul_eq_mul, mul_one] using hc

theorem residueAffinePolynomial_homogeneousComponent (q h : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ h) :
    homogeneousComponent h (residueAffinePolynomial q r P) =
      C ((q : ℝ) ^ h) * homogeneousComponent h P := by
  rw [residueAffinePolynomial_eq_dilation_translate,
    homogeneousComponent_polynomial_dilation, homogeneousComponent_polynomialTranslate h _ P hP]

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

theorem coefficientRowPolynomial_eval (c : CoefficientArray (K := K) U)
    (j : Fin m) (i : J j) (x : K → ℝ) :
    MvPolynomial.eval x (coefficientRowPolynomial U c j i) =
      eval x (boundedArrayPolynomial (W := J j → ℝ) (j.val + 1) (fun d => (c ⟨j, d⟩).val)) i := by
  simp [coefficientRowPolynomial, monomialArrayPolynomial, boundedArrayPolynomial,
    eval_monomial, MvPolynomial.eval_monomial, Finset.sum_apply, mul_comm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledProductReconstruction
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)]
  {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realification_liePiEval_liePiMap (φ : ∀ a, L →ₗ⁅ℚ⁆ M a)
    (x : ℝ ⊗[ℚ] L) (a : α) :
    realificationLieHom (liePiEval a) (realificationLieHom (liePiMap φ) x) =
      realificationLieHom (φ a) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Fintype α] {κ : α → Type*}

theorem realification_pi_basis_repr (f : ∀ a, Basis (κ a) ℚ (M a))
    (x : ℝ ⊗[ℚ] (∀ a, M a)) (a : α) (i : κ a) :
    ((Pi.basis f).baseChange ℝ).repr x ⟨a, i⟩ =
      ((f a).baseChange ℝ).repr (realificationLieHom (liePiEval a) x) i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul,
      Pi.basis_repr, liePiEval_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolRepresentativeSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

variable (w : σ → ℕ)

theorem realSymbolRepresentative_coefficient_splitting (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) :
    coefficients (F.realSymbolRepresentative b ω hlayers w x) α =
      (F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ
        (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  rw [F.gradedBasisSplitting_real_coordinate]
  by_cases h : Finsupp.weight w α = ω i
  · exact (F.realSymbolRepresentative_coefficient b ω hlayers w x ⟨(α, i), h⟩).trans
      (F.realGradedSymbolPolynomial_coordinate b ω hlayers w x ⟨(α, i), h⟩).symm
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w x α i h,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w x α i h]

theorem realSymbolRepresentative_eq_map (x : F.RealPolynomialSymbol w) :
    F.realSymbolRepresentative b ω hlayers w x =
      VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ).restrictScalars ℚ)
        (F.realGradedSymbolPolynomial b ω hlayers w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact F.realSymbolRepresentative_coefficient_splitting b ω hlayers w x α

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem realFilteredPolynomialMap_polynomial
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    G.realAdaptedPolynomialMap w ((F.filteredPolynomialMap G φ hφ w).toLinearMap.baseChange ℝ x) =
      VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
        (F.realAdaptedPolynomialMap w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r p =>
    apply coefficients.injective
    ext α
    rw [LinearMap.baseChange_tmul, G.realAdaptedPolynomialMap_coefficient_tmul,
      coefficients_map, F.realAdaptedPolynomialMap_coefficient_tmul]
    change r ⊗ₜ[ℚ] coefficients (F.filteredPolynomialMap G φ hφ w p).val α =
      r ⊗ₜ[ℚ] φ (coefficients p.val α)
    rw [F.filteredPolynomialMap_coefficient]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def constantMultidegreeOrbit (a : F.Group) : F.PolynomialOrbit :=
  ⟨⟨monomial 0 a.coord⟩, F.monomial_mem_adaptedSubmodule 0 (by
    change a.coord ∈ F.layer 0
    rw [F.zero_eq_top]
    trivial)⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem adapted_rationalDilation (r : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) : F.Adapted (weightedDilation (fun _ : σ => 1) r p) := by
  intro a
  rw [coefficients_weightedDilation]
  exact (F.layer _).smul_mem _ (hp a)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmbeddingCoordinateHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem embedding_basis_coordinate_height {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L) (hφ : Function.Injective φ)
    {H : ℕ} (hH : 1 ≤ H) (hB : ∀ i j, RationalHeightLE (e.repr (φ (b j)) i) H)
    (x : M) {K : ℕ} (hx : ∀ i, RationalHeightLE (e.repr (φ x) i) K) (j : κ) :
    RationalHeightLE (b.repr x j)
      ((Fintype.card ι + 1) * (rationalSolveHeight (Fintype.card κ) H * K) ^ Fintype.card ι) := by
  classical
  let B := LinearMap.toMatrix b e φ
  obtain ⟨P, hPB, hP⟩ := exists_bounded_rational_left_inverse B
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ hφ)) hH
    (by simpa only [B, LinearMap.toMatrix_apply] using hB)
  have hretract : P *ᵥ e.repr (φ x) = b.repr x := by
    rw [← LinearMap.toMatrix_mulVec_repr b e φ x, Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec]
  rw [← congrFun hretract j]
  exact rationalHeightLE_sum (fun i => P j i * e.repr (φ x) i)
    (fun i => (hP j i).mul (hx i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeNilpotentLieAlgebra
namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

namespace FreeNilpotentLieAlgebra

theorem mk_eq_zero (x : FreeLieAlgebra ℚ X) :
    mk X s x = 0 ↔ x ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s :=
  lieQuotientMap_eq_zero _ x

theorem lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ (FreeNilpotentLieAlgebra X s) (FreeNilpotentLieAlgebra X s) s = ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq s (mk_surjective X s), LieIdeal.map_eq_bot_iff]
  intro x hx
  exact (mk_eq_zero X s x).mpr hx

variable {X s} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lift_mk (f : X → L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (x : FreeLieAlgebra ℚ X) : lift f hnil (mk X s x) = FreeLieAlgebra.lift ℚ f x := rfl

theorem hom_ext {f g : FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ L}
    (h : ∀ x, f (of X s x) = g (of X s x)) : f = g := by
  have heq : f.comp (mk X s) = g.comp (mk X s) := FreeLieAlgebra.hom_ext h
  apply LieHom.ext
  intro x
  obtain ⟨y, rfl⟩ := mk_surjective X s x
  exact LieHom.congr_fun heq y

theorem mk_truncation (x : FreeLieAlgebra ℚ X) :
    mk X s (freeLieTruncation s x) = mk X s x := by
  have h := lift_freeLieTruncation ((mk X s) ∘ FreeLieAlgebra.of ℚ)
    (lowerCentralSeries_eq_bot X s) x
  simpa only [FreeLieAlgebra.lift_comp_of] using h

end FreeNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FreeLieTruncationKernel
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem freeLieTruncation_eq_zero_iff (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieTruncation s p = 0 ↔
      p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s := by
  constructor
  · intro hp
    apply (FreeNilpotentLieAlgebra.mk_eq_zero X s p).mp
    rw [← FreeNilpotentLieAlgebra.mk_truncation p, hp, map_zero]
  · exact freeLie_lowerCentralSeries_truncation_zero s p

theorem freeLie_lowerCentralSeries_iff_low_coeff_zero (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s ↔
      ∀ w, w.length ≤ s → (freeLieWordExpansion p).coeff w = 0 := by
  rw [← freeLieTruncation_eq_zero_iff, ← wordTruncation_eq_zero_iff]
  constructor
  · intro hp
    rw [← freeLieTruncation_expansion, hp, map_zero]
  · intro hp
    apply freeLieWordExpansion_injective
    rw [freeLieTruncation_expansion, hp, map_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeNilpotentSourceBounds
namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

theorem freeLieBoundedCoordinates_eq_zero_iff (p : FreeLieAlgebra ℚ X) :
    freeLieBoundedCoordinates X s p = 0 ↔
      p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s := by
  rw [freeLie_lowerCentralSeries_iff_low_coeff_zero]
  constructor
  · intro hp w hw
    exact congrFun hp ⟨w, hw⟩
  · intro hp
    ext w
    exact hp w.val w.property

namespace FreeNilpotentLieAlgebra

noncomputable def coordinates : FreeNilpotentLieAlgebra X s →ₗ[ℚ] (BoundedFreeWord X s → ℚ) :=
  (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s).toSubmodule.liftQ
    (freeLieBoundedCoordinates X s)
    (fun p hp => (freeLieBoundedCoordinates_eq_zero_iff X s p).mpr hp)

theorem coordinates_injective : Function.Injective (coordinates X s) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := mk_surjective X s x
  obtain ⟨b, rfl⟩ := mk_surjective X s y
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (mk_eq_zero X s (a - b)).mpr
  apply (freeLieBoundedCoordinates_eq_zero_iff X s (a - b)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

instance finite [Fintype X] : Module.Finite ℚ (FreeNilpotentLieAlgebra X s) :=
  Module.Finite.of_injective (coordinates X s) (coordinates_injective X s)

theorem finrank_le [Fintype X] :
    Module.finrank ℚ (FreeNilpotentLieAlgebra X s) ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  have h := LinearMap.finrank_le_finrank_of_injective (coordinates_injective X s)
  calc
    _ ≤ Module.finrank ℚ (BoundedFreeWord X s → ℚ) := h
    _ = Fintype.card (BoundedFreeWord X s) := by simp
    _ ≤ _ := boundedFreeWord_card_le

end FreeNilpotentLieAlgebra

end Erdos3

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

variable (X : Type*) (s : ℕ)

theorem mk_tree_eq_zero_of_length_gt (a : FreeMagma X) (ha : s < a.length) :
    mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a) = 0 := by
  apply (mk_eq_zero X s _).mpr
  apply (freeLie_lowerCentralSeries_iff_low_coeff_zero s _).mpr
  intro w hw
  rw [freeLieWordExpansion_tree]
  by_contra h
  have he := commutatorTree_homogeneous a w h
  omega

noncomputable def treeGenerators [Fintype X] : Finset (FreeNilpotentLieAlgebra X s) := by
  classical
  exact ((finiteLieTrees X s).filter (fun a => a.length ≤ s)).image
    (fun a => mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a))

theorem treeGenerators_span [Fintype X] :
    Submodule.span ℚ (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s)) = ⊤ := by
  classical
  apply top_unique
  intro x _
  obtain ⟨p, rfl⟩ := mk_surjective X s x
  apply freeLie_linear_induction
    (fun p => mk X s p ∈ Submodule.span ℚ (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s)))
  · simpa only [map_zero] using (Submodule.zero_mem
      (Submodule.span ℚ (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s))))
  · intro p q hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · intro c p hp
    rw [map_smul]
    exact Submodule.smul_mem _ c hp
  · intro a
    by_cases ha : a.length ≤ s
    · apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨mem_finiteLieTrees_of_length_le X a ha, ha⟩, rfl⟩
    · rw [mk_tree_eq_zero_of_length_gt X s a (Nat.lt_of_not_ge ha)]
      exact Submodule.zero_mem _

theorem treeGenerators_card_le [Fintype X] :
    (treeGenerators X s).card ≤ (Fintype.card X + 2) ^ (3 ^ s) := by
  classical
  exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans
    (finiteLieTrees_card_le X s)

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s : ℕ)

theorem treeGenerators_coordinate_height (x : FreeNilpotentLieAlgebra X s)
    (hx : x ∈ treeGenerators X s) (w : BoundedFreeWord X s) :
    RationalHeightLE (coordinates X s x w) ((2 * (s + 1)) ^ s) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hlen := (Finset.mem_filter.mp ha).2
  change RationalHeightLE ((freeLieWordExpansion (lieTreeEval (FreeLieAlgebra.of ℚ) a)).coeff w.val) _
  rw [freeLieWordExpansion_tree]
  exact (commutatorTree_coefficient_height s a w.val w.property).mono
    (Nat.pow_le_pow_right (by omega) (by omega))

theorem treeGenerators_coordinate_integral (x : FreeNilpotentLieAlgebra X s)
    (hx : x ∈ treeGenerators X s) (w : BoundedFreeWord X s) :
    ∃ z : ℤ, (z : ℚ) = coordinates X s x w ∧ z.natAbs ≤ (2 * (s + 1)) ^ s := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hlen := (Finset.mem_filter.mp ha).2
  obtain ⟨z, hz, hbound⟩ := commutatorTree_coefficient_integral s a w.val w.property
  refine ⟨z, ?_, hbound.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩
  change (z : ℚ) = (freeLieWordExpansion (lieTreeEval (FreeLieAlgebra.of ℚ) a)).coeff w.val
  rwa [freeLieWordExpansion_tree]

theorem exists_bounded_tree_basis :
    ∃ b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
      (∀ i, b i ∈ treeGenerators X s) ∧
      (∀ i w, RationalHeightLE (coordinates X s (b i) w) ((2 * (s + 1)) ^ s)) ∧
      ∀ i w, ∃ z : ℤ, (z : ℚ) = coordinates X s (b i) w ∧ z.natAbs ≤ (2 * (s + 1)) ^ s := by
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s))
  rw [treeGenerators_span, finrank_top] at hex
  obtain ⟨v, hv, hspan, hlin⟩ := hex
  let b := Basis.mk hlin (le_of_eq hspan.symm)
  have hb (i) : b i ∈ treeGenerators X s := by
    simpa only [b, Basis.mk_apply, Finset.mem_coe] using hv i
  exact ⟨b, hb, fun i w => treeGenerators_coordinate_height X s (b i) (hb i) w,
    fun i w => treeGenerators_coordinate_integral X s (b i) (hb i) w⟩

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module

variable {X ι L : Type*} [Fintype X] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s H : ℕ} (e : Basis ι ℚ L) (f : X → L)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

theorem lift_treeGenerator_height
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hf : ∀ x i, RationalHeightLE (e.repr (f x) i) H)
    (x : FreeNilpotentLieAlgebra X s) (hx : x ∈ treeGenerators X s) (i : ι) :
    RationalHeightLE (e.repr (lift f hnil x) i) (lieTreeHeight (Fintype.card ι) H s) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  rw [lift_mk, lift_lieTreeEval]
  exact finiteLieTrees_coordinate_height e f hc hf s a (Finset.mem_filter.mp ha).1 i

theorem lift_basis_matrix_height
    (b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (hb : ∀ j, b j ∈ treeGenerators X s)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hf : ∀ x i, RationalHeightLE (e.repr (f x) i) H) (i j) :
    RationalHeightLE (LinearMap.toMatrix b e (lift f hnil).toLinearMap i j)
      (lieTreeHeight (Fintype.card ι) H s) := by
  rw [LinearMap.toMatrix_apply]
  exact lift_treeGenerator_height e f hnil hc hf (b j) (hb j) i

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module
attribute [local instance] LieRing.ofAssociativeRing

variable (X : Type*) [Fintype X] (s : ℕ)

theorem treeGenerators_lie_or_zero {x y : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ treeGenerators X s) (hy : y ∈ treeGenerators X s) :
    ⁅x, y⁆ = 0 ∨ ⁅x, y⁆ ∈ treeGenerators X s := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
  have he : ⁅mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a),
      mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) b)⁆ =
      mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) (a * b)) := (LieHom.map_lie _ _ _).symm
  rw [he]
  by_cases hab : (a * b).length ≤ s
  · right
    exact Finset.mem_image.mpr ⟨a * b, Finset.mem_filter.mpr
      ⟨mem_finiteLieTrees_of_length_le X (a * b) hab, hab⟩, rfl⟩
  · exact Or.inl (mk_tree_eq_zero_of_length_gt X s (a * b) (Nat.lt_of_not_ge hab))

theorem treeGenerators_lie_coordinate_height {x y : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ treeGenerators X s) (hy : y ∈ treeGenerators X s) (w : BoundedFreeWord X s) :
    RationalHeightLE (coordinates X s ⁅x, y⁆ w) ((2 * (s + 1)) ^ s) := by
  rcases treeGenerators_lie_or_zero X s hx hy with hzero | hmem
  · rw [hzero, map_zero, Pi.zero_apply]
    have hH : 1 ≤ (2 * (s + 1)) ^ s := one_le_pow₀ (by omega)
    simpa only [RationalHeightLE, Rat.num_zero, Int.natAbs_zero, Rat.den_zero, Nat.zero_le,
      true_and] using hH
  · exact treeGenerators_coordinate_height X s _ hmem w

theorem exists_bounded_structure_basis :
    let n := Fintype.card (BoundedFreeWord X s)
    let d := finrank ℚ (FreeNilpotentLieAlgebra X s)
    let H := (2 * (s + 1)) ^ s
    ∃ b : Basis (Fin d) ℚ (FreeNilpotentLieAlgebra X s),
      (∀ i, b i ∈ treeGenerators X s) ∧
      (∀ i w, RationalHeightLE (coordinates X s (b i) w) H) ∧
      ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
        ((n + 1) * (rationalSolveHeight d H * H) ^ n) := by
  dsimp only
  obtain ⟨b, hb, hcoord, _⟩ := exists_bounded_tree_basis X s
  refine ⟨b, hb, hcoord, ?_⟩
  intro i j k
  have h := embedding_basis_coordinate_height b (Pi.basisFun ℚ (BoundedFreeWord X s))
    (coordinates X s) (coordinates_injective X s)
    (show 1 ≤ (2 * (s + 1)) ^ s from one_le_pow₀ (by omega))
    (fun w l => by simpa only [Pi.basisFun_repr] using hcoord l w)
    ⁅b i, b j⁆ (fun w => by simpa only [Pi.basisFun_repr] using
      treeGenerators_lie_coordinate_height X s (hb i) (hb j) w) k
  simpa only [Fintype.card_fin, lieStructureConstants] using h

end Erdos3.FreeNilpotentLieAlgebra

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedLayerBounds
namespace OAI

section

namespace Erdos3.FreeNilpotentLieAlgebra

variable (X : Type*) (s : ℕ)

variable [Fintype X]

noncomputable def weightedLayerGenerators (w : X → ℕ) (d : ℕ) : Finset (FreeNilpotentLieAlgebra X s) := by
  classical
  exact ((finiteLieTrees X s).filter (fun a => a.length ≤ s ∧ d ≤ lieTreeWeight w a)).image
    (fun a => mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a))

theorem weightedLayer_eq_span (w : X → ℕ) (d : ℕ) :
    weightedLayer X s w d = Submodule.span ℚ (weightedLayerGenerators X s w d : Set _) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, ha, rfl⟩
    by_cases hlen : a.length ≤ s
    · apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨mem_finiteLieTrees_of_length_le X a hlen, hlen, ha⟩, mk_lieTreeEval X s a⟩
    · rw [← mk_lieTreeEval, mk_tree_eq_zero_of_length_gt X s a (Nat.lt_of_not_ge hlen)]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact Submodule.subset_span ⟨a, (Finset.mem_filter.mp ha).2.2, (mk_lieTreeEval X s a).symm⟩

theorem weightedLayerGenerators_subset (w : X → ℕ) (d : ℕ) :
    weightedLayerGenerators X s w d ⊆ treeGenerators X s := by
  classical
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1⟩, rfl⟩

theorem weightedLayerGenerators_card_le (w : X → ℕ) (d : ℕ) :
    (weightedLayerGenerators X s w d).card ≤ (Fintype.card X + 2) ^ (3 ^ s) :=
  (Finset.card_le_card (weightedLayerGenerators_subset X s w d)).trans (treeGenerators_card_le X s)

end Erdos3.FreeNilpotentLieAlgebra

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeWeightedNilpotentLieAlgebra
namespace OAI

section

namespace Erdos3

namespace FreeWeightedNilpotentLieAlgebra

variable (X : Type*) (s : ℕ) (w : X → ℕ)

instance finite [Fintype X] : Module.Finite ℚ (FreeWeightedNilpotentLieAlgebra X s w) :=
  Module.Finite.of_surjective (mk X s w).toLinearMap (mk_surjective X s w)

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedModelBounds
namespace OAI

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

noncomputable def layerGenerators (d : ℕ) : Finset (FreeWeightedNilpotentLieAlgebra X s w) := by
  classical
  exact (FreeNilpotentLieAlgebra.weightedLayerGenerators X s w d).image (mk X s w)

theorem layerGenerators_card_le (d : ℕ) :
    (layerGenerators X s w d).card ≤ (Fintype.card X + 2) ^ (3 ^ s) := by
  classical
  exact Finset.card_image_le.trans (FreeNilpotentLieAlgebra.weightedLayerGenerators_card_le X s w d)

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CenteredAffineCoefficient
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K V : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j)

noncomputable def centeredAffineCoefficientArray (center : ∀ j, U j) (frame : Option K → V → ℝ) :
    CoefficientArray (K := K) U :=
  affineSampleCoefficientArray U p hm frame - constantCoefficientArray U (fun s => center s.1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem siteLaw_mean {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X) (f : X → ℝ) :
    (p.siteLaw F).mean f = p.mean (fun z => 𝔼 t, f (F z t)) := by
  rw [siteLaw, fiberLaw_mean, mean_prod]
  simp_rw [uniform_mean]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem siteLaw_excessMass_le_of_test_bound {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (r : FiniteProbabilityWeights X) (F : Ω → T → X)
    {C ε : ℝ}
    (htest : ∀ (φ : X → ℝ), (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ t, p.mean (fun z => φ (F z t)) ≤ C * r.mean φ + ε) :
    r.excessMass (p.siteLaw F) C ≤ ε := by
  apply excessMass_le_of_mass_le
  intro A
  let φ : X → ℝ := fun x => if x ∈ A then 1 else 0
  have hφ : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1 := by intro x; dsimp only [φ]; split_ifs <;> norm_num
  have hmean : (p.siteLaw F).mean φ ≤ C * r.mean φ + ε := by
    rw [siteLaw_mean]
    simp_rw [← uniform_mean]
    rw [mean_comm]
    exact ((uniform T).mean_mono (htest φ hφ)).trans_eq ((uniform T).mean_const _)
  have hfilter : Finset.univ.filter (fun x => x ∈ A) = A := by ext x; simp
  simpa only [mean, φ, mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hfilter,
    mass] using hmean

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeFullSliceLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
namespace ResidueBoxSlice
variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q s d : ℕ}

noncomputable def fullSliceLaw (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i) :
    FiniteProbabilityWeights (integerBox N) := by
  letI : ∀ i, Nonempty (Fin (S.length i)) := fun i => ⟨⟨0,hlen i⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ i, Fin (S.length i))).finitePushforward S.fullSlicePointInIntegerBox

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeHistogramMeasure
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

noncomputable def imageMeasure {X Y : Type*} [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) : Measure Y :=
  ∑ x, ENNReal.ofReal (p.weight x) • Measure.dirac (F x)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedExpectationWeights
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def ofDensity {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (𝔼 x, w x) = 1) : FiniteProbabilityWeights X where
  weight x := (Fintype.card X : ℝ)⁻¹ * w x
  nonneg x := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hw x)
  total := by
    rw [← Finset.mul_sum]
    simpa only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm] using htotal

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ProductFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem piFrequency_apply (eta : ∀ i, L i →ₗ[ℚ] ℚ) (x : ∀ i, L i) :
    piFrequency eta x = ∑ i, eta i (x i) := by
  simp only [piFrequency, LinearMap.sum_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    liePiEval_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r) (A : ℕ → Submodule ℚ M)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1)

theorem mem_layerHorizontalImage (d : ℕ) (v : Fin 4 → F.HigherHorizontal d) :
    v ∈ F.layerHorizontalImage A φ hφ d ↔
      ∃ w : A d, F.layerHorizontalMap A φ hφ d w = v := Iff.rfl

theorem layerHorizontalImage_frequency {E : Type*} [AddCommGroup E] [Module ℚ E]
    (η : L →ₗ[ℚ] E) (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ u : I → M, (∀ i, u i ∈ A (d i)) →
      η (φ (lieTreeEval u a) 0) + η (φ (lieTreeEval u a) 1) -
        η (φ (lieTreeEval u a) 2) - η (φ (lieTreeEval u a) 3) = 0)
    (v : ∀ i, Fin 4 → F.HigherHorizontal (d i))
    (hv : ∀ i, v i ∈ F.layerHorizontalImage A φ hφ (d i)) :
    η (F.horizontalTreeValue d a (fun i => v i 0)) +
      η (F.horizontalTreeValue d a (fun i => v i 1)) -
      η (F.horizontalTreeValue d a (fun i => v i 2)) -
      η (F.horizontalTreeValue d a (fun i => v i 3)) = 0 := by
  classical
  have hlift (i : I) := (F.mem_layerHorizontalImage A φ hφ (d i) (v i)).mp (hv i)
  choose w hw using hlift
  let u (i : I) : M := (w i).val
  let lifted (k : Fin 4) (i : I) : F.layer (d i) 1 :=
    ⟨φ (u i) k, hφ (d i) (u i) (w i).property k⟩
  have hmap (k : Fin 4) :
      (fun i => F.higherHorizontalMk (d i) (lifted k i)) = (fun i => v i k) := by
    funext i
    exact congrFun (hw i) k
  have hvalue (k : Fin 4) : F.horizontalTreeValue d a (fun i => v i k) = φ (lieTreeEval u a) k := by
    rw [← hmap k]
    calc
      _ = lieTreeEval (fun i => φ (u i) k) a := F.horizontalTreeValue_mk d a hd hr (lifted k)
      _ = lieTreeEval (fun i => φ (u i)) a k := (lieTreeEval_pi _ a k).symm
      _ = _ := congrFun (lieTreeEval_hom φ u a) k
  rw [hvalue 0, hvalue 1, hvalue 2, hvalue 3]
  exact hker u (fun i => (w i).property)

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontalSymbolCoefficient_symbol (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α (F.polynomialSymbolMap w p) =
      G.layerHorizontalMap F.layer φ hφ (Finsupp.weight w α)
        ⟨coefficients p.val α, p.property α⟩ := by
  funext k
  change G.higherHorizontalSymbolCoefficient w α
    (F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
      (G.projectedComponent_mem_layer F φ hφ k) w (F.polynomialSymbolMap w p)) = _
  rw [F.filteredPolynomialSymbolMap_symbol, G.higherHorizontalSymbolCoefficient_map]
  apply congrArg (G.higherHorizontalMk (Finsupp.weight w α))
  apply Subtype.ext
  exact F.filteredPolynomialMap_coefficient G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) w p α

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem real_projectedHorizontalSymbolCoefficient_component (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.PolynomialSymbol w) (k : Fin 4) :
    (LinearMap.proj k : (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) →ₗ[ℚ]
      G.HigherHorizontal (Finsupp.weight w α)).baseChange ℝ
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ x) =
      (G.higherHorizontalSymbolCoefficient w α).baseChange ℝ
        ((G.projectedComponentSymbolMap F φ hφ w k).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r)

variable (F : NilpotentLieFiltration M t) (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedLayerCoefficient_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    G.fourHorizontalMap (Finsupp.weight w α) (G.projectedLayerCoefficient F φ hφ w α p) =
      G.projectedHorizontalSymbolCoefficient F φ hφ w α (F.polynomialSymbolMap w p) := by
  rw [G.projectedHorizontalSymbolCoefficient_symbol]
  rfl

theorem projectedLayerCoefficient_tensor_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (G.fourHorizontalMap (Finsupp.weight w α)).baseChange ℝ
        ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x) =
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
        (F.realExtendedSymbolMap w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    change (G.fourHorizontalMap (Finsupp.weight w α)).baseChange ℝ
      ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ (a ⊗ₜ[ℚ] p)) =
        (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
          (a ⊗ₜ[ℚ] F.polynomialSymbolMap w p)
    simp only [LinearMap.baseChange_tmul, G.projectedLayerCoefficient_horizontal]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r)

def horizontalImageOfSubmodule (B : Submodule ℚ (Fin 4 → L)) (d : ℕ) :
    Submodule ℚ (Fin 4 → F.HigherHorizontal d) :=
  (B.comap (F.fourHorizontalLayer d).subtype).map (F.fourHorizontalMap d)

theorem layerHorizontalImage_eq_of_submodule (A : ℕ → Submodule ℚ M)
    (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
    (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1) (d : ℕ) :
    F.layerHorizontalImage A φ hφ d =
      F.horizontalImageOfSubmodule ((A d).map φ.toLinearMap) d := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨φ x.val, (F.mem_fourHorizontalLayer d _).mpr (hφ d x.val x.property)⟩, ?_, rfl⟩
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply congrArg (F.fourHorizontalMap d)
    exact Subtype.ext hxy

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realFourCoordinateEquiv :
    (ℝ ⊗[ℚ] (Fin 4 → ι → ℚ)) ≃ₗ[ℝ] ((Σ _ : Fin 4, ι) → ℝ) :=
  ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).equivFun

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype μ] {V : Submodule ℚ L}

theorem realQuotientCoordinateMap_norm_bound (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    {H : ℕ} (hf : ∀ i j, RationalHeightLE (f.repr (V.mkQ (b j)) i) H)
    (x : ℝ ⊗[ℚ] L) :
    ‖realQuotientCoordinateMap f x‖ ≤
      ((Fintype.card μ : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [realQuotientCoordinateMap_eq_matrix b f x]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hf i j).abs_real_le) _

theorem realQuotientCoordinateMap_grid (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    (l : ℕ) (x : ℝ ⊗[ℚ] L) (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realQuotientCoordinateMap f x ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  rw [realQuotientCoordinateMap_eq_matrix b f x]
  exact real_matrix_denominator_grid (quotientCoordinateMatrix b f) l _ hx

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_pi_projection_coordinates {μ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (b : Basis μ ℚ L) (x : ℝ ⊗[ℚ] (Fin 4 → L)) (k : Fin 4) (i : μ) :
    (b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x) i =
      ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x ⟨k, i⟩ :=
  (realification_pi_basis_repr (fun _ : Fin 4 => b) x k i).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FreeWeightedRankGenerators
namespace OAI

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

abbrev RankAlphabet := Σ i : Fin (s + 1), layerGenerators X s w (i.val + 1)

def rankAlphabetWeight (a : RankAlphabet X s w) : ℕ := a.1.val + 1

noncomputable def rankAlphabetVector (a : RankAlphabet X s w) : FreeWeightedNilpotentLieAlgebra X s w := a.2.val

theorem rankAlphabetWeight_pos (a : RankAlphabet X s w) : 0 < rankAlphabetWeight X s w a := Nat.succ_pos _

theorem rankAlphabet_card_le : Fintype.card (RankAlphabet X s w) ≤
    (s + 1) * (Fintype.card X + 2) ^ (3 ^ s) := by
  classical
  simp only [RankAlphabet, Fintype.card_sigma, Fintype.card_coe]
  calc
    _ ≤ ∑ _i : Fin (s + 1), (Fintype.card X + 2) ^ (3 ^ s) :=
      Finset.sum_le_sum (fun i _ => layerGenerators_card_le X s w (i.val + 1))
    _ = _ := by simp

noncomputable def topRankGenerators (k : ℕ) : Finset (FreeWeightedNilpotentLieAlgebra X s w) :=
  finiteWeightedLieValues (rankAlphabetVector X s w) (rankAlphabetWeight X s w) s k

theorem topRankGenerators_card_le (k : ℕ) :
    (topRankGenerators X s w k).card ≤
      ((s + 1) * (Fintype.card X + 2) ^ (3 ^ s) + 2) ^ (3 ^ s) :=
  (finiteWeightedLieValues_card_le (rankAlphabetVector X s w) (rankAlphabetWeight X s w) s k).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right (rankAlphabet_card_le X s w) 2) _)

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTagConstraintSpaces
namespace OAI

section

namespace Erdos3.VectorPolynomial

namespace RationalTagConstraint

variable {m : ℕ} {J : Fin m → Type*}

def BudgetLE (c : RationalTagConstraint J) (B : ℝ) : Prop :=
  (c.count : ℝ) ≤ B ∧ ∀ a i, rationalLogHeight (c.generators a i) ≤ B

theorem BudgetLE.mono {c : RationalTagConstraint J} {B B' : ℝ}
    (h : c.BudgetLE B) (hBB' : B ≤ B') : c.BudgetLE B' :=
  ⟨h.1.trans hBB', fun a i => (h.2 a i).trans hBB'⟩

end RationalTagConstraint

def RationalTaggedConstraintCertificate {m : ℕ} (J : Fin m → Type*) {X : Type*}
    (Kinitial K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (B : ℝ) (Cblocks : ℕ) : Prop :=
  ∃ cs : List (RationalTagConstraint J), cs.length ≤ Cblocks ∧
    (∀ c ∈ cs, c.BudgetLE B) ∧
    K = Kinitial ∩ {t | ∀ c ∈ cs, c.member t}

namespace RationalTaggedConstraintCertificate

variable {m : ℕ} {J : Fin m → Type*} {X : Type*}
  {K₀ K₁ K₂ : Set ((X ⊕ (Σ j, J j)) → ℝ)} {B B' : ℝ} {C C₁ C₂ : ℕ}

theorem empty (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (B : ℝ) :
    RationalTaggedConstraintCertificate J K K B 0 := by
  refine ⟨[], le_rfl, ?_, ?_⟩
  · simp
  · simp

theorem monoB (h : RationalTaggedConstraintCertificate J K₀ K₁ B C)
    (hBB' : B ≤ B') : RationalTaggedConstraintCertificate J K₀ K₁ B' C := by
  obtain ⟨cs, hlength, hbudget, hK⟩ := h
  exact ⟨cs, hlength, fun c hc => (hbudget c hc).mono hBB', hK⟩

theorem subset (h : RationalTaggedConstraintCertificate J K₀ K₁ B C) : K₁ ⊆ K₀ := by
  obtain ⟨cs, _, _, rfl⟩ := h
  exact Set.inter_subset_left

theorem trans (h₁ : RationalTaggedConstraintCertificate J K₀ K₁ B C₁)
    (h₂ : RationalTaggedConstraintCertificate J K₁ K₂ B C₂) :
    RationalTaggedConstraintCertificate J K₀ K₂ B (C₁ + C₂) := by
  obtain ⟨cs, hcs, hcb, hK₁⟩ := h₁
  obtain ⟨ds, hds, hdb, hK₂⟩ := h₂
  refine ⟨cs ++ ds, ?_, ?_, ?_⟩
  · simpa only [List.length_append] using Nat.add_le_add hcs hds
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcb c hc
    · exact hdb c hc
  · rw [hK₂, hK₁]
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.mem_append,
      or_imp, forall_and]
    exact and_assoc

end RationalTaggedConstraintCertificate

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

structure IndexedComparableScalarGeometryData (d r : ℕ)
    {K I : Type*} [Fintype K] [Fintype I]
    (L W τ : ℝ) (parameters : K → ℕ) (N : I → ℕ) : Prop where
  hτ : 0 < τ
  hτ1 : τ ≤ 1
  hL : 1 ≤ L
  hwidth : ∀ z : Option K × I, 0 < trimmedSpatialWidths W τ N z
  hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i
  hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0}
    (trimmedSpatialWidths (K := K) W τ N) z
  hparam : ∀ j, (0 : ℤ) < (parameters j : ℤ)
  sourceGeometry :
    (∀ t : Option K × I, smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 ≤
      canonicalJointFrameWindowConstant (r*d) τ *
        ((jointFrameSourceHi N (trimmedSpatialWidths W τ N) t -
          jointFrameSourceLo (trimmedSpatialWidths W τ N) t : ℤ) : ℝ)) ∧
    (∀ z ∈ Fintype.piFinset (fun t : Option K × I =>
        Finset.Ico (jointFrameSourceLo (trimmedSpatialWidths W τ N) t)
          (jointFrameSourceHi N (trimmedSpatialWidths W τ N) t)), ∀ t,
      |(z t : ℝ) - (0 : ℤ)| ≤ smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 / 2) ∧
    (∀ k : K, ∀ i,
      |(jointFrameSourceLo (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L) ∧
    (∀ k : K, ∀ i,
      |(jointFrameSourceHi N (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L)
  hroot : ∀ i, trimmedSpatialWidths (K := K) W τ N (none, i) ≤
    (spatialTrimMargin τ N i : ℝ)
  hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1 / 2
  hscale : ∀ z : Option K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤
    residueProfileWidth (fun _ : I => 1) (trimmedSpatialWidths W τ N) z
  physicalSize : ∀ i, L * L ^ (d + 1) ≤ 2 * (N i : ℝ)
  parameterBox :
    (∀ j, (0 : ℤ) < (parameters j : ℤ)) ∧
    0 < L ∧
    (∀ j, L ≤ (((parameters j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (parameters j : ℤ) - 0 ≤ (comparableScalarParameterRadius (r : ℝ) L : ℤ)) ∧
    (comparableScalarParameterRadius (r : ℝ) L : ℝ) ≤ ((r : ℝ) + 1) * L ∧
    1 * L ≤ L ∧
    |(0 : ℝ) / L| ≤ r ∧
    (∀ j, |(((parameters j : ℤ) : ℝ)) / L| ≤ r) ∧
    0 ≤ W ∧ L ≤ W ∧ W ≤ (r : ℝ) * d * L

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace FaceRegularityState

@[simp]
theorem partition_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition =
      FacePartition.join S.partition
        (FacePartition.generatedBy ({A} : Finset (Finset Ω))) :=
  rfl

theorem refineBy_le (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition ≤ S.partition :=
  FacePartition.join_le_left _ _

theorem booleanCut_measurable_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    IsPartitionMeasurable (S.refineBy A).partition A.eval := by
  apply IsPartitionMeasurable.of_le
    (FacePartition.join_le_right S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))))
  exact booleanCut_measurable_generatedBy A

@[simp]
theorem conditionalMean_residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean S.partition (S.residual f) x = 0 := by
  change
    conditionalMean S.partition
      (fun y => f y - conditionalMean S.partition f y) x = 0
  rw [conditionalMean_sub]
  rw [conditionalMean_idem]
  ring

@[simp]
theorem mean_residual (S : FaceRegularityState Ω) (f : Ω → ℝ) :
    mean (S.residual f) = 0 := by
  change
    mean (fun x => f x - conditionalMean S.partition f x) = 0
  rw [mean_sub]
  rw [mean_conditionalMean]
  ring

theorem conditionalMean_residual_refineBy
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) (x : Ω) :
    conditionalMean (S.refineBy A).partition (S.residual f) x =
      (S.refineBy A).structured f x - S.structured f x := by
  change
    conditionalMean (S.refineBy A).partition
        (fun y => f y - conditionalMean S.partition f y) x =
      conditionalMean (S.refineBy A).partition f x -
        conditionalMean S.partition f x
  rw [conditionalMean_sub]
  rw [conditionalMean_reverse_tower_of_le
    (S.refineBy A).partition S.partition (S.refineBy_le A)]

theorem mean_mul_eq_mean_conditionalMean_mul
    (P : FacePartition Ω) (u v : Ω → ℝ)
    (hv : IsPartitionMeasurable P v) :
    mean (fun x => u x * v x) =
      mean (fun x => conditionalMean P u x * v x) := by
  calc
    mean (fun x => u x * v x) =
        mean (conditionalMean P (fun x => u x * v x)) :=
      (mean_conditionalMean P _).symm
    _ = mean (fun x => conditionalMean P u x * v x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_right_of_constant_on_part
        P u v x (hv x)

theorem booleanCutCorrelation_eq_projection
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
  rw [booleanCutCorrelation]
  calc
    mean (fun x => S.residual f x * A.eval x) =
        mean (fun x =>
          conditionalMean (S.refineBy A).partition (S.residual f) x *
            A.eval x) :=
      mean_mul_eq_mean_conditionalMean_mul
        (S.refineBy A).partition (S.residual f) A.eval
        (S.booleanCut_measurable_refineBy A)
    _ = mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
      apply congrArg mean
      funext x
      rw [S.conditionalMean_residual_refineBy f A x]

omit [DecidableEq Ω] in

theorem mean_mul_sq_le_sq_mul_sq (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) * mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

theorem mean_booleanCut_sq_le_one [Nonempty Ω]
    (A : BooleanCutTest Ω) :
    mean (fun x => A.eval x ^ 2) ≤ 1 := by
  apply mean_le_of_le_const
  intro x
  rw [A.eval_sq x]
  exact A.eval_le_one x

theorem energy_refineBy_sub_eq_mean_sq
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).energy f - S.energy f =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) ^ 2) := by
  simpa [energy, structured] using
    partitionEnergy_sub_eq_mean_sq
      (S.refineBy A).partition S.partition (S.refineBy_le A) f

theorem booleanCutCorrelation_sq_le_energyIncrement [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A ^ 2 ≤
      (S.refineBy A).energy f - S.energy f := by
  rw [S.booleanCutCorrelation_eq_projection f A]
  let d : Ω → ℝ :=
    fun x => (S.refineBy A).structured f x - S.structured f x
  have hcs :
      mean (fun x => d x * A.eval x) ^ 2 ≤
        mean (fun x => d x ^ 2) *
          mean (fun x => A.eval x ^ 2) :=
    mean_mul_sq_le_sq_mul_sq d A.eval
  have hd : 0 ≤ mean (fun x => d x ^ 2) :=
    mean_nonneg fun x => sq_nonneg _
  have hA := mean_booleanCut_sq_le_one A
  calc
    mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) ^ 2 =
        mean (fun x => d x * A.eval x) ^ 2 := rfl
    _ ≤ mean (fun x => d x ^ 2) *
        mean (fun x => A.eval x ^ 2) := hcs
    _ ≤ mean (fun x => d x ^ 2) := by
      nlinarith
    _ = (S.refineBy A).energy f - S.energy f := by
      exact (S.energy_refineBy_sub_eq_mean_sq f A).symm

theorem energy_increment_of_booleanCut [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcorrelation : ε ≤ |S.booleanCutCorrelation f A|) :
    S.energy f + ε ^ 2 ≤ (S.refineBy A).energy f := by
  have hsquare :
      ε ^ 2 ≤ S.booleanCutCorrelation f A ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hε] using hcorrelation
  have hincrement :=
    S.booleanCutCorrelation_sq_le_energyIncrement f A
  linarith

end FaceRegularityState

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) :
    BooleanCutTest (Fin r → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b ⟨i, eraseCoordinate i x⟩ = true

@[simp]
theorem mem_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    x ∈ booleanFaceCutSupport b ↔
      ∀ i, b ⟨i, eraseCoordinate i x⟩ = true := by
  simp [booleanFaceCutSupport]

namespace FaceRegularityState

noncomputable def faceCutCorrelation
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x => S.residual f x * cutTestProduct u x

def IsFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    IsBoundedCutTest u →
      |S.faceCutCorrelation f u| ≤ ε

end FaceRegularityState

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedBoundaryPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev OrderedFacePartitionSystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ) :=
  (e : OrderedFace k j) → FacePartition (Fin j → G)

def OrderedFacePartitionRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j) : Prop :=
  ∀ e, fine e ≤ coarse e

namespace OrderedFacePartitionRefines

theorem refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j) :
    OrderedFacePartitionRefines P P :=
  fun _ => le_rfl

theorem trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {P Q R : OrderedFacePartitionSystem G k j}
    (hPQ : OrderedFacePartitionRefines P Q)
    (hQR : OrderedFacePartitionRefines Q R) :
    OrderedFacePartitionRefines P R :=
  fun e => le_trans (hPQ e) (hQR e)

end OrderedFacePartitionRefines

def orderedImmediateBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.pullback (eraseBoundaryCoordinate i)
    (P (eraseBoundaryFace e i))

def orderedBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ : Finset (Fin (j + 1)))
    (orderedImmediateBoundaryPartition P e)

theorem orderedBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    orderedBoundaryPartition P e ≤
      orderedImmediateBoundaryPartition P e i := by
  exact FacePartition.joinFinset_le_of_mem
    (orderedImmediateBoundaryPartition P e)
    (Finset.mem_univ i)

theorem orderedBoundaryPartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1)) :
    orderedBoundaryPartition fine e ≤
      orderedBoundaryPartition coarse e := by
  unfold orderedBoundaryPartition
  apply FacePartition.le_joinFinset_iff.mpr
  intro i _
  exact le_trans
    (orderedBoundaryPartition_le_immediate fine e i)
    (FacePartition.pullback_mono (eraseBoundaryCoordinate i)
      (hfc (eraseBoundaryFace e i)))

theorem mem_orderedBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryPartition P e).part x ↔
      ∀ i : Fin (j + 1),
        eraseBoundaryCoordinate i y ∈
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) := by
  rw [orderedBoundaryPartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedImmediateBoundaryPartition,
    FacePartition.mem_part_pullback_iff_image_mem]

noncomputable def orderedBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryPartition P e).parts :=
  ⟨(orderedBoundaryPartition P e).part x,
    (orderedBoundaryPartition P e).part_mem.2
      (Finset.mem_univ x)⟩

@[simp]
theorem orderedBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryAtomAt P e x).1 =
      (orderedBoundaryPartition P e).part x :=
  rfl

noncomputable def orderedBoundaryStructured
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    (Fin (j + 1) → G) → ℝ :=
  conditionalMean (orderedBoundaryPartition P e) f

structure OrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  partition :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        FacePartition (Fin j.1 → G)

namespace OrderedPartitionComplex

def layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (j : ℕ) (hj : j ≤ r) :
    OrderedFacePartitionSystem G k j :=
  C.partition ⟨j, Nat.lt_succ_iff.mpr hj⟩

def boundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    (C : OrderedPartitionComplex G k r)
    (hj : j < r)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  orderedBoundaryPartition (C.layer j (Nat.le_of_lt hj)) e

def Refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r) : Prop :=
  ∀ j e, fine.partition j e ≤ coarse.partition j e

theorem Refines.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    C.Refines C :=
  fun _ _ => le_rfl

end OrderedPartitionComplex

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedAtomEnergy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω ι : Type*}
  [Fintype Ω] [DecidableEq Ω]

namespace FaceRegularityState

structure FamilyIrregularWitness
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) where
  index : ι
  cut : BooleanCutTest Ω
  mem_cuts : cut ∈ cuts
  correlation :
    ε < |S.booleanCutCorrelation (f index) cut|

end FaceRegularityState

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) :
    Ω → ℝ :=
  finsetIndicator a.1

@[simp]
theorem partitionAtomIndicator_of_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∈ a.1) :
    partitionAtomIndicator Q a x = 1 :=
  finsetIndicator_of_mem hx

@[simp]
theorem partitionAtomIndicator_of_not_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∉ a.1) :
    partitionAtomIndicator Q a x = 0 :=
  finsetIndicator_of_not_mem hx

theorem partitionAtomIndicator_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ^ 2 =
      partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem sum_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (x : Ω) :
    ∑ a : Q.parts, partitionAtomIndicator Q a x = 1 := by
  classical
  let ax : Q.parts :=
    ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x)⟩
  rw [Finset.sum_eq_single ax]
  · exact partitionAtomIndicator_of_mem Q ax
      (Q.mem_part (Finset.mem_univ x))
  · intro b _hb hba
    apply partitionAtomIndicator_of_not_mem
    intro hxb
    have heq :
        b = ax := by
      apply Subtype.ext
      exact Q.eq_of_mem_parts b.2 ax.2 hxb
        (Q.mem_part (Finset.mem_univ x))
    exact hba heq
  · intro hax
    exact (hax (Finset.mem_univ ax)).elim

noncomputable def partitionAtomEnergy
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) : ℝ :=
  ∑ a : Q.parts,
    Erdos3.FixedDensity.partitionEnergy P
      (partitionAtomIndicator Q a)

theorem partitionAtomEnergy_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) :
    0 ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  exact Finset.sum_nonneg fun a _ =>
    Erdos3.FixedDensity.partitionEnergy_nonneg P
      (partitionAtomIndicator Q a)

theorem partitionAtomEnergy_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P Q : FacePartition Ω) :
    partitionAtomEnergy P Q ≤ 1 := by
  unfold partitionAtomEnergy
  calc
    (∑ a : Q.parts,
        Erdos3.FixedDensity.partitionEnergy P
          (partitionAtomIndicator Q a)) ≤
        ∑ a : Q.parts,
          mean (fun x =>
            partitionAtomIndicator Q a x ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact partitionEnergy_le_mean_sq P
        (partitionAtomIndicator Q a)
    _ =
        ∑ a : Q.parts,
          mean (partitionAtomIndicator Q a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg mean
      funext x
      exact partitionAtomIndicator_sq Q a x
    _ =
        mean (fun x =>
          ∑ a : Q.parts, partitionAtomIndicator Q a x) := by
      unfold mean
      exact
        (Finset.expect_sum_comm
          (Finset.univ : Finset Ω)
          (Finset.univ : Finset Q.parts)
          (fun x a => partitionAtomIndicator Q a x)).symm
    _ = mean (fun _x : Ω => (1 : ℝ)) := by
      apply congrArg mean
      funext x
      exact sum_partitionAtomIndicator Q x
    _ = 1 := mean_const 1

theorem partitionAtomEnergy_mono
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : FacePartition Ω} (hPR : P ≤ R)
    (Q : FacePartition Ω) :
    partitionAtomEnergy R Q ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  apply Finset.sum_le_sum
  intro a _
  exact partitionEnergy_mono P R hPR
    (partitionAtomIndicator Q a)

noncomputable def orderedAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) : ℝ :=
  partitionAtomEnergy (orderedBoundaryPartition lower e) upper

theorem orderedAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    0 ≤ orderedAtomEnergy lower e upper :=
  partitionAtomEnergy_nonneg _ _

theorem orderedAtomEnergy_le_one
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy lower e upper ≤ 1 :=
  partitionAtomEnergy_le_one _ _

theorem orderedAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy coarse e upper ≤
      orderedAtomEnergy fine e upper := by
  exact partitionAtomEnergy_mono
    (orderedBoundaryPartition_mono hfc e) upper

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BoundaryBernoulli
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def boundaryBooleanComponentCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    BooleanCutTest (Fin j → G) := by
  classical
  exact Finset.univ.filter fun z => b i z = true

@[simp]
theorem mem_boundaryBooleanComponentCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) (z : Fin j → G) :
    z ∈ boundaryBooleanComponentCut b i ↔
      b i z = true := by
  simp [boundaryBooleanComponentCut]

noncomputable def boundaryBooleanCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutTest (Fin (j + 1) → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b i (eraseBoundaryCoordinate i x) = true

@[simp]
theorem mem_boundaryBooleanCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (x : Fin (j + 1) → G) :
    x ∈ boundaryBooleanCutSupport b ↔
      ∀ i, b i (eraseBoundaryCoordinate i x) = true := by
  simp [boundaryBooleanCutSupport]

noncomputable def orderedBoundaryComponentCuts
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    Finset (BooleanCutTest (Fin j → G)) := by
  classical
  exact
    ((Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => eraseBoundaryFace e i = g)).image
      (fun i => boundaryBooleanComponentCut b i)

theorem boundaryBooleanComponentCut_mem_orderedBoundaryComponentCuts
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    boundaryBooleanComponentCut b i ∈
      orderedBoundaryComponentCuts e b
        (eraseBoundaryFace e i) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, rfl⟩
  simp

noncomputable def refineOrderedFacePartitionsByBoundaryCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    OrderedFacePartitionSystem G k j :=
  fun g =>
    FacePartition.join (P g)
      (FacePartition.generatedBy
        (orderedBoundaryComponentCuts e b g))

theorem refineOrderedFacePartitionsByBoundaryCut_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    OrderedFacePartitionRefines
      (refineOrderedFacePartitionsByBoundaryCut P e b) P := by
  intro g
  exact FacePartition.join_le_left _ _

theorem refineOrderedFacePartitionsByBoundaryCut_le_component
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    refineOrderedFacePartitionsByBoundaryCut P e b
          (eraseBoundaryFace e i) ≤
      FacePartition.generatedBy
        ({boundaryBooleanComponentCut b i} :
          Finset (Finset (Fin j → G))) := by
  apply le_trans (FacePartition.join_le_right _ _)
  apply FacePartition.generatedBy_antitone
  intro A hA
  have hAeq : A = boundaryBooleanComponentCut b i := by
    simpa using hA
  subst A
  exact
    boundaryBooleanComponentCut_mem_orderedBoundaryComponentCuts
      e b i

theorem boundaryComponentBit_eq_of_mem_refined_part
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1))
    (x y : Fin j → G)
    (hy :
      y ∈
        (refineOrderedFacePartitionsByBoundaryCut P e b
          (eraseBoundaryFace e i)).part x) :
    b i x = b i y := by
  have hpart :
      y ∈
        (FacePartition.generatedBy
          ({boundaryBooleanComponentCut b i} :
            Finset (Finset (Fin j → G)))).part x :=
    FacePartition.part_subset_of_le
      (refineOrderedFacePartitionsByBoundaryCut_le_component
        P e b i) x hy
  have hsignature :=
    (FacePartition.mem_part_generatedBy_iff
      ({boundaryBooleanComponentCut b i} :
        Finset (Finset (Fin j → G))) x y).1 hpart
      (boundaryBooleanComponentCut b i) (by simp)
  cases hbx : b i x <;> cases hby : b i y <;>
    simp [mem_boundaryBooleanComponentCut, hbx, hby] at hsignature ⊢

theorem orderedBoundaryPartition_refined_le_generatedSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    orderedBoundaryPartition
        (refineOrderedFacePartitionsByBoundaryCut P e b) e ≤
      FacePartition.generatedBy
        ({boundaryBooleanCutSupport b} :
          Finset (Finset (Fin (j + 1) → G))) := by
  rw [FacePartition.le_iff_part_subset]
  intro x y hy
  rw [FacePartition.mem_part_generatedBy_iff]
  intro A hA
  have hAeq : A = boundaryBooleanCutSupport b := by
    simpa using hA
  subst A
  rw [mem_boundaryBooleanCutSupport,
    mem_boundaryBooleanCutSupport]
  have hboundary :=
    (mem_orderedBoundaryPartition_part_iff
      (refineOrderedFacePartitionsByBoundaryCut P e b)
      e x y).1 hy
  constructor
  · intro hx i
    have hbit :=
      boundaryComponentBit_eq_of_mem_refined_part
        P e b i
        (eraseBoundaryCoordinate i x)
        (eraseBoundaryCoordinate i y)
        (hboundary i)
    exact hbit ▸ hx i
  · intro hy' i
    have hbit :=
      boundaryComponentBit_eq_of_mem_refined_part
        P e b i
        (eraseBoundaryCoordinate i x)
        (eraseBoundaryCoordinate i y)
        (hboundary i)
    exact hbit.symm ▸ hy' i

theorem orderedBoundaryPartition_refined_le_refineBy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
      orderedBoundaryPartition
        (refineOrderedFacePartitionsByBoundaryCut P e b) e ≤
      ((⟨orderedBoundaryPartition P e⟩ :
          FaceRegularityState (Fin (j + 1) → G)).refineBy
        (boundaryBooleanCutSupport b)).partition := by
  apply FacePartition.le_join_iff.mpr
  constructor
  · exact orderedBoundaryPartition_mono
      (refineOrderedFacePartitionsByBoundaryCut_refines P e b) e
  · exact orderedBoundaryPartition_refined_le_generatedSupport
      P e b

noncomputable def orderedLayerAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) : ℝ :=
  ∑ e : OrderedFace k (j + 1),
    orderedAtomEnergy lower e (upper e)

theorem orderedLayerAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    0 ≤ orderedLayerAtomEnergy lower upper := by
  unfold orderedLayerAtomEnergy
  exact Finset.sum_nonneg fun e _ =>
    orderedAtomEnergy_nonneg lower e (upper e)

theorem orderedLayerAtomEnergy_le_card
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    orderedLayerAtomEnergy lower upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) := by
  unfold orderedLayerAtomEnergy
  calc
    (∑ e : OrderedFace k (j + 1),
        orderedAtomEnergy lower e (upper e)) ≤
        ∑ _e : OrderedFace k (j + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact orderedAtomEnergy_le_one lower e (upper e)
    _ = (Fintype.card (OrderedFace k (j + 1)) : ℝ) := by
      simp

theorem orderedLayerAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    orderedLayerAtomEnergy coarse upper ≤
      orderedLayerAtomEnergy fine upper := by
  unfold orderedLayerAtomEnergy
  apply Finset.sum_le_sum
  intro e _
  exact orderedAtomEnergy_mono hfc e (upper e)

theorem orderedLayerAtomEnergy_increment_of_boundaryCut
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (e : OrderedFace k (j + 1))
    (a : (upper e).parts)
    (b : BoundaryBooleanCutAssignment G j)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorrelation :
      ε ≤
        |FaceRegularityState.booleanCutCorrelation
          (⟨orderedBoundaryPartition lower e⟩ :
            FaceRegularityState (Fin (j + 1) → G))
            (partitionAtomIndicator (upper e) a)
            (boundaryBooleanCutSupport b)|) :
    orderedLayerAtomEnergy lower upper + ε ^ 2 ≤
      orderedLayerAtomEnergy
        (refineOrderedFacePartitionsByBoundaryCut lower e b)
        upper := by
  classical
  let fine :=
    refineOrderedFacePartitionsByBoundaryCut lower e b
  let S : FaceRegularityState (Fin (j + 1) → G) :=
    ⟨orderedBoundaryPartition lower e⟩
  have hincrement :
      S.energy (partitionAtomIndicator (upper e) a) + ε ^ 2 ≤
        (S.refineBy (boundaryBooleanCutSupport b)).energy
          (partitionAtomIndicator (upper e) a) :=
    S.energy_increment_of_booleanCut
      (partitionAtomIndicator (upper e) a)
      (boundaryBooleanCutSupport b) hε hcorrelation
  have hrefined :
      orderedBoundaryPartition fine e ≤
        (S.refineBy (boundaryBooleanCutSupport b)).partition := by
    exact orderedBoundaryPartition_refined_le_refineBy
      lower e b
  have hatom :
      orderedAtomEnergy lower e (upper e) + ε ^ 2 ≤
        orderedAtomEnergy fine e (upper e) := by
    unfold orderedAtomEnergy partitionAtomEnergy
    let U : Finset (upper e).parts := Finset.univ
    have haU : a ∈ U := by simp [U]
    have hother :
        ∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) c) ≤
          ∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c) := by
      apply Finset.sum_le_sum
      intro c _
      exact partitionEnergy_mono
        (orderedBoundaryPartition fine e)
        (orderedBoundaryPartition lower e)
        (orderedBoundaryPartition_mono
          (refineOrderedFacePartitionsByBoundaryCut_refines
            lower e b) e)
        (partitionAtomIndicator (upper e) c)
    have hchosen :
        partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) a) +
            ε ^ 2 ≤
          partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) a) := by
      exact le_trans hincrement
        (partitionEnergy_mono
          (orderedBoundaryPartition fine e)
          (S.refineBy (boundaryBooleanCutSupport b)).partition
          hrefined
          (partitionAtomIndicator (upper e) a))
    change
      (∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition lower e)
            (partitionAtomIndicator (upper e) c)) +
          ε ^ 2 ≤
        ∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition fine e)
            (partitionAtomIndicator (upper e) c)
    calc
      (∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition lower e)
            (partitionAtomIndicator (upper e) c)) +
            ε ^ 2 =
          (∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) c)) +
            (partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) a) +
              ε ^ 2) := by
        rw [← Finset.sum_erase_add U _ haU]
        ring
      _ ≤
          (∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c)) +
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) a) :=
        add_le_add hother hchosen
      _ =
          ∑ c ∈ U,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c) :=
        Finset.sum_erase_add U _ haU
  unfold orderedLayerAtomEnergy
  let E : Finset (OrderedFace k (j + 1)) := Finset.univ
  have heE : e ∈ E := by simp [E]
  have hotherFaces :
      ∑ d ∈ E.erase e,
          orderedAtomEnergy lower d (upper d) ≤
        ∑ d ∈ E.erase e,
          orderedAtomEnergy fine d (upper d) := by
    apply Finset.sum_le_sum
    intro d _
    exact orderedAtomEnergy_mono
      (refineOrderedFacePartitionsByBoundaryCut_refines
        lower e b)
      d (upper d)
  change
    (∑ d ∈ E, orderedAtomEnergy lower d (upper d)) +
        ε ^ 2 ≤
      ∑ d ∈ E, orderedAtomEnergy fine d (upper d)
  calc
    (∑ d ∈ E, orderedAtomEnergy lower d (upper d)) +
          ε ^ 2 =
        (∑ d ∈ E.erase e,
          orderedAtomEnergy lower d (upper d)) +
        (orderedAtomEnergy lower e (upper e) + ε ^ 2) := by
      rw [← Finset.sum_erase_add E _ heE]
      ring
    _ ≤
        (∑ d ∈ E.erase e,
          orderedAtomEnergy fine d (upper d)) +
        orderedAtomEnergy fine e (upper e) :=
      add_le_add hotherFaces hatom
    _ =
        ∑ d ∈ E, orderedAtomEnergy fine d (upper d) :=
      Finset.sum_erase_add E _ heE

def IsPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts)
      (b : BoundaryBooleanCutAssignment G j),
    |FaceRegularityState.booleanCutCorrelation
        (⟨orderedBoundaryPartition lower e⟩ :
          FaceRegularityState (Fin (j + 1) → G))
        (partitionAtomIndicator (upper e) a)
        (boundaryBooleanCutSupport b)| ≤ ε

theorem exists_boundaryCut_of_not_preliminaryRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ}
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    ∃ (e : OrderedFace k (j + 1))
        (a : (upper e).parts)
        (b : BoundaryBooleanCutAssignment G j),
      ε <
        |FaceRegularityState.booleanCutCorrelation
          (⟨orderedBoundaryPartition lower e⟩ :
            FaceRegularityState (Fin (j + 1) → G))
          (partitionAtomIndicator (upper e) a)
          (boundaryBooleanCutSupport b)| := by
  unfold IsPreliminaryOrderedRegular at h
  obtain ⟨e, he⟩ := not_forall.mp h
  obtain ⟨a, ha⟩ := not_forall.mp he
  obtain ⟨b, hb⟩ := not_forall.mp ha
  exact ⟨e, a, b, lt_of_not_ge hb⟩

structure PreliminaryIrregularWitness
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) where
  face : OrderedFace k (j + 1)
  atom : (upper face).parts
  cut : BoundaryBooleanCutAssignment G j
  correlation :
    ε <
      |FaceRegularityState.booleanCutCorrelation
        (⟨orderedBoundaryPartition lower face⟩ :
          FaceRegularityState (Fin (j + 1) → G))
        (partitionAtomIndicator (upper face) atom)
        (boundaryBooleanCutSupport cut)|

noncomputable def chosenPreliminaryIrregularWitness
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ)
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    PreliminaryIrregularWitness lower upper ε := by
  classical
  let hex :=
    exists_boundaryCut_of_not_preliminaryRegular
      lower upper h
  let e := Classical.choose hex
  let he := Classical.choose_spec hex
  let a := Classical.choose he
  let ha := Classical.choose_spec he
  let b := Classical.choose ha
  have hcorr := Classical.choose_spec ha
  exact ⟨e, a, b, hcorr⟩

noncomputable def preliminaryOrderedRegularityStep
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    OrderedFacePartitionSystem G k j := by
  classical
  exact
    if h : IsPreliminaryOrderedRegular lower upper ε then
      lower
    else
      let W :=
        chosenPreliminaryIrregularWitness lower upper ε h
      refineOrderedFacePartitionsByBoundaryCut
        lower W.face W.cut

theorem preliminaryOrderedRegularityStep_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    OrderedFacePartitionRefines
      (preliminaryOrderedRegularityStep lower upper ε)
      lower := by
  classical
  by_cases h :
      IsPreliminaryOrderedRegular lower upper ε
  · simpa [preliminaryOrderedRegularityStep, h] using
      OrderedFacePartitionRefines.refl lower
  · simp only [preliminaryOrderedRegularityStep, dif_neg h]
    let W :=
      chosenPreliminaryIrregularWitness lower upper ε h
    exact refineOrderedFacePartitionsByBoundaryCut_refines
      lower W.face W.cut

theorem preliminaryOrderedRegularityStep_energy_increment
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    orderedLayerAtomEnergy lower upper + ε ^ 2 ≤
      orderedLayerAtomEnergy
        (preliminaryOrderedRegularityStep lower upper ε)
        upper := by
  classical
  simp only [preliminaryOrderedRegularityStep, dif_neg h]
  let W :=
    chosenPreliminaryIrregularWitness lower upper ε h
  exact orderedLayerAtomEnergy_increment_of_boundaryCut
    lower upper W.face W.atom W.cut hε
    (le_of_lt W.correlation)

noncomputable def preliminaryOrderedRegularityRun
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    ℕ → OrderedFacePartitionSystem G k j
  | 0 => lower
  | n + 1 =>
      preliminaryOrderedRegularityStep
        (preliminaryOrderedRegularityRun lower upper ε n)
        upper ε

@[simp]
theorem preliminaryOrderedRegularityRun_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    preliminaryOrderedRegularityRun lower upper ε 0 =
      lower :=
  rfl

@[simp]
theorem preliminaryOrderedRegularityRun_succ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    preliminaryOrderedRegularityRun lower upper ε (n + 1) =
      preliminaryOrderedRegularityStep
        (preliminaryOrderedRegularityRun lower upper ε n)
        upper ε :=
  rfl

theorem preliminaryOrderedRegularityRun_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    OrderedFacePartitionRefines
      (preliminaryOrderedRegularityRun lower upper ε n)
      lower := by
  induction n with
  | zero =>
      exact OrderedFacePartitionRefines.refl lower
  | succ n ih =>
      exact OrderedFacePartitionRefines.trans
        (preliminaryOrderedRegularityStep_refines
          (preliminaryOrderedRegularityRun lower upper ε n)
          upper ε)
        ih

theorem exists_preliminaryOrderedRegularityRun_index_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ, n < m ∧
      IsPreliminaryOrderedRegular
        (preliminaryOrderedRegularityRun
          lower upper ε n)
        upper ε := by
  by_contra hregular
  have hnotregular :
      ∀ n, n < m →
        ¬IsPreliminaryOrderedRegular
          (preliminaryOrderedRegularityRun
            lower upper ε n)
          upper ε := by
    intro n hn hreg
    exact hregular ⟨n, hn, hreg⟩
  have hgain :
      ∀ n, n < m →
        orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper +
            ε ^ 2 ≤
          orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε (n + 1))
            upper := by
    intro n hn
    rw [preliminaryOrderedRegularityRun_succ]
    exact preliminaryOrderedRegularityStep_energy_increment
      (preliminaryOrderedRegularityRun
        lower upper ε n)
      upper hε (hnotregular n hn)
  have growth :
      ∀ n : ℕ,
        (∀ i, i < n →
          orderedLayerAtomEnergy
              (preliminaryOrderedRegularityRun
                lower upper ε i)
              upper +
              ε ^ 2 ≤
            orderedLayerAtomEnergy
              (preliminaryOrderedRegularityRun
                lower upper ε (i + 1))
              upper) →
        orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε 0)
            upper +
            (n : ℝ) * ε ^ 2 ≤
          orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hprevious :=
          ih (fun i hi =>
            hn i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        have hstep := hn n (Nat.lt_succ_self n)
        calc
          orderedLayerAtomEnergy
                (preliminaryOrderedRegularityRun
                  lower upper ε 0)
                upper +
                (↑(Nat.succ n) : ℝ) * ε ^ 2 =
              (orderedLayerAtomEnergy
                  (preliminaryOrderedRegularityRun
                    lower upper ε 0)
                  upper +
                (n : ℝ) * ε ^ 2) +
                ε ^ 2 := by
            push_cast
            ring
          _ ≤
              orderedLayerAtomEnergy
                  (preliminaryOrderedRegularityRun
                    lower upper ε n)
                  upper +
                ε ^ 2 := by
            linarith
          _ ≤
              orderedLayerAtomEnergy
                (preliminaryOrderedRegularityRun
                  lower upper ε (n + 1))
                upper :=
            hstep
  have hgrowth := growth m hgain
  have hnonneg :
      0 ≤
        orderedLayerAtomEnergy
          (preliminaryOrderedRegularityRun
            lower upper ε 0)
          upper :=
    orderedLayerAtomEnergy_nonneg _ _
  have hupper :
      orderedLayerAtomEnergy
          (preliminaryOrderedRegularityRun
            lower upper ε m)
          upper ≤
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) :=
    orderedLayerAtomEnergy_le_card _ _
  linarith

theorem card_orderedBoundaryComponentCuts_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    (orderedBoundaryComponentCuts e b g).card ≤
      j + 1 := by
  classical
  let I : Finset (Fin (j + 1)) :=
    (Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => eraseBoundaryFace e i = g)
  calc
    (orderedBoundaryComponentCuts e b g).card ≤
        I.card := by
      exact Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin (j + 1))).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = j + 1 := by simp

theorem complexity_refineOrderedFacePartitionsByBoundaryCut_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    FacePartition.complexity
        (refineOrderedFacePartitionsByBoundaryCut P e b g) ≤
      2 ^ (j + 1) *
        FacePartition.complexity (P g) := by
  have hgenerated :
      FacePartition.complexity
          (FacePartition.generatedBy
            (orderedBoundaryComponentCuts e b g)) ≤
        2 ^ (j + 1) := by
    exact le_trans
      (FacePartition.complexity_generatedBy_le
        (orderedBoundaryComponentCuts e b g))
      (Nat.pow_le_pow_right (by decide)
        (card_orderedBoundaryComponentCuts_le e b g))
  calc
    FacePartition.complexity
        (refineOrderedFacePartitionsByBoundaryCut P e b g) ≤
        FacePartition.complexity (P g) *
          FacePartition.complexity
            (FacePartition.generatedBy
              (orderedBoundaryComponentCuts e b g)) :=
      FacePartition.complexity_join_le _ _
    _ ≤
        FacePartition.complexity (P g) *
          2 ^ (j + 1) :=
      Nat.mul_le_mul_left _ hgenerated
    _ =
        2 ^ (j + 1) *
          FacePartition.complexity (P g) :=
      Nat.mul_comm _ _

theorem complexity_preliminaryOrderedRegularityStep_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (g : OrderedFace k j) :
    FacePartition.complexity
        (preliminaryOrderedRegularityStep
          lower upper ε g) ≤
      2 ^ (j + 1) *
        FacePartition.complexity (lower g) := by
  classical
  by_cases h :
      IsPreliminaryOrderedRegular lower upper ε
  · simp only [preliminaryOrderedRegularityStep, dif_pos h]
    exact Nat.le_mul_of_pos_left _
      (by positivity : 0 < 2 ^ (j + 1))
  · simp only [preliminaryOrderedRegularityStep, dif_neg h]
    let W :=
      chosenPreliminaryIrregularWitness lower upper ε h
    exact
      complexity_refineOrderedFacePartitionsByBoundaryCut_le
        lower W.face W.cut g

theorem complexity_preliminaryOrderedRegularityRun_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) (g : OrderedFace k j) :
    FacePartition.complexity
        (preliminaryOrderedRegularityRun
          lower upper ε n g) ≤
      (2 ^ (j + 1)) ^ n *
        FacePartition.complexity (lower g) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        FacePartition.complexity
            (preliminaryOrderedRegularityRun
              lower upper ε (n + 1) g) ≤
            2 ^ (j + 1) *
              FacePartition.complexity
                (preliminaryOrderedRegularityRun
                  lower upper ε n g) := by
          rw [preliminaryOrderedRegularityRun_succ]
          exact complexity_preliminaryOrderedRegularityStep_le
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper ε g
        _ ≤
            2 ^ (j + 1) *
              ((2 ^ (j + 1)) ^ n *
                FacePartition.complexity (lower g)) :=
          Nat.mul_le_mul_left _ ih
        _ =
            (2 ^ (j + 1)) ^ (n + 1) *
              FacePartition.complexity (lower g) := by
          rw [pow_succ]
          ring

theorem exists_preliminaryOrderedRegular_refinement_with_complexity_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ,
      ∃ fine : OrderedFacePartitionSystem G k j,
        n < m ∧
        OrderedFacePartitionRefines fine lower ∧
        IsPreliminaryOrderedRegular fine upper ε ∧
        ∀ g,
          FacePartition.complexity (fine g) ≤
            (2 ^ (j + 1)) ^ n *
              FacePartition.complexity (lower g) := by
  obtain ⟨n, hn, hregular⟩ :=
    exists_preliminaryOrderedRegularityRun_index_before
      lower upper hε hlong
  exact
    ⟨n,
      preliminaryOrderedRegularityRun lower upper ε n,
      hn,
      preliminaryOrderedRegularityRun_refines
        lower upper ε n,
      hregular,
      complexity_preliminaryOrderedRegularityRun_le
        lower upper ε n⟩

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def boundaryBooleanAssignmentOfBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    BoundaryBooleanCutAssignment G j :=
  fun i z => b ⟨i, z⟩

def booleanAssignmentOfBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutAssignment G (j + 1) :=
  fun q => b q.1 q.2

@[simp]
theorem booleanAssignmentOfBoundary_ofBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        (boundaryBooleanAssignmentOfBoolean b) = b := by
  funext q
  cases q
  rfl

@[simp]
theorem boundaryBooleanAssignmentOfBoolean_ofBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanAssignmentOfBoolean
        (booleanAssignmentOfBoundary b) = b := by
  funext i z
  rfl

def booleanBoundaryAssignmentEquiv
    (G : Type*) (j : ℕ) :
    BooleanCutAssignment G (j + 1) ≃
      BoundaryBooleanCutAssignment G j where
  toFun := boundaryBooleanAssignmentOfBoolean
  invFun := booleanAssignmentOfBoundary
  left_inv := booleanAssignmentOfBoundary_ofBoolean
  right_inv := boundaryBooleanAssignmentOfBoolean_ofBoundary

@[simp]
theorem booleanAssignmentOfBoundary_equiv_apply
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        ((booleanBoundaryAssignmentEquiv G j) b) = b :=
  booleanAssignmentOfBoundary_ofBoolean b

def boundaryBernoulliWeight
    {G : Type*} [Fintype G] {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (b : BoundaryBooleanCutAssignment G j) : ℝ :=
  bernoulliAssignmentWeight
    (cutTestCoordinateValue u)
    (booleanAssignmentOfBoundary b)

def IsPreliminaryOrderedBoundedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts),
    (⟨orderedBoundaryPartition lower e⟩ :
      FaceRegularityState (Fin (j + 1) → G)).IsFaceCutRegular
        (partitionAtomIndicator (upper e) a) ε

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedGoodAtoms
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def partitionAtomAt
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) :
    P.parts :=
  ⟨P.part x, P.part_mem.2 (Finset.mem_univ x)⟩

@[simp]
theorem partitionAtomAt_val
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) :
    (partitionAtomAt P x).1 = P.part x :=
  rfl

@[simp]
theorem partitionAtomAt_eq_iff_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) (a : P.parts) :
    partitionAtomAt P x = a ↔ x ∈ a.1 := by
  constructor
  · intro h
    rw [← h]
    exact P.mem_part (Finset.mem_univ x)
  · intro hx
    apply Subtype.ext
    exact P.part_eq_of_mem a.2 hx

def partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    Finset Ω :=
  s.biUnion fun a => a.1

@[simp]
theorem mem_partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ partitionAtomUnion P s ↔
      ∃ a ∈ s, x ∈ a.1 := by
  simp [partitionAtomUnion]

noncomputable def smallAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    conditionalMean P f (P.representative b) < α

noncomputable def smallAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (smallAverageBaseAtoms P f α)

noncomputable def largeAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    β < conditionalMean P f (P.representative b)

noncomputable def largeAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (largeAverageBaseAtoms P f β)

noncomputable def atomBoundaryDefect
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  conditionalMean fine (partitionAtomIndicator upper a) x -
    conditionalMean coarse (partitionAtomIndicator upper a) x

noncomputable def atomBoundaryDefectSq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  atomBoundaryDefect fine coarse upper a x ^ 2

noncomputable def orderedAtomBoundaryDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G) : ℝ :=
  atomBoundaryDefect
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a x

structure ClosedOrderedAtomConfiguration
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) (C : OrderedPartitionComplex G k r) where
  witness : Fin k → G
  atom :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        (C.partition j e).parts
  mem_atom :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      orderedFaceTuple e witness ∈ (atom j e).1

namespace ClosedOrderedAtomConfiguration

def ofTuple
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (C : OrderedPartitionComplex G k r)
    (x : Fin k → G) :
    ClosedOrderedAtomConfiguration G k r C where
  witness := x
  atom j e :=
    partitionAtomAt (C.partition j e)
      (orderedFaceTuple e x)
  mem_atom j e :=
    (C.partition j e).mem_part
      (Finset.mem_univ (orderedFaceTuple e x))

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPatternPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedPartitionComplex

def topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    OrderedFacePartitionSystem G k r :=
  C.partition (Fin.last r)

def dropTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    OrderedPartitionComplex G k r where
  partition j := C.partition j.castSucc

def appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    OrderedPartitionComplex G k (r + 1) where
  partition j :=
    Fin.lastCases top (fun i => C.partition i) j

def withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    OrderedPartitionComplex G k r where
  partition j :=
    Fin.lastCases top (fun i => C.partition i.castSucc) j

@[simp]
theorem topLayer_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).topLayer = top := by
  simp [topLayer, appendTop]

@[simp]
theorem dropTop_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).dropTop = C := by
  cases C with
  | mk partition =>
      simp [dropTop, appendTop]

@[simp]
theorem topLayer_withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    (withTopLayer C top).topLayer = top := by
  simp [topLayer, withTopLayer]

@[simp]
theorem withTopLayer_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1))
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (withTopLayer C top).partition j.castSucc =
      C.partition j.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (appendTop C top).partition j.castSucc =
      C.partition j := by
  simp [appendTop]

@[simp]
theorem appendTop_partition_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).partition (Fin.last (r + 1)) =
      top := by
  simp [appendTop]

@[simp]
theorem withTopLayer_partition_castSucc_general
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (i : Fin r) :
    (withTopLayer C top).partition i.castSucc =
      C.partition i.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_dropTop_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    appendTop C.dropTop C.topLayer = C := by
  cases C with
  | mk partition =>
      simp only [dropTop, topLayer, appendTop]
      congr 1
      funext j e
      cases j using Fin.lastCases <;>
        simp only [Fin.lastCases_last,
          Fin.lastCases_castSucc]

end OrderedPartitionComplex

structure OrderedCoarseFineComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse

def IsFullyPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (C.partition j.castSucc)
      (C.partition j.succ)
      (ε j)

def HasOrderedRegularityComplexityBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (steps : OrderedRegularityStepSchedule r) : Prop :=
  ∀ (j : Fin r) (e : OrderedFace k j.1),
    FacePartition.complexity
        (fine.partition j.castSucc e) ≤
      (2 ^ (j.1 + 1)) ^ (steps j) *
        FacePartition.complexity
          (coarse.partition j.castSucc e)

structure FullOrderedRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (coarse : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r) where
  steps : OrderedRegularityStepSchedule r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  topLayer_eq :
    fine.topLayer = coarse.topLayer
  steps_lt : ∀ j, steps j < m j
  regular :
    IsFullyPreliminaryOrderedRegular fine ε
  complexity :
    HasOrderedRegularityComplexityBound
      fine coarse steps

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

noncomputable def OrderedPattern.edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) : Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter (H.edge e)

@[simp]
theorem OrderedPattern.mem_edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ H.edgeFinset e ↔ H.edge e y := by
  simp [OrderedPattern.edgeFinset]

noncomputable def orderedPatternTopPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    OrderedFacePartitionSystem G k r := by
  classical
  exact fun e =>
    FacePartition.generatedBy ({H.edgeFinset e} :
      Finset (Finset (Fin r → G)))

def indiscreteOrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) : OrderedPartitionComplex G k r where
  partition _ _ := FacePartition.indiscrete

noncomputable def orderedPatternInitialComplex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    OrderedPartitionComplex G k r :=
  (indiscreteOrderedPartitionComplex G k r).withTopLayer
    (orderedPatternTopPartition H)

@[simp]
theorem orderedPatternInitialComplex_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    (orderedPatternInitialComplex H).topLayer =
      orderedPatternTopPartition H := by
  exact OrderedPartitionComplex.topLayer_withTopLayer _ _

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CoarseAtomBridge
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

noncomputable def coarseUpperFaceAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) : ℝ :=
  orderedAtomEnergy
      (P.fine.partition j.castSucc) e
      (P.coarse.partition j.succ e) -
    orderedAtomEnergy
      (P.coarse.partition j.castSucc) e
      (P.coarse.partition j.succ e)

noncomputable def coarseUpperLayerAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) : ℝ :=
  orderedLayerAtomEnergy
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ) -
    orderedLayerAtomEnergy
      (P.coarse.partition j.castSucc)
      (P.coarse.partition j.succ)

end OrderedCoarseFineComplex

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CoarseOrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev OrderedPositiveSubface (r : ℕ) :=
  (j : Fin r) ×' OrderedFace r (j.1 + 1)

noncomputable def orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    orderedFaceTuple d y ∈ S

@[simp]
theorem mem_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G))
    (y : Fin r → G) :
    y ∈ orderedFacePullbackFinset d S ↔
      orderedFaceTuple d y ∈ S := by
  simp [orderedFacePullbackFinset]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.StrongOrderedComplexRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure FixedUpperLayerRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ) where
  steps : ℕ
  fine : OrderedFacePartitionSystem G k j
  steps_lt : steps < budget
  refines : OrderedFacePartitionRefines fine lower
  regular : IsPreliminaryOrderedRegular fine upper ε
  complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        (2 ^ (j + 1)) ^ steps *
          FacePartition.complexity (lower e)

theorem FixedUpperLayerRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {budget : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    Nonempty
      (FixedUpperLayerRegularityCertificate
        G k j lower upper ε budget) := by
  obtain ⟨steps, fine, hsteps, hrefines,
      hregular, hcomplexity⟩ :=
    exists_preliminaryOrderedRegular_refinement_with_complexity_before
      lower upper hε hlong
  exact ⟨{
    steps := steps
    fine := fine
    steps_lt := hsteps
    refines := hrefines
    regular := hregular
    complexity := hcomplexity }⟩

noncomputable def chosenFixedUpperLayerRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    FixedUpperLayerRegularityCertificate
      G k j lower upper ε budget :=
  Classical.choice
    (FixedUpperLayerRegularityCertificate.nonempty
      lower upper hε hlong)

noncomputable def fixedUpperLayerRegularityTower
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ℕ → OrderedFacePartitionSystem G k j
  | 0 => initial
  | n + 1 =>
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine

@[simp]
theorem fixedUpperLayerRegularityTower_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong 0 = initial :=
  rfl

@[simp]
theorem fixedUpperLayerRegularityTower_succ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1) =
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine :=
  rfl

theorem fixedUpperLayerRegularityTower_refines
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    OrderedFacePartitionRefines
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).refines

theorem fixedUpperLayerRegularityTower_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ n,
      OrderedFacePartitionRefines
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        initial := by
  intro n
  induction n with
  | zero =>
      exact OrderedFacePartitionRefines.refl initial
  | succ n ih =>
      exact OrderedFacePartitionRefines.trans
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong n)
        ih

theorem fixedUpperLayerRegularityTower_regular
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    IsPreliminaryOrderedRegular
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      upper (ε n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).regular

def fixedUpperLayerComplexityFactor
    (j : ℕ) (budget : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 ^ (j + 1)) ^ (budget n) *
        fixedUpperLayerComplexityFactor j budget n

theorem complexity_fixedUpperLayerRegularityTower_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ (n : ℕ) (e : OrderedFace k j),
      FacePartition.complexity
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n e) ≤
        fixedUpperLayerComplexityFactor j budget n *
          FacePartition.complexity (initial e) := by
  intro n
  induction n with
  | zero =>
      intro e
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      intro e
      let certificate :=
        chosenFixedUpperLayerRegularityCertificate
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n)
          upper (ε n) (budget n)
          (hε n) (hlong n)
      have hstep := certificate.complexity e
      have hexponent :
          (2 ^ (j + 1)) ^ certificate.steps ≤
            (2 ^ (j + 1)) ^ (budget n) :=
        Nat.pow_le_pow_right (by positivity)
          (Nat.le_of_lt certificate.steps_lt)
      rw [fixedUpperLayerRegularityTower_succ]
      calc
        FacePartition.complexity (certificate.fine e) ≤
            (2 ^ (j + 1)) ^ certificate.steps *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          hstep
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          Nat.mul_le_mul_right _ hexponent
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              (fixedUpperLayerComplexityFactor
                  j budget n *
                FacePartition.complexity (initial e)) :=
          Nat.mul_le_mul_left _ (ih e)
        _ =
            fixedUpperLayerComplexityFactor
                j budget (n + 1) *
              FacePartition.complexity (initial e) := by
          simp [fixedUpperLayerComplexityFactor,
            Nat.mul_assoc]

structure FixedUpperLayerCoarseFine
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (length : ℕ) where
  index : ℕ
  index_lt : index < length
  coarse : OrderedFacePartitionSystem G k j
  fine : OrderedFacePartitionSystem G k j
  refines : OrderedFacePartitionRefines fine coarse
  coarse_refines_initial :
    OrderedFacePartitionRefines coarse initial
  fine_regular :
    IsPreliminaryOrderedRegular fine upper (ε index)
  gap_nonneg :
    0 ≤ orderedLayerAtomEnergy fine upper -
      orderedLayerAtomEnergy coarse upper
  gap_le :
    orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        (length : ℝ)
  coarse_complexity :
    ∀ e,
      FacePartition.complexity (coarse e) ≤
        fixedUpperLayerComplexityFactor
            j budget index *
          FacePartition.complexity (initial e)
  fine_complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        fixedUpperLayerComplexityFactor
            j budget (index + 1) *
          FacePartition.complexity (initial e)

theorem FixedUpperLayerCoarseFine.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    {length : ℕ} (hlength : 0 < length) :
    Nonempty
      (FixedUpperLayerCoarseFine
        G k j initial upper ε budget length) := by
  let tower :=
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong
  obtain ⟨i, hi, hgap⟩ :=
    exists_adjacent_real_sub_le_div
      (fun n => orderedLayerAtomEnergy
        (tower n) upper)
      hlength
      (orderedLayerAtomEnergy_nonneg
        (tower 0) upper)
      (orderedLayerAtomEnergy_le_card
        (tower length) upper)
  refine ⟨{
    index := i
    index_lt := hi
    coarse := tower i
    fine := tower (i + 1)
    refines := ?_
    coarse_refines_initial := ?_
    fine_regular := ?_
    gap_nonneg := ?_
    gap_le := hgap
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · exact fixedUpperLayerRegularityTower_refines
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_refines_initial
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_regular
      initial upper ε budget hε hlong i
  · exact sub_nonneg.mpr
      (orderedLayerAtomEnergy_mono
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong i)
        upper)
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong i
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong (i + 1)

noncomputable def chosenFixedUpperLayerCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (length : ℕ) (hlength : 0 < length) :
    FixedUpperLayerCoarseFine
      G k j initial upper ε budget length :=
  Classical.choice
    (FixedUpperLayerCoarseFine.nonempty
      initial upper ε budget hε hlong hlength)

structure StrongOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt : ∀ j, index j < length j
  regular :
    IsFullyPreliminaryOrderedRegular fine
      (selectedOrderedComplexTolerance ε index)
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ) ≤
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  coarse_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (coarse.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j) *
          FacePartition.complexity
            (initial.partition j.castSucc e)
  fine_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (fine.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j + 1) *
          FacePartition.complexity
            (initial.partition j.castSucc e)

namespace StrongOrderedComplexRegularityCertificate

def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines

end StrongOrderedComplexRegularityCertificate

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure CoarseTargetOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt : ∀ j, index j < length j
  mixedRegular :
    ∀ j : Fin r,
      IsPreliminaryOrderedRegular
        (fine.partition j.castSucc)
        (coarse.partition j.succ)
        (ε j (index j))
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ) ≤
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  coarse_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (coarse.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j) *
          FacePartition.complexity
            (initial.partition j.castSucc e)
  fine_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (fine.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j + 1) *
          FacePartition.complexity
            (initial.partition j.castSucc e)

namespace CoarseTargetOrderedComplexRegularityCertificate

def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines

end CoarseTargetOrderedComplexRegularityCertificate

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.AdaptiveCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

namespace AdaptiveCoarseTargetSchedule

def IsAdmissible {k r : ℕ} :
    AdaptiveCoarseTargetSchedule k r → Prop
  | .nil => True
  | .node tolerance budget length next =>
      (∀ n, 0 ≤ tolerance n) ∧
      (∀ n,
        (Fintype.card (OrderedFace k r) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2) ∧
      0 < length ∧
      ∀ i, (next i).IsAdmissible

structure Realization
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r) where
  landing : S.Landing
  certificate :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial
        landing.tolerance landing.budget landing.length
  index_eq : certificate.index = landing.index

end AdaptiveCoarseTargetSchedule

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedConfigurationCounting
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure PositiveOrderedFace (k r : ℕ) where
  lowerRank : Fin r
  face : OrderedFace k (lowerRank.1 + 1)
deriving DecidableEq

namespace PositiveOrderedFace

def equivSigma (k r : ℕ) :
    PositiveOrderedFace k r ≃
      Σ j : Fin r, OrderedFace k (j.1 + 1) where
  toFun e := ⟨e.lowerRank, e.face⟩
  invFun e := ⟨e.1, e.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

noncomputable instance instFintype (k r : ℕ) :
    Fintype (PositiveOrderedFace k r) :=
  Fintype.ofEquiv
    (Σ j : Fin r, OrderedFace k (j.1 + 1))
    (equivSigma k r).symm

def rank {k r : ℕ} (e : PositiveOrderedFace k r) : ℕ :=
  e.lowerRank.1 + 1

@[simp]
theorem rank_pos {k r : ℕ} (e : PositiveOrderedFace k r) :
    0 < e.rank := by
  simp [rank]

noncomputable def boundary
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨e.lowerRank.1 - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) e.lowerRank.2⟩
  refine ⟨j, ?_⟩
  have hj : j.1 + 1 = e.lowerRank.1 := by
    simp only [j]
    omega
  exact hj ▸ eraseBoundaryFace e.face i

@[simp]
theorem boundary_lowerRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    (e.boundary hpos i).lowerRank.1 =
      e.lowerRank.1 - 1 := by
  rfl

end PositiveOrderedFace

def configurationFaceWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (C.partition e.lowerRank.succ e.face)
    (A.atom e.lowerRank.succ e.face) y

noncomputable def partialConfigurationWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) : ℝ :=
  ∏ e ∈ s,
    configurationFaceWeight A e
      (orderedFaceTuple e.face x)

noncomputable def partialConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r)) : ℝ :=
  mean (partialConfigurationWeight A s)

noncomputable def fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) : ℝ :=
  partialConfigurationCount A Finset.univ

@[simp]
theorem partialConfigurationWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    partialConfigurationWeight A ∅ x = 1 := by
  simp [partialConfigurationWeight]

@[simp]
theorem partialConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    partialConfigurationCount A ∅ = 1 := by
  change mean (fun _x : Fin k → G => (1 : ℝ)) = 1
  exact mean_const 1

def positiveFaceLowerLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    OrderedFacePartitionSystem G k e.lowerRank.1 :=
  C.partition e.lowerRank.castSucc

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.ConfigurationWeightedDefect
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def OrderedCoarseFineComplex.coarseDiagonal
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    OrderedCoarseFineComplex G k r where
  coarse := P.coarse
  fine := P.coarse
  refines := OrderedPartitionComplex.Refines.refl P.coarse

noncomputable def mixedConfigurationCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.coarse e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    (orderedFaceTuple e.face A.witness)

noncomputable def mixedConfigurationFineDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.fine e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    y

noncomputable def mixedConfigurationDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationFineDensity P A e y -
    mixedConfigurationCoarseDensity P A e

noncomputable def mixedConfigurationUniform
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  configurationFaceWeight A e y -
    mixedConfigurationFineDensity P A e y

noncomputable def mixedConfigurationBoundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    (orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness))
    y

def IsFullyMixedPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (τ : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ)
      (τ j)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleFrozenUniformity
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    Finset (Fin k) :=
  Finset.univ.map e.face.toEmbedding

@[simp]
theorem positiveOrderedFaceEdge_card
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card = e.rank := by
  simp [positiveOrderedFaceEdge, PositiveOrderedFace.rank]

theorem positiveOrderedFaceEdge_nonempty
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).Nonempty := by
  apply Finset.card_pos.mp
  rw [positiveOrderedFaceEdge_card]
  exact e.rank_pos

theorem positiveOrderedFaceEdge_card_le
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card ≤ r := by
  rw [positiveOrderedFaceEdge_card]
  unfold PositiveOrderedFace.rank
  omega

@[simp]
theorem mem_positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (v : Fin k) :
    v ∈ positiveOrderedFaceEdge e ↔
      v ∈ Set.range e.face := by
  simp [positiveOrderedFaceEdge]

noncomputable def positiveOrderedFaceOfEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨t.card - 1, by
      have htcard : 0 < t.card :=
        Finset.card_pos.mpr ht
      omega⟩
  refine ⟨j, ?_⟩
  have hcard : t.card = j.1 + 1 := by
    dsimp [j]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact t.orderEmbOfFin hcard

@[simp]
theorem positiveOrderedFaceEdge_ofEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    positiveOrderedFaceEdge
        (positiveOrderedFaceOfEdge t ht htr) = t := by
  dsimp only [positiveOrderedFaceEdge, positiveOrderedFaceOfEdge]
  exact Finset.map_orderEmbOfFin_univ t _

noncomputable def orderedConfigurationBaseEdges
    (k r : ℕ) : Finset (Finset (Fin k)) :=
  insert ∅
    (Finset.univ.image
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)))

@[simp]
theorem empty_mem_orderedConfigurationBaseEdges
    (k r : ℕ) :
    ∅ ∈ orderedConfigurationBaseEdges k r := by
  simp [orderedConfigurationBaseEdges]

@[simp]
theorem mem_orderedConfigurationBaseEdges_iff
    {k r : ℕ} (t : Finset (Fin k)) :
    t ∈ orderedConfigurationBaseEdges k r ↔
      t.card ≤ r := by
  constructor
  · intro ht
    rw [orderedConfigurationBaseEdges,
      Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · simp
    · obtain ⟨e, _he, rfl⟩ :=
        Finset.mem_image.mp ht
      exact positiveOrderedFaceEdge_card_le e
  · intro htr
    by_cases ht0 : t = ∅
    · subst t
      exact empty_mem_orderedConfigurationBaseEdges k r
    · have ht : t.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr ht0
      rw [orderedConfigurationBaseEdges,
        Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      refine
        ⟨positiveOrderedFaceOfEdge t ht htr,
          Finset.mem_univ _, ?_⟩
      exact positiveOrderedFaceEdge_ofEdge t ht htr

noncomputable def orderedConfigurationInitialBundle
    (k r : ℕ) :
    HypergraphBundle (Fin k) (Fin k)
      (orderedConfigurationBaseEdges k r) where
  edges := orderedConfigurationBaseEdges k r
  projection := id
  projection_injective_on_edge := by
    intro g hg x hx y hy hxy
    exact hxy
  projection_mem_base := by
    intro g hg
    simpa using hg

@[simp]
theorem orderedConfigurationInitialBundle_edges
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).edges =
      orderedConfigurationBaseEdges k r :=
  rfl

@[simp]
theorem orderedConfigurationInitialBundle_projection
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).projection =
      id :=
  rfl

noncomputable def orderedConfigurationEdgeTuple
    {G : Type*} {k r : ℕ}
    (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r)
    (y : {v : Fin k // v ∈ t} → G) :
    Fin ((positiveOrderedFaceOfEdge t ht htr).lowerRank.1 + 1) → G := by
  let e := positiveOrderedFaceOfEdge t ht htr
  have hcard : t.card = e.lowerRank.1 + 1 := by
    dsimp [e, positiveOrderedFaceOfEdge]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact fun i => y (t.orderIsoOfFin hcard i)

@[simp]
theorem positiveOrderedFaceEdge_orderIsoOfFin_val
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (i : Fin (e.lowerRank.1 + 1)) :
    ((positiveOrderedFaceEdge e).orderIsoOfFin
        (by
          simp [PositiveOrderedFace.rank]) i).1 =
      e.face i := by
  rw [Finset.coe_orderIsoOfFin_apply]
  have hcanonical :
      e.face =
        (positiveOrderedFaceEdge e).orderEmbOfFin
          (by
            simp [PositiveOrderedFace.rank]) := by
    apply Finset.orderEmbOfFin_unique'
    intro q
    simp [positiveOrderedFaceEdge]
  exact congrArg (fun f => f i) hcanonical.symm

noncomputable def orderedConfigurationBaseWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseEdgeWeight (Fin k) G := by
  classical
  intro t y
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact configurationFaceWeight A
        (positiveOrderedFaceOfEdge t ht htr)
        (orderedConfigurationEdgeTuple t ht htr y)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (y : {v : Fin k // v ∈ (∅ : Finset (Fin k))} → G) :
    orderedConfigurationBaseWeight A ∅ y = 1 := by
  simp [orderedConfigurationBaseWeight]

noncomputable def orderedConfigurationBaseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    Finset (Fin k) → ℝ := by
  classical
  intro t
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact mixedConfigurationCoarseDensity P A
        (positiveOrderedFaceOfEdge t ht htr)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    orderedConfigurationBaseDensity P A ∅ = 1 := by
  simp [orderedConfigurationBaseDensity]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem projectedEdge_nonempty
    {K : Type*} [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (_hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (g.image B.projection).Nonempty := by
  exact Finset.image_nonempty.mpr hne

theorem projectedEdge_card_le
    {K : Type*} [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card ≤ r := by
  exact
    (mem_orderedConfigurationBaseEdges_iff
      (g.image B.projection)).1
      (B.projection_mem_base g hg)

noncomputable def orderedConfigurationBundleFace
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    PositiveOrderedFace k r :=
  positiveOrderedFaceOfEdge
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)

noncomputable def orderedConfigurationBundleFaceTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G :=
  orderedConfigurationEdgeTuple
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)
    (B.projectedEdgeTuple hg y)

noncomputable def orderedConfigurationBundleDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationDefect P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

noncomputable def orderedConfigurationBundleUniform
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationUniform P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

noncomputable def orderedConfigurationBundleLocalizedDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  B.orderedConfigurationBundleDefect P A hg hne y *
    B.strictBoundaryLocalProduct g
      (B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)) y

def HasOrderedConfigurationBundleLocalizedDefect
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      mean (fun y =>
        B.orderedConfigurationBundleLocalizedDefect
            P A hg₀ hne y ^ 2) ≤
        β g₀.card *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A))

def HasOrderedConfigurationBundleFrozenUniformity
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        |B.frozenEdgeCorrelation g₀
            (B.orderedConfigurationBundleUniform
              P A hg₀ hne)
            (B.pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) z| ≤
          τ

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem exists_selectedVertex_not_mem_of_mem_erase
    {J K : Type*} [DecidableEq J] [DecidableEq K]
    {H : Finset (Finset J)}
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card) :
    ∃ v ∈ g₀, v ∉ g := by
  classical
  by_contra hmissing
  have hsubset : g₀ ⊆ g := by
    intro v hv
    by_contra hvg
    exact hmissing ⟨v, hv, hvg⟩
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le hsubset (hmax g hgB)
  exact (Finset.mem_erase.mp hg).1 heq.symm

noncomputable def orderedConfigurationBundleFaceState
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    FaceRegularityState
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  ⟨orderedBoundaryPartition
    (positiveFaceLowerLayer P.fine
      (B.orderedConfigurationBundleFace hg hne))
    (B.orderedConfigurationBundleFace hg hne).face⟩

noncomputable def orderedConfigurationBundleFaceTarget
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
      G) → ℝ :=
  partitionAtomIndicator
    (P.coarse.partition
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)
    (A.atom
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)

def HasOrderedConfigurationBundleFrozenCutRepresentation
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        ∃ u :
            CutTestFamily G
              ((B.orderedConfigurationBundleFace
                hg₀ hne).lowerRank.1 + 1),
          IsBoundedCutTest u ∧
            B.frozenEdgeCorrelation g₀
                (B.orderedConfigurationBundleUniform
                  P A hg₀ hne)
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) z =
              (B.orderedConfigurationBundleFaceState
                  P hg₀ hne).faceCutCorrelation
                (B.orderedConfigurationBundleFaceTarget
                  P A hg₀ hne)
                u

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedFullBoundary
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev ProperPositiveOrderedSubface (n : ℕ) :=
  PositiveOrderedFace (n + 1) n

@[simp]
theorem properPositiveOrderedSubface_rank_lt_upper {n : ℕ}
    (d : ProperPositiveOrderedSubface n) :
    d.rank < n + 1 := by
  simp only [PositiveOrderedFace.rank]
  exact Nat.succ_lt_succ d.lowerRank.2

abbrev orderedFullLowerComplexRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    Fin (r + 1) :=
  ⟨d.lowerRank.1 + 1, by
    have hd : d.rank < e.rank := by
      exact properPositiveOrderedSubface_rank_lt_upper d
    have he : e.rank ≤ r := by
      simp only [PositiveOrderedFace.rank]
      exact e.lowerRank.2
    omega⟩

@[simp]
theorem orderedFullLowerComplexRank_val
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    (orderedFullLowerComplexRank e d).1 =
      d.lowerRank.1 + 1 :=
  rfl

abbrev orderedFullLowerAmbientFace
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    OrderedFace k (d.lowerRank.1 + 1) :=
  d.face.trans e.face

@[simp]
theorem orderedFaceTuple_orderedFullLowerAmbientFace
    {G : Type*} {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1)
    (x : Fin k → G) :
    orderedFaceTuple (orderedFullLowerAmbientFace e d) x =
      orderedFaceTuple d.face (orderedFaceTuple e.face x) :=
  rfl

noncomputable def orderedFullLowerConstituentPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.pullback
    (orderedFaceTuple d.face)
    (C.partition
      (orderedFullLowerComplexRank e d)
      (orderedFullLowerAmbientFace e d))

noncomputable def orderedFullLowerPositivePartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ :
      Finset (ProperPositiveOrderedSubface e.lowerRank.1))
    (orderedFullLowerConstituentPartition C e)

noncomputable def orderedFullLowerBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.join
    (orderedBoundaryPartition
      (positiveFaceLowerLayer C e) e.face)
    (orderedFullLowerPositivePartition C e)

noncomputable def orderedFullLowerBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryPartition C e).parts :=
  partitionAtomAt (orderedFullLowerBoundaryPartition C e) x

@[simp]
theorem orderedFullLowerBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryAtomAt C e x).1 =
      (orderedFullLowerBoundaryPartition C e).part x :=
  rfl

noncomputable def orderedFullLowerBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedFullLowerBoundaryPartition C e)
    (orderedFullLowerBoundaryAtomAt C e x)
    y

@[simp]
theorem orderedFullLowerBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y ^ 2 =
      orderedFullLowerBoundaryWeight C e x y :=
  partitionAtomIndicator_sq _ _ _

@[simp]
theorem orderedFullLowerBoundaryWeight_self
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x x = 1 := by
  apply partitionAtomIndicator_of_mem
  exact
    (orderedFullLowerBoundaryPartition C e).mem_part
      (Finset.mem_univ x)

noncomputable def sourceFullMixedCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mixedConfigurationCoarseDensity P A e

noncomputable def sourceFullMixedDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationDefect P A e y

noncomputable def sourceFullMixedBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedFullLowerBoundaryWeight P.coarse e
    (orderedFaceTuple e.face A.witness) y

@[simp]
theorem sourceFullMixedBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y ^ 2 =
      sourceFullMixedBoundaryWeight P A e y :=
  orderedFullLowerBoundaryWeight_sq _ _ _ _

def SourceFullMixedGoodAtFace
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) : Prop :=
  α ≤ sourceFullMixedCoarseDensity P A e ∧
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) ≤
      β

def ClosedOrderedAtomConfiguration.IsSourceFullMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    SourceFullMixedGoodAtFace P A e
      (α e.rank) (β e.rank)

noncomputable def sourceFullMixedLocalizedDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mean fun y =>
    sourceFullMixedDefect P A e y ^ 2 *
      sourceFullMixedBoundaryWeight P A e y

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleSourceGoodnessBridge
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

noncomputable def projectedEdgeOrderIso
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.orderedConfigurationBundleFace hg hne
  have hcard : t.card = e.lowerRank.1 + 1 := by
    have hedge :
        positiveOrderedFaceEdge e = t := by
      dsimp [e, orderedConfigurationBundleFace, t]
      exact positiveOrderedFaceEdge_ofEdge
        (g.image B.projection)
        (B.projectedEdge_nonempty hg hne)
        (B.projectedEdge_card_le hg)
    calc
      t.card = (positiveOrderedFaceEdge e).card :=
        congrArg Finset.card hedge.symm
      _ = e.rank := positiveOrderedFaceEdge_card e
      _ = e.lowerRank.1 + 1 := rfl
  exact (t.orderIsoOfFin hcard).toEquiv

@[simp]
theorem projectedEdgeOrderIso_apply_val
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (i : Fin ((B.orderedConfigurationBundleFace
      hg hne).lowerRank.1 + 1)) :
    ((B.projectedEdgeOrderIso hg hne) i).1 =
      (B.orderedConfigurationBundleFace hg hne).face i := by
  rfl

noncomputable def orderedConfigurationBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.projectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem orderedConfigurationBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.orderedConfigurationBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold orderedConfigurationBundleFaceTupleEquiv
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple projectedEdgeOrderIso
  rfl

def ambientPositiveFaceOfProperSubface
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    PositiveOrderedFace k r where
  lowerRank :=
    ⟨d.lowerRank.1,
      lt_trans d.lowerRank.2 e.lowerRank.2⟩
  face := orderedFullLowerAmbientFace e d

@[simp]
theorem ambientPositiveFaceOfProperSubface_rank
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    (ambientPositiveFaceOfProperSubface e d).rank = d.rank := by
  rfl

noncomputable def orderedConfigurationStrictFaceFamily
    (e : PositiveOrderedFace k r) :
    Finset (PositiveOrderedFace k r) :=
  Finset.univ.filter fun f =>
    positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e

@[simp]
theorem mem_orderedConfigurationStrictFaceFamily
    (e f : PositiveOrderedFace k r) :
    f ∈ orderedConfigurationStrictFaceFamily e ↔
      positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e := by
  simp [orderedConfigurationStrictFaceFamily]

noncomputable def extendConfigurationFaceTuple
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    Fin k → G :=
  (splitOrderedFaceEquiv e.face).symm
    (y, orderedFaceComplementTuple e.face A.witness)

@[simp]
theorem orderedFaceTuple_extendConfigurationFaceTuple
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFaceTuple e.face
        (extendConfigurationFaceTuple P A e y) = y := by
  exact orderedFaceTuple_splitOrderedFaceEquiv_symm _ _ _

@[simp]
theorem extendConfigurationFaceTuple_projection
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G)
    (v : {v : K // v ∈ g}) :
    extendConfigurationFaceTuple P A
        (B.orderedConfigurationBundleFace hg hne)
        (B.orderedConfigurationBundleFaceTuple hg hne y)
        (B.projection v.1) =
      y v := by
  let j := B.projectionEquiv hg v
  let i :=
    (B.projectedEdgeOrderIso hg hne).symm j
  have hi :
      B.projectedEdgeOrderIso hg hne i = j :=
    (B.projectedEdgeOrderIso hg hne).apply_symm_apply j
  have hface :
      (B.orderedConfigurationBundleFace hg hne).face i =
        B.projection v.1 := by
    calc
      (B.orderedConfigurationBundleFace hg hne).face i =
          ((B.projectedEdgeOrderIso hg hne) i).1 := by
        rw [B.projectedEdgeOrderIso_apply_val]
      _ = j.1 := congrArg Subtype.val hi
      _ = B.projection v.1 := by
        exact B.projectionEquiv_apply_val hg v
  rw [← hface]
  change
    orderedFaceTuple
        (B.orderedConfigurationBundleFace hg hne).face
        (extendConfigurationFaceTuple P A
          (B.orderedConfigurationBundleFace hg hne)
          (B.orderedConfigurationBundleFaceTuple hg hne y)) i =
      y v
  rw [orderedFaceTuple_extendConfigurationFaceTuple]
  change
    B.projectedEdgeTuple hg y
        ((B.projectedEdgeOrderIso hg hne) i) =
      y v
  rw [hi]
  exact congrArg y
    ((B.projectionEquiv hg).symm_apply_apply v)

def liftProjectedSubedge
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    Finset K :=
  g₀.filter fun v => B.projection v ∈ t

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullOrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

def topPositiveOrderedFace
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    PositiveOrderedFace k (n + 1) where
  lowerRank := Fin.last n
  face := e

@[simp]
theorem topPositiveOrderedFace_rank
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).rank = n + 1 := by
  rfl

@[simp]
theorem topPositiveOrderedFace_lowerRank_succ
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).lowerRank.succ =
      Fin.last (n + 1) := by
  apply Fin.ext
  rfl

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

noncomputable def sourceFullAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  atomBoundaryDefectSq
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.fine e) e.face)
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    upper a x

noncomputable def sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  largeAverageBaseSupport
    (orderedFullLowerBoundaryPartition P.coarse e)
    (P.sourceFullAtomDefectSq e upper a) β

noncomputable def sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  smallAverageBaseSupport
      (orderedBoundaryPartition
        (positiveFaceLowerLayer P.coarse e) e.face)
      (partitionAtomIndicator upper a) α ∪
    P.sourceFullLargeDefectBaseSupport e upper a β

noncomputable def sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ P.sourceFullAtomBadBaseSupport e upper a α β

noncomputable def sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  P.sourceFullOwnAtomBadBaseSupport e
    (P.coarse.partition e.lowerRank.succ e.face) α β

end OrderedCoarseFineComplex

namespace ClosedOrderedAtomConfiguration

def AvoidsSourceFullBadBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    orderedFaceTuple e.face A.witness ∉
      P.sourceFullCoarseOwnAtomBadBaseSupport e
        (α e.rank) (β e.rank)

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

noncomputable def sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (OrderedPositiveSubface r)).biUnion fun q =>
      orderedFacePullbackFinset q.2
        (P.sourceFullCoarseOwnAtomBadBaseSupport
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

noncomputable def sourceFullBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => P.sourceFullTopBadBaseDeletion e α β

end OrderedCoarseFineComplex

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemovalAssembly
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def orderedRemovalRegularityBudget
    (k j : ℕ) (τ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        τ ^ 2) +
    1

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

noncomputable def growthRegularityLength
    (k j : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card
        (OrderedFace k (j + 1)) : ℝ) / γ) +
    1

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

def adaptiveSelectedCoarseLayerBound
    {k r : ℕ}
    (initialBound : Fin (r + 1) → ℕ)
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      fixedUpperLayerComplexityFactor
          j.1 (P.budget j) (P.index j) *
        initialBound j.castSucc)

structure SourceFullCoarseTargetSchedule
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  schedule : AdaptiveCoarseTargetSchedule k r
  schedule_admissible : schedule.IsAdmissible
  scale : schedule.Landing → Fin (r + 1) → ℕ
  scaleFloor_le_deepest :
    ∀ P, scaleFloor ≤ scale P (Fin.last r)
  scale_hierarchy :
    ∀ P (j : Fin r),
      F (scale P j.succ) ≤ scale P j.castSucc
  selected_tolerance_le_common :
    ∀ P (j : Fin r),
      P.tolerance j (P.index j) ≤
        sourceFullCommonTolerance F (scale P)
  reciprocal_gap_le :
    ∀ P (j : Fin r),
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (P.length j : ℝ) ≤
        sourceFullRankGap F (scale P) j
  selected_coarse_bound :
    ∀ P q,
      adaptiveSelectedCoarseLayerBound initialBound P q ≤
        scale P q

namespace SourceFullCoarseTargetSchedule

theorem scale_antitone
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing) :
    Antitone (S.scale P) := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (S.scale P j.succ)).trans
        (S.scale_hierarchy P j))

theorem scaleFloor_le
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing)
    (q : Fin (r + 1)) :
    scaleFloor ≤ S.scale P q := by
  exact (S.scaleFloor_le_deepest P).trans
    (S.scale_antitone P (Fin.le_last q))

structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  regularity :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length
  scale : Fin (r + 1) → ℕ
  scaleFloor_le : ∀ q, scaleFloor ≤ scale q
  scale_hierarchy :
    ∀ j : Fin r,
      F (scale j.succ) ≤ scale j.castSucc
  selected_tolerance_nonneg :
    ∀ j : Fin r,
      0 ≤
        selectedOrderedComplexTolerance
          tolerance regularity.index j
  selected_tolerance_le_common :
    ∀ j : Fin r,
      selectedOrderedComplexTolerance
          tolerance regularity.index j ≤
        sourceFullCommonTolerance F scale
  rank_gap_le :
    ∀ j : Fin r,
      regularity.toCoarseFine.coarseUpperLayerAtomEnergyGap j ≤
        sourceFullRankGap F scale j
  coarse_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (regularity.coarse.partition q e) ≤
        scale q

def zero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    SourceFullCoarseTargetSchedule
      k 0 initialBound F scaleFloor where
  schedule := .nil
  schedule_admissible := trivial
  scale := fun _ _ =>
    max scaleFloor (initialBound 0)
  scaleFloor_le_deepest := by
    intro P
    exact le_max_left _ _
  scale_hierarchy := by
    intro P j
    exact Fin.elim0 j
  selected_tolerance_le_common := by
    intro P j
    exact Fin.elim0 j
  reciprocal_gap_le := by
    intro P j
    exact Fin.elim0 j
  selected_coarse_bound := by
    intro P q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    change initialBound 0 ≤
      max scaleFloor (initialBound 0)
    exact le_max_right _ _

def lowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (budget : ℕ → ℕ)
    {length : ℕ}
    (i : Fin length) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (fixedUpperLayerComplexityFactor r budget i.1 *
      initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

def node
    {k r : ℕ}
    {initialBound : Fin (r + 2) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (topScale : ℕ)
    (tolerance : ℕ → ℝ)
    (budget : ℕ → ℕ)
    (length : ℕ)
    (next :
      (i : Fin length) →
        SourceFullCoarseTargetSchedule
          k r (lowerInitialBound initialBound budget i)
            F (F topScale))
    (htolerance : ∀ n, 0 ≤ tolerance n)
    (hbudget :
      ∀ n,
        (Fintype.card
            (OrderedFace k (r + 1)) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2)
    (hlength : 0 < length)
    (hscaleFloor : scaleFloor ≤ topScale)
    (hinitialTop :
      initialBound (Fin.last (r + 1)) ≤ topScale)
    (htopTolerance :
      ∀ (i : Fin length)
          (P : (next i).schedule.Landing),
        tolerance i.1 ≤
          sourceFullCommonTolerance F ((next i).scale P))
    (htopGap :
      (Fintype.card
          (OrderedFace k (r + 1)) : ℝ) /
            (length : ℝ) ≤
        1 / (F topScale : ℝ) ^ 2) :
    SourceFullCoarseTargetSchedule
      k (r + 1) initialBound F scaleFloor where
  schedule :=
    .node tolerance budget length
      (fun i => (next i).schedule)
  schedule_admissible := by
    exact ⟨htolerance, hbudget, hlength,
      fun i => (next i).schedule_admissible⟩
  scale :=
    nodeScale topScale
      (fun i => (next i).scale)
  scaleFloor_le_deepest := by
    intro P
    cases P with
    | node chosen lower =>
        simpa only [nodeScale_node_last] using
          hscaleFloor
  scale_hierarchy := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [Fin.succ_last,
              nodeScale_node_last,
              nodeScale_node_castSucc] using
              (next chosen).scaleFloor_le_deepest lower
        | cast q =>
            simpa only [Fin.succ_castSucc,
              nodeScale_node_castSucc] using
              (next chosen).scale_hierarchy lower q
  selected_tolerance_le_common := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_last,
              AdaptiveCoarseTargetSchedule.Landing.index_node_last,
              sourceFullCommonTolerance_nodeScale] using
              htopTolerance chosen lower
        | cast q =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_castSucc,
              AdaptiveCoarseTargetSchedule.Landing.index_node_castSucc,
              sourceFullCommonTolerance_nodeScale] using
              (next chosen).selected_tolerance_le_common
                lower q
  reciprocal_gap_le := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_last,
              sourceFullRankGap, Fin.succ_last,
              nodeScale_node_last, Fin.val_last]
            convert htopGap using 1
        | cast q =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_castSucc,
              sourceFullRankGap, Fin.succ_castSucc,
              nodeScale_node_castSucc,
              Fin.val_castSucc]
            convert
              (next chosen).reciprocal_gap_le lower q using 1
            · congr 1
  selected_coarse_bound := by
    intro P q
    cases P with
    | node chosen lower =>
        cases q using Fin.lastCases with
        | last =>
            simpa [adaptiveSelectedCoarseLayerBound,
              nodeScale_node_last] using
              hinitialTop
        | cast q =>
            cases q using Fin.lastCases with
            | last =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower (Fin.last r)
            | cast j =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower j.castSucc

structure Bounded
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  plan :
    SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor
  ceiling : ℕ
  scale_zero_le :
    ∀ P : plan.schedule.Landing,
      plan.scale P 0 ≤ ceiling

namespace Bounded

def castInitialBound
    {k r : ℕ}
    {initialBound newInitialBound :
      Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : Bounded k r initialBound F scaleFloor)
    (h : initialBound = newInitialBound) :
    Bounded k r newInitialBound F scaleFloor where
  plan := h ▸ S.plan
  ceiling := S.ceiling
  scale_zero_le := by
    subst newInitialBound
    exact S.scale_zero_le

end Bounded

def boundedZero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Bounded k 0 initialBound F scaleFloor where
  plan := zero k initialBound F scaleFloor
  ceiling := max scaleFloor (initialBound 0)
  scale_zero_le := by
    intro P
    change
      max scaleFloor (initialBound 0) ≤
        max scaleFloor (initialBound 0)
    exact le_rfl

noncomputable def sourceFullStageFactor
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      let previous :=
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n
      let lower :=
        lowerBuilder
          (factorLowerInitialBound
            initialBound previous)
      let tolerance :=
        growthRegularityStepTolerance
          F lower.ceiling
      let budget :=
        orderedRemovalRegularityBudget
          k r tolerance
      (2 ^ (r + 1)) ^ budget * previous

noncomputable def sourceFullStageBound
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Fin (r + 1) → ℕ :=
  factorLowerInitialBound initialBound
    (sourceFullStageFactor
      initialBound F topScale lowerBuilder n)

noncomputable def sourceFullStagePlan
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Bounded k r
      (sourceFullStageBound
        initialBound F topScale lowerBuilder n)
      F (F topScale) :=
  lowerBuilder
    (sourceFullStageBound
      initialBound F topScale lowerBuilder n)

noncomputable def sourceFullStageTolerance
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℝ :=
  growthRegularityStepTolerance F
    (sourceFullStagePlan
      initialBound F topScale lowerBuilder n).ceiling

noncomputable def sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℕ :=
  orderedRemovalRegularityBudget k r
    (sourceFullStageTolerance
      initialBound F topScale lowerBuilder n)

@[simp]
theorem sourceFullStageFactor_zero
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    sourceFullStageFactor
      initialBound F topScale lowerBuilder 0 = 1 :=
  rfl

@[simp]
theorem sourceFullStageFactor_succ
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    sourceFullStageFactor
        initialBound F topScale lowerBuilder (n + 1) =
      (2 ^ (r + 1)) ^
          sourceFullStageBudget
            initialBound F topScale lowerBuilder n *
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n :=
  rfl

theorem fixedUpperLayerComplexityFactor_sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ∀ n,
      fixedUpperLayerComplexityFactor r
          (sourceFullStageBudget
            initialBound F topScale lowerBuilder) n =
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            fixedUpperLayerComplexityFactor r
              (sourceFullStageBudget
                initialBound F topScale lowerBuilder) n =
          (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            sourceFullStageFactor
              initialBound F topScale lowerBuilder n
      rw [ih]

theorem lowerInitialBound_sourceFullStageBudget
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i =
      sourceFullStageBound
        initialBound F topScale lowerBuilder i.1 := by
  funext q
  cases q using Fin.lastCases with
  | last =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound,
        fixedUpperLayerComplexityFactor_sourceFullStageBudget]
  | cast q =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound]

noncomputable def sourceFullStageNext
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    Bounded k r
      (lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i)
      F (F topScale) :=
  (sourceFullStagePlan
      initialBound F topScale lowerBuilder i.1).castInitialBound
    (lowerInitialBound_sourceFullStageBudget
      initialBound F topScale lowerBuilder i).symm

@[simp]
theorem sourceFullStageNext_ceiling
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    (sourceFullStageNext
      initialBound F topScale lowerBuilder i).ceiling =
      (sourceFullStagePlan
        initialBound F topScale lowerBuilder i.1).ceiling :=
  rfl

end SourceFullCoarseTargetSchedule

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullBundleRemovalParameters
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def sourceBundleRemovalGrowth (Q N : ℕ) : NatGrowthFunction where
  toFun m := Q * (m + 1) ^ N + (m + 1)
  monotone' := by
    intro a b hab
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left Q
        (Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) N)
    · exact Nat.add_le_add_right hab 1
  above_diagonal := by
    intro m
    exact (Nat.le_add_left (m + 1) (Q * (m + 1) ^ N))

@[simp]
theorem sourceBundleRemovalGrowth_apply
    (Q N m : ℕ) :
    sourceBundleRemovalGrowth Q N m =
      Q * (m + 1) ^ N + (m + 1) :=
  rfl

namespace SourceFullCoarseTargetSchedule.Bounded

structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r) where
  toSourceFull :
    SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor
  scale_zero_le_ceiling : toSourceFull.scale 0 ≤ S.ceiling

end SourceFullCoarseTargetSchedule.Bounded

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Conclusions
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

noncomputable def frozenProjectedEdgeOrderIso
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.orderedConfigurationBundleFace hg hne
  have hcard : t.card = e.lowerRank.1 + 1 := by
    have hedge :
        positiveOrderedFaceEdge e = t := by
      dsimp [e, orderedConfigurationBundleFace, t]
      exact positiveOrderedFaceEdge_ofEdge
        (g.image B.projection)
        (B.projectedEdge_nonempty hg hne)
        (B.projectedEdge_card_le hg)
    calc
      t.card = (positiveOrderedFaceEdge e).card :=
        congrArg Finset.card hedge.symm
      _ = e.rank := positiveOrderedFaceEdge_card e
      _ = e.lowerRank.1 + 1 := rfl
  exact (t.orderIsoOfFin hcard).toEquiv

noncomputable def frozenOccurrenceOrderEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {v : K // v ∈ g} :=
  (B.frozenProjectedEdgeOrderIso hg hne).trans
    (B.projectionEquiv hg).symm

noncomputable def frozenBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.frozenProjectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.frozenBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold frozenBundleFaceTupleEquiv frozenProjectedEdgeOrderIso
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple
  rfl

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_symm_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G)
    (v : {v : K // v ∈ g}) :
    (B.frozenBundleFaceTupleEquiv hg hne).symm x v =
      x ((B.frozenOccurrenceOrderEquiv hg hne).symm v) := by
  rfl

noncomputable def frozenBundleMissingVertex
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) : {v : K // v ∈ g₀} :=
  if hg : g ∈ B.edges.erase g₀ then
    ⟨Classical.choose
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax),
      (Classical.choose_spec
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).1⟩
  else
    ⟨Classical.choose hne, Classical.choose_spec hne⟩

noncomputable def frozenBundleMissingCoordinate
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) :
    Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
    (B.frozenBundleMissingVertex hmax hne g)

noncomputable def frozenBundleInsertedSelectedTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G) :
    {v : K // v ∈ g₀} → G :=
  (B.frozenBundleFaceTupleEquiv hg₀ hne).symm
    (Fin.insertNth i a y)

noncomputable def frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G)
    (z : EdgeComplement g₀ → G) : K → G :=
  (splitEdgeEquiv g₀).symm
    (B.frozenBundleInsertedSelectedTuple hg₀ hne i a y, z)

noncomputable def frozenBundleRemainderCutTest
    {K : Type*} [Fintype K] [DecidableEq K]
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G) :
    CutTestFamily G
      ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  fun i y =>
    ∏ g ∈ B.edges.erase g₀,
      if _hcoord :
          B.frozenBundleMissingCoordinate hg₀ hmax hne g = i
      then
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a y z))
      else 1

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def sourceBundleRemovalHorizon (k r : ℕ) : ℕ :=
  bundleReverseDoublingHorizon r
    (orderedConfigurationInitialBundle k r).edges.card 0

noncomputable def sourceBundleRemovalDensityBudget
    (ε : ℝ) (r : ℕ) : ℝ :=
  min ε 1 /
    (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ)

noncomputable def sourceBundleRemovalStep (k r : ℕ) : ℝ :=
  1 /
    (4 * (r * sourceBundleRemovalHorizon k r + 1 : ℕ) : ℕ)

noncomputable def sourceBundleRemovalKappa (k r : ℕ) : ℝ :=
  sourceBundleRemovalStep k r / 8

noncomputable def sourceBundleRemovalCountThreshold
    (k r ceiling : ℕ) (δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    sourceBundleDensity δ ceiling ^
      Fintype.card (PositiveOrderedFace k r)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UnbalancedBohrShape
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

noncomputable def unbalancedMinimumWidth (S : CyclicBohr.Set N) (M c p H : ℝ) (q : ℕ) : ℝ :=
  (localizedAverageScale S.rank (M ^ (2 * q)) ((1 + c) ^ q - (1 + c / 2) ^ q) : ℝ) *
    (localizedAverageScale (S.rank + unbalancedRankExtra c p H) (M ^ 2) (c / 64) : ℝ) *
    S.radius / 8 * Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
      (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + S.rank))))

end Erdos3.LocalConvolution

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3

open Module

theorem FreeNilpotentLieAlgebra.of_mem_treeGenerators
    (X : Type*) [Fintype X] (s : ℕ) (hs : 1 ≤ s) (x : X) :
    FreeNilpotentLieAlgebra.of X s x ∈ FreeNilpotentLieAlgebra.treeGenerators X s := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨FreeMagma.of x, Finset.mem_filter.mpr ⟨?_, hs⟩, rfl⟩
  exact mem_finiteLieTrees_of_length_le X (FreeMagma.of x) hs

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

namespace LieGradingExpansion

variable {v : I → L} {g : I → σ →₀ ℕ} (E : LieGradingExpansion v g)

theorem component_mem_span {S : Set (σ →₀ ℕ)} {x : L} (hx : x ∈ homogeneousLieSpan v g S)
    (α : σ →₀ ℕ) : E.component α x ∈ homogeneousLieSpan v g (S ∩ {α}) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [E.component_tree]
    split_ifs with h
    · exact Submodule.subset_span ⟨a, ⟨ha, h⟩, rfl⟩
    · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem component_eq_zero {S : Set (σ →₀ ℕ)} {x : L} (hx : x ∈ homogeneousLieSpan v g S)
    {α : σ →₀ ℕ} (hα : α ∉ S) : E.component α x = 0 := by
  have hc := E.component_mem_span hx α
  have he : S ∩ {α} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro β ⟨hβ, rfl⟩
    exact hα hβ
  rw [he, homogeneousLieSpan_empty, Submodule.mem_bot] at hc
  exact hc

include E in
theorem span_inter (S T : Set (σ →₀ ℕ)) :
    homogeneousLieSpan v g (S ∩ T) = homogeneousLieSpan v g S ⊓ homogeneousLieSpan v g T := by
  apply le_antisymm
  · exact le_inf (homogeneousLieSpan_mono v g Set.inter_subset_left)
      (homogeneousLieSpan_mono v g Set.inter_subset_right)
  · intro x hx
    have hc : ∀ α, coefficients (E.expand x) α ∈ homogeneousLieSpan v g (S ∩ T) := by
      intro α
      change E.component α x ∈ homogeneousLieSpan v g (S ∩ T)
      by_cases hα : α ∈ T
      · apply homogeneousLieSpan_mono v g _ (E.component_mem_span hx.1 α)
        rintro β ⟨hβ, rfl⟩
        exact ⟨hβ, hα⟩
      · rw [E.component_eq_zero hx.2 hα]
        exact Submodule.zero_mem _
    have h := (eval_mem_iff_coefficients (homogeneousLieSpan v g (S ∩ T)) (E.expand x)).mpr
      hc (fun _ : σ => (1 : ℚ))
    rwa [E.eval_one] at h

end LieGradingExpansion
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationSizes
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct Matrix
open VectorPolynomial

structure RankPreparationLayer (I J : Type) where
  Coord : Type
  Column : Type
  Row : Type
  coordFinite : Fintype Coord
  columnFinite : Fintype Column
  rowFinite : Fintype Row
  label : Coord → J
  basis : Matrix Coord Column ℚ
  rows : Matrix Row Coord ℚ
  poly : VectorPolynomial I ℝ (Coord → ℝ)

attribute [instance] RankPreparationLayer.coordFinite RankPreparationLayer.columnFinite
  RankPreparationLayer.rowFinite

namespace RankPreparationLayer

variable {I J : Type}

noncomputable def space (L : RankPreparationLayer I J) : Submodule ℝ (L.Coord → ℝ) :=
  jointRationalSpace L.basis L.rows

noncomputable def rank (L : RankPreparationLayer I J) : ℕ := Module.finrank ℝ L.space

noncomputable def value [DecidableEq J] (L : RankPreparationLayer I J) (x : I → ℝ) : J → ℝ :=
  coordinateCopySum L.label (eval x L.poly)

noncomputable def reindex (L : RankPreparationLayer I J) (f : I → MvPolynomial I ℝ) :
    RankPreparationLayer I J := { L with poly := substitute f L.poly }

@[simp] theorem reindex_space (L : RankPreparationLayer I J) (f : I → MvPolynomial I ℝ) :
    (L.reindex f).space = L.space := rfl

@[simp] theorem reindex_rank (L : RankPreparationLayer I J) (f : I → MvPolynomial I ℝ) :
    (L.reindex f).rank = L.rank := rfl

noncomputable def empty : RankPreparationLayer I J where
  Coord := PEmpty
  Column := PEmpty
  Row := PEmpty
  coordFinite := inferInstance
  columnFinite := inferInstance
  rowFinite := inferInstance
  label := PEmpty.elim
  basis := 0
  rows := 0
  poly := 0

@[simp] theorem empty_rank : (empty : RankPreparationLayer I J).rank = 0 := by
  apply Module.finrank_zero_iff.mpr
  change Subsingleton (jointRationalSpace (0 : Matrix PEmpty PEmpty ℚ) 0)
  infer_instance

@[simp] theorem empty_value [DecidableEq J] (x : I → ℝ) :
    (empty : RankPreparationLayer I J).value x = 0 := by
  have hzero (y : PEmpty → ℝ) : coordinateCopySum (PEmpty.elim : PEmpty → J) y = 0 := by
    ext j
    simp only [coordinateCopySum_apply, Fintype.sum_empty, Pi.zero_apply]
  exact hzero _

noncomputable def initial [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) : RankPreparationLayer I J where
  Coord := J
  Column := J
  Row := PEmpty
  coordFinite := inferInstance
  columnFinite := inferInstance
  rowFinite := inferInstance
  label := id
  basis := 1
  rows := 0
  poly := p

@[simp] theorem initial_value [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) (x : I → ℝ) : (initial p).value x = eval x p := by
  ext j
  change (coordinateCopySum (R := ℝ) (id : J → J) (eval x p)) j = _
  simp [coordinateCopySum_apply]

end RankPreparationLayer
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

abbrev RankPreparationFamily (I J : Type) (s : ℕ) := Fin s → RankPreparationLayer I J

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

attribute [local instance] OAI.Erdos3.crtInputModulusNeZero
noncomputable def crtPolynomialInputLaw
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l)) :
    FiniteProbabilityWeights (V → ZMod (∏ l, p l ^ A l)) :=
  (crtPrimePowerPolynomialLaw (V := V) p A).fiberLaw
    (prescribedCRTPolynomialInput p A e hq origin)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateRootBudget_eq :
    allocatedExternalCandidateRootBudget B U b S =
      allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  simp only [allocatedExternalCandidateRootBudget, allocatedPhysicalRootBudget,
    Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add]

theorem allocatedExternalCandidateRootBudget_nonneg :
    0 ≤ allocatedExternalCandidateRootBudget B U b S :=
  mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end Erdos3.VectorPolynomial

end

end OAI
end


