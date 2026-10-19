-- Prove2me | Definitions.Def_OAIE3v2B208
-- name    : OAIE3v2B208
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:12:10.070823+00:00
-- url     : https://prove2.me/theorems/eb4d87e1-d2ce-4ac9-bc00-b8b1e329c571
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 212 of 311
-- statement:
--   Definitions bundle 212 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B178`, `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B189`, `OAIE3v2B190` of this split.
--
--   Modules: `Dynamics/ActualPathCurrentGradeReset.lean`, `Dynamics/TranslationMajorDetectedPotential.lean`, `Dynamics/TranslationMajorDimensionBudget.lean`, `Estimates/ControlledDetectedTranslationBaseBounds.lean`, `Estimates/DetectedTranslationMajorBase.lean`, `Estimates/DetectedTranslationNormalizedLogBounds.lean`, `Estimates/JoinedPairQuotientRefiltration.lean`, `Estimates/PreparedLayerFreezing.lean`, `Estimates/RealSymbolGradeQuotientSplitting.lean`, `Estimates/TranslationMajorCorrelationIdentity.lean`, `Fourier/MajorPhaseLowFourierExtraction.lean`, `Geometry/AllocatedRecoveredNormalizedTopChart.lean`, `Geometry/DetectedTranslationLogCoordinates.lean`, `Lattices/IntegerFrozenChart.lean`, `Lattices/LowTaggedAffineCoordinates.lean`, `Lattices/NativePairAffineCellStepDrop.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Linear/NativePairSymbolProjection.lean`, `Linear/SpatialFrameSlopeBudget.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/DetectedTranslationBasePolynomialBounds.lean`, `Polynomial/DetectedTranslationPhaseDegree.lean`, `Polynomial/FrozenPolynomialAffineRange.lean`, `Polynomial/HomogeneousRealSymbolPolynomial.lean`, `Polynomial/LowTaggedPolynomialCoordinates.lean`, `Polynomial/MajorPhaseDetectedDecomposition.lean`, `Polynomial/TranslationMajorTwistedCorrelationStepDropPolynomial.lean`, `Probability/AllocatedMixedLiftNormalizedMass.lean`, `Probability/AllocatedRecoveredChartMass.lean`, `Sampling/LowTaggedSamplingRank.lean`, `Sampling/RationalHomogeneousSymbolPullbackGrid.lean`, `Sampling/WeightedTranslationProjectionGridBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B189
import Definitions.Def_OAIE3v2B190

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ)

theorem scalarSymbolPolynomial_weightedComponent_normalized_splitting
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (hθ : ∀ x ∈ W, θ x = 0) (k : ℕ)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (hE : F.realSymbolGradeQuotientHom w k E₀ = F.realSymbolGradeQuotientHom w k E)
    (hR : F.realSymbolGradeQuotientHom w k R = F.realSymbolGradeQuotientHom w k R₀) :
    MvPolynomial.weightedHomogeneousComponent w k
      (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * (E * P * R) * R₀⁻¹)) =
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * E)) +
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (R * R₀⁻¹)) := by
  have hproj := (F.polynomialSymbolFiltration w).realGradeProjection_normalized_splitting
    (F.polynomialSymbolBasis b ω hF w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hF w) k E P R E₀ R₀ hE hR
  have he := congrArg (fun x => F.realGradedSymbolPolynomial b ω hF w x) hproj
  simp only [map_add,
    F.realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart] at he
  have hc := congrArg (coordinate (realifyFunctional θ).toAddMonoidHom) he
  have hcoord_add (p q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
      coordinate (realifyFunctional θ).toAddMonoidHom (p + q) =
        coordinate (realifyFunctional θ).toAddMonoidHom p +
        coordinate (realifyFunctional θ).toAddMonoidHom q := by
    ext α
    simp only [coeff_coordinate, map_add, Finsupp.add_apply, MvPolynomial.coeff_add]
  simp only [hcoord_add, coordinate_weightedHomogeneousPart] at hc
  change MvPolynomial.weightedHomogeneousComponent w k
      (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * (E * P * R) * R₀⁻¹)) =
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * E)) +
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ P) +
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (R * R₀⁻¹)) at hc
  simpa only [F.scalarSymbolPolynomial_eq_zero_of_fast b ω hF w θ W hθ P hP,
    map_zero, add_zero] using hc

theorem scalarSymbolPolynomial_homogeneous_normalized_splitting
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hθW : ∀ x ∈ W, θ x = 0) (k : ℕ)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : σ => 1) W))
    (hE : F.realSymbolGradeQuotientHom (fun _ : σ => 1) k E₀ =
      F.realSymbolGradeQuotientHom (fun _ : σ => 1) k E)
    (hR : F.realSymbolGradeQuotientHom (fun _ : σ => 1) k R =
      F.realSymbolGradeQuotientHom (fun _ : σ => 1) k R₀) :
    MvPolynomial.homogeneousComponent k
      (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) θ
        (E₀⁻¹ * (E * P * R) * R₀⁻¹)) =
      MvPolynomial.homogeneousComponent k
        (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) θ (E₀⁻¹ * E)) +
      MvPolynomial.homogeneousComponent k
        (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) θ (R * R₀⁻¹)) :=
  F.scalarSymbolPolynomial_weightedComponent_normalized_splitting b ω hF
    (fun _ : σ => 1) W θ hθW k E P R E₀ R₀ hP hE hR

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.HomogeneousRealSymbolPolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct
attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolHomogeneousPullback realSymbolOfGradedPolynomial realSymbolOfPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)

theorem realPolynomialSymbolHom_homogeneousChart
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (h : (F.realification.adaptedPolynomialFiltration v).Group)
    (hlog : (h.coord : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) :
    F.realPolynomialSymbolHom b ω hF v h =
      F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
        (F.realPolynomialSymbolHom b ω hF w g) := by
  apply NilpotentLieBCHGroup.ext
  change F.realSymbolOfPolynomial b ω hF v (h.coord : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
    F.realSymbolHomogeneousPullback b ω hF w v β
      (F.realSymbolOfPolynomial b ω hF w (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  rw [hlog]
  exact F.realSymbolOfPolynomial_homogeneousChart b ω hF w v β hβ _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ActualPathCurrentGradeReset
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_actual_path_common_quotient_splitting
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ,
      (fun i => MvPolynomial.eval u (weightedHomogeneousComponent v (w i) (β i))) ∈ K)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t
        (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈ realificationLieSubalgebra U)
    (El Pl Rl : F.RealPolynomialSymbolGroup v)
    (hlocal : El * Pl * Rl = F.realPolynomialSymbolHom b ω hF v
      (F.weightedAdaptedRealChartHom w v β hβ g)) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
      (fun i => weightedHomogeneousComponent v (w i) (β i))
      (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    ∃ P₀ : F.RealPolynomialSymbolGroup v,
      F.realSymbolGradeQuotientHom v k P₀ ∈
        (NilpotentLieBCHGroup.realificationSubgroup
          (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
          (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) ∧
      pull E * P₀ * pull R = El * Pl * Rl := by
  have hactual := F.realPolynomialSymbolHom_weightedAdaptedRealChart b ω hF w v β hβ g
  exact F.exists_restricted_path_common_quotient_splitting b ω hF w v
    (fun i => weightedHomogeneousComponent v (w i) (β i))
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    U K hK E (F.realPolynomialSymbolHom b ω hF w g) R k hx El Pl Rl (hlocal.trans hactual)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativePairSymbolProjection
namespace OAI

universe sourceLevel

section

namespace Erdos3.RationalFilteredNilmanifold
open Module
variable {L M : Type sourceLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}

 theorem pairFrequency_zero_comp (η : L →ₗ[ℚ] ℚ) :
    pairFrequency η (0 : M →ₗ[ℚ] ℚ) =
      η.comp (liePiEval (R := ℚ) (M := BoolLieFamily L M) true).toLinearMap := by
  apply LinearMap.ext
  intro x
  change pairFrequency η (0 : M →ₗ[ℚ] ℚ) x = η (x true)
  rw [pairFrequency_apply]
  exact add_zero _

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ J : Type*} [Fintype σ]

theorem exists_controlled_projected_potential_lifts
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype))
    (g : J → PolynomialTranslationLie σ)
    (hspan : Submodule.span ℚ (Set.range g) = U)
    {H : ℕ} (hH : 1 ≤ H)
    (hbaseHeight : ∀ j i, RationalHeightLE ((g j).base i) H)
    (hpolyHeight : ∀ j, RationalPolynomialHeightLE (g j).polynomial H) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (A : (Fin n → ℚ) →ₗ[ℚ] (σ → ℚ))
      (L : Fin n → PolynomialTranslationLie σ),
      n ≤ Fintype.card σ ∧ (∀ j, 0 < v j) ∧ (∀ j, v j ≤ d) ∧
      Function.Injective A ∧ A.range = U.map baseLinear ∧
      (∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0) ∧
      (∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) ∧
      (∀ j, L j ∈ U) ∧ (∀ j, (L j).base = A (Pi.single j 1)) ∧
      (∀ j, (L j).polynomial.IsWeightedHomogeneous w (d - v j)) ∧
      (∀ j, RationalPolynomialHeightLE (L j).polynomial H) ∧
      ∀ j, (L j).polynomial.totalDegree ≤ d := by
  classical
  have hgm : ∀ a, g a ∈ U := by
    intro a
    rw [← hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hspanbase : Submodule.span ℚ (Set.range (fun a => (g a).base)) =
      U.map baseLinear := by
    rw [← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  obtain ⟨n, v, A, hn, hv, hvd, hinj, hrange, hweight, hheight, hselected⟩ :=
    exists_controlled_graded_base_coordinates w d hw hwd (U.map baseLinear)
      (basisGradedSubmodule_ambient_base_image w d hw U hU hgraded)
      (fun a => (g a).base) hspanbase hH hbaseHeight
  choose a ha using hselected
  let x (j : Fin n) : weightedSubalgebra w d := ⟨g (a j), hU (hgm (a j))⟩
  let y (j : Fin n) : weightedSubalgebra w d :=
    basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) (v j) (x j)
  refine ⟨n, v, A, fun j => (y j).val, hn, hv, hvd, hinj, hrange, hweight,
    hheight, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hgraded (v j) (x j) (hgm (a j))
  · intro j
    change weightedBaseLinear w d (y j) = A (Pi.single j 1)
    rw [show y j = basisGradeProjection (weightedBasis w d hw)
      (weightedBasisGrade w d) (v j) (x j) from rfl, base_gradeProjection]
    exact (ha j).symm
  · intro j
    exact weightedBasis_projection_isWeightedHomogeneous w d (v j) hw (x j)
  · intro j
    exact weightedBasis_projection_polynomial_height w d (v j) hw (x j) hH
      (hpolyHeight (a j))
  · intro j
    have hhom := weightedBasis_projection_isWeightedHomogeneous w d (v j) hw (x j)
    exact (_root_.OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights hhom hw).trans (Nat.sub_le d (v j))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ J : Type*} [Fintype σ]

theorem exists_controlled_projected_potential
    (w : σ → ℕ) {d H : ℕ} (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hbound : U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.toSubmodule.comap (weightedSubalgebra w d).subtype))
    (g : J → PolynomialTranslationLie σ)
    (hspan : Submodule.span ℚ (Set.range g) = U.toSubmodule) (hH : 1 ≤ H)
    (hbase : ∀ j i, RationalHeightLE ((g j).base i) H)
    (hpoly : ∀ j, RationalPolynomialHeightLE (g j).polynomial H)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    ∃ (n : ℕ) (W : MvPolynomial σ ℚ), n ≤ Fintype.card σ ∧
      W.IsWeightedHomogeneous w d ∧
      (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map baseLinear,
        eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial) ∧
      RationalPolynomialHeightLE W
        (linearRestrictionHeight n (Fintype.card σ) d
          (rationalKernelHeight (Fintype.card σ) H)
          ((n + 1) * (d * linearRestrictionHeight (Fintype.card σ) n d H H) ^ n)) := by
  classical
  obtain ⟨n, v, A, L, hn, hv, hvd, hA, hrange, hweight, hAheight,
    hL, hLbase, hLhom, hLheight, hLdegree⟩ :=
    exists_controlled_projected_potential_lifts w d hw hwd U.toSubmodule
      hbound hgraded g hspan hH hbase hpoly
  obtain ⟨B, hBA, hBweight, hBheight⟩ :=
    exists_controlled_weighted_leftInverse A v w hweight hA hH hAheight
  let P := fun j => polynomialLinearRestriction A (L j).polynomial
  let V := weightedPolynomialPotential v d P
  let W := polynomialLinearRestriction B V
  have hPheight : ∀ j, RationalPolynomialHeightLE (P j)
      (linearRestrictionHeight (Fintype.card σ) n d H H) := by
    intro j
    simpa only [Fintype.card_fin] using polynomialLinearRestriction_height
      A (L j).polynomial (fun i k => hAheight k i) (hLheight j) (hLdegree j)
  have hPhom : ∀ j, (P j).IsWeightedHomogeneous v (d - v j) :=
    fun j => polynomialLinearRestriction_isWeightedHomogeneous A v w hweight (hLhom j)
  have hVheight : RationalPolynomialHeightLE V
      ((n + 1) * (d * linearRestrictionHeight (Fintype.card σ) n d H H) ^ n) := by
    simpa only [Fintype.card_fin] using weightedPolynomialPotential_height v hd P hvd hPheight
  have hVhom : V.IsWeightedHomogeneous v d :=
    weightedPolynomialPotential_homogeneous v d P hvd hPhom
  have hW := explicit_projected_weighted_potential w v hd hvd A hA B hBA hweight hBweight
    U (fun _ hx => topProjection_mem_of_basisGraded w d hw hd U.toSubmodule hbound hgraded hx)
    frequency hfrequency hkill L hL hLbase hLhom
  refine ⟨n, W, hn, hW.1, ?_, ?_⟩
  · intro x hx z hz
    apply hW.2 x hx
    · rw [hrange]
      exact ⟨x, hx, rfl⟩
    · rwa [hrange]
  · simpa only [Fintype.card_fin] using polynomialLinearRestriction_height B V
      (fun i j => hBheight j i) hVheight (_root_.OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights hVhom hv)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

theorem exists_controlled_projected_potential_bounds (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ J : Type*} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i),
      (∀ i, w i ≤ d) →
      ∀ U : LieSubalgebra ℚ (PolynomialTranslationLie σ),
      U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule →
      BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
        (U.toSubmodule.comap (weightedSubalgebra w d).subtype) →
      ∀ (g : J → PolynomialTranslationLie σ),
      Submodule.span ℚ (Set.range g) = U.toSubmodule →
      ∀ H : ℕ, 1 ≤ H →
      (∀ j i, RationalHeightLE ((g j).base i) H) →
      (∀ j, RationalPolynomialHeightLE (g j).polynomial H) →
      ∀ (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ),
      frequency constantDirection ≠ 0 →
      (∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) →
      ∀ p : ℝ, 0 ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      ∃ (W : MvPolynomial σ ℚ) (q : ℕ),
        W.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map baseLinear,
          eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (fun α => W.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (map (algebraMap ℚ ℝ) W) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ α, ((W.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((W.coeff α).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_projectedPotential_height_budget d
  refine ⟨C, hC, ?_⟩
  intro σ J _ w hw hwd U hbound hgraded g hspan H hH hbase hpoly
    frequency hfrequency hkill p hp hN hHp
  obtain ⟨n, W, hn, hW, hderiv, hheight⟩ := exists_controlled_projected_potential
    w hw hd hwd U hbound hgraded g hspan hH hbase hpoly frequency hfrequency hkill
  change RationalPolynomialHeightLE W (projectedPotentialHeight (Fintype.card σ) n d H) at hheight
  have hb := hbudget (Fintype.card σ) n H p hp hn hN hHp
  have hdegree := _root_.OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights hW hw
  have hcard : W.support.card ≤ (Fintype.card σ + 1) ^ d :=
    boundedExponentSet_card_le W.support d (fun _ hα => (le_totalDegree hα).trans hdegree)
  have hden : polynomialDenominator W ≤
      projectedPotentialHeight (Fintype.card σ) n d H ^ ((Fintype.card σ + 1) ^ d) :=
    (polynomialDenominator_le W hheight).trans
      (Nat.pow_le_pow_right hheight.one_le hcard)
  refine ⟨W, polynomialDenominator W, hW, hderiv, polynomialDenominator_pos W,
    (Nat.cast_le.mpr hden).trans hb.2.2, polynomialDenominator_coefficientGrid W, ?_, ?_⟩
  · have hm := rationalPolynomial_realMass_le W hheight hdegree
    exact hm.trans (by simpa only [Nat.mul_comm] using hb.2.1)
  · intro α
    exact ⟨(Nat.cast_le.mpr (hheight α).1).trans hb.1,
      (Nat.cast_le.mpr (hheight α).2).trans hb.1⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

theorem exists_intrinsic_controlled_projected_potential_bounds (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ J : Type*} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d),
      ∀ U : LieSubalgebra ℚ (weightedSubalgebra w d),
      BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U.toSubmodule →
      ∀ (g : J → weightedSubalgebra w d),
      Submodule.span ℚ (Set.range g) = U.toSubmodule →
      ∀ H : ℕ, 1 ≤ H →
      (∀ j i, RationalHeightLE ((g j).val.base i) H) →
      (∀ j, RationalPolynomialHeightLE (g j).val.polynomial H) →
      ∀ (frequency : weightedSubalgebra w d →ₗ[ℚ] ℚ),
      frequency (centralRationalElement w d hd 1) = 1 →
      (∀ x ∈ U, x ∈ (weightedFiltration w d hwd).layer d → frequency x = 0) →
      ∀ p : ℝ, 0 ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      ∃ (W : MvPolynomial σ ℚ) (q : ℕ),
        W.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base W) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (fun α => W.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (map (algebraMap ℚ ℝ) W) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ α, ((W.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((W.coeff α).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_controlled_projected_potential_bounds d hd
  refine ⟨C, hC, ?_⟩
  intro σ J _ w hw hwd U hgraded g hspan H hH hbase hpoly
    frequency hfrequency hkill p hp hN hHp
  let V : LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
    U.map (weightedSubalgebra w d).incl
  have hVsub : V.toSubmodule =
      U.toSubmodule.map (weightedSubalgebra w d).subtype := rfl
  have hbound : V.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hVgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (V.toSubmodule.comap (weightedSubalgebra w d).subtype) := by
    rw [hVsub, Submodule.comap_map_eq_of_injective
      (weightedSubalgebra w d).subtype_injective]
    exact hgraded
  have hVspan : Submodule.span ℚ (Set.range (fun j => (g j).val)) = V.toSubmodule := by
    rw [hVsub, ← hspan, ← Submodule.span_image, ← Set.range_comp]
    rfl
  obtain ⟨η, hη⟩ := LinearMap.exists_extend
    (show (weightedSubalgebra w d).toSubmodule →ₗ[ℚ] ℚ from frequency)
  have hext (x : weightedSubalgebra w d) : η x.val = frequency x :=
    congrArg (fun f : weightedSubalgebra w d →ₗ[ℚ] ℚ => f x) hη
  have hconstant : (centralRationalElement w d hd 1).val =
      (constantDirection : PolynomialTranslationLie σ) := by
    apply PolynomialTranslationLie.ext <;> simp [centralRationalElement, constantDirection]
  have hηconstant : η constantDirection ≠ 0 := by
    rw [← hconstant, hext, hfrequency]
    exact one_ne_zero
  have hηkill : ∀ x ∈ V, x ∈ weightedLayer w d d → η x = 0 := by
    rintro x ⟨y, hy, rfl⟩ htop
    change η y.val = 0
    rw [hext]
    exact hkill y hy htop
  obtain ⟨W, q, hW, hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential w hw hwd V hbound hVgraded (fun j => (g j).val) hVspan
      H hH hbase hpoly η hηconstant hηkill p hp hN hHp
  refine ⟨W, q, hW, ?_, hq, hqp, hgrid, hmass, hcoeff⟩
  intro x hx z hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact hderiv x.val ⟨x, hx, rfl⟩ _ ⟨y.val, ⟨y, hy, rfl⟩, rfl⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

theorem exists_associatedGraded_controlled_potential (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L d) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
      (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)
      (W : LieSubalgebra ℚ F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      ∀ (v : J → F.AssociatedGraded), Submodule.span ℚ (Set.range v) = W.toSubmodule →
      ∀ (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p) →
      (∀ j i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j) i) ≤ p) →
      ∀ η : weightedSubalgebra w d →ₗ[ℚ] ℚ,
      η (centralRationalElement w d hd 1) = 1 →
      (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω d x = x →
        F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x = 0) →
      let U := W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)
      ∃ (V : MvPolynomial σ ℚ) (q : ℕ),
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (map (algebraMap ℚ ℝ) V) ≤
          Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_intrinsic_controlled_projected_potential_bounds d hd
  refine ⟨C, hC, ?_⟩
  intro σ ι J L _ _ _ _ F b ω hF w hw hwd φ hφ W hW v hv
    p hp hι hσ hentries hcoords η hη hkill U
  let π := weightedTranslationGradedProjection F w d hw hwd φ hφ
  let g : J → weightedSubalgebra w d := fun j => π (v j)
  let H := ⌈Real.exp ((p + 2)^4)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp _
  have hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      U.toSubmodule :=
    weightedTranslationGradedProjection_image_graded F w d hw hwd φ hφ b ω hF W hW
  have hspan : Submodule.span ℚ (Set.range g) = U.toSubmodule :=
    F.homogeneousGradedProjection_span (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ W v hv
  have hheight (j : J) (i : WeightedBasisIndex w d) :
      RationalHeightLE ((weightedBasis w d hw).repr (g j) i) H :=
    F.homogeneousGradedProjection_coordinate_ceil_height (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF
      hp hι hentries (v j) (hcoords j) i
  have hbase (j : J) (i : σ) : RationalHeightLE ((g j).val.base i) H :=
    weightedBasis_base_height w d hw (g j) (hheight j) i
  have hpoly (j : J) : RationalPolynomialHeightLE (g j).val.polynomial H :=
    weightedBasis_polynomial_height_of_coordinates w d hw (g j) hH (hheight j)
  have hfrequency : ∀ x ∈ U, x ∈ (weightedFiltration w d hwd).layer d → η x = 0 := by
    intro x hx htop
    exact F.homogeneousGradedProjection_top_frequency_zero (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF W hW η hkill hx htop
  have hpow : 0 ≤ (p + 2)^4 := by positivity
  have hp' : 0 ≤ p + (p + 2)^4 + 1 := by linarith
  have hσ' : (Fintype.card σ : ℝ) ≤ p + (p + 2)^4 + 1 := by linarith
  have hHp : (H : ℝ) ≤ Real.exp (p + (p + 2)^4 + 1) :=
    (ceil_exp_le_exp_add_one hpow).trans (Real.exp_le_exp.mpr (by linarith))
  exact hpotential w hw hwd U hgraded g hspan H hH hbase hpoly η hη hfrequency
    (p + (p + 2)^4 + 1) hp' hσ' hHp

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDimensionBudget
namespace OAI

section

universe level

namespace Erdos3

open Module

namespace RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ}

theorem finrank_eq_dimension (D : RationalFilteredNilmanifold L s d) :
    finrank ℚ L = d := by
  rw [finrank_eq_card_basis D.basis, Fintype.card_fin]

theorem geometry_finrank_le (D : RationalFilteredNilmanifold L s d) {p : ℝ}
    (hD : D.GeometryComplexityLE p) : (finrank ℚ L : ℝ) ≤ p := by
  rw [D.finrank_eq_dimension]
  exact hD.1

end RationalFilteredNilmanifold

namespace RationalFilteredNilmanifold

variable {L M : Type level} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ}

theorem geometry_pair_finrank_le (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) {p q : ℝ}
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE q) :
    (finrank ℚ (PairAlgebra L M) : ℝ) ≤ p + q := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ M := E.basis.finiteDimensional_of_finite
  let : ∀ i : Bool, Module.Finite ℚ (BoolLieFamily L M i) := by
    intro i
    cases i
    · exact (inferInstance : Module.Finite ℚ M)
    · exact (inferInstance : Module.Finite ℚ L)
  have hpair : finrank ℚ (PairAlgebra L M) = finrank ℚ L + finrank ℚ M := by
    change finrank ℚ (∀ i : Bool, BoolLieFamily L M i) = _
    rw [finrank_pi_fintype, Fintype.sum_bool]
    rfl
  rw [hpair, Nat.cast_add]
  exact add_le_add (D.geometry_finrank_le hD) (E.geometry_finrank_le hE)

end RationalFilteredNilmanifold

namespace RationalFilteredNilmanifold

theorem geometry_pair_finrank_le_budget
    {L M : Type level} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    {a : ℕ} (ha : 2 ≤ a) :
    (finrank ℚ (PairAlgebra L M) : ℝ) ≤ (p + (a : ℝ)) ^ a := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hpair : (finrank ℚ (PairAlgebra L M) : ℝ) ≤ 2 * p := by
    simpa only [two_mul] using D.geometry_pair_finrank_le E hD hE
  exact hpair.trans (two_mul_le_translation_major_budget hp ha)

end RationalFilteredNilmanifold

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

theorem weightedTranslationResidueNilmanifold_base_card_le {p : ℝ}
    (hG : (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p) :
    (Fintype.card σ : ℝ) ≤ p :=
  (Nat.cast_le.mpr (card_le_weightedBasisIndex w d)).trans hG.1

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledDetectedTranslationBaseBounds
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

 theorem detectedTranslationBaseFunctional_lie (i : B)
    (x y : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded) :
    detectedTranslationBaseFunctional w d hw hwd M hM D i ⁅x, y⁆ = 0 := by
  change (weightedTranslationGradedProjection
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
    w d hw hwd (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      ⁅x, y⁆).val.base i = 0
  rw [LieHom.map_lie]
  rfl

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

 theorem detectedTranslationBaseFunctional_basis_apply
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i})) (i : B) (j : ι) :
    detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF j) =
      if ω j = w i then (b j true).val.base i else 0 := by
  let F := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra w d) L) true
  exact weightedTranslationGradedProjection_basis_base F w d hw hwd φ
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    b ω hF j i

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (v : σ → ℕ)

theorem realSymbolRepresentative_coordinate_top
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (i : ι) :
    coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom
      (F.realSymbolRepresentative b ω hF v (F.realSymbolOfPolynomial b ω hF v P)) =
      weightedHomogeneousComponent v (ω i)
        (coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom P) := by
  classical
  apply MvPolynomial.ext
  intro α
  rw [coeff_coordinate, coeff_weightedHomogeneousComponent, coeff_coordinate]
  simp only [LinearMap.toAddMonoidHom_coe, Basis.coord_apply]
  by_cases h : Finsupp.weight v α = ω i
  · rw [if_pos h]
    have hh := (F.realSymbolRepresentative_coefficient b ω hF v _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfPolynomial_coordinate b ω hF v P ⟨(α, i), h⟩)
    convert hh using 1
  · rw [if_neg h]
    have hh := F.realSymbolRepresentative_coefficient_of_ne b ω hF v
      (F.realSymbolOfPolynomial b ω hF v P) α i h
    convert hh using 1

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DetectedTranslationBasePolynomialBounds
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

 theorem detectedTranslationBasePolynomial_coefficients
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (α : σ →₀ ℕ) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) α =
      realifyCoordinateMap (detectedTranslationBaseMap w d hw hwd M hM D)
        (coefficients ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.realGradedSymbolPolynomial b ω hN (fun _ : σ => 1) g.coord) α) := by
  funext i
  rw [detectedTranslationBasePolynomial_coefficients_apply,
    NilpotentLieFiltration.coeff_scalarSymbolPolynomial]
  rfl

 theorem detectedTranslationBasePolynomial_mul (hd : 1 ≤ d)
    (x y : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) :
    detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN (x * y) =
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN x +
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN y := by
  apply coefficients.injective
  ext α i
  simp only [map_add, Finsupp.add_apply, Pi.add_apply,
    detectedTranslationBasePolynomial_coefficients_apply]
  rw [(pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_mul b ω hN (fun _ : σ => 1)
    (detectedTranslationBaseFunctional w d hw hwd M hM D i)
    (detectedTranslationBaseFunctional_lie w d hw hwd M hM D i) hd,
    MvPolynomial.coeff_add]

 theorem detectedTranslationBasePolynomial_factorization (hd : 1 ≤ d)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hprod : E * P * Q = X) :
    detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X =
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E +
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P +
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q := by
  rw [← hprod, detectedTranslationBasePolynomial_mul w d hw hwd M hM D b ω hN hd,
    detectedTranslationBasePolynomial_mul w d hw hwd M hM D b ω hN hd]

 theorem detectedTranslationBasePolynomial_fast_coefficients_mem_span {J : Type*}
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded) (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : σ => 1) W)) (α : σ →₀ ℕ) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P) α ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  rw [detectedTranslationBasePolynomial_coefficients]
  exact realifyCoordinateMap_mem_span W.toSubmodule v hv _
    (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.mem_real_symbolPointwiseSubalgebra_iff_coefficients
      b ω hN (fun _ : σ => 1) W P.coord).mp hP α)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DetectedTranslationMajorBase
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

section General

variable {B ι J L : Type*} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
    (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)

noncomputable def detectedTranslationProjectedGenerators (v : J → F.AssociatedGraded) :
    J → weightedSubalgebra w d :=
  fun j => weightedTranslationGradedProjection F w d hw hwd φ hφ (v j)

noncomputable def detectedTranslationProjectedBaseMatrix (v : J → F.AssociatedGraded) :
    Matrix B J ℚ :=
  fun i j => (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).val.base i

theorem detectedTranslationProjectedGenerators_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v)) =
      (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule :=
  F.homogeneousGradedProjection_span (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ W v hv

theorem detectedTranslationProjectedBaseMatrix_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (fun j i => detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j)) =
      (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype) :=
  (coordinateImage_eq_span _ _ (detectedTranslationProjectedGenerators_span F w d hw hwd φ hφ W v hv)
    (baseLinear.comp (weightedSubalgebra w d).subtype)).symm

theorem detectedTranslationProjectedBaseMatrix_real_image_eq_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    ((W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) =
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j : ℝ))) :=
  realifyCoordinateMap_image_eq_span _ _
    (detectedTranslationProjectedGenerators_span F w d hw hwd φ hφ W v hv)
    (baseLinear.comp (weightedSubalgebra w d).subtype)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p)
    (v : J → F.AssociatedGraded)
    (hcoords : ∀ j i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j) i) ≤ p)

include b ω hF hp hι hentries hcoords

theorem detectedTranslationProjectedGenerators_coordinate_logHeight (j : J) (i : WeightedBasisIndex w d) :
    rationalLogHeight ((weightedBasis w d hw).repr
      (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j) i) ≤ (p + 2)^4 :=
  F.homogeneousGradedProjection_coordinate_logHeight (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF hp hι hentries (v j) (hcoords j) i

theorem detectedTranslationProjectedBaseMatrix_logHeight (i : B) (j : J) :
    rationalLogHeight (detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j) ≤ (p + 2)^4 :=
  detectedTranslationProjectedGenerators_coordinate_logHeight F w d hw hwd φ hφ b ω hF
    hp hι hentries v hcoords j (Sum.inl i)

theorem detectedTranslationProjectedGenerators_polynomial_logHeight (j : J) (a : B →₀ ℕ) :
    rationalLogHeight
      ((detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).val.polynomial.coeff a) ≤ (p + 2)^4 := by
  by_cases ha : Finsupp.weight w a < d
  · exact detectedTranslationProjectedGenerators_coordinate_logHeight F w d hw hwd φ hφ b ω hF
      hp hι hentries v hcoords j (Sum.inr ⟨a, ha⟩)
  · have hz : (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).val.polynomial.coeff a = 0 := by
      by_contra hne
      have hh := (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).property.2
        (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w a + 1 ≤ d at hh
      omega
    rw [hz]
    simp only [rationalLogHeight, Rat.num_zero, Int.natAbs_zero, Nat.cast_zero,
      Rat.den_zero, Nat.cast_one, max_eq_right (zero_le_one : (0 : ℝ) ≤ 1), Real.log_one]
    positivity

end General

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {B L σ ι : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

 theorem detectedTranslationBase_span_eq_real_image {J : Type*}
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) =
      (((W.map (weightedTranslationGradedProjection
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))).toSubmodule).baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  exact (detectedTranslationProjectedBaseMatrix_real_image_eq_span
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
    w d hw hwd (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) W v hv).symm

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationMajorTwistedCorrelationStepDropPolynomial
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem majorTranslationDegreeReduced_twisted_integerEval
    {U : Type*} {m : ℕ} (w : Fin m → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (x : U → ℤ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ
        (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial F) 0) T
        (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x
            (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
              (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF) A hA))) =
      T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ))
          (fun i => (β i : ZMod M)) *
        (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (fun j => ((Sum.elim x β j : ℤ) : ℝ)) F) : ℂ) := by
  rw [majorTranslationPolynomialOrbit_integerEval,
    twistedBufferedTranslationPhase_majorSymbol M Ψ _ _ T A _ β hβ]
  have hcast : Sum.elim (fun j => (x j : ℝ)) (fun i => (β i : ℝ)) =
      (fun j => ((Sum.elim x β j : ℤ) : ℝ)) := by
    funext j
    cases j <;> rfl
  rw [hcast, fractionalCoefficientPolynomial_fourierChar]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ L : Type} {U ι : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M) {e : ℕ}
    (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationSymbolLift_value_mem_fast
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W)) (t : U → ℝ) :
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval (fun _ : U => 1) t
      (detectedTranslationSymbolLift w d hw hwd M hM D P)).coord ∈
      realificationLieSubalgebra
        (W.map (weightedTranslationGradedProjection (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))) := by
  change eval₂ t (detectedTranslationSymbolLift w d hw hwd M hM D P).log ∈ _
  rw [detectedTranslationSymbolLift_log]
  unfold weightedTranslationGradedProjection
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.projected_realSymbolRepresentative_mem_homogeneous_image (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true) (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1) W P.coord hP t
  convert h using 1

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (v : σ → ℕ)

theorem realGradedSymbolPolynomial_constant (x : F.RealPolynomialSymbol v) :
    coefficients (F.realGradedSymbolPolynomial b ω hF v x) 0 = 0 := by
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  change ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
    (coefficients (F.realGradedSymbolPolynomial b ω hF v x) 0) i = 0
  apply F.realGradedSymbolPolynomial_coordinate_of_ne
  rw [map_zero]
  exact (F.adaptedBasis_weight_pos b ω hF i).ne

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie

open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationBasePolynomial_constant
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup
      (fun _ : σ => 1)) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) 0 = 0 := by
  rw [detectedTranslationBasePolynomial_coefficients,
    NilpotentLieFiltration.realGradedSymbolPolynomial_constant, map_zero]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationGroupEval (u : U → ℝ) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1) →*
      PolynomialTranslationGroupOver ℝ B :=
  (bchRealTranslationHom w d hwd).comp
    (((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u).comp (detectedTranslationSymbolLift w d hw hwd M hM D))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationGroupEval_fast_potential
    (hd : 0 < d)
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W))
    (V : MvPolynomial B ℚ) :
    let fast := W.map (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))
    (∀ x ∈ fast, ∀ z ∈ fast.toSubmodule.map
      (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) →
    ∀ u z, z ∈ (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
    eval z (detectedTranslationGroupEval w d hw hwd M hM D u P).polynomial =
      eval₂ (algebraMap ℚ ℝ) z V -
        eval₂ (algebraMap ℚ ℝ) (z - (detectedTranslationGroupEval w d hw hwd M hM D u P).base) V := by
  intro fast hderiv u z hz
  have hg := detectedTranslationSymbolLift_value_mem_fast w d hw hwd M hM D b ω hN W P hP u
  have h := bchRealTranslationHom_eval_potential w d hw hd hwd fast V hderiv
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u (detectedTranslationSymbolLift w d hw hwd M hM D P)) hg z hz
  simpa only [detectedTranslationGroupEval, MonoidHom.comp_apply, eval_map] using h

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationLogCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realSymbolCoordinate_coeff_of_ne (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α ≠ ω i) :
    (F.realSymbolCoordinate b ω hlayers w x i).coeff α = 0 := by
  rw [F.coeff_realSymbolCoordinate]
  exact F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w x α i h

theorem realSymbolCoordinate_isWeightedHomogeneous (x : F.RealPolynomialSymbol w)
    (i : ι) :
    (F.realSymbolCoordinate b ω hlayers w x i).IsWeightedHomogeneous w (ω i) := by
  intro α hα
  by_contra h
  exact hα (F.realSymbolCoordinate_coeff_of_ne b ω hlayers w x α i h)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem nativeTranslationLogCoordinate_eval (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) (u : U → ℝ) :
    VectorPolynomial.eval₂ u p =
      ∑ k, (eval u (nativeTranslationLogCoordinate w d b p k)) ⊗ₜ[ℚ] b k := by
  calc
    VectorPolynomial.eval₂ u p =
        ∑ k, (b.baseChange ℝ).repr (VectorPolynomial.eval₂ u p) k •
          (b.baseChange ℝ) k := ((b.baseChange ℝ).sum_repr _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      change ((b.baseChange ℝ).coord k) (VectorPolynomial.eval₂ u p) •
        (b.baseChange ℝ) k = _
      rw [VectorPolynomial.coordinate_eval₂, Basis.baseChange_apply]
      simp only [nativeTranslationLogCoordinate, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem realifyFunctional_basis_coord {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (i : ι) :
    realifyFunctional (b.coord i) = (b.baseChange ℝ).coord i := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [realifyFunctional_tmul]
    change a * (b.repr x i : ℝ) = (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] x) i
    rw [Basis.baseChange_repr_tmul]
    simp only [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace NilpotentLieFiltration

theorem scalarSymbolPolynomial_joint_grid
    {σ ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (θ : κ → F.AssociatedGraded →ₗ[ℚ] ℚ) (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g) :
    (fun z : (σ →₀ ℕ) × κ =>
      (F.scalarSymbolPolynomial b ω hF w (θ z.2) g).coeff z.1) ∈
        realDenominatorGrid (matrixDenominator (fun k i => θ k (F.associatedGradedBasis b ω hF i)) * m) := by
  classical
  let ℓ : F.AssociatedGraded →ₗ[ℚ] (κ → ℚ) := LinearMap.pi θ
  have hval (α : σ →₀ ℕ) :
      realifyCoordinateMap ℓ
        (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) =
        fun k => (F.scalarSymbolPolynomial b ω hF w (θ k) g).coeff α := by
    funext k
    rw [F.coeff_scalarSymbolPolynomial]
    rfl
  have hgrid (α : σ →₀ ℕ) :
      (fun k => (F.scalarSymbolPolynomial b ω hF w (θ k) g).coeff α) ∈
        realDenominatorGrid (matrixDenominator (fun k i => θ k (F.associatedGradedBasis b ω hF i)) * m) := by
    have h := realifyCoordinateMap_grid (F.associatedGradedBasis b ω hF) ℓ m _
      (F.realGradedSymbolPolynomial_rational_coordinates b ω hF w m g hg α)
    rw [hval] at h
    exact h
  choose a ha using hgrid
  refine ⟨fun z => a z.1 z.2, ?_⟩
  funext z
  exact congrFun (ha z.1) z.2

end NilpotentLieFiltration

namespace PolynomialTranslationLie

open RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationLogCoordinate_homogeneous
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).IsWeightedHomogeneous
      (fun _ : U => 1) (weightedBasisGrade w d k) := by
  rw [detectedTranslationLogCoordinate_eq_canonical]
  exact (weightedFiltration w d hwd).realSymbolCoordinate_isWeightedHomogeneous
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) _ _ k

noncomputable def detectedTranslationLogFunctional (k : WeightedBasisIndex w d) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded →ₗ[ℚ] ℚ :=
  ((weightedBasis w d hw).coord k).comp
    (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
      w d hw hwd (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).toLinearMap

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DetectedTranslationNormalizedLogBounds
namespace OAI

section

namespace Erdos3

namespace PolynomialTranslationLie

open Module VectorPolynomial RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationLogCoordinate_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).totalDegree ≤ d :=
  (degreeLE_one_iff_basis_totalDegree ((weightedBasis w d hw).baseChange ℝ) d
    (detectedTranslationSymbolLift w d hw hwd M hM D E).log).mp
      (detectedTranslationSymbolLift w d hw hwd M hM D E).degreeLE k

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JoinedPairQuotientRefiltration
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

open Module
open RationalFilteredNilmanifold

section ControlledWitness

variable {σ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] {s : ℕ}
  (H : NilpotentLieFiltration V s) (b : Basis ι ℚ V) (ω : ι → ℕ)
  (hH : ∀ k, H.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))

def ControlledSymbolFactorizationAtFast (η : V →ₗ[ℚ] ℚ) (side : σ → ℝ)
    (X : H.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (U : LieSubalgebra ℚ H.AssociatedGraded) : Prop :=
  ∃ (m : ℕ) (E P R : H.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (v : ι → H.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ E * P * R = X ∧
    H.SymbolSlowBound b ω hH (fun _ => 1) side (Real.exp p) E ∧
    H.SymbolRationalGrid b ω hH (fun _ => 1) m R ∧
    Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
    BasisGradedSubmodule (H.associatedGradedBasis b ω hH) ω U.toSubmodule ∧
    (∀ i j, rationalLogHeight ((H.associatedGradedBasis b ω hH).repr (v i) j) ≤ p) ∧
    (∀ x ∈ U, basisGradeProjection (H.associatedGradedBasis b ω hH) ω s x = x →
      H.gradedFrequency b ω hH η x = 0) ∧
    P.coord ∈ realificationLieSubalgebra (H.symbolPointwiseSubalgebra b ω hH (fun _ => 1) U)

theorem ControlledSymbolFactorization.exists_fastWitness
    {η : V →ₗ[ℚ] ℚ} {side : σ → ℝ}
    {X : H.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : H.ControlledSymbolFactorization b ω hH η side X p) :
    ∃ U, H.ControlledSymbolFactorizationAtFast b ω hH η side X p U := by
  obtain ⟨m, E, P, R, U, v, hdata⟩ := h
  exact ⟨U, m, E, P, R, v, hdata⟩

end ControlledWitness

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedLayerFreezing
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch.LowestLayerModel

variable {σ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}
    (L : A.LowestLayerModel h)

noncomputable def normalizedOrigin : Fin D → MvPolynomial σ ℝ :=
  polynomialMatrixAction (L.integerChange⁻¹.map (Int.castRingHom ℝ)) L.origin

end PolynomialPatch.LowestLayerModel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

variable {X : Type*}

theorem lowTaggedPolynomial_coeff (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) (α : X →₀ ℕ) :
    (lowTaggedPolynomial J d poly i).coeff α =
      coefficients (poly (lowTaggedIndex J d i).1) α (lowTaggedIndex J d i).2 := by
  rw [lowTaggedPolynomial, coeff_coordinate]
  rfl

theorem lowTaggedPolynomial_degree (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    (lowTaggedPolynomial J d poly i).totalDegree ≤ lowTaggedWeight J d i := by
  have hw : (lowTaggedPolynomial J d poly i).weightedTotalDegree (1 : X → ℕ) ≤
      lowTaggedWeight J d i := by
    apply (scalar_weightedDegree_le_iff _ _ _).mpr
    intro α hα
    rw [lowTaggedPolynomial_coeff, hpoly _ α hα]
    rfl
  simpa only [MvPolynomial.weightedTotalDegree_one] using hw

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

theorem normalizedTwistFrequencyPolynomial_truncate_correlation
    {X Ω : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (cover d : ℕ) (W : ∀ j, Submodule ℝ (J j → ℝ))
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (hann : ∀ j, d < j.val + 1 →
      W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)))
    (s : Finset Ω) (u : Ω → X → ℝ) (signal : Ω → ℂ) :
    ‖𝔼 x ∈ s, (Real.fourierChar (MvPolynomial.eval (u x)
      (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * signal x‖ =
    ‖𝔼 x ∈ s, (Real.fourierChar (MvPolynomial.eval (u x)
      (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly)) : ℂ) *
        signal x‖ := by
  have he (x : Ω) :
      (Real.fourierChar (MvPolynomial.eval (u x)
        (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * signal x =
      (Real.fourierChar (normalizedTwistHighFrequencyConstant cover d a poly) : ℂ) *
        ((Real.fourierChar (MvPolynomial.eval (u x)
          (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly)) : ℂ) *
            signal x) := by
    rw [normalizedTwistFrequencyPolynomial_low_add_constant cover d W a poly hcoeff hann,
      map_add, eval_C, Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp_rw [he]
  rw [← Finset.mul_expect, norm_mul, Circle.norm_coe, one_mul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.WeightedTranslationProjectionGridBudget
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

universe u v

variable {σ : Type u} {ι : Type v} [Fintype σ] [Fintype ι]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) [Fintype (WeightedBasisIndex w d)]

include hw in

theorem weightedBasisIndex_card_le_pair_basis
    {L : Type u} [LieRing L] [LieAlgebra ℚ L]
    (b : Module.Basis ι ℚ
      (RationalFilteredNilmanifold.PairAlgebra (weightedSubalgebra w d) L)) :
    Fintype.card (WeightedBasisIndex w d) ≤ Fintype.card ι := by
  let : Module.Finite ℚ
      (RationalFilteredNilmanifold.PairAlgebra (weightedSubalgebra w d) L) :=
    b.finiteDimensional_of_finite
  have hproj := LinearMap.finrank_le_finrank_of_surjective
    (LinearMap.proj_surjective (R := ℚ) (φ := BoolLieFamily (weightedSubalgebra w d) L) true)
  change Module.finrank ℚ (weightedSubalgebra w d) ≤
    Module.finrank ℚ (RationalFilteredNilmanifold.PairAlgebra (weightedSubalgebra w d) L) at hproj
  rw [Module.finrank_eq_card_basis (weightedBasis w d hw),
    Module.finrank_eq_card_basis b] at hproj
  exact hproj

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DetectedTranslationPhaseDegree
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)

theorem weightedBasis_base_abs_le_one (a : WeightedBasisIndex w d) (i : σ) :
    |((weightedBasis w d hw a).val.base i : ℝ)| ≤ 1 := by
  classical
  cases a with
  | inl j =>
    rw [weightedBasis_inl_base]
    by_cases h : i = j <;> simp [h]
  | inr a => simp

theorem weightedBasis_polynomial_mass_le_one (a : WeightedBasisIndex w d) :
    realPolynomialMass
      (MvPolynomial.map (Rat.castHom ℝ) (weightedBasis w d hw a).val.polynomial) ≤ 1 := by
  cases a with
  | inl i => simp [realPolynomialMass_zero]
  | inr a => simp [realPolynomialMass_monomial]

theorem weightedBasis_base_integer (a : WeightedBasisIndex w d) (i : σ) :
    ∃ z : ℤ, (z : ℚ) = (weightedBasis w d hw a).val.base i := by
  classical
  cases a with
  | inl j =>
    rw [weightedBasis_inl_base]
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | inr a => exact ⟨0, by simp⟩

theorem weightedBasis_polynomial_real_grid (a : WeightedBasisIndex w d) :
    realPolynomialCoefficientGrid 1
      (MvPolynomial.map (Rat.castHom ℝ) (weightedBasis w d hw a).val.polynomial) := by
  apply (realPolynomialCoefficientGrid_iff 1 _).mpr
  simp only [Nat.cast_one, map_one, one_mul]
  cases a with
  | inl i =>
    simp only [weightedBasis_inl_polynomial, map_zero]
    exact (integralRealPolynomialSubring σ).zero_mem
  | inr a =>
    simp only [weightedBasis_inr_polynomial, map_monomial, map_one]
    exact ⟨monomial a.val (1 : ℤ), by simp⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LowTaggedSamplingRank
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

variable {X : Type*}

noncomputable def lowTaggedTopPolynomial (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    VectorPolynomial X ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :=
  ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
    (fun i => homogeneousComponent (lowTaggedWeight J d i) (lowTaggedPolynomial J d poly i))

theorem lowTaggedTopPolynomial_coeff_apply (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (α : X →₀ ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    coefficients (lowTaggedTopPolynomial J d poly) α i =
      if α.degree = lowTaggedWeight J d i then
        coefficients (poly (lowTaggedIndex J d i).1) α (lowTaggedIndex J d i).2 else 0 := by
  rw [lowTaggedTopPolynomial, coefficients_ofCoordinates_pi_apply,
    coeff_homogeneousComponent, lowTaggedPolynomial_coeff]

theorem lowTaggedTopPolynomial_coeff_of_degree (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (j : Fin m) (hj : j.val + 1 ≤ d) (α : X →₀ ℕ)
    (hα : α.degree = j.val + 1) :
    coefficients (lowTaggedTopPolynomial J d poly) α =
      lowTaggedEmbedding J d j hj (coefficients (poly j) α) := by
  classical
  funext i
  rw [lowTaggedTopPolynomial_coeff_apply]
  by_cases hi : (lowTaggedIndex J d i).1 = j
  · obtain ⟨k, hk⟩ := lowTaggedSlot_eq_of_tag J d j hj i hi
    subst i
    rw [lowTaggedEmbedding_apply_slot]
    simp only [lowTaggedWeight, lowTaggedIndex_slot, hα, ite_true]
    rw [lowTaggedIndex_slot]
  · rw [lowTaggedEmbedding_apply_of_ne J d j hj _ i hi]
    have hne : α.degree ≠ lowTaggedWeight J d i := by
      intro he
      apply hi
      apply Fin.ext
      unfold lowTaggedWeight at he
      omega
    simp only [hne, ite_false]

theorem lowTaggedTopPolynomial_row_layer (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (j : Fin m) (hj : j.val + 1 ≤ d)
    (a : Fin (Fintype.card (LowTaggedIndex J d)) → ℤ) :
    homogeneousComponent (j.val + 1)
        (integerRowPolynomial a (lowTaggedTopPolynomial J d poly)) =
      homogeneousComponent (j.val + 1)
        (integerRowPolynomial (fun k => a (lowTaggedSlot J d j hj k)) (poly j)) := by
  classical
  ext α
  simp only [coeff_homogeneousComponent]
  split
  · rename_i hα
    rw [integerRowPolynomial_coeff, integerRowPolynomial_coeff,
      lowTaggedTopPolynomial_coeff_of_degree J d poly j hj α hα]
    exact lowTaggedEmbedding_pairing J d j hj (fun i => (a i : ℝ)) _
  · rfl

theorem lowTaggedTopPolynomial_hasLayerSamplingRank (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (T : X → ℝ) (R : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) T R (W j) (poly j))
    (h : Fin d) :
    HasLayerSamplingRank (h.val + 1) T R (lowTaggedRetained J d W h)
      (lowTaggedTopPolynomial J d poly) := by
  classical
  intro a ha hw
  by_cases hm : h.val < m
  · let j : Fin m := ⟨h.val, hm⟩
    have hj : j.val + 1 ≤ d := by dsimp [j]; omega
    obtain ⟨w, hw⟩ := hw
    have hwmem : w.val ∈ (W j).map (lowTaggedEmbedding J d j hj) := by
      simpa only [lowTaggedRetained, dif_pos hm] using w.property
    obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp hwmem
    have hpair : ∃ v : W j,
        (∑ k, (a (lowTaggedSlot J d j hj k) : ℝ) * v.val k) ≠ 0 := by
      refine ⟨⟨v, hv⟩, ?_⟩
      change (∑ k, (a (lowTaggedSlot J d j hj k) : ℝ) * v k) ≠ 0
      rw [← lowTaggedEmbedding_pairing J d j hj (fun i => (a i : ℝ)) v, he]
      exact hw
    have hn := hrank j (fun k => a (lowTaggedSlot J d j hj k))
      (fun k => ha _) hpair
    rw [lowTaggedTopPolynomial_row_layer J d poly j hj]
    exact hn
  · obtain ⟨w, hw⟩ := hw
    have hwzero : w.val = 0 := by
      have := w.property
      simpa only [lowTaggedRetained, dif_neg hm, Submodule.mem_bot] using this
    simp only [hwzero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, ne_eq,
      not_true_eq_false] at hw

theorem lowTaggedTopPolynomial_coeff_mem_iSup (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (α : X →₀ ℕ) :
    coefficients (lowTaggedTopPolynomial J d poly) α ∈
      ⨆ h : Fin d, lowTaggedRetained J d W h := by
  classical
  by_cases hs : ∃ i, α.degree = lowTaggedWeight J d i
  · obtain ⟨i, hi⟩ := hs
    let j := (lowTaggedIndex J d i).1
    have hj : j.val + 1 ≤ d := lowTaggedIndex_property J d i
    let h : Fin d := ⟨j.val, by omega⟩
    have hα : α.degree = j.val + 1 := hi
    have hα0 : α ≠ 0 := by
      intro he
      subst α
      simp at hα
    apply Submodule.mem_iSup_of_mem h
    rw [lowTaggedTopPolynomial_coeff_of_degree J d poly j hj α hα]
    have heq : lowTaggedRetained J d W h =
        (W j).map (lowTaggedEmbedding J d j hj) := by
      simp only [lowTaggedRetained, h, dif_pos j.isLt]
    rw [heq]
    exact Submodule.mem_map.mpr ⟨_, hcoeff j α hα0, rfl⟩
  · have hz : coefficients (lowTaggedTopPolynomial J d poly) α = 0 := by
      funext i
      rw [lowTaggedTopPolynomial_coeff_apply]
      simp only [show α.degree ≠ lowTaggedWeight J d i from fun he => hs ⟨i, he⟩,
        ite_false, Pi.zero_apply]
    rw [hz]
    exact Submodule.zero_mem _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LowTaggedAffineCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

theorem lowTaggedTopPolynomial_residueAffine_coeff_mem_iSup (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (q : ℕ) (r : X → ℤ) (α : X →₀ ℕ) :
    coefficients (lowTaggedTopPolynomial J d (fun j => residueAffine q r (poly j))) α ∈
      ⨆ h : Fin d, lowTaggedRetained J d W h :=
  lowTaggedTopPolynomial_coeff_mem_iSup J d (fun j => residueAffine q r (poly j)) W
    (fun j β hβ => coefficients_residueAffine_nonzero_mem (W j) q r (poly j)
      (hcoeff j) β hβ) α

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseDetectedDecomposition
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem majorPhase_residue_lowTagged_rank {m : ℕ} {X : Type*}
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (N lengths : X → ℕ) (hN : ∀ i, 0 < (N i : ℝ))
    (hlengths : ∀ i, 0 < lengths i) (q : ℕ) (hq : 0 < q) (start : X → ℤ)
    (p E D B Rrank : ℝ) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hqbound : (q : ℝ) ≤ Real.exp p)
    (hcomparison : ∀ i, (N i : ℝ) ≤ Real.exp E * q * lengths i)
    (hrow : D ≤ B) (hden : (m : ℝ) * p + D ≤ B)
    (hslow : (m : ℝ) * E + D ≤ B) (hRrank : Real.exp B ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    ∀ h : Fin d, HasLayerSamplingRank (h.val + 1)
      (fun i => (lengths i : ℝ)) (Real.exp D) (lowTaggedRetained J d U h)
      (lowTaggedTopPolynomial J d (fun j => residueAffine q start (poly j))) := by
  have hsliced (j : Fin m) : HasLayerSamplingRank (j.val + 1)
      (fun i => (lengths i : ℝ)) (Real.exp D) (U j)
      (residueAffine q start (poly j)) := by
    apply (hrank j).residueAffine (hpoly j) hN
      (fun i => Nat.cast_pos.mpr (hlengths i)) q hq start (Real.exp E) hcomparison
    · exact (Real.exp_le_exp.mpr hrow).trans hRrank
    · exact (pow_mul_exp_le_exp_of_le_budget (Nat.cast_nonneg q) hqbound hp
        (Nat.succ_le_of_lt j.isLt) hden).trans hRrank
    · exact (pow_mul_exp_le_exp_of_le_budget (Real.exp_nonneg E) le_rfl hE
        (Nat.succ_le_of_lt j.isLt) hslow).trans hRrank
  exact lowTaggedTopPolynomial_hasLayerSamplingRank J d _ U _ _ hsliced

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem sampledCurrentGrade_sampledCurrentGrade_realifyFunctional_basis_coord {V η : Type*} [AddCommGroup V] [Module ℚ V]
    (e : Module.Basis η ℚ V) (j : η) :
    realifyFunctional (e.coord j) = (e.baseChange ℝ).coord j := by
  classical
  apply (e.baseChange ℝ).ext
  intro i
  rw [Module.Basis.baseChange_apply, realifyFunctional_tmul, one_mul]
  simp

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem majorPhasePlateauKernel_one {d : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ 1 / 8) : (majorPhasePlateauKernel d).value x = 1 := by
  apply linearCutoff_eq_one _ _ (by norm_num)
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (by
    simpa only [Real.norm_eq_abs] using hx)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFrozenChart
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

theorem freezePolynomial_sub_lower (keep : I → Prop)
    (fixed fixed' : {i // ¬keep i} → R) {P : MvPolynomial I R} {d : ℕ}
    (hP : P ∈ weightedSupportLE (fun _ => 1) d) :
    freezePolynomial keep fixed P - freezePolynomial keep fixed' P ∈
      weightedSupportLT (fun _ => 1) d := by
  apply weightedComparison_difference (fun _ => 1) (fun _ => 1)
    (freezePolynomial keep fixed) (freezePolynomial keep fixed')
    (fun i => by simpa only [freezePolynomial, aeval_X] using frozenCoordinate_support keep fixed i)
    (fun i => by simpa only [freezePolynomial, aeval_X] using frozenCoordinate_support keep fixed' i)
    _ hP
  intro i
  by_cases hi : keep i
  · simp only [freezePolynomial, aeval_X, frozenCoordinate, dif_pos hi, sub_self]
    exact Submodule.zero_mem _
  · simp only [freezePolynomial, aeval_X, frozenCoordinate, dif_neg hi, ← map_sub]
    exact weightedSupportLE_lt_succ (weightedSupportLE_C (fun _ => 1) 0 _)

theorem freezePolynomial_top_independent (keep : I → Prop)
    (fixed fixed' : {i // ¬keep i} → R) {P : MvPolynomial I R} {d : ℕ}
    (hP : P.totalDegree ≤ d) :
    homogeneousComponent d (freezePolynomial keep fixed P) =
      homogeneousComponent d (freezePolynomial keep fixed' P) := by
  have hlower := freezePolynomial_sub_lower keep fixed fixed'
    ((mem_weightedSupportLE_one_iff _ _).mpr hP)
  change weightedHomogeneousComponent (fun _ => 1) d _ =
    weightedHomogeneousComponent (fun _ => 1) d _
  ext α
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
  split_ifs with hα
  · have hz : (freezePolynomial keep fixed P - freezePolynomial keep fixed' P).coeff α = 0 := by
      by_contra hn
      have hlt := hlower (mem_support_iff.mpr hn)
      exact (Nat.lt_irrefl d) (hα ▸ hlt)
    exact sub_eq_zero.mp (by simpa only [MvPolynomial.coeff_sub] using hz)
  · rfl

theorem freezePolynomial_top (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    {P : MvPolynomial I R} {d : ℕ} (hP : P.totalDegree ≤ d) :
    homogeneousComponent d (freezePolynomial keep fixed P) =
      freezePolynomial keep 0 (homogeneousComponent d P) := by
  rw [freezePolynomial_top_independent keep fixed 0 hP]
  exact (aeval_weightedHomogeneousComponent (fun _ : I => 1) (fun _ => 1)
    (frozenCoordinate keep 0) (frozenCoordinate_zero_homogeneous keep) d P).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRecoveredNormalizedTopChart
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem aeval_frozen_integer_top {σ K : Type*}
    (w : σ → ℕ) (β : σ → MvPolynomial K ℤ)
    (hβ : ∀ z, MvPolynomial.map (Int.castRingHom ℝ) (β z) ∈
      weightedSupportLE (fun _ => 1) (w z))
    (keep : K → Prop) (fixed : {i // ¬keep i} → ℤ)
    (p : MvPolynomial σ ℝ) :
    aeval (fun z => homogeneousComponent (w z)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β z)))) p =
      freezePolynomial keep (0 : {i // ¬keep i} → ℝ)
        (aeval (fun z => homogeneousComponent (w z)
          (MvPolynomial.map (Int.castRingHom ℝ) (β z))) p) := by
  simp_rw [freezePolynomial_map, freezePolynomial_top keep _
    ((mem_weightedSupportLE_one_iff _ _).mp (hβ _))]
  exact (MvPolynomial.comp_aeval_apply _ (freezePolynomial keep 0) p).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem ControlledSymbolFactorizationAtFast.dilate_ratio
    {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q r : ℝ}
    {U : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.ControlledSymbolFactorizationAtFast b ω hF η S X p U)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdr : (d : ℝ) ≤ Real.exp r)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.ControlledSymbolFactorizationAtFast b ω hF η T
      (F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d) X)
      (p + (s : ℝ) * (q + r)) U := by
  obtain ⟨m, E, P, R, v, hm, hmp, hprod, hE, hR, hv, hgraded, hh, hzero, hP⟩ := h
  have hf : F.SymbolFactorizationIn b ω hF S X p m U :=
    ⟨E, P, R, hprod, hE, hR, hP⟩
  have hcost : p + (s : ℝ) * q ≤ p + (s : ℝ) * (q + r) := by
    have := mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hr
    nlinarith
  have hp : p ≤ p + (s : ℝ) * (q + r) := le_add_of_nonneg_right (by positivity)
  obtain ⟨E', P', R', hprod', hE', hR', hP'⟩ :=
    (SymbolFactorizationIn.dilate_ratio F b ω hF hf a d ha hd hS hT hq hphysical).mono
      F b ω hF hcost hT
  refine ⟨m * d ^ s, E', P', R', v, Nat.mul_pos hm (pow_pos hd _), ?_, hprod',
    hE', hR', hv, hgraded, (fun i j => (hh i j).trans hp), hzero, hP'⟩
  calc
    ((m * d ^ s : ℕ) : ℝ) = (m : ℝ) * (d : ℝ) ^ s := by push_cast; rfl
    _ ≤ Real.exp p * (Real.exp r) ^ s :=
      mul_le_mul hmp (pow_le_pow_left₀ (Nat.cast_nonneg d) hdr s)
        (by positivity) (Real.exp_pos p).le
    _ = Real.exp (p + (s : ℝ) * r) := by rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp (p + (s : ℝ) * (q + r)) := by
      apply Real.exp_le_exp.mpr
      have := mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hq
      nlinarith

theorem ControlledSymbolFactorization.dilate_ratio
    {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q r : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η S X p)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdr : (d : ℝ) ≤ Real.exp r)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.ControlledSymbolFactorization b ω hF η T
      (F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d) X)
      (p + (s : ℝ) * (q + r)) := by
  obtain ⟨U, hU⟩ := h.exists_fastWitness F b ω hF
  obtain ⟨m, E, P, R, v, hdata⟩ :=
    hU.dilate_ratio F b ω hF a d ha hd hS hT hq hr hdr hphysical
  exact ⟨m, E, P, R, U, v, hdata⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem ControlledSymbolFactorizationAtFast.mono {η : L →ₗ[ℚ] ℚ}
    {T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)}
    {p q : ℝ} {U : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.ControlledSymbolFactorizationAtFast e ω hF η T X p U)
    (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.ControlledSymbolFactorizationAtFast e ω hF η T X q U := by
  obtain ⟨m, E, P, R, v, hm, hmp, hprod, hE, hR, hv, hgraded, hheight, hzero, hP⟩ := h
  exact ⟨m, E, P, R, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    F.symbolSlowBound_mono e ω hF _ T hT (Real.exp_le_exp.mpr hpq) E hE,
    hR, hv, hgraded, fun i j => (hheight i j).trans hpq, hzero, hP⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialFrameSlopeBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {G J X : Type*} [Fintype G] [Fintype J] [Fintype X]

theorem narrowSpatial_frame_slope_sum
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (v : Option (G ⊕ J) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (x : X) :
    (∑ k, |(v (some k, x) : ℝ)| * T k) ≤ τ * (N x : ℝ) / 8 := by
  have hden : 0 < 8 * (1 + W) := by positivity
  have hcoef : 0 ≤ τ * (N x : ℝ) / (8 * (1 + W)) := by positivity
  calc
    _ ≤ ∑ k, (τ * (N x : ℝ) / (8 * (1 + W))) * T k :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
        (narrowSpatial_frame_slope_bound hW hτ hξ N hN v hv k x) (hT k))
    _ = (τ * (N x : ℝ) / (8 * (1 + W))) * ∑ k, T k :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (τ * (N x : ℝ) / (8 * (1 + W))) * (1 + W) :=
      mul_le_mul_of_nonneg_left (hsum.trans (by linarith)) hcoef
    _ = τ * (N x : ℝ) / 8 := by
      have hw : 1 + W ≠ 0 := by positivity
      field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FrozenPolynomialAffineRange
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

theorem longChart_frozen_top_eval_mem {J Full : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (keep : Full → Prop)
    (fixed : {i // ¬ keep i} → ℤ) (r : ℕ)
    (hdegree : ∀ j, (β j).totalDegree ≤ r)
    (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ α : {i // keep i} →₀ ℕ, α.degree = r →
      (fun j => (((β j).coeff (α.mapDomain Subtype.val) : ℤ) : ℝ)) ∈ K)
    (x : {i // keep i} → ℝ) :
    (fun j => MvPolynomial.eval x (homogeneousComponent r
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))))) ∈ K := by
  have htop (j : J) : homogeneousComponent r
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))) =
      killCompl (Subtype.val_injective (p := keep))
        (homogeneousComponent r (MvPolynomial.map (Int.castRingHom ℝ) (β j))) := by
    rw [freezePolynomial_map, freezePolynomial_top keep _
      ((totalDegree_map_le _ _).trans (hdegree j)), longChart_freezePolynomial_zero_eq_killCompl]
  simp only [htop]
  exact longChart_top_eval_mem β (Function.Embedding.subtype keep) r K hcoeff x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMixedLiftNormalizedMass
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedLayerSupported_normalized_mass (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val a i)) ≤
      ((j.val + 2 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ (j.val + 1) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  apply mixedLiftPolynomial_scaled_mass (euclideanSubspace (U j)) (b j) (o j)
    Subtype.val Subtype.val_injective a _ hT (hC j) (hR j).le (hchart j)
  · intro k d
    exact continuousPolynomialDensity_coefficient_le_radius Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j k) (hR j) (hσ j) (hσ1 j) (hs.1 k) d
  · intro k d
    exact allocatedIntegerCoefficient_le_radius
      (layerIntegerPrincipalSlots B j k) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) k) S.value (layerTailDegree m) (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) k) S.positive (layerSamplerBox B U b S) hT
      (layerSamplerBox_le B U b S) Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (hσ1 j) (S.gap j k) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j k) rfl
      (layerSamplerSides_integer_principal B U b R S.value j k) d (hs.2 k d)
  · intro d
    exact d.property

theorem allocatedLayerSupported_normalized_mass_uniform
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val a i)) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  apply (allocatedLayerSupported_normalized_mass B U b o hR hσ S hσ1 C hC hchart j a ha i).trans
  calc
    _ ≤ ((j.val + 2 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ (j.val + 1) * 1 :=
      mul_le_mul_of_nonneg_left (hsmall j) (by positivity)
    _ ≤ ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
      rw [mul_one]
      apply mul_le_mul
      · exact_mod_cast (show j.val + 2 ≤ m + 1 by omega)
      · exact pow_le_pow_right₀ (by norm_cast; omega) (by omega)
      · positivity
      · positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalHomogeneousSymbolPullbackGrid
namespace OAI

section

namespace Erdos3
open Module _root_.MvPolynomial
open scoped TensorProduct

namespace VectorPolynomial

variable {σ τ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem CoefficientGrid.realChartSubstitute_rational
    (b : Basis ι ℝ V) (q D d : ℕ) (P : VectorPolynomial σ ℚ V)
    (hdegree : DegreeLE (fun _ => 1) d P) (hP : CoefficientGrid b q P)
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, realPolynomialCoefficientGrid D (A i)) :
    CoefficientGrid b (q * D ^ d) (realChartSubstitute A P) := by
  rw [coefficientGrid_iff_coordinate]
  intro i
  rw [coordinate_realChartSubstitute_for_grid]
  exact realPolynomialCoefficientGrid_substitute
    (coordinate (b.coord i).toAddMonoidHom P) A q D d
    ((degreeLE_one_iff_basis_totalDegree b d P).mp hdegree i)
    ((coefficientGrid_iff_coordinate b q P).mp hP i) hA

end VectorPolynomial

namespace NilpotentLieFiltration
open VectorPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (v : τ → ℕ)

theorem symbolRationalGrid_homogeneousPullback_rational_of_coefficientGrid
    (hw : ∀ i, 0 < w i)
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, (A i).IsWeightedHomogeneous v (w i))
    (q D : ℕ) (hAD : ∀ i, realPolynomialCoefficientGrid D (A i))
    (R : F.RealPolynomialSymbolGroup w)
    (hR : CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
      (F.realGradedSymbolPolynomial b ω hF w R.coord)) :
    F.SymbolRationalGrid b ω hF v (q * D ^ s)
      (F.realSymbolHomogeneousPullbackHom b ω hF w v A hA R) := by
  apply F.symbolRationalGrid_of_gradedPolynomial b ω hF v (q * D ^ s)
  change CoefficientGrid _ (q * D ^ s)
    (F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v A R.coord))
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v A hA]
  with_reducible exact (CoefficientGrid.realChartSubstitute_rational
    (V := ℝ ⊗[ℚ] F.AssociatedGraded)
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) q D s
    (F.realGradedSymbolPolynomial b ω hF w R.coord)
    (F.realGradedSymbolPolynomial_degreeLE_one b ω hF w hw R) hR A hAD)

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedRecoveredChartMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {K X : Type*} [Fintype K]

variable {G : Type*} [Fintype G] {I J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem layerSamplerBox_sum_le_zero_root_budget :
    (∑ k, layerSamplerBox B U b S k) ≤
      allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (S.value : ℝ) :=
      Finset.sum_le_sum (fun k _ => layerSamplerBox_le B U b S k)
    _ = _ := by simp [allocatedPhysicalRootBudget]

end Erdos3.VectorPolynomial

end

end OAI
end


