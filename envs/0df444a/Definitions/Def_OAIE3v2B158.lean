-- Prove2me | Definitions.Def_OAIE3v2B158
-- name    : OAIE3v2B158
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:30:56.968764+00:00
-- url     : https://prove2.me/theorems/3908535d-0391-4c83-9188-fb4fa85cabb2
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 160 of 311
-- statement:
--   Definitions bundle 160 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B140`, `OAIE3v2B141`, `OAIE3v2B142`, `OAIE3v2B143`, `OAIE3v2B144`, `OAIE3v2B145`, `OAIE3v2B146`, `OAIE3v2B147`, `OAIE3v2B148` of this split.
--
--   Modules: `Dynamics/RealProjectedPotentialGroupIdentity.lean`, `Dynamics/RestrictedGradePathMembership.lean`, `Dynamics/TranslationMajorCorrelationBudget.lean`, `Estimates/RefilteredPointwiseSplitting.lean`, `Estimates/SymbolCommonCorrections.lean`, `Estimates/SymbolFastMembership.lean`, `Estimates/WeightedTranslationCentralTop.lean`, `Fourier/HomogeneousGradedProjectionFrequency.lean`, `Fourier/WeightedTranslationBufferedCentralFrequency.lean`, `Geometry/ControlledGradedBaseCoordinates.lean`, `Geometry/LowTaggedCoordinateRestriction.lean`, `Geometry/MajorTranslationBaseCoordinates.lean`, `Geometry/SymbolFactorizationTransport.lean`, `Geometry/TranslationLogCoordinateHomogeneous.lean`, `Lattices/ActualResidueSpatialFreezing.lean`, `Lattices/MajorTranslationIntegerEvaluation.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Linear/HomogeneousGradedProjectionBounds.lean`, `Linear/WeightedTranslationAssociatedGradedProjection.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Nilpotent/WeightedTranslationNilmanifold.lean`, `Nilpotent/WeightedTranslationRealBCHCoordinates.lean`, `Nilpotent/WeightedTranslationResidueNilmanifold.lean`, `Polynomial/FormalPolynomialCorrectionStep.lean`, `Polynomial/MajorTranslationDegreeSymbol.lean`, `Polynomial/RefilteredPolynomialProjection.lean`, `Polynomial/TranslationLogCoordinateWeightedDegree.lean`, `Polynomial/TwistedBufferedTranslationPhase.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B140
import Definitions.Def_OAIE3v2B141
import Definitions.Def_OAIE3v2B142
import Definitions.Def_OAIE3v2B143
import Definitions.Def_OAIE3v2B144
import Definitions.Def_OAIE3v2B145
import Definitions.Def_OAIE3v2B146
import Definitions.Def_OAIE3v2B147
import Definitions.Def_OAIE3v2B148

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.HomogeneousGradedProjectionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_image_graded
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule) :
    BasisGradedSubmodule c ν
      (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)).toSubmodule := by
  rintro r y ⟨x, hx, rfl⟩
  exact ⟨basisGradeProjection (F.associatedGradedBasis b ω hF) ω r x, hW r x hx,
    F.homogeneousGradedProjection_gradeProjection G c ν hG hc φ hφ b ω hF r x⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped BigOperators

variable {ι κ L M : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_coordinate_logHeight {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p)
    (x : F.AssociatedGraded)
    (hx : ∀ i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr x i) ≤ p) (j : κ) :
    rationalLogHeight (c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j) ≤
      (p + 2) ^ 4 := by
  apply rational_functional_value_logHeight (F.associatedGradedBasis b ω hF)
    ((c.coord j).comp (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap)
    hp hι _ x hx
  intro i
  change rationalLogHeight (c.repr
    (F.homogeneousGradedProjection G c ν hG hc φ hφ (F.associatedGradedBasis b ω hF i)) j) ≤ p
  rw [F.homogeneousGradedProjection_basis_repr G c ν hG hc φ hφ b ω hF]
  split_ifs
  · exact hentries i j
  · simpa [rationalLogHeight] using hp

theorem homogeneousGradedProjection_coordinate_ceil_height {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p)
    (x : F.AssociatedGraded)
    (hx : ∀ i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr x i) ≤ p) (j : κ) :
    RationalHeightLE (c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j)
      ⌈Real.exp ((p + 2) ^ 4)⌉₊ :=
  rationalHeightLE_ceil_exp
    (F.homogeneousGradedProjection_coordinate_logHeight G c ν hG hc φ hφ b ω hF
      hp hι hentries x hx j)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem gradedFrequency_top_natural (η : M →ₗ[ℚ] ℚ) (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis e ω hF) ω s x = x) :
    F.gradedFrequency e ω hF (η.comp φ.toLinearMap) x =
      G.gradedFrequency f ν hG η (F.associatedGradedMap G φ hφ x) := by
  obtain ⟨v, rfl⟩ := F.exists_associatedGradedPieceMap_of_pure e ω hF s x hx
  rw [F.associatedGradedMap_piece, F.gradedFrequency_top_piece,
    G.gradedFrequency_top_piece]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_top_frequency (η : M →ₗ[ℚ] ℚ)
    (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x) :
    η (F.homogeneousGradedProjection G c ν hG hc φ hφ x) =
      F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x := by
  obtain ⟨v, hv⟩ := F.exists_associatedGradedPieceMap_of_pure b ω hF s x hx
  rw [← hv, F.gradedFrequency_top_piece]
  change η (G.homogeneousAssociatedGradedEquiv c ν hG hc
    (F.associatedGradedMap G φ hφ (F.associatedGradedPieceMap s v))) = η (φ v.val)
  rw [F.associatedGradedMap_piece G φ hφ,
    G.homogeneousAssociatedGradedEquiv_top_piece c ν hG hc]

theorem homogeneousGradedProjection_top_frequency_zero
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (η : M →ₗ[ℚ] ℚ)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x = 0)
    {y : M} (hy : y ∈ W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ))
    (htop : y ∈ G.layer s) : η y = 0 := by
  apply graded_image_frequency_zero (F.associatedGradedBasis b ω hF) ω c ν
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap s
    (F.homogeneousGradedProjection_gradeProjection G c ν hG hc φ hφ b ω hF s)
    W.toSubmodule hW η ?_ hy (G.basisGradeProjection_top c ν hG ⟨y, htop⟩)
  intro x hx hpure
  exact (F.homogeneousGradedProjection_top_frequency G c ν hG hc φ hφ b ω hF η x hpure).trans
    (hη x hx hpure)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolFastMembership
namespace OAI

section

namespace Erdos3

open Module

theorem monomialScale_div_const {σ : Type*} (S : σ → ℝ) (c : ℝ) (α : σ →₀ ℕ) :
    monomialScale (fun i => S i / c) α =
      monomialScale S α / c ^ Finsupp.weight (fun _ => 1) α := by
  calc
    _ = monomialScale (fun i => c⁻¹ * S i) α := by
      congr 1
      funext i
      simp only [div_eq_mul_inv, mul_comm]
    _ = c⁻¹ ^ Finsupp.weight (fun _ => 1) α * monomialScale S α := monomialScale_const_mul S c⁻¹ α
    _ = _ := by rw [inv_pow, div_eq_mul_inv, mul_comm]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolSlowBound_dilation_inverse_scale (S : σ → ℝ) (hS : ∀ i, 0 < S i)
    (p : ℝ) (r : ℚ) (hr : r ≠ 0) (E : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ => 1) S (Real.exp p) E) :
    F.SymbolSlowBound b ω hF (fun _ => 1) (fun i => S i / |(r : ℝ)|) (Real.exp p)
      (F.realPolynomialSymbolDilationHom (fun _ => 1) r E) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have habs : 0 < |(r : ℝ)| := abs_pos.mpr hrR
  intro z
  rw [F.realPolynomialSymbolDilationHom_coord, F.realPolynomialSymbolDilation_repr, abs_mul, abs_pow]
  apply (mul_le_mul_of_nonneg_left (hE z) (pow_nonneg habs.le _)).trans_eq
  rw [monomialScale_div_const]
  field_simp [(monomialScale_pos S hS z.val.1).ne', habs.ne']

theorem symbolSlowBound_dilation_physical (S T : σ → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (p q : ℝ) (hq : 0 ≤ q)
    (r : ℚ) (hr : r ≠ 0)
    (hphysical : ∀ i, Real.exp (-q) * (|(r : ℝ)| * T i) ≤ S i)
    (E : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ => 1) S (Real.exp p) E) :
    F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp (p + (s : ℝ) * q))
      (F.realPolynomialSymbolDilationHom (fun _ => 1) r E) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have habs : 0 < |(r : ℝ)| := abs_pos.mpr hrR
  have hscaled := F.symbolSlowBound_dilation_inverse_scale b ω hF S hS p r hr E hE
  apply F.symbolSlowBound_rescale b ω hF (fun i => S i / |(r : ℝ)|) T
    (fun i => div_pos (hS i) habs) hT hq _ _ hscaled
  intro i
  apply (le_div_iff₀ habs).mpr
  calc
    Real.exp (-q) * T i * |(r : ℝ)| = Real.exp (-q) * (|(r : ℝ)| * T i) := by ring
    _ ≤ S i := hphysical i

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RestrictedGradePathMembership
namespace OAI

section

namespace Erdos3
open Module VectorPolynomial
open scoped TensorProduct BigOperators

namespace NilpotentLieFiltration
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem truncateRealSymbol_mem_of_grade_values
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t : σ → ℝ, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x.coord ∈ realificationLieSubalgebra U) :
    (F.truncateRealSymbol b ω hF w k x).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w U _).mpr
  intro t
  rw [F.truncateRealSymbol_coord, basisBelowProjection_eq_sum_grades]
  simp only [map_sum]
  apply (realificationLieSubalgebra U).toSubmodule.sum_mem
  intro j hj
  exact hx t j (Finset.mem_range.mp hj)

theorem realSymbolGradeQuotient_mem_of_grade_values
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t : σ → ℝ, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x.coord ∈ realificationLieSubalgebra U) :
    F.realSymbolGradeQuotientHom w k x ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
        (F.symbolPointwiseSubalgebra b ω hF w U)).map (F.realSymbolGradeQuotientHom w k) := by
  apply Subgroup.mem_map.mpr
  refine ⟨F.truncateRealSymbol b ω hF w k x,
    F.truncateRealSymbol_mem_of_grade_values b ω hF w U x k hx, ?_⟩
  exact F.truncateRealSymbol_quotient b ω hF w k x

theorem realSymbolGradeQuotient_mem_of_restricted_path
    (w : σ → ℕ) (v : τ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (K : Set (σ → ℝ)) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (x : F.RealPolynomialSymbol w) (y : F.RealPolynomialSymbolGroup v) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x ∈ realificationLieSubalgebra U)
    (hy : ∀ u : τ → ℝ, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF v j u y.coord =
        F.realSymbolGradeEvaluation b ω hF w j
          (fun i => MvPolynomial.eval u (β i)) x) :
    F.realSymbolGradeQuotientHom v k y ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
        (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) := by
  apply F.realSymbolGradeQuotient_mem_of_grade_values b ω hF v U y k
  intro u j hj
  rw [hy u j hj]
  exact hx _ (hβ u) j hj

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolCommonCorrections
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem outer_sum_mem_of_identity_mod_layer (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) {j k : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    (a d p p' : L) (ha : a ∈ U.toSubmodule ⊔ F.layer j) (hd : d ∈ U.toSubmodule ⊔ F.layer j)
    (hp : p ∈ U.toSubmodule ⊔ F.layer k) (hp' : p' ∈ U.toSubmodule ⊔ F.layer k)
    (heq : p - lieBCH s (lieBCH s a p') d ∈ F.layer k) :
    a + d ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
  have hkw : U.toSubmodule ⊔ F.layer k ≤ U.toSubmodule ⊔ F.layer (j + 1) :=
    sup_le_sup_left (F.antitone hjk) _
  have hwj : U.toSubmodule ⊔ F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer j :=
    sup_le_sup_left (F.antitone (Nat.le_succ j)) _
  have hrem := F.bch_triple_remainder_mem_subalgebra_sup_layer hs U hj a p' d ha (hwj (hkw hp')) hd
  have herr : p - lieBCH s (lieBCH s a p') d ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    Submodule.mem_sup_right (F.antitone hjk heq)
  convert Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (hkw hp) (hkw hp')) herr) hrem using 1
  abel

theorem outer_factors_mem_mod_layer_of_separation (U : LieSubalgebra ℚ L)
    (k : ℕ) (hk : k ≤ s + 1) (A D P P' : F.Group)
    (hP : P.coord ∈ U.toSubmodule ⊔ F.layer k) (hP' : P'.coord ∈ U.toSubmodule ⊔ F.layer k)
    (hidentity : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) P =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (A * P' * D))
    (hseparate : ∀ j : ℕ, 1 ≤ j → j < k →
      A.coord + D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      A.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧ D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    A.coord ∈ U.toSubmodule ⊔ F.layer k ∧ D.coord ∈ U.toSubmodule ⊔ F.layer k := by
  cases k with
  | zero =>
    have hall (x : L) : x ∈ F.layer 0 := F.antitone (Nat.zero_le 1) (by rw [F.one_eq_top]; trivial)
    exact ⟨Submodule.mem_sup_right (hall _), Submodule.mem_sup_right (hall _)⟩
  | succ k =>
    have herr : P.coord - lieBCH s (lieBCH s A.coord P'.coord) D.coord ∈ F.layer (k + 1) := by
      apply (lieQuotientMap_eq_zero (F.layerIdeal (k + 1)) _).mp
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg NilpotentLieBCHGroup.coord hidentity)
    have hind : ∀ n : ℕ, n ≤ k →
        A.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) ∧ D.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [Nat.zero_add, F.one_eq_top, sup_top_eq]
        exact ⟨Submodule.mem_top, Submodule.mem_top⟩
      | succ n ih =>
        intro hn
        obtain ⟨ha, hd⟩ := ih (by omega)
        apply hseparate (n + 1) (by omega) (by omega)
        exact F.outer_sum_mem_of_identity_mod_layer (by omega) U (by omega) (by omega)
          A.coord D.coord P.coord P'.coord ha hd hP hP' herr
    exact hind k le_rfl

theorem compatible_factors_mem_mod_layer_of_separation (U : LieSubalgebra ℚ L)
    (k : ℕ) (hk : k ≤ s + 1) (E P R E' P' R' : F.Group)
    (hP : P.coord ∈ U.toSubmodule ⊔ F.layer k) (hP' : P'.coord ∈ U.toSubmodule ⊔ F.layer k)
    (hidentity : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (E * P * R) =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (E' * P' * R'))
    (hseparate : ∀ j : ℕ, 1 ≤ j → j < k →
      (E⁻¹ * E').coord + (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      (E⁻¹ * E').coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧
        (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    (E⁻¹ * E').coord ∈ U.toSubmodule ⊔ F.layer k ∧ (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer k := by
  let q := NilpotentLieBCHGroup.quotientHom (hnil := F.lowerCentralSeries_eq_bot) (F.layerIdeal k)
  change q (E * P * R) = q (E' * P' * R') at hidentity
  have hmiddle : q P = q ((E⁻¹ * E') * P' * (R' * R⁻¹)) := by
    have h := congrArg (fun x => (q E)⁻¹ * x * (q R)⁻¹) hidentity
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  exact F.outer_factors_mem_mod_layer_of_separation U k hk (E⁻¹ * E') (R' * R⁻¹) P P' hP hP' hmiddle hseparate

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredPointwiseSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem mem_realGradedRefiltrationLayer_iff {ι : Type*} (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (j : ℕ) (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realGradedRefiltrationLayer U j ↔ v ∈ F.realification.layer j ∧
      (F.gradedPieceProjection b ω hlayers j).baseChange ℝ v ∈ realificationLieSubalgebra U := by
  rw [realGradedRefiltrationLayer, F.gradedRefiltrationLayer_eq_inf_comap b ω hlayers,
    realification_inf, realification_comap, Submodule.mem_inf, Submodule.mem_comap]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem real_symbol_values_iff_refiltration_coefficients
    (p : F.realification.adaptedLieSubalgebra w) :
    (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra U) ↔
    ∀ α, coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      F.realGradedRefiltrationLayer U (Finsupp.weight w α) := by
  refine (eval₂_mem_iff_coefficients (realificationLieSubalgebra U).toSubmodule _).trans ?_
  apply forall_congr'
  intro α
  rw [F.mem_realGradedRefiltrationLayer_iff U b ω hlayers,
    F.realPolynomialSymbolMap_apply, F.realGradedSymbolPolynomial_coefficient_of_polynomial]
  exact (and_iff_right (p.property α)).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationRealBCHCoordinates
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomialExponentialCoordinate_eval_potential_on_submodule
    {σ : Type*} [Fintype σ] (K : Submodule ℚ (σ → ℚ))
    (x : σ → ℚ) (hx : x ∈ K) (P V : MvPolynomial σ ℚ)
    (hderiv : ∀ z ∈ K, eval z (scalarDirectionalDerivative x V) = eval z P)
    (z : σ → ℚ) (hz : z ∈ K) :
    eval z (polynomialExponentialCoordinate x P) = eval z V - eval (z - x) V := by
  classical
  let A : (Fin 2 → ℚ) →ₗ[ℚ] (σ → ℚ) :=
    { toFun := fun t => t 0 • x + t 1 • z
      map_add' := by intros; simp only [Pi.add_apply, add_smul]; abel
      map_smul' := by
        intros
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul] }
  have hAx : A ![1, 0] = x := by simp [A]
  have hAz : A ![0, 1] = z := by simp [A]
  have hAK (t : Fin 2 → ℚ) : A t ∈ K :=
    K.add_mem (K.smul_mem _ hx) (K.smul_mem _ hz)
  have hres : scalarDirectionalDerivative ![1, 0] (polynomialLinearRestriction A V) =
      polynomialLinearRestriction A P := by
    apply MvPolynomial.funext
    intro t
    rw [scalarDirectionalDerivative_linearRestriction, hAx,
      eval_polynomialLinearRestriction, eval_polynomialLinearRestriction]
    exact hderiv _ (hAK t)
  have h := polynomialLinearRestriction_exponentialCoordinate A ![1, 0] P
  rw [hAx, ← hres, polynomialExponentialCoordinate_potential] at h
  have he := congrArg (eval ![0, 1]) h
  rw [eval_polynomialLinearRestriction, hAz, map_sub,
    eval_polynomialLinearRestriction, hAz, eval_translate_rational,
    eval_polynomialLinearRestriction, map_add, map_neg, hAz, hAx] at he
  simpa only [sub_eq_add_neg] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RealProjectedPotentialGroupIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

theorem bchRealTranslationHom_rational_eval_potential
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial)
    (x : weightedSubalgebra w d) (hx : x ∈ U) (z : σ → ℚ)
    (hz : z ∈ U.toSubmodule.map (baseLinear.comp (weightedSubalgebra w d).subtype)) :
    eval (fun i => (z i : ℝ))
        (bchRealTranslationHom w d hwd ⟨(1 : ℝ) ⊗ₜ[ℚ] x⟩).polynomial =
      eval (fun i => (z i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) V) -
        eval ((fun i => (z i : ℝ)) -
          (bchRealTranslationHom w d hwd ⟨(1 : ℝ) ⊗ₜ[ℚ] x⟩).base)
          (MvPolynomial.map (algebraMap ℚ ℝ) V) := by
  have hq := polynomialExponentialCoordinate_eval_potential_on_submodule
    (U.toSubmodule.map (baseLinear.comp (weightedSubalgebra w d).subtype))
    x.val.base ⟨x, hx, rfl⟩ x.val.polynomial V (hderiv x hx) z hz
  have hr : bchRealTranslationHom w d hwd ⟨(1 : ℝ) ⊗ₜ[ℚ] x⟩ =
      PolynomialTranslationGroupOver.map (algebraMap ℚ ℝ)
        (PolynomialTranslationGroupOver.rationalEquiv
          (bchTranslationHom w d hw hwd ⟨x⟩)) :=
    bchRealTranslationHom_rational w d hw hwd ⟨x⟩
  rw [hr]
  change eval (fun i => (z i : ℝ))
    (MvPolynomial.map (algebraMap ℚ ℝ) (polynomialExponentialCoordinate x.val.base x.val.polynomial)) =
    eval (fun i => (z i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) V) -
      eval ((fun i => (z i : ℝ)) - (fun i => (x.val.base i : ℝ)))
        (MvPolynomial.map (algebraMap ℚ ℝ) V)
  have hzsub : ((fun i => (z i : ℝ)) - (fun i => (x.val.base i : ℝ))) =
      (fun i => ((z - x.val.base) i : ℝ)) := by
    ext i
    simp only [Pi.sub_apply, Rat.cast_sub]
  rw [hzsub, eval_real_map_at_rational, eval_real_map_at_rational, eval_real_map_at_rational]
  exact_mod_cast hq

theorem bchRealTranslationHom_eval_potential_on_real_base_image
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial)
    (g : (weightedFiltration w d hwd).realification.Group)
    (hg : g.coord ∈ U.toSubmodule.baseChange ℝ) (b : σ → ℝ)
    (hb : b ∈ (U.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) :
    eval b (bchRealTranslationHom w d hwd g).polynomial =
      eval b (MvPolynomial.map (algebraMap ℚ ℝ) V) -
        eval (b - (bchRealTranslationHom w d hwd g).base)
          (MvPolynomial.map (algebraMap ℚ ℝ) V) := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    ((weightedBasis w d hw).baseChange ℝ).finiteDimensional_of_finite
  let ℓ := baseLinear.comp (weightedSubalgebra w d).subtype
  let B := realifyCoordinateMap ℓ
  have hB : Continuous B := LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) B
  obtain ⟨y, hy, rfl⟩ := hb
  let f : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (ℝ ⊗[ℚ] weightedSubalgebra w d) → ℝ :=
    fun z => eval (B z.2) (bchRealTranslationHom w d hwd ⟨z.1⟩).polynomial
  let r : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (ℝ ⊗[ℚ] weightedSubalgebra w d) → ℝ :=
    fun z => eval (B z.2) (MvPolynomial.map (algebraMap ℚ ℝ) V) -
      eval (B z.2 - (bchRealTranslationHom w d hwd ⟨z.1⟩).base)
        (MvPolynomial.map (algebraMap ℚ ℝ) V)
  have hf0 := continuous_bchRealTranslationHom_polynomial_eval w d hw hd hwd
  have hf : Continuous f := continuous_pair_pullback hf0 hB
  have hr : Continuous r := continuous_pair_potential_difference
    (continuous_bchRealTranslationHom_base w d hw hd hwd) hB
    (MvPolynomial.continuous_eval (MvPolynomial.map (algebraMap ℚ ℝ) V))
  have hrat (x y : U.toSubmodule) :
      f ((1 : ℝ) ⊗ₜ[ℚ] (x : weightedSubalgebra w d),
        (1 : ℝ) ⊗ₜ[ℚ] (y : weightedSubalgebra w d)) =
      r ((1 : ℝ) ⊗ₜ[ℚ] (x : weightedSubalgebra w d),
        (1 : ℝ) ⊗ₜ[ℚ] (y : weightedSubalgebra w d)) := by
    have hBy : B ((1 : ℝ) ⊗ₜ[ℚ] (y : weightedSubalgebra w d)) =
        (fun i => (y.val.val.base i : ℝ)) := by
      funext i
      exact (realifyCoordinateMap_tmul ℓ 1 y.val i).trans (one_mul _)
    dsimp only [f, r]
    rw [hBy]
    exact bchRealTranslationHom_rational_eval_potential w d hw hwd U V hderiv
      x.val x.property y.val.val.base ⟨y.val, y.property, rfl⟩
  exact realification_pair_eq_of_rational U.toSubmodule hf hr hrat hg hy

theorem bchRealTranslationHom_eval_potential
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial)
    (g : (weightedFiltration w d hwd).realification.Group)
    (hg : g.coord ∈ U.toSubmodule.baseChange ℝ) (b : σ → ℝ)
    (hb : b ∈ (U.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) :
    eval b (bchRealTranslationHom w d hwd g).polynomial =
      eval b (MvPolynomial.map (algebraMap ℚ ℝ) V) -
        eval (b - (bchRealTranslationHom w d hwd g).base)
          (MvPolynomial.map (algebraMap ℚ ℝ) V) := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    realification_moduleTopology_t2 (weightedBasis w d hw)
  exact bchRealTranslationHom_eval_potential_on_real_base_image
    w d hw hd hwd U V hderiv g hg b hb

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorCorrelationBudget
namespace OAI

section

namespace Erdos3

theorem translationMajorPairBudget_controls (a : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : 2 ≤ a) :
    p ≤ raisedNiltestBudget p ∧
      raisedNiltestBudget p ≤ translationMajorPairBudget a p ∧
      2 ≤ translationMajorPairBudget a p := by
  have hq : (2 : ℝ) ≤ raisedNiltestBudget p := by
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (p + 2)]
  have hbase : (1 : ℝ) ≤ raisedNiltestBudget p + a := by
    linarith [Nat.cast_nonneg a (α := ℝ)]
  have hpow : raisedNiltestBudget p + a ≤ translationMajorPairBudget a p := by
    exact (pow_one (raisedNiltestBudget p + a)).symm.le.trans
      (pow_le_pow_right₀ hbase (by omega : 1 ≤ a))
  have hqr : raisedNiltestBudget p ≤ translationMajorPairBudget a p :=
    (le_add_of_nonneg_right (Nat.cast_nonneg a)).trans hpow
  exact ⟨le_raisedNiltestBudget p, hqr, hq.trans hqr⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationNilmanifold
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module
variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationNilmanifold_complexity {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (WeightedBasisIndex w d) : ℝ) ≤ p)
    (hgrid : (d.factorial : ℝ) ≤ Real.exp p)
    (hstructure : ((2*d+1 : ℕ) : ℝ) ≤ Real.exp p) :
    (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p := by
  refine ⟨hdim,hgrid,?_,?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (weightedOrderedBasis_structure_height w d hw i j k) hstructure
  · intro i j k
    exact rationalLogHeight_le_of_height (weightedLayerFinBasis_height w d hw hwd (i.val+1) j k)
      (by simpa using Real.one_le_exp_iff.mpr hp)

theorem weightedTranslationNilmanifold_complexity_budget :
    (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE
      ((Fintype.card σ + (Fintype.card σ + 1)^d + d.factorial + 2*d + 1 : ℕ) : ℝ) := by
  let n := Fintype.card σ + (Fintype.card σ + 1)^d + d.factorial + 2*d + 1
  have hdim : (Fintype.card (WeightedBasisIndex w d) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (weightedBasisIndex_card_le w d hw).trans
      (show Fintype.card σ + (Fintype.card σ + 1)^d ≤ n by dsimp [n]; omega)
  have hf : (d.factorial : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show d.factorial ≤ n by dsimp [n]; omega)
  have hs : ((2*d+1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 2*d+1 ≤ n by dsimp [n]; omega)
  have he : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  exact weightedTranslationNilmanifold_complexity w d hw hwd (Nat.cast_nonneg n)
    hdim (hf.trans he) (hs.trans he)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TwistedBufferedTranslationPhase
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ}

theorem bufferedTranslationPhase_eq_phaseFunction (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    bufferedTranslationPhase Ψ D₀ g =
      (Ψ.value (fun i => g.base i - (⌊g.base i + 1 / 2⌋ : ℝ)) : ℂ) *
        translationPhaseFunction D₀ g := by
  apply bufferedTranslationPhase_eq_chart Ψ D₀ g (fun i => ⌊g.base i + 1 / 2⌋)
  intro i
  apply abs_le.mpr
  have hl := Int.floor_le (g.base i + 1 / 2)
  have hu := Int.lt_floor_add_one (g.base i + 1 / 2)
  constructor <;> linarith

theorem bufferedTranslationPhase_majorSymbol {U : Type*} (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ) (D₀ : MvPolynomial (Fin m) ℝ)
    (A : Fin m → MvPolynomial U ℝ) (u : U → ℝ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) :
    bufferedTranslationPhase Ψ D₀ (algebraicMajorSymbol D D₀ A u) =
      (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ) := by
  rw [bufferedTranslationPhase_eq_chart Ψ D₀ _ β hβ]
  unfold bufferedTranslationTerm
  rw [translationPhaseArgument_majorSymbol]
  rfl

theorem bufferedTranslationPhase_central (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (a : ℝ) :
    bufferedTranslationPhase Ψ D₀ (g * ⟨0, C a⟩) =
      bufferedTranslationPhase Ψ D₀ g * (Real.fourierChar a : ℂ) := by
  rw [bufferedTranslationPhase_eq_phaseFunction, bufferedTranslationPhase_eq_phaseFunction,
    translationPhaseFunction_central]
  have hb : (g * (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ (Fin m))).base = g.base := by simp
  rw [hb, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (M : ℕ)

theorem twistedBufferedTranslationPhase_majorSymbol {U : Type*} (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ) (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (A : Fin m → MvPolynomial U ℝ) (u : U → ℝ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ D₀ T (algebraicMajorSymbol D D₀ A u) =
      T (fun i => eval u (A i) - (β i : ℝ)) (fun i => (β i : ZMod M)) *
        (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ) := by
  rw [twistedBufferedTranslationPhase_eq_chart M Ψ D₀ T _ β hβ]
  unfold twistedBufferedTranslationTerm bufferedTranslationTerm
  rw [translationPhaseArgument_majorSymbol, mul_assoc]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

section RealBasis

variable {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)
  (b : Basis ι ℝ L) (ω : ι → ℕ) (v : σ → ℕ)

theorem polynomialOrbit_log_mul_mem_graded (hb : BasisHomogeneousBrackets b ω)
    (p q : F.PolynomialOrbit v)
    (hp : p.log ∈ gradedPolynomialSubmodule b ω v)
    (hq : q.log ∈ gradedPolynomialSubmodule b ω v) :
    (p * q).log ∈ gradedPolynomialSubmodule b ω v :=
  lieBCH_mem (gradedPolynomialSubalgebra b ω hb v) s hp hq

end RealBasis

section RationalBasis

variable {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ) (v : σ → ℕ)

theorem realPolynomialOrbit_log_mul_mem_graded (hb : BasisHomogeneousBrackets b ω)
    (p q : F.realification.PolynomialOrbit v)
    (hp : p.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v)
    (hq : q.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v) :
    (p * q).log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v :=
  F.realification.polynomialOrbit_log_mul_mem_graded (b.baseChange ℝ) ω v
    (hb.baseChange b ω) p q hp hq

end RationalBasis

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymbolFactorizationTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem SymbolFactorizationIn.dilate_ratio
    {S T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)}
    {p q : ℝ} {D : ℕ} {U : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.SymbolFactorizationIn b ω hF S X p D U)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.SymbolFactorizationIn b ω hF T
      (F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d) X)
      (p + (s : ℝ) * q) (D * d ^ s) U := by
  have hr : (a : ℚ) / d ≠ 0 := div_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hd.ne')
  let φ := F.realPolynomialSymbolDilationHom (fun _ : σ => 1) ((a : ℚ) / d)
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := h
  refine ⟨φ E, φ P, φ R, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg φ hprod
  · exact F.symbolSlowBound_dilation_physical b ω hF S T hS hT p q hq _ hr hphysical E hE
  · exact F.symbolRationalGrid_dilation_ratio b ω hF (fun _ => 1) D d a hd R hR
  · exact F.realSymbolDilation_mem_pointwise b ω hF (fun _ => 1) U _ P.coord hP

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I V : Type*} {N : I → ℕ} {q : ℕ}

variable [Fintype I] [DecidableEq I]

theorem mem_integerPoints_iff (A : ResidueBoxSlice N q) (x : I → ℤ) :
    x ∈ A.integerPoints ↔
      ∀ i, x i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i) := by
  rw [A.integerPoints_eq_commonStrideBox]
  exact Fintype.mem_piFinset

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationDegreeSymbol
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorTranslationJointPolynomial_degree_weightedHomogeneousComponent (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (majorTranslationJointPolynomial D A) =
      majorTranslationJointPolynomial
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
        (majorTranslationTopCoordinates w A) := by
  have hlower := majorTranslationJointPolynomial_sub_degree_top_lower w hD A hA
  have hzero : weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
      (majorTranslationJointPolynomial D A -
        majorTranslationJointPolynomial
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) A) = 0 :=
    weightedHomogeneousComponent_eq_zero' d _ (fun α hα => (hlower hα).ne)
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero]
  exact majorTranslationJointPolynomial_weightedHomogeneousComponent w
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _) A hA

theorem majorTranslationJointPolynomial_degree_slot_top (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) (α : B →₀ ℕ) :
    weightedHomogeneousComponent (fun _ : U => 1) (d - Finsupp.weight w α)
        (polynomialSlotCoefficient α (majorTranslationJointPolynomial D A)) =
      polynomialSlotCoefficient α
        (majorTranslationJointPolynomial
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
          (majorTranslationTopCoordinates w A)) := by
  rw [polynomialSlotCoefficient_weightedHomogeneousComponent (fun _ : U => 1) w
    (majorTranslationJointPolynomial_degree w hD A hA),
    majorTranslationJointPolynomial_degree_weightedHomogeneousComponent w hD A hA]

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

theorem translationBasePolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationBasePolynomialOrbit w d hw hwd A hA)) =
      ⟨fun i => eval u (A i), 0⟩ := by
  let g := (weightedFiltration w d hwd).realification.polynomialOrbitRealEval
    (fun _ : U => 1) u (translationBasePolynomialOrbit w d hw hwd A hA)
  have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord
    (fun i => eval u (A i)) (0 : weightedSupportLT (R := ℝ) w d) ?_ ?_
  · exact bchRealTranslationHom_pure_base_of_shape w d hwd g.coord _ hs.1
      (by simpa only [ZeroMemClass.coe_zero, map_zero] using hs.2)
  · intro i
    exact translationBasePolynomialOrbit_eval_coordinates w d hw hwd A hA u (Sum.inl i)
  · intro α
    simpa only [translationBaseCoordinatePolynomial, Sum.elim_inr, map_zero,
      ZeroMemClass.coe_zero, MvPolynomial.coeff_zero] using
      translationBasePolynomialOrbit_eval_coordinates w d hw hwd A hA u (Sum.inr α)

theorem translationPurePolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hPslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationPurePolynomialOrbit w d hw hwd P hP)) =
      ⟨0, specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
  let g := (weightedFiltration w d hwd).realification.polynomialOrbitRealEval
    (fun _ : U => 1) u (translationPurePolynomialOrbit w d hw hwd P hP)
  let Pu : weightedSupportLT (R := ℝ) w d :=
    ⟨specializeMajorParameters (RingHom.id ℝ) P u, hPslot u⟩
  have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord 0 Pu ?_ ?_
  · exact bchRealTranslationHom_pure_polynomial_of_shape w d hwd g.coord Pu.val
      (fun i => by simpa only [Pi.zero_apply, map_zero] using hs.1 i) hs.2
  · intro i
    simpa only [translationPolynomialCoordinatePolynomial, Sum.elim_inl, map_zero,
      Pi.zero_apply] using
      translationPurePolynomialOrbit_eval_coordinates w d hw hwd P hP u (Sum.inl i)
  · intro α
    have h := translationPurePolynomialOrbit_eval_coordinates w d hw hwd P hP u (Sum.inr α)
    change ((weightedBasis w d hw).baseChange ℝ).repr g.coord (Sum.inr α) =
      eval u (polynomialSlotCoefficient α.val P) at h
    rw [h]
    simpa only [MvPolynomial.aeval_eq_eval, Pu, specializeMajorParameters,
      RingHom.comp_id, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
      Algebra.algebraMap_self, MvPolynomial.eval₂_id, MvPolynomial.coe_eval₂Hom] using
      polynomialSlotCoefficient_eval u α.val P

theorem translationCoordinatePolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hPslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationCoordinatePolynomialOrbit w d hw hwd A hA P hP)) =
      ⟨fun i => eval u (A i), specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
  rw [translationCoordinatePolynomialOrbit, map_mul, map_mul,
    translationBasePolynomialOrbit_realEval, translationPurePolynomialOrbit_realEval
      w d hw hwd P hP hPslot]
  apply PolynomialTranslationGroupOver.ext <;> simp

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module VectorPolynomial
open NilpotentLieFiltration
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

theorem translationBasePolynomialOrbit_symbol_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolHom w d hw hwd
      (translationBasePolynomialOrbit w d hw hwd A hA) =
    translationPolynomialSymbolHom w d hw hwd
      (translationBasePolynomialOrbit w d hw hwd (majorTranslationTopCoordinates w A)
        (majorTranslationTopCoordinates_degree w A)) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  have hcoords : (fun i : WeightedBasisIndex w d =>
      weightedHomogeneousComponent (fun _ : U => 1) (weightedBasisGrade w d i)
        (translationBaseCoordinatePolynomial w d A i)) =
      translationBaseCoordinatePolynomial w d (majorTranslationTopCoordinates w A) := by
    funext i
    cases i with
    | inl i => rfl
    | inr α => exact map_zero _
  apply NilpotentLieBCHGroup.ext
  simp only [translationPolynomialSymbolHom_coord, translationBasePolynomialOrbit_log]
  rw [(weightedFiltration w d hwd).realSymbolOfPolynomial_ofCoordinates_top
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)]
  rw [hcoords]

theorem translationPurePolynomialOrbit_symbol_eq_of_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P Q : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hQ : Q ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (htop : ∀ α : B →₀ ℕ,
      weightedHomogeneousComponent (fun _ : U => 1) (d - Finsupp.weight w α)
        (polynomialSlotCoefficient α P) = polynomialSlotCoefficient α Q) :
    translationPolynomialSymbolHom w d hw hwd
      (translationPurePolynomialOrbit w d hw hwd P hP) =
    translationPolynomialSymbolHom w d hw hwd
      (translationPurePolynomialOrbit w d hw hwd Q hQ) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  have hcoords : (fun i : WeightedBasisIndex w d =>
      weightedHomogeneousComponent (fun _ : U => 1) (weightedBasisGrade w d i)
        (translationPolynomialCoordinatePolynomial w d P i)) =
      translationPolynomialCoordinatePolynomial w d Q := by
    funext i
    cases i with
    | inl i => exact map_zero _
    | inr α => exact htop α.val
  apply NilpotentLieBCHGroup.ext
  simp only [translationPolynomialSymbolHom_coord, translationPurePolynomialOrbit_log]
  rw [(weightedFiltration w d hwd).realSymbolOfPolynomial_ofCoordinates_top
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)]
  rw [hcoords]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

theorem majorTranslationPolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)) =
      algebraicMajorSymbol D (specializeMajorParameters (RingHom.id ℝ) D 0) A u := by
  rw [majorTranslationPolynomialOrbit, translationCoordinatePolynomialOrbit_realEval
    w d hw hwd A hA _ _ (majorTranslationJointPolynomial_specialize_lower w hw hD A),
    majorTranslationJointPolynomial_specialize]
  rfl

theorem majorTranslationPolynomialOrbit_top_log_graded
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) :
    (majorTranslationPolynomialOrbit w d hw hwd D
      (fun _ hα => (hD (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)).log ∈
      gradedPolynomialSubmodule ((weightedBasis w d hw).baseChange ℝ)
        (weightedBasisGrade w d) (fun _ : U => 1) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  apply (weightedFiltration w d hwd).realPolynomialOrbit_log_mul_mem_graded
    (weightedBasis w d hw) (weightedBasisGrade w d) (fun _ : U => 1)
    (weightedBasis_homogeneous_brackets w d hw)
  · rw [translationBasePolynomialOrbit_log]
    apply ofCoordinates_mem_gradedPolynomialSubmodule
    intro i
    cases i with
    | inl i => exact majorTranslationTopCoordinates_homogeneous w A i
    | inr α => exact isWeightedHomogeneous_zero ℝ _ _
  · rw [translationPurePolynomialOrbit_log]
    apply ofCoordinates_mem_gradedPolynomialSubmodule
    intro i
    cases i with
    | inl i => exact isWeightedHomogeneous_zero ℝ _ _
    | inr α =>
      change (polynomialSlotCoefficient α.val
        (majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A))).IsWeightedHomogeneous
          (fun _ : U => 1) (d - Finsupp.weight w α.val)
      have htop := majorTranslationJointPolynomial_top_homogeneous w hD A
      have hle : majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A) ∈
          weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
        fun _ hβ => (htop (mem_support_iff.mp hβ)).le
      have he := polynomialSlotCoefficient_weightedHomogeneousComponent
        (fun _ : U => 1) w hle α.val
      rw [htop.weightedHomogeneousComponent_same] at he
      rw [← he]
      exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

 theorem majorTranslationPolynomialOrbit_symbol_degree_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd D hD A hA) =
    translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
        (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
          (mem_support_iff.mp hα)).le)
        (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)) := by
  simp only [majorTranslationPolynomialOrbit, translationCoordinatePolynomialOrbit, map_mul]
  rw [translationBasePolynomialOrbit_symbol_top w d hw hwd A hA]
  rw [translationPurePolynomialOrbit_symbol_eq_of_top w d hw hwd
    (majorTranslationJointPolynomial D A)
    (majorTranslationJointPolynomial
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
      (majorTranslationTopCoordinates w A))
    (majorTranslationJointPolynomial_degree w hD A hA)
    (majorTranslationJointPolynomial_degree w
      (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A))
    (majorTranslationJointPolynomial_degree_slot_top w hD A hA)]

 theorem majorTranslationPolynomialOrbit_degree_symbol_representative
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realSymbolRepresentative
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
      (translationPolynomialSymbolHom w d hw hwd
        (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)).coord =
    (majorTranslationPolynomialOrbit w d hw hwd
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
      (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)).log := by
  rw [majorTranslationPolynomialOrbit_symbol_degree_top w d hw hwd D hD A hA,
    translationPolynomialSymbolHom_coord]
  exact (weightedFiltration w d hwd).realSymbolRepresentative_of_gradedPolynomial
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) _
    (majorTranslationPolynomialOrbit_top_log_graded w d hw hwd _
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) A)

 theorem majorTranslationPolynomialOrbit_degree_symbolLift_eq
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolLift w d hw hwd
      (translationPolynomialSymbolHom w d hw hwd
        (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)) =
    majorTranslationPolynomialOrbit w d hw hwd
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
      (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A) := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (translationPolynomialSymbolLift w d hw hwd
    (translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd D hD A hA))).log = _
  rw [translationPolynomialSymbolLift_log,
    majorTranslationPolynomialOrbit_degree_symbol_representative w d hw hwd D hD A hA]
  rfl

 theorem majorTranslationPolynomialOrbit_degree_symbolLift_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u
        (translationPolynomialSymbolLift w d hw hwd
          (translationPolynomialSymbolHom w d hw hwd
            (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)))) =
      algebraicMajorSymbol
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
        (specializeMajorParameters (RingHom.id ℝ)
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) 0)
        (majorTranslationTopCoordinates w A) u := by
  rw [majorTranslationPolynomialOrbit_degree_symbolLift_eq w d hw hwd D hD A hA]
  exact majorTranslationPolynomialOrbit_realEval w d hw hwd _ _ _ _ u

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

variable [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedTranslationBufferedNiltest_complexity {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) {p : ℝ}
    (hgeometry : (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p)
    (hbound : Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p) :
    (weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD q).ComplexityLE p := by
  refine ⟨hgeometry, ?_⟩
  simpa only [weightedTranslationBufferedNiltest, NNReal.coe_one,
    show (2 : ℝ) + 1 = 3 by norm_num] using hbound

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedTranslationBufferedCentralFrequency
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

 theorem centralRealLine_commute (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    Commute (centralRealLine w d hw hd hwd t) g := by
  apply bchRealTranslationHom_injective w d hwd
  simp only [map_mul, centralRealLine_map]
  apply PolynomialTranslationGroupOver.ext <;> simp [add_comm]

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationBufferedObservable_central
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (t : ℝ)
    (q : (weightedTranslationNilmanifold w d hw hwd).Space) :
    weightedTranslationBufferedObservable w d hw hwd Ψ D₀
      (centralRealLine w d hw hd hwd t • q) =
    weightedTranslationBufferedObservable w d hw hwd Ψ D₀ q *
      (Real.fourierChar t : ℂ) := by
  induction q using Quotient.inductionOn with
  | h g =>
    change weightedTranslationBufferedObservable w d hw hwd Ψ D₀
      (QuotientGroup.mk (centralRealLine w d hw hd hwd t * g)) = _
    rw [(centralRealLine_commute w d hw hd hwd t g).eq]
    simp only [weightedTranslationBufferedObservable_mk, map_mul, centralRealLine_map]
    exact bufferedTranslationPhase_central Ψ D₀ _ t

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationCentralTop
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

 theorem centralRationalElement_mem_top (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) (q : ℚ) :
    centralRationalElement w d hd q ∈ (weightedFiltration w d hwd).layer d := by
  refine ⟨fun i hi => rfl, ?_⟩
  exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledGradedBaseCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [fintypeSigma : Fintype σ]

theorem base_gradeProjection (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (j : ℕ) (x : weightedSubalgebra w d) :
    weightedBaseLinear w d
      (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x) =
      basisGradeProjection (Pi.basisFun ℚ σ) w j (weightedBaseLinear w d x) := by
  funext i
  rw [weightedBaseLinear_apply, weightedBasis_projection_base]
  have h := basisGradeProjection_repr (Pi.basisFun ℚ σ) w j x.val.base i
  simpa only [Pi.basisFun_repr, weightedBaseLinear_apply] using h.symm

theorem basisGradedSubmodule_ambient_base_image (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype)) :
    BasisGradedSubmodule (Pi.basisFun ℚ σ) w (U.map baseLinear) := by
  intro j b hb
  obtain ⟨x, hx, rfl⟩ := hb
  let y : weightedSubalgebra w d := ⟨x, hU hx⟩
  let z := basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j y
  have hz : z.val ∈ U := hgraded j y hx
  refine ⟨z.val, hz, ?_⟩
  exact base_gradeProjection w d hw j y

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem mem_native_refiltration_layer (j : ℕ)
    (x : ℝ ⊗[ℚ] F.gradedRefiltrationSubalgebra W) :
    x ∈ (F.gradedRefiltration W).realification.layer j ↔
      realificationLieHom (F.gradedRefiltrationSubalgebra W).incl x ∈
        F.realGradedRefiltrationLayer W j := by
  change x ∈ ((F.gradedRefiltrationLayer W j).comap
    (F.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  rfl

theorem native_refiltered_orbit_real_value (w : σ → ℕ)
    (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hmap : VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = p) (t : σ → ℝ) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
        (⟨eval₂ t p⟩ : F.realification.Group) := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (F.gradedRefiltrationSubalgebra W).incl (eval₂ t q.log) = eval₂ t p
  rw [← hmap]
  exact (eval₂_map (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl).toLinearMap t q.log).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationResidueNilmanifold
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationResidueNilmanifold_complexity_add_log
    (M : ℕ) (hM : 0 < M) {p : ℝ}
    (hG : (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
      (p + Real.log (M : ℝ)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt hM))
  have hp : p ≤ p + Real.log (M : ℝ) := le_add_of_nonneg_right hlog
  obtain ⟨hdim, hgrid, hstructure, hlayer⟩ := hG
  refine ⟨hdim.trans hp, ?_, fun i j k => (hstructure i j k).trans hp,
    fun i j k => (hlayer i j k).trans hp⟩
  change ((d.factorial * M : ℕ) : ℝ) ≤ Real.exp (p + Real.log (M : ℝ))
  rw [Nat.cast_mul, Real.exp_add, Real.exp_log hMr]
  exact mul_le_mul_of_nonneg_right hgrid hMr.le

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualResidueSpatialFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlated_residue_progression_box {I : Type*} [Fintype I]
    [DecidableEq I] (N : I → ℕ) (q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : ∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) (f : (I → ℕ) → ℂ) :
    ∃ start length : I → ℕ,
      (∀ i, 0 < length i) ∧
      (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
      (∀ i (j : Fin (length i)), start i + q * j.val < N i) ∧
      (∀ i (j : Fin (length i)), (start i + q * j.val) % q = start i % q) ∧
      (∀ i (j : Fin (length i)),
        |((start i + q * j.val : ℕ) : ℝ) / N i - (start i : ℝ) / N i| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ i (j k : Fin (length i)),
        |((start i + q * j.val : ℕ) : ℝ) / N i -
          ((start i + q * k.val : ℕ) : ℝ) / N i| ≤ Real.exp (-(2 * p)) / 4) ∧
      ‖𝔼 x : (∀ i, Fin (N i)), f (fun i => (x i).val)‖ ≤
        ‖𝔼 j : (∀ i, Fin (length i)), f (fun i => start i + q * (j i).val)‖ := by
  classical
  let H : I → ℕ := fun i => exponentialProgressionScale (N i) q p
  have hscale (i : I) := exponentialProgressionScale_bounds (N i) q p hp hq hqexp (hN i)
  let P : ∀ i, FiniteProgressionPartition (N i) := fun i =>
    FiniteProgressionPartition.comparableResidueProgressions (N i) q (H i) hq
      (hscale i).1 (hscale i).2.1
  have hstep (i : I) (a : (P i).Label) : (P i).step a = q :=
    FiniteProgressionPartition.comparableResidueProgressions_step _ _ _ _ _ _ _
  have hlength (i : I) (a : (P i).Label) :
      H i ≤ (P i).length a ∧ (P i).length a < 2 * H i :=
    FiniteProgressionPartition.comparableResidueProgressions_length_bounds _ _ _ _ _ _ _
  have hNpos (i : I) : 0 < N i := by
    have : (0 : ℝ) < N i := (Real.exp_pos _).trans_le (hN i)
    exact_mod_cast this
  obtain ⟨a, hpositive, hmean⟩ :=
    BoxProgressionPartition.exists_positive_box_norm_mean_le P hNpos f
  refine ⟨fun i => (P i).start (a i), fun i => (P i).length (a i), hpositive,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hscale i).2.2.1.trans (by exact_mod_cast (hlength i (a i)).1)
  · intro i j
    simpa only [hstep] using (P i).point_lt (a i) j.isLt
  · intro i j
    exact Nat.add_mul_mod_self_left _ _ _
  · intro i j
    simpa only [FiniteProgressionPartition.point_val, hstep] using
      (P i).normalized_point_sub_start_le_of_bound (a i) (hstep i (a i))
        (hlength i (a i)).2 (hNpos i) (hscale i).2.2.2 j
  · intro i j k
    simpa only [FiniteProgressionPartition.point_val, hstep] using
      (P i).normalized_point_sub_point_le_of_bound (a i) (hstep i (a i))
        (hlength i (a i)).2 (hNpos i) (hscale i).2.2.2 j k
  · simpa only [hstep] using hmean

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlated_integer_residue_box {I : Type*} [Fintype I]
    [DecidableEq I] (N : I → ℕ) (q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : ∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) (f : (I → ℤ) → ℂ) :
    ∃ start length : I → ℕ,
      (∀ i, 0 < length i) ∧
      (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
      (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * q * length i) ∧
      (∀ v ∈ integerBox length,
        (fun i => (start i : ℤ) + (q : ℤ) * v i) ∈ integerBox N) ∧
      (∀ v ∈ integerBox length, ∀ i,
        ((start i : ℤ) + (q : ℤ) * v i) % q = (start i : ℤ) % q) ∧
      (∀ v ∈ integerBox length, ∀ i,
        |((start i : ℝ) + (q : ℝ) * v i) / N i - (start i : ℝ) / N i| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ v ∈ integerBox length, ∀ w ∈ integerBox length, ∀ i,
        |((start i : ℝ) + (q : ℝ) * v i) / N i -
          ((start i : ℝ) + (q : ℝ) * w i) / N i| ≤ Real.exp (-(2 * p)) / 4) ∧
      ‖𝔼 u ∈ integerBox N, f u‖ ≤
        ‖𝔼 v ∈ integerBox length, f (fun i => (start i : ℤ) + (q : ℤ) * v i)‖ := by
  obtain ⟨start, length, hpos, hlength, hinside, _, hdiam, hpair, hmean⟩ :=
    exists_correlated_residue_progression_box N q p hp hq hqexp hN
      (fun u => f (fun i => (u i : ℤ)))
  have hrepr (v : I → ℤ) (hv : v ∈ integerBox length) :
      ∃ j : ∀ i, Fin (length i), ∀ i, ((j i).val : ℤ) = v i := by
    have hb := (mem_integerBox length v).mp hv
    refine ⟨fun i => ⟨(v i).toNat, by have := hb i; omega⟩, ?_⟩
    exact fun i => Int.toNat_of_nonneg (hb i).1
  refine ⟨start, length, hpos, hlength, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hbase : (N i : ℝ) ≤ (length i : ℝ) * Real.exp (3 * p + 16) := by
      apply (div_le_iff₀ (Real.exp_pos _)).mp
      simpa only [Real.exp_neg, div_eq_mul_inv] using hlength i
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    calc
      (N i : ℝ) ≤ Real.exp (3 * p + 16) * length i := by simpa only [mul_comm] using hbase
      _ ≤ Real.exp (3 * p + 16) * q * length i := by
        gcongr
        exact le_mul_of_one_le_right (Real.exp_pos _).le hqone
  · intro v hv
    obtain ⟨j, hj⟩ := hrepr v hv
    rw [mem_integerBox]
    intro i
    rw [← hj i]
    constructor
    · positivity
    · exact_mod_cast hinside i (j i)
  · intro v _ i
    exact Int.add_mul_emod_self_left _ _ _
  · intro v hv i
    obtain ⟨j, hj⟩ := hrepr v hv
    have hjR : ((j i).val : ℝ) = v i := by exact_mod_cast hj i
    simpa only [Nat.cast_add, Nat.cast_mul, hjR] using hdiam i (j i)
  · intro v hv w hw i
    obtain ⟨j, hj⟩ := hrepr v hv
    obtain ⟨k, hk⟩ := hrepr w hw
    have hjR : ((j i).val : ℝ) = v i := by exact_mod_cast hj i
    have hkR : ((k i).val : ℝ) = w i := by exact_mod_cast hk i
    simpa only [Nat.cast_add, Nat.cast_mul, hjR, hkR] using hpair i (j i) (k i)
  · rw [integerBox_expect_eq_fin, integerBox_expect_eq_fin]
    simpa only [Nat.cast_add, Nat.cast_mul] using hmean

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LowTaggedCoordinateRestriction
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTagged_comap_eq_map (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) K) :
    K.comap (lowTaggedEmbedding J d j hj) = K.map (lowTaggedRestriction J d j hj) := by
  apply le_antisymm
  · intro v hv
    exact ⟨lowTaggedEmbedding J d j hj v, hv,
      lowTaggedRestriction_embedding J d j hj v⟩
  · rintro v ⟨z, hz, rfl⟩
    change lowTaggedEmbedding J d j hj (lowTaggedRestriction J d j hj z) ∈ K
    rw [lowTaggedEmbedding_restriction]
    exact hK (j.val + 1) z hz

theorem lowTagged_comap_span_eq {A : Type*} (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d)
    (g : A → Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (hg : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d)
      (Submodule.span ℝ (Set.range g))) :
    (Submodule.span ℝ (Set.range g)).comap (lowTaggedEmbedding J d j hj) =
      Submodule.span ℝ (Set.range (fun a k => g a (lowTaggedSlot J d j hj k))) := by
  rw [lowTagged_comap_eq_map J d j hj _ hg, Submodule.map_span, ← Set.range_comp]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MajorTranslationBaseCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

theorem bchRealTranslationHom_base_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group) (i : B) :
    (bchRealTranslationHom w d hwd g).base i =
      ((weightedBasis w d hw).baseChange ℝ).repr g.coord (Sum.inl i) := by
  obtain ⟨b, P, hb, _⟩ := realShearEmbedding_shape w d g.coord
  have hact := congrArg (fun f : MvPolynomial (B ⊕ Unit) ℝ ≃ₐ[ℝ]
      MvPolynomial (B ⊕ Unit) ℝ => f (X (Sum.inl i)))
    (bchRealTranslationHom_action w d hwd g)
  change PolynomialTranslationGroupOver.actionHom (bchRealTranslationHom w d hwd g)
    (X (Sum.inl i)) = polynomialShearExp (realShearEmbedding w d g.coord)
      (X (Sum.inl i)) at hact
  rw [PolynomialTranslationGroupOver.actionHom_X_inl,
    polynomialShearExp_X_of_derivation_eq_C _ _ _ (hb i)] at hact
  have hbase : (bchRealTranslationHom w d hwd g).base i = b i := by
    simpa using congrArg (fun polynomial : MvPolynomial (B ⊕ Unit) ℝ => polynomial.coeff 0) hact
  have hcoord := realShearEmbedding_base_coeff w d hw g.coord i
  rw [hb i] at hcoord
  exact hbase.trans (by simpa using hcoord)

theorem majorTranslationPolynomialOrbit_base_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) (i : B) :
    VectorPolynomial.coordinate
      (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)).toAddMonoidHom
      (majorTranslationPolynomialOrbit w d hw hwd D hD A hA).log = A i := by
  apply MvPolynomial.funext
  intro u
  rw [← VectorPolynomial.coordinate_eval₂]
  change ((weightedBasis w d hw).baseChange ℝ).repr
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)).coord
        (Sum.inl i) = eval u (A i)
  rw [← bchRealTranslationHom_base_coordinate w d hw hwd,
    majorTranslationPolynomialOrbit_realEval]
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationLogCoordinateWeightedDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*}

namespace PolynomialTranslationLie

variable [Fintype B] (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]

theorem translationLogBasePolynomial_weightedBasis
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ) (i : B) :
    translationLogBasePolynomial w d (weightedBasis w d hw) f i = f (Sum.inl i) := by
  classical
  unfold translationLogBasePolynomial
  rw [Finset.sum_eq_single (Sum.inl i)]
  · simp
  · intro k _ hki
    cases k with
    | inl j =>
      have hji : j ≠ i := fun h => hki (congrArg Sum.inl h)
      simp [Ne.symm hji]
    | inr α => simp
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationLogCoordinateHomogeneous
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

theorem translationLogBasePolynomial_weightedBasis_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous v (weightedBasisGrade w d k)) (i : B) :
    (translationLogBasePolynomial w d (weightedBasis w d hw) f i).IsWeightedHomogeneous
      v (w i) := by
  rw [translationLogBasePolynomial_weightedBasis]
  exact hf (Sum.inl i)

theorem pack_translationLogPhasePolynomial_weightedBasis_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous v (weightedBasisGrade w d k)) :
    (packTranslationPolynomial (translationLogPhasePolynomial w d (weightedBasis w d hw) f)).IsWeightedHomogeneous
      (Sum.elim v w) d := by
  classical
  rw [pack_translationLogPhasePolynomial]
  apply (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).sum_mem
  intro k _
  cases k with
  | inl i =>
    simp only [weightedBasis_inl_polynomial, map_zero, mul_zero]
    exact isWeightedHomogeneous_zero ℝ _ _
  | inr a =>
    simp only [weightedBasis_inr_polynomial, map_monomial, map_one]
    have hleft : (rename Sum.inl (f (Sum.inr a))).IsWeightedHomogeneous (Sum.elim v w)
        (d - Finsupp.weight w a.val) := by
      rw [rename_eq_aeval]
      exact aeval_isWeightedHomogeneous v (Sum.elim v w) _
        (fun i => isWeightedHomogeneous_X ℝ (Sum.elim v w) (Sum.inl i)) (hf (Sum.inr a))
    have hright : (rename Sum.inr (monomial a.val (1 : ℝ))).IsWeightedHomogeneous
        (Sum.elim v w) (Finsupp.weight w a.val) := by
      rw [rename_eq_aeval]
      exact aeval_isWeightedHomogeneous w (Sum.elim v w) _
        (fun i => isWeightedHomogeneous_X ℝ (Sum.elim v w) (Sum.inr i))
        (isWeightedHomogeneous_monomial w a.val 1 rfl)
    simpa only [mem_weightedHomogeneousSubmodule, Nat.sub_add_cancel a.property.le]
      using hleft.mul hright

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MajorTranslationIntegerEvaluation
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {U B : Type*} [Fintype B]

theorem majorTranslationPolynomialOrbit_integerEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (x : U → ℤ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitEval
        (fun _ : U => 1) x (majorTranslationPolynomialOrbit w d hw hwd F hF A hA)) =
      algebraicMajorSymbol F (specializeMajorParameters (RingHom.id ℝ) F 0) A
        (fun i => (x i : ℝ)) := by
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
  exact majorTranslationPolynomialOrbit_realEval w d hw hwd F hF A hA _

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationAssociatedGradedProjection
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module _root_.MvPolynomial

variable {σ L ι : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
    (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem weightedTranslationGradedProjection_basis_base (i : ι) (a : σ) :
    (weightedTranslationGradedProjection F w d hw hwd φ hφ
      (F.associatedGradedBasis b ω hF i)).val.base a =
      if ω i = w a then (φ (b i)).val.base a else 0 := by
  simpa only [weightedTranslationGradedProjection, weightedBasis_repr_inl, weightedBasisGrade_inl] using
    F.homogeneousGradedProjection_basis_repr (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF i (Sum.inl a)

theorem weightedTranslationGradedProjection_image_graded
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule) :
    BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule :=
  F.homogeneousGradedProjection_image_graded (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF W hW

end Erdos3.PolynomialTranslationLie

end

end OAI
end


