-- Prove2me | Definitions.Def_OAIE3v2B189
-- name    : OAIE3v2B189
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:06:14.533017+00:00
-- url     : https://prove2.me/theorems/92e348e2-0125-4535-ae5a-2d2c534b0777
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 192 of 311
-- statement:
--   Definitions bundle 192 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B167`, `OAIE3v2B169`, `OAIE3v2B170`, `OAIE3v2B172` of this split.
--
--   Modules: `Dynamics/RestrictedSymbolGradeIteration.lean`, `Estimates/ControlledDetectedTranslationBaseBounds.lean`, `Estimates/ControlledPrescribedMarkedNativeFactorization.lean`, `Estimates/HomogeneousQuotientSymbolLiftBounds.lean`, `Estimates/LowTaggedGradedSpace.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/RealSymbolGradeQuotientSplitting.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Estimates/UnitProductOrbitFamily.lean`, `Fourier/NormalizedTwistLocalizedFourierSelection.lean`, `Geometry/GlobalChartNativeFactorization.lean`, `Geometry/NormalizedTwistSpatialPartition.lean`, `Geometry/RestrictedChartPrefixControl.lean`, `Lattices/AffineRefinedCoefficients.lean`, `Lattices/CommonLocalAffineFamily.lean`, `Lattices/IntegerHomogeneousSymbolPullbackGrid.lean`, `Lattices/SharedFreeAffineOrbitFamily.lean`, `Linear/RealFourAnnihilatorKernel.lean`, `Linear/SharedFreeCommonProjection.lean`, `Linear/SpatialFrameSlopeBudget.lean`, `Polynomial/HomogeneousRealSymbolPolynomial.lean`, `Polynomial/OrdinaryPhasePairFunctionalBounds.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Polynomial/PolynomialTagRestrictionBudget.lean`, `Probability/AllocatedMixedLiftNormalizedMass.lean`, `Sampling/AllocatedExternalCandidateSamplerFamily.lean`, `Sampling/LowTaggedSamplingRank.lean`, `Sampling/ScalarSymbolFamilyCoefficientGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B167
import Definitions.Def_OAIE3v2B169
import Definitions.Def_OAIE3v2B170
import Definitions.Def_OAIE3v2B172

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

 theorem real_symbolPointwiseSubalgebra_map_mem
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x ∈
      realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c ν hG w (U.map (F.associatedGradedMap G φ hφ))) := by
  have hmap : realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x ∈
      realificationLieSubalgebra ((F.symbolPointwiseSubalgebra b ω hF w U).map
        (F.filteredPolynomialSymbolMap G φ hφ w)) := by
    rw [realificationLieSubalgebra_map]
    exact ⟨x, hx, rfl⟩
  exact Submodule.baseChange_mono ℝ
    (F.symbolPointwiseSubalgebra_map_le G b ω hF c ν hG φ hφ w U) hmap

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

theorem projected_realSymbolRepresentative_mem_homogeneous_image
    (W : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (u : σ → ℝ) :
    eval₂ u (G.realSymbolRepresentative c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) ∈
      realificationLieSubalgebra (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)) := by
  have hmap := F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ w W x hx
  have hvalue := (G.mem_real_symbolPointwiseSubalgebra_iff_values c ν hG w
    (W.map (F.associatedGradedMap G φ hφ))
    (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)).mp hmap u
  rw [G.realSymbolRepresentative_eval₂,
    ← F.homogeneousGradedProjection_image_eq G c ν hG hc φ hφ W,
    realificationLieSubalgebra_map]
  exact ⟨_, hvalue, rfl⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L Q : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousQuotientGradedPolynomial_coefficient (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (α : σ →₀ ℕ) :
    coefficients (F.homogeneousQuotientGradedPolynomial b ω hF k S p) α =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
        (S (coefficients p α)) := by
  rw [homogeneousQuotientGradedPolynomial, coefficients_map]
  rfl

theorem homogeneousQuotientGradedPolynomial_eval (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (t : σ → ℝ) :
    eval₂ t (F.homogeneousQuotientGradedPolynomial b ω hF k S p) =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
        (S (eval₂ t p)) := by
  exact eval₂_map _ t p

theorem homogeneousQuotientGradedPolynomial_graded (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (hhom : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) :
    F.homogeneousQuotientGradedPolynomial b ω hF k S p ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w := by
  apply homogeneous_mem_gradedPolynomialSubmodule _ _ _ k
  · intro α hα
    rw [F.homogeneousQuotientGradedPolynomial_coefficient, hhom α hα, map_zero, map_zero]
  · intro α
    rw [F.homogeneousQuotientGradedPolynomial_coefficient]
    exact basisCoordinateProjection_idempotent _ _ _

theorem homogeneousQuotientSymbolLift_coordinate (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) z =
      if ω z.val.2 = k then
        ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
          (S (coefficients p z.val.1)) z.val.2 else 0 := by
  rw [homogeneousQuotientSymbolLift, F.realSymbolOfGradedPolynomial_coordinate,
    F.homogeneousQuotientGradedPolynomial_coefficient, basisGradeProjection_repr]

theorem realGradedSymbolPolynomial_homogeneousQuotientSymbolLift (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (hhom : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) :
    F.realGradedSymbolPolynomial b ω hF w
        (F.homogeneousQuotientSymbolLift b ω hF w k S p) =
      F.homogeneousQuotientGradedPolynomial b ω hF k S p := by
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF w _
    (F.homogeneousQuotientGradedPolynomial_graded b ω hF w k S p hhom)

theorem homogeneousQuotientSymbolLift_eval (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (hhom : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) (t : σ → ℝ) :
    eval₂ t (F.realGradedSymbolPolynomial b ω hF w
      (F.homogeneousQuotientSymbolLift b ω hF w k S p)) =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
        (S (eval₂ t p)) := by
  rw [F.realGradedSymbolPolynomial_homogeneousQuotientSymbolLift b ω hF w k S p hhom]
  exact F.homogeneousQuotientGradedPolynomial_eval b ω hF k S p t

theorem homogeneousQuotientSymbolLift_pure (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q) :
    basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
      (fun z => ω z.val.2) k (F.homogeneousQuotientSymbolLift b ω hF w k S p) =
      F.homogeneousQuotientSymbolLift b ω hF w k S p := by
  apply ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr.injective
  ext z
  rw [basisGradeProjection_repr, F.homogeneousQuotientSymbolLift_coordinate]
  split_ifs <;> rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realGradedSymbolPolynomial_slow_coordinates (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) (i : ι) :
    |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i| ≤
      M / monomialScale T α := by
  by_cases h : Finsupp.weight w α = ω i
  · have hc := F.realGradedSymbolPolynomial_coordinate b ω hF w g.coord ⟨(α, i), h⟩
    exact (congrArg abs hc).le.trans (hg ⟨(α, i), h⟩)
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord α i h, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem scalarSymbolPolynomial_slow_coefficients [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hθ : ∀ i, |(θ (F.associatedGradedBasis b ω hF i) : ℝ)| ≤ H)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) :
    |(F.scalarSymbolPolynomial b ω hF w θ g).coeff α| ≤
      (Fintype.card ι : ℝ) * H * M / monomialScale T α := by
  classical
  rw [F.coeff_scalarSymbolPolynomial, realifyFunctional_eq_sum_basis (F.associatedGradedBasis b ω hF)]
  calc
    _ ≤ ∑ i, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i *
          (θ (F.associatedGradedBasis b ω hF i) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (M / monomialScale T α) * H := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hθ i) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right
          (F.realGradedSymbolPolynomial_slow_coordinates b ω hF w T hT hM g hg α i) hH)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem realGradedSymbolPolynomial_rational_coordinates [Fintype ι] (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g)
    (α : σ →₀ ℕ) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).equivFun
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α)
        ∈ realDenominatorGrid m := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun i => if h : Finsupp.weight w α = ω i then a ⟨(α, i), h⟩ else 0, ?_⟩
  funext i
  change ((if h : Finsupp.weight w α = ω i then a ⟨(α, i), h⟩ else 0 : ℤ) : ℝ) =
    (m : ℝ) * ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i
  by_cases h : Finsupp.weight w α = ω i
  · rw [dif_pos h, F.realGradedSymbolPolynomial_coordinate b ω hF w g.coord ⟨(α, i), h⟩]
    exact congrFun ha ⟨(α, i), h⟩
  · rw [dif_neg h, Int.cast_zero,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord α i h, mul_zero]

theorem scalarSymbolPolynomial_rational_coefficients [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun (_ : Unit) i => θ (F.associatedGradedBasis b ω hF i)) * m)
      (F.scalarSymbolPolynomial b ω hF w θ g) := by
  classical
  have h : ∀ α, ∃ z : ℤ,
      ((matrixDenominator (fun (_ : Unit) i => θ (F.associatedGradedBasis b ω hF i)) * m : ℕ) : ℝ) *
        (F.scalarSymbolPolynomial b ω hF w θ g).coeff α = (z : ℝ) := by
    intro α
    rw [F.coeff_scalarSymbolPolynomial]
    exact realifyFunctional_denominator_grid (F.associatedGradedBasis b ω hF) θ m _
      (F.realGradedSymbolPolynomial_rational_coordinates b ω hF w m g hg α)
  choose z hz using h
  exact ⟨z, funext (fun α => (hz α).symm)⟩

theorem scalarSymbolPolynomial_slow_coefficients_of_height [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) {H : ℕ}
    (hθ : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) :
    |(F.scalarSymbolPolynomial b ω hF w θ g).coeff α| ≤
      (Fintype.card ι : ℝ) * H * M / monomialScale T α :=
  F.scalarSymbolPolynomial_slow_coefficients b ω hF w θ T hT hM (Nat.cast_nonneg H)
    (fun i => (hθ i).abs_real_le) g hg α

theorem scalarSymbolPolynomial_exists_coefficient_grid [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) {H : ℕ}
    (hθ : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (m : ℕ) (hm : 0 < m) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolRationalGrid b ω hF w m g) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ Fintype.card ι * m ∧
      realPolynomialCoefficientGrid q (F.scalarSymbolPolynomial b ω hF w θ g) := by
  refine ⟨_, Nat.mul_pos (scalarFunctionalDenominator_pos (F.associatedGradedBasis b ω hF) θ) hm,
    Nat.mul_le_mul_right m (scalarFunctionalDenominator_le (F.associatedGradedBasis b ω hF) θ hθ), ?_⟩
  exact F.scalarSymbolPolynomial_rational_coefficients b ω hF w θ m g hg

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem scalarSymbolPolynomial_mul (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (hθ : ∀ x y : F.AssociatedGraded, θ ⁅x, y⁆ = 0) (hs : 1 ≤ s)
    (x y : F.RealPolynomialSymbolGroup w) :
    F.scalarSymbolPolynomial b ω hF w θ (x * y) =
      F.scalarSymbolPolynomial b ω hF w θ x + F.scalarSymbolPolynomial b ω hF w θ y := by
  apply MvPolynomial.funext
  intro u
  simp only [scalarSymbolPolynomial, MvPolynomial.eval_add, ← coordinate_eval₂,
    NilpotentLieBCHGroup.coord_mul, map_lieBCH]
  have he := map_lieBCH (eval₂Lie (R := ℚ) (S := ℝ) u) s
    (F.realGradedSymbolPolynomial b ω hF w x.coord)
    (F.realGradedSymbolPolynomial b ω hF w y.coord)
  rw [eval₂Lie_apply] at he
  rw [he]
  exact realifyFunctional_lieBCH θ hθ hs _ _

theorem scalarSymbolPolynomial_eq_zero_of_fast
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hθ : ∀ x ∈ W, θ x = 0) (P : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    F.scalarSymbolPolynomial b ω hF w θ P = 0 := by
  have hle : W.toSubmodule ≤ LinearMap.ker θ := hθ
  ext α
  rw [F.coeff_scalarSymbolPolynomial, MvPolynomial.coeff_zero]
  apply (mem_realified_frequency_kernel_iff θ _).mp
  apply Submodule.baseChange_mono ℝ hle
  exact (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w W P.coord).mp hP α

theorem scalarSymbolPolynomial_approximation_of_factorization [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (hθlie : ∀ x y : F.AssociatedGraded, θ ⁅x, y⁆ = 0) (hs : 1 ≤ s)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (R M : ℝ) (hM : 0 ≤ M)
    {H m : ℕ} (hm : 0 < m)
    (hθH : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (hden : ((H ^ Fintype.card ι * m : ℕ) : ℝ) ≤ R)
    (hslow : (Fintype.card ι : ℝ) * H * M ≤ R)
    (E P Q X : F.RealPolynomialSymbolGroup w) (hprod : E * P * Q = X)
    (hE : F.SymbolSlowBound b ω hF w T M E)
    (hQ : F.SymbolRationalGrid b ω hF w m Q)
    (W : LieSubalgebra ℚ F.AssociatedGraded) (hθW : ∀ x ∈ W, θ x = 0)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    PolynomialRationalApproximation T R (F.scalarSymbolPolynomial b ω hF w θ X) := by
  have hsplit : F.scalarSymbolPolynomial b ω hF w θ X =
      F.scalarSymbolPolynomial b ω hF w θ E + F.scalarSymbolPolynomial b ω hF w θ Q := by
    rw [← hprod, F.scalarSymbolPolynomial_mul b ω hF w θ hθlie hs,
      F.scalarSymbolPolynomial_mul b ω hF w θ hθlie hs,
      F.scalarSymbolPolynomial_eq_zero_of_fast b ω hF w θ W hθW P hP, add_zero]
  obtain ⟨q, hq, hqbound, hgrid⟩ :=
    F.scalarSymbolPolynomial_exists_coefficient_grid b ω hF w θ hθH m hm Q hQ
  obtain ⟨Z, hZ⟩ := (realPolynomialCoefficientGrid_iff q _).mp hgrid
  refine ⟨q, hq, (Nat.cast_le.mpr hqbound).trans hden, Z, ?_⟩
  intro α
  have hz := congrArg (fun polynomial => polynomial.coeff α) hZ
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hz
  change ((Z.coeff α : ℤ) : ℝ) = (q : ℝ) * (F.scalarSymbolPolynomial b ω hF w θ Q).coeff α at hz
  rw [hsplit, MvPolynomial.coeff_add, hz,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hq.ne'), add_sub_cancel_right]
  exact (F.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF w θ T hT hM
    hθH E hE α).trans (div_le_div_of_nonneg_right hslow (monomialScale_pos T hT α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolGradeEvaluation_quotientLift
    {Q : Type*} [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
    (k : ℕ) (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded))
    (p : VectorPolynomial σ ℚ Q)
    (hp : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) (t : σ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF w k t
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) =
        basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
          (S (eval₂ t p)) := by
  rw [F.realSymbolGradeEvaluation_apply, F.homogeneousQuotientSymbolLift_pure]
  exact F.homogeneousQuotientSymbolLift_eval b ω hF w k S p hp t

theorem restricted_symbol_grade_terminal
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realGradedSymbolPolynomial b ω hF w x) ∈ U.baseChange ℝ ↔
      ∀ j ≤ s, F.realSymbolGradeEvaluation b ω hF w j t x ∈ U.baseChange ℝ := by
  constructor
  · intro hx j _
    rw [F.realSymbolGradeEvaluation_eq_projection]
    exact hU.baseChange (F.associatedGradedBasis b ω hF) ω U j _ hx
  · intro hx
    let y := eval₂ t (F.realGradedSymbolPolynomial b ω hF w x)
    have hfull : basisBelowProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ)
        ω (s + 1) y = y := by
      apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
      ext i
      rw [basisBelowProjection_repr, if_pos (Nat.lt_succ_of_le
        (F.adaptedBasis_weight_le_step b ω hF i))]
    change y ∈ U.baseChange ℝ
    rw [← hfull, basisBelowProjection_eq_sum_grades]
    apply Submodule.sum_mem
    intro j hj
    have h := hx j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    rwa [F.realSymbolGradeEvaluation_eq_projection] at h

theorem restricted_symbol_grade_matching
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
    (hS : ∀ y, U.mkQ (S y) = y)
    (k : ℕ) (Z E R : F.RealPolynomialSymbolGroup w)
    (K₀ K : Set (σ → ℝ)) (hK : K ⊆ K₀)
    (pS pR : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (hpS : ∀ α, Finsupp.weight w α ≠ k → coefficients pS α = 0)
    (hpR : ∀ α, Finsupp.weight w α ≠ k → coefficients pR α = 0)
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈ U.baseChange ℝ)
    (hquot : ∀ t ∈ K,
      U.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF w k t (E⁻¹ * Z * R⁻¹).coord) =
          eval₂ t pS + eval₂ t pR) :
    ∃ A D : F.RealPolynomialSymbolGroup w,
      A.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pS ∧
      D.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pR ∧
      A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      (E * A) * ((E * A)⁻¹ * Z * (D * R)⁻¹) * (D * R) = Z ∧
      (∀ t, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord =
          F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord) ∧
      ∀ t ∈ K, ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord ∈
          U.baseChange ℝ := by
  let A : F.RealPolynomialSymbolGroup w :=
    ⟨F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pS⟩
  let D : F.RealPolynomialSymbolGroup w :=
    ⟨F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pR⟩
  have hlift (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
      F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) p ∈
        (F.polynomialSymbolFiltration w).realification.layer k := by
    rw [← F.homogeneousQuotientSymbolLift_pure b ω hF w k (S.baseChange ℝ) p]
    exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer
      (F.polynomialSymbolBasis b ω hF w) (fun z => ω z.val.2)
      (F.polynomialSymbolFiltration_layer b ω hF w) k _
  have hA : A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k := hlift pS
  have hD : D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k := hlift pR
  have hmiddle : (E * A)⁻¹ * Z * (D * R)⁻¹ = A⁻¹ * (E⁻¹ * Z * R⁻¹) * D⁻¹ := by group
  have hbelow (t : σ → ℝ) (j : ℕ) (hj : j < k) :
      F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord =
        F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord := by
    rw [hmiddle]
    exact F.realSymbolGradeEvaluation_correction_below b ω hF w k t A
      (E⁻¹ * Z * R⁻¹) D hA hD j hj
  refine ⟨A, D, rfl, rfl, hA, hD, by group, hbelow, ?_⟩
  intro t ht j hj
  rcases lt_or_eq_of_le hj with hlt | heq
  · rw [hbelow t j hlt]
    exact hlower t (hK ht) j hlt
  · subst j
    rw [hmiddle, F.realSymbolGradeEvaluation_current_correction b ω hF w k t A
      (E⁻¹ * Z * R⁻¹) D hA hD]
    have hevalA : F.realSymbolGradeEvaluation b ω hF w k t A.coord =
        basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
          (S.baseChange ℝ (eval₂ t pS)) := by
      dsimp only [A]
      apply F.realSymbolGradeEvaluation_quotientLift
      exact hpS
    have hevalD : F.realSymbolGradeEvaluation b ω hF w k t D.coord =
        basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
          (S.baseChange ℝ (eval₂ t pR)) := by
      dsimp only [D]
      apply F.realSymbolGradeEvaluation_quotientLift
      exact hpR
    rw [hevalA, hevalD]
    exact real_graded_quotient_section_residual (F.associatedGradedBasis b ω hF) ω U hU S hS k
      _ (eval₂ t pS) (eval₂ t pR)
      (F.realSymbolGradeEvaluation_homogeneous b ω hF w k t _) (hquot t ht)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolGradeQuotientPolynomial_eval
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ)
    (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) =
      U.mkQ.baseChange ℝ (F.realSymbolGradeEvaluation b ω hF w k t x) := by
  exact eval₂_map _ t _

theorem realSymbolGradeQuotientPolynomial_homogeneous
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ)
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≠ k) :
    coefficients (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) α = 0 := by
  rw [realSymbolGradeQuotientPolynomial, coefficients_map,
    F.realGradedSymbolPolynomial_gradeProjection_homogeneous b ω hF w k x α hα, map_zero]

theorem restricted_symbol_major_grade_step
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
    (hS : ∀ y, U.mkQ (S y) = y)
    (k : ℕ) (Z E R : F.RealPolynomialSymbolGroup w)
    (K₀ K : Set (σ → ℝ)) (hK : K ⊆ K₀)
    (hdilate : ∀ t ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * t i) ∈ K)
    (pS pR : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈ U.baseChange ℝ)
    (hquot : ∀ t ∈ K,
      U.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF w k t (E⁻¹ * Z * R⁻¹).coord) =
          eval₂ t pS + eval₂ t pR) :
    ∃ A D : F.RealPolynomialSymbolGroup w,
      A.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
        (weightedHomogeneousPart w k pS) ∧
      D.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
        (weightedHomogeneousPart w k pR) ∧
      A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      (E * A) * ((E * A)⁻¹ * Z * (D * R)⁻¹) * (D * R) = Z ∧
      (∀ t, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord =
          F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord) ∧
      ∀ t ∈ K, ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord ∈
          U.baseChange ℝ := by
  apply F.restricted_symbol_grade_matching b ω hF w U hU S hS k Z E R K₀ K hK
    (weightedHomogeneousPart w k pS) (weightedHomogeneousPart w k pR)
    (weightedHomogeneousPart_homogeneous w k pS)
    (weightedHomogeneousPart_homogeneous w k pR) hlower
  intro t ht
  let p := F.realSymbolGradeQuotientPolynomial b ω hF w U k (E⁻¹ * Z * R⁻¹).coord
  have hp : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0 :=
    F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF w U k _
  have heq : ∀ x ∈ K, eval₂ x p = eval₂ x pS + eval₂ x pR := by
    intro x hx
    rw [realSymbolGradeQuotientPolynomial_eval]
    exact hquot x hx
  have h := eval₂_weightedHomogeneousPart_decomposition_on w p pS pR K hdilate k hp heq t ht
  rw [F.realSymbolGradeQuotientPolynomial_eval] at h
  exact h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RestrictedSymbolGradeIteration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)
  (U : Submodule ℚ F.AssociatedGraded)
  (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

theorem realSymbolGradeEvaluation_zero (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF w 0 t x = 0 := by
  have hz : basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
      (fun z => ω z.val.2) 0 x = 0 := by
    apply ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr.injective
    ext z
    rw [basisGradeProjection_repr, if_neg
      (Nat.ne_of_gt (F.adaptedBasis_weight_pos b ω hF z.val.2)), map_zero, Finsupp.zero_apply]
  rw [F.realSymbolGradeEvaluation_apply, hz, map_zero, map_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitProductOrbitFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct BigOperators

theorem piRealOrbit_normalized {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}
    (g : ∀ i, (F i).realification.PolynomialOrbit w)
    (hg : ∀ i, (F i).realification.polynomialOrbitEval w 0 (g i) = 1) :
    (pi F).realification.polynomialOrbitEval w 0 (piRealOrbit F g) = 1 := by
  classical
  apply (realBCHPiEquiv F).injective
  funext i
  change NilpotentLieBCHGroup.realificationMap
    (hnil := (pi F).lowerCentralSeries_eq_bot) (hM := (F i).lowerCentralSeries_eq_bot)
    (liePiEval i) ((pi F).realification.polynomialOrbitEval w 0 (piRealOrbit F g)) = _
  rw [piRealOrbit_eval, hg]
  simp only [map_one, Pi.one_apply]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι σ τ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  {I : ι → Type*} [∀ i, Fintype (I i)] {w : σ → ℕ}
  (K : ∀ i, I i → (D i).Niltest w)

omit [Nonempty ι] [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productObservable_unit
    (hunit : ∀ i x, ∑ j, ‖(K i j).observable x‖ ^ 2 = 1) (x : (pi D).Space) :
    ∑ j : ∀ i, I i, ‖productObservable D (fun i => K i (j i)) x‖ ^ 2 = 1 := by
  classical
  simp only [productObservable, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ i, ∑ j, ‖(K i j).observable (productProjection D i x)‖ ^ 2 :=
      (Fintype.prod_sum (fun i j => ‖(K i j).observable (productProjection D i x)‖ ^ 2)).symm
    _ = ∏ _i : ι, (1 : ℝ) := Finset.prod_congr rfl (fun i _ => hunit i (productProjection D i x))
    _ = 1 := by simp only [Finset.prod_const_one]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFourAnnihilatorKernel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem mem_real_petal_annihilator_iff
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype J]
    (D : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (hker : LinearMap.ker ℓ = K)
    (v : ℝ ⊗[ℚ] V) :
    v ∈ (fourPetalSpace D K).baseChange ℝ ↔
      v ∈ D.baseChange ℝ ∧ ∀ j, realifyFunctional
        (((LinearMap.proj j).comp ℓ).comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) v = 0 := by
  rw [fourPetalSpace_eq_inf_ker D K ℓ hker, realification_inf, Submodule.mem_inf,
    mem_realified_coordinate_kernel_iff]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ScalarSymbolFamilyCoefficientGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι J L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
  (w : σ → ℕ)

theorem scalarSymbolPolynomial_family_rational_coefficients [Fintype ι] [Fintype J]
    (θ : J → F.AssociatedGraded →ₗ[ℚ] ℚ) (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g)
    (j : J) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun j i => θ j (F.associatedGradedBasis b ω hF i)) * m)
      (F.scalarSymbolPolynomial b ω hF w (θ j) g) := by
  classical
  let ℓ : F.AssociatedGraded →ₗ[ℚ] (J → ℚ) := LinearMap.pi θ
  have h : ∀ α : σ →₀ ℕ, ∃ z : J → ℤ,
      (fun j => (z j : ℝ)) =
        ((matrixDenominator (fun j i => θ j (F.associatedGradedBasis b ω hF i)) * m : ℕ) : ℝ) •
          realifyCoordinateMap ℓ
            (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) := by
    intro α
    exact realifyCoordinateMap_grid (F.associatedGradedBasis b ω hF) ℓ m _
      (F.realGradedSymbolPolynomial_rational_coordinates b ω hF w m g hg α)
  choose z hz using h
  refine ⟨fun α => z α j, funext fun α => ?_⟩
  change (z α j : ℝ) =
    ((matrixDenominator (fun j i => θ j (F.associatedGradedBasis b ω hF i)) * m : ℕ) : ℝ) *
      (F.scalarSymbolPolynomial b ω hF w (θ j) g).coeff α
  rw [F.coeff_scalarSymbolPolynomial]
  have hθ : (LinearMap.proj j).comp ℓ = θ j := by ext; rfl
  have hα := congrFun (hz α) j
  change (z α j : ℝ) = _ * realifyFunctional ((LinearMap.proj j).comp ℓ) _ at hα
  rwa [hθ] at hα

theorem scalarSymbolPolynomial_family_exists_coefficient_grid [Fintype ι] [Fintype J]
    (θ : J → F.AssociatedGraded →ₗ[ℚ] ℚ) {H : ℕ}
    (hθ : ∀ j i, RationalHeightLE (θ j (F.associatedGradedBasis b ω hF i)) H)
    (m : ℕ) (hm : 0 < m) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolRationalGrid b ω hF w m g) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ (Fintype.card J * Fintype.card ι) * m ∧
      ∀ j, realPolynomialCoefficientGrid q (F.scalarSymbolPolynomial b ω hF w (θ j) g) := by
  refine ⟨_, Nat.mul_pos (matrixDenominator_pos _) hm,
    Nat.mul_le_mul_right m (matrixDenominator_le _ hθ), ?_⟩
  exact F.scalarSymbolPolynomial_family_rational_coefficients b ω hF w θ m g hg

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledDetectedTranslationBaseBounds
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module VectorPolynomial _root_.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {U B L ι : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

omit [Fintype (WeightedBasisIndex w d)] in
theorem realifyTranslationBaseFunctional_eq_coord (i : B) :
    realifyFunctional ((LinearMap.proj i).comp
      (baseLinear.comp (weightedSubalgebra w d).subtype)) =
      ((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [realifyFunctional_tmul]
    change a * (x.val.base i : ℝ) =
      ((weightedBasis w d hw).baseChange ℝ).repr (a ⊗ₜ[ℚ] x) (Sum.inl i)
    rw [Basis.baseChange_repr_tmul, weightedBasis_repr_inl]
    simp only [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct NNReal

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)
  [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w ν)]

noncomputable def filteredSymbolMapDenominator : ℕ :=
  matrixDenominator (fun i j => (G.polynomialSymbolBasis c ν hG w).repr
    (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis b ω hF w j)) i)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RestrictedChartPrefixControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

theorem substitute_weightedHomogeneousPart
    {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (w : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ R V) :
    substitute f (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart v d (substitute f p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul P x =>
    rw [weightedHomogeneousPart_tmul, substitute_tmul, substitute_tmul,
      weightedHomogeneousPart_tmul, aeval_weightedHomogeneousComponent w v f hf]
  | add p q hp hq => simp only [map_add, hp, hq]

variable {σ τ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem realCoefficientEquiv_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ ℚ V) :
    realCoefficientEquiv (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart w d (realCoefficientEquiv p) := by
  apply coefficients.injective
  ext α
  simp only [coefficients_realCoefficientEquiv, coefficients_weightedHomogeneousPart]

theorem realCoefficientEquiv_symm_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ ℝ V) :
    realCoefficientEquiv.symm (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart w d (realCoefficientEquiv.symm p) := by
  apply coefficients.injective
  ext α
  simp only [coefficients_realCoefficientEquiv_symm, coefficients_weightedHomogeneousPart]

theorem realChartSubstitute_weightedHomogeneousPart (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute f (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart v d (realChartSubstitute f p) := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, realCoefficientEquiv_weightedHomogeneousPart,
    substitute_weightedHomogeneousPart w v f hf,
    realCoefficientEquiv_symm_weightedHomogeneousPart]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerHomogeneousSymbolPullbackGrid
namespace OAI

section

namespace Erdos3
open Module _root_.MvPolynomial
open scoped TensorProduct

namespace VectorPolynomial

variable {σ τ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem coordinate_realChartSubstitute_for_grid
    (A : σ → MvPolynomial τ ℝ) (f : V →ₗ[ℝ] ℝ)
    (P : VectorPolynomial σ ℚ V) :
    coordinate f.toAddMonoidHom (realChartSubstitute A P) =
      aeval A (coordinate f.toAddMonoidHom P) := by
  apply MvPolynomial.funext
  intro u
  rw [← coordinate_eval₂, eval₂_realChartSubstitute, coordinate_eval₂]
  exact (MvPolynomial.comp_aeval_apply A (MvPolynomial.aeval u) _).symm

omit [IsScalarTower ℚ ℝ V] in
theorem coefficientGrid_iff_coordinate (b : Basis ι ℝ V) (q : ℕ)
    (P : VectorPolynomial σ ℚ V) :
    CoefficientGrid b q P ↔
      ∀ i, realPolynomialCoefficientGrid q (coordinate (b.coord i).toAddMonoidHom P) := by
  constructor
  · intro h i
    choose z hz using h
    refine ⟨fun α => z α i, funext fun α => ?_⟩
    simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply,
      Pi.smul_apply, smul_eq_mul]
      using congrFun (hz α) i
  · intro h α
    choose z hz using h
    refine ⟨fun i => z i α, funext fun i => ?_⟩
    simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply,
      Pi.smul_apply, smul_eq_mul]
      using congrFun (hz i) α

theorem CoefficientGrid.realChartSubstitute_integral
    (b : Basis ι ℝ V) (q : ℕ) (P : VectorPolynomial σ ℚ V)
    (hP : CoefficientGrid b q P) (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, realPolynomialCoefficientGrid 1 (A i)) :
    CoefficientGrid b q (realChartSubstitute A P) := by
  rw [coefficientGrid_iff_coordinate]
  intro i
  rw [coordinate_realChartSubstitute_for_grid]
  exact realPolynomialCoefficientGrid_aeval_integral
    (coordinate (b.coord i).toAddMonoidHom P) A q
    ((coefficientGrid_iff_coordinate b q P).mp hP i) hA

end VectorPolynomial

namespace NilpotentLieFiltration
open VectorPolynomial
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (v : τ → ℕ)

theorem symbolRationalGrid_homogeneousPullback_of_coefficientGrid
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, (A i).IsWeightedHomogeneous v (w i))
    (hAZ : ∀ i, realPolynomialCoefficientGrid 1 (A i))
    (q : ℕ) (R : F.RealPolynomialSymbolGroup w)
    (hR : CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
      (F.realGradedSymbolPolynomial b ω hF w R.coord)) :
    F.SymbolRationalGrid b ω hF v q
      (F.realSymbolHomogeneousPullbackHom b ω hF w v A hA R) := by
  apply F.symbolRationalGrid_of_gradedPolynomial b ω hF v q
  change CoefficientGrid _ q
    (F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v A R.coord))
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v A hA]
  with_reducible exact (CoefficientGrid.realChartSubstitute_integral
    (V := ℝ ⊗[ℚ] F.AssociatedGraded)
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
    (F.realGradedSymbolPolynomial b ω hF w R.coord) hR A hAZ)

theorem symbolRationalGrid_integerTopPullback_of_coefficientGrid
    (βZ : σ → MvPolynomial τ ℤ) (q : ℕ) (R : F.RealPolynomialSymbolGroup w)
    (hR : CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
      (F.realGradedSymbolPolynomial b ω hF w R.coord)) :
    F.SymbolRationalGrid b ω hF v q
      (F.realSymbolHomogeneousPullbackHom b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (MvPolynomial.map (Int.castRingHom ℝ) (βZ i)))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _) R) := by
  apply F.symbolRationalGrid_homogeneousPullback_of_coefficientGrid b ω hF w v _ _ ?_ q R hR
  intro i
  exact realPolynomialCoefficientGrid_weightedHomogeneousComponent v (w i) 1 _
    (realPolynomialCoefficientGrid_intCast (βZ i))

end NilpotentLieFiltration
end Erdos3

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

theorem realSymbolOfPolynomial_homogeneousChart
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    F.realSymbolOfPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolHomogeneousPullback b ω hF w v β
        (F.realSymbolOfPolynomial b ω hF w p) := by
  classical
  apply ((F.polynomialSymbolBasis b ω hF v).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfPolynomial_coordinate, realSymbolHomogeneousPullback,
    F.realSymbolOfGradedPolynomial_coordinate]
  rw [coefficients_realChartSubstitute, coefficients_realChartSubstitute]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr_of_eq_on_inter
  · intro γ hγ hγ'
    have hz : coefficients (F.realGradedSymbolPolynomial b ω hF w
        (F.realSymbolOfPolynomial b ω hF w p)) γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · have he := F.realGradedSymbolPolynomial_coordinate b ω hF w
        (F.realSymbolOfPolynomial b ω hF w p) ⟨(γ, z.val.2), h⟩
      rw [hz, map_zero, Finsupp.zero_apply, F.realSymbolOfPolynomial_coordinate] at he
      rw [← he, mul_zero]
    · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _
        (fun he => h (he.symm.trans z.property)), zero_mul]
  · intro γ hγ hγ'
    have hz : coefficients p γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfPolynomial_coordinate, hz, map_zero, Finsupp.zero_apply, mul_zero]
    · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ γ z.val.2 h, mul_zero]
  · intro γ hγ hγ'
    have hz := z.property
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfPolynomial_coordinate]
    · have ha : Finsupp.weight v z.val.1 ≠ Finsupp.weight w γ :=
        fun he => h (he.symm.trans hz)
      rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _ ha]
      simp only [zero_mul]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute realSymbolOfPolynomial

theorem realSymbolOfPolynomial_chart_eq_top
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolOfPolynomial b ω hF v
        (realChartSubstitute (fun i => weightedHomogeneousComponent v (w i) (β i)) p) := by
  classical
  apply ((F.polynomialSymbolBasis b ω hF v).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfPolynomial_coordinate, F.realSymbolOfPolynomial_coordinate,
    coefficients_realChartSubstitute, coefficients_realChartSubstitute]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro γ _
  rcases lt_trichotomy (Finsupp.weight w γ) (ω z.val.2) with hlt | heq | hgt
  · have hzero : (aeval β (monomial γ (1 : ℝ))).coeff z.val.1 = 0 := by
      by_contra hc
      have hle := aeval_monomial_weightedSupport β w v hβ γ (mem_support_iff.mpr hc)
      have hz := z.property
      omega
    have htop : (aeval (fun i => weightedHomogeneousComponent v (w i) (β i))
        (monomial γ (1 : ℝ))).IsWeightedHomogeneous v (Finsupp.weight w γ) :=
      isWeightedHomogeneous_aeval_monomial w v _
        (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) γ 1
    rw [hzero, htop.coeff_eq_zero _ (by have hz := z.property; omega)]
  · rw [coeff_aeval_monomial_eq_top w v β hβ γ 1 z.val.1
      (z.property.trans heq.symm)]
  · have hzero := (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
      ((F.realification.adapted_iff_coefficients w p).mp hp γ) z.val.2 (by omega)
    rw [hzero, mul_zero, mul_zero]

theorem realSymbolOfPolynomial_inhomogeneousChart
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolHomogeneousPullback b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (β i))
        (F.realSymbolOfPolynomial b ω hF w p) := by
  rw [F.realSymbolOfPolynomial_chart_eq_top b ω hF w v β hβ p hp]
  exact F.realSymbolOfPolynomial_homogeneousChart b ω hF w v _
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) p

theorem realPolynomialSymbolHom_weightedAdaptedRealChart
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF v (F.weightedAdaptedRealChartHom w v β hβ g) =
      F.realSymbolHomogeneousPullbackHom b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (β i))
        (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (F.realPolynomialSymbolHom b ω hF w g) := by
  apply NilpotentLieBCHGroup.ext
  change F.realSymbolOfPolynomial b ω hF v
      ((F.weightedAdaptedRealChartHom w v β hβ g).coord :
        VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) = _
  rw [F.weightedAdaptedRealChartHom_coord]
  exact F.realSymbolOfPolynomial_inhomogeneousChart b ω hF w v β hβ _
    ((F.realification.mem_adaptedSubmodule w _).mp g.coord.property)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem weightedRealChart_comp_support
    {σ τ υ : Type*} (w : σ → ℕ) (v : τ → ℕ) (u : υ → ℕ)
    (β : σ → MvPolynomial τ ℝ) (γ : τ → MvPolynomial υ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i)) :
    ∀ i, MvPolynomial.aeval γ (β i) ∈ weightedSupportLE u (w i) :=
  fun i => weightedSupportLE_aeval v u γ hγ (hβ i)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realPolynomialSymbolLift

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realSymbolHomogeneousPullback_mem_of_range
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (K : Set (σ → ℝ)) (P : F.RealPolynomialSymbolGroup w)
    (hP : ∀ t ∈ K, eval₂ t (F.realGradedSymbolPolynomial b ω hF w P.coord) ∈
      W.toSubmodule.baseChange ℝ)
    (hK : ∀ t : τ → ℝ, (fun i => MvPolynomial.eval t (β i)) ∈ K) :
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ P).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v W) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF v W _).mpr
  intro t
  rw [F.realSymbolHomogeneousPullbackHom_coord,
    F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
    eval₂_realChartSubstitute]
  exact hP _ (hK t)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedTwistSpatialPartition
namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist
open scoped NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def frozenTorus
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (y : Y → UnitAddCircle) : ℂ :=
  W.mask residue * W.smooth (center, y)

theorem norm_frozenTorus_le
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (y : Y → UnitAddCircle) :
    ‖W.frozenTorus residue center y‖ ≤ 1 := by
  rw [frozenTorus, norm_mul]
  exact (mul_le_mul (W.mask_bound _) (W.smooth_bound _) (norm_nonneg _) zero_le_one).trans_eq
    (mul_one 1)

theorem frozenTorus_lipschitz
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) :
    LipschitzWith L (W.frozenTorus residue center) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have h := W.smooth_lipschitz.dist_le_mul (center, y) (center, z)
  simp only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] at h
  calc
    _ = ‖W.mask residue‖ * dist (W.smooth (center, y)) (W.smooth (center, z)) := by
      simp only [frozenTorus, dist_eq_norm, ← mul_sub, norm_mul]
    _ ≤ 1 * ((L : ℝ) * dist y z) :=
      mul_le_mul (W.mask_bound _) h dist_nonneg zero_le_one
    _ = _ := one_mul _

theorem frozenTorus_spatial_error
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (x center : X → ℝ) (y : Y → UnitAddCircle) :
    ‖W.mask residue * W.smooth (x, y) - W.frozenTorus residue center y‖ ≤
      (L : ℝ) * dist x center := by
  have h := W.smooth_lipschitz.dist_le_mul (x, y) (center, y)
  simp only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] at h
  calc
    _ = ‖W.mask residue‖ * dist (W.smooth (x, y)) (W.smooth (center, y)) := by
      simp only [frozenTorus, dist_eq_norm, ← mul_sub, norm_mul]
    _ ≤ 1 * ((L : ℝ) * dist x center) :=
      mul_le_mul (W.mask_bound _) h dist_nonneg zero_le_one
    _ = _ := one_mul _

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def frozenSpatialEval
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) : ℂ :=
  W.frozenTorus (fun i => (u i : ZMod W.modulus)) center
    (physicalGridFactorInput W.cover p (fun i => (u i : ℝ)))

theorem eval_sub_frozenSpatialEval
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (center : X → ℝ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    ‖W.eval N p u - W.frozenSpatialEval center p u‖ ≤
      (L : ℝ) * dist (fun i => (u i : ℝ) / N i) center :=
  W.frozenTorus_spatial_error _ _ _ _

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NormalizedTwistLocalizedFourierSelection
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

open _root_.MvPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def normalizedTwistFrequencyPolynomial (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    MvPolynomial X ℝ :=
  C (1 / (cover : ℝ)) * ∑ j, integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)

theorem normalizedTwistFrequencyPolynomial_eval (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ) :
    MvPolynomial.eval u (normalizedTwistFrequencyPolynomial cover a poly) =
      ∑ i : Σ j, J j, (a i : ℝ) * (eval u (poly i.1) i.2 / cover) := by
  simp only [normalizedTwistFrequencyPolynomial, map_mul, eval_C, map_sum,
    integerRowPolynomial_eval, Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem physicalGrid_character_eq_polynomial_phase (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ) :
    (∏ i, CircleFourier.character (a i • physicalGridFactorInput cover poly u i)) =
      (Real.fourierChar (MvPolynomial.eval u
        (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) := by
  rw [normalizedTwistFrequencyPolynomial_eval]
  exact torus_integer_character_real_phase a _

namespace NormalizedPolynomialTwist

variable [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem exists_frozen_ambient_fourier
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ)
    {δ p : ℝ} (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hL : (L : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → (Σ j, J j) → ℤ) (coeff : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ a j, |(frequency a j : ℝ)| ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∑ a, ‖coeff a‖) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ),
        ‖W.frozenTorus residue center (physicalGridFactorInput W.cover poly u) -
          ∑ a, coeff a * (Real.fourierChar (MvPolynomial.eval u
            (normalizedTwistFrequencyPolynomial W.cover (frequency a) poly)) : ℂ)‖ ≤ δ := by
  obtain ⟨F, inst, freq, coeff, hcard, hfreq, hmass, herr⟩ :=
    exists_ambient_torus_fourier_approximation (W.frozenTorus residue center) L 1
      (W.frozenTorus_lipschitz residue center) (W.norm_frozenTorus_le residue center)
      hδ hp hdim hL hδp
  let := inst
  refine ⟨F, inst, freq, coeff, hcard, hfreq, ?_, ?_⟩
  · simpa only [NNReal.coe_one, mul_one] using hmass
  · intro poly u
    simpa only [physicalGrid_character_eq_polynomial_phase] using
      herr (physicalGridFactorInput W.cover poly u)

end NormalizedPolynomialTwist
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped BigOperators NNReal

variable {X Ω : Type*} [Fintype X] [Fintype Ω]
  {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
  {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem norm_correlation_star_eq_product (μ : FiniteProbabilityWeights Ω)
    (signal test : Ω → ℂ) :
    ‖μ.correlation (fun x => star (signal x)) test‖ =
      ‖μ.complexMean (fun x => signal x * test x)‖ := by
  have he : μ.correlation (fun x => star (signal x)) test =
      star (μ.complexMean (fun x => signal x * test x)) := by
    unfold FiniteProbabilityWeights.correlation FiniteProbabilityWeights.complexMean
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [he, norm_star]

theorem exists_correlating_frequency
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
    (radius ε δ p : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hL : (L : ℝ) ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p)
    (hcell : ∀ x, 0 < μ.weight x →
      (fun i => (u x i : ZMod W.modulus)) = residue ∧
        dist (fun i => (u x i : ℝ) / N i) center ≤ radius)
    (hsignal : ∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1)
    (herror : (L : ℝ) * radius + ε ≤ δ / 2)
    (hcorr : δ ≤ ‖μ.correlation signal (fun x => W.eval N poly (u x))‖) :
    ∃ a : (Σ j, J j) → ℤ,
      (∀ j, |(a j : ℝ)| ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      δ / (2 * Real.exp (2 * p * (2 * p + 2) ^ 4)) ≤
        ‖μ.correlation signal (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ))‖ := by
  classical
  obtain ⟨F, inst, freq, coeff, _hcard, hfreq, hmass, herr⟩ :=
    W.exists_frozen_ambient_fourier residue center hε hp hdim hL hεp
  let := inst
  let atom : F → Ω → ℂ := fun a x =>
    Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
      (normalizedTwistFrequencyPolynomial W.cover (freq a) poly))
  let approx : Ω → ℂ := fun x => ∑ a, coeff a * atom a x
  have happrox (x : Ω) (hx : μ.weight x ≠ 0) :
      ‖W.eval N poly (u x) - approx x‖ ≤ (L : ℝ) * radius + ε := by
    have hxpos := lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx)
    obtain ⟨hres, hdist⟩ := hcell x hxpos
    have hfreeze : W.frozenSpatialEval center poly (u x) =
        W.frozenTorus residue center
          (physicalGridFactorInput W.cover poly (fun i => (u x i : ℝ))) := by
      simp only [frozenSpatialEval, hres]
    have he := herr poly (fun i => (u x i : ℝ))
    calc
      _ ≤ ‖W.eval N poly (u x) - W.frozenSpatialEval center poly (u x)‖ +
          ‖W.frozenSpatialEval center poly (u x) - approx x‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (L : ℝ) * radius + ε := add_le_add
        ((W.eval_sub_frozenSpatialEval N center poly (u x)).trans
          (mul_le_mul_of_nonneg_left hdist L.coe_nonneg))
        (by rw [hfreeze]; exact he)
  have hmean : ‖μ.correlation signal (fun x => W.eval N poly (u x)) -
      μ.correlation signal approx‖ ≤ (L : ℝ) * radius + ε := by
    rw [μ.correlation_eq_complexMean, μ.correlation_eq_complexMean]
    apply (μ.norm_complexMean_sub_le _ _ (fun _ => (L : ℝ) * radius + ε) ?_).trans_eq
      (μ.mean_const _)
    intro x hx
    rw [← mul_sub, ← star_sub, norm_mul, norm_star]
    calc
      _ ≤ 1 * ‖W.eval N poly (u x) - approx x‖ :=
        mul_le_mul_of_nonneg_right
          (hsignal x (lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx))) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact happrox x hx
  have hexpand : μ.correlation signal approx =
      ∑ a, star (coeff a) * μ.correlation signal (atom a) := by
    simp only [FiniteProbabilityWeights.correlation_eq_complexMean, approx, star_sum, star_mul]
    simpa only [mul_comm] using μ.complexMean_weighted_expansion signal
      (fun a => star (coeff a)) (fun a x => star (atom a x))
  have hlarge : δ / 2 ≤ ‖∑ a, star (coeff a) * μ.correlation signal (atom a)‖ := by
    have htriangle := norm_le_norm_add_norm_sub (μ.correlation signal approx)
      (μ.correlation signal (fun x => W.eval N poly (u x)))
    rw [norm_sub_rev] at htriangle
    rw [← hexpand]
    linarith
  obtain ⟨a, ha⟩ := exists_large_weighted_term (fun a => star (coeff a))
    (fun a => μ.correlation signal (atom a)) (by positivity : 0 < δ / 2)
    (Real.exp_pos _) (by simpa only [norm_star] using hmass) hlarge
  refine ⟨freq a, hfreq a, ?_⟩
  simpa only [div_div, atom] using ha

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem integerRowPolynomial_constant_of_annihilates {I K : Type*} [Fintype K]
    (W : Submodule ℝ (K → ℝ)) (a : K → ℤ) (p : VectorPolynomial I ℝ (K → ℝ))
    (hp : ∀ α, α ≠ 0 → coefficients p α ∈ W)
    (ha : W ≤ LinearMap.ker (integerRowLinear a)) :
    integerRowPolynomial a p = C ((integerRowPolynomial a p).coeff 0) := by
  classical
  ext α
  by_cases hα : α = 0
  · subst α
    simp
  · have hz : integerRowLinear a (coefficients p α) = 0 := ha (hp α hα)
    rw [integerRowPolynomial_coeff, ← integerRowLinear_apply, hz, coeff_C]
    simp only [Ne.symm hα, ite_false]

theorem integerRowPolynomial_truncateTaggedFrequency (d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (j : Fin m) :
    integerRowPolynomial (fun i => truncateTaggedFrequency d a ⟨j, i⟩) (poly j) =
      if j.val + 1 ≤ d then integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) else 0 := by
  classical
  by_cases hj : j.val + 1 ≤ d
  · simp only [truncateTaggedFrequency, hj, ite_true]
  · simp only [truncateTaggedFrequency, hj, ite_false]
    ext α
    simp only [integerRowPolynomial_coeff, Int.cast_zero, zero_mul,
      Finset.sum_const_zero, MvPolynomial.coeff_zero]

theorem normalizedTwistFrequencyPolynomial_truncate (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly =
      C (1 / (cover : ℝ)) * taggedScalarLowPolynomial d
        (fun j => integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)) := by
  simp only [normalizedTwistFrequencyPolynomial, integerRowPolynomial_truncateTaggedFrequency,
    taggedScalarLowPolynomial]

noncomputable def normalizedTwistHighFrequencyConstant (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) : ℝ :=
  (1 / (cover : ℝ)) * taggedScalarHighConstant d
    (fun j => integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j))

theorem normalizedTwistFrequencyPolynomial_low_degree (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) :
    (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly).totalDegree ≤ d := by
  rw [normalizedTwistFrequencyPolynomial_truncate]
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact taggedScalarLowPolynomial_degree d _
    (fun j => integerRowPolynomial_totalDegree_le _ (hpoly j))

theorem normalizedTwistFrequencyPolynomial_low_add_constant (cover d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (hann : ∀ j, d < j.val + 1 →
      W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))) :
    normalizedTwistFrequencyPolynomial cover a poly =
      normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly +
        C (normalizedTwistHighFrequencyConstant cover d a poly) := by
  rw [normalizedTwistFrequencyPolynomial_truncate]
  unfold normalizedTwistFrequencyPolynomial normalizedTwistHighFrequencyConstant
  rw [taggedScalar_sum_eq_low_add_constant d _ (fun j hj =>
    integerRowPolynomial_constant_of_annihilates (W j) _ _ (hcoeff j) (hann j hj)),
    mul_add, ← map_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal

theorem exists_correlating_frequency_early :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω : Type*} [Fintype X] [Fintype Ω]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
      (p : ℝ), 0 ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (L : ℝ) ≤ Real.exp p →
      (∀ x, 0 < μ.weight x →
        (fun i => (u x i : ZMod W.modulus)) = residue ∧
          dist (fun i => (u x i : ℝ) / N i) center ≤ Real.exp (-2 * p) / 4) →
      (∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖μ.correlation signal (fun x => W.eval N poly (u x))‖ →
      ∃ a : (Σ j, J j) → ℤ,
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖μ.correlation signal (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ))‖ := by
  let Q : Polynomial ℕ := Polynomial.X + 4 +
    (2 * (Polynomial.X + 4) + 1) * (2 * (Polynomial.X + 4) + 2) ^ 4
  obtain ⟨C, hC, hQ⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro X Ω _ _ m J _ periodCap coverCap L W μ u N poly signal residue center p hp hdim hL
    hcell hsignal hcorr
  let q := p + 4
  let A := 2 * q * (2 * q + 2) ^ 4
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hε : 0 < Real.exp (-p) / 4 := by positivity
  have hεp : (Real.exp (-p) / 4)⁻¹ ≤ Real.exp q := by
    rw [inv_div, Real.exp_neg, div_inv_eq_mul]
    change 4 * Real.exp p ≤ Real.exp (p + 4)
    rw [Real.exp_add]
    nlinarith [Real.exp_pos p]
  have herr : (L : ℝ) * (Real.exp (-2 * p) / 4) + Real.exp (-p) / 4 ≤
      Real.exp (-p) / 2 := by
    calc
      _ ≤ Real.exp p * (Real.exp (-2 * p) / 4) + Real.exp (-p) / 4 := by
        gcongr
      _ = _ := by
        have he : Real.exp p * Real.exp (-2 * p) = Real.exp (-p) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← mul_div_assoc, he]
        ring
  obtain ⟨a, ha, hscore⟩ := W.exists_correlating_frequency μ u N poly signal residue center
    (Real.exp (-2 * p) / 4) (Real.exp (-p) / 4) (Real.exp (-p)) q hε (Real.exp_pos _)
    hq (hdim.trans hpq) (hL.trans (Real.exp_le_exp.mpr hpq)) hεp hcell hsignal herr hcorr
  have hbudget : p + 4 + (2 * q + 1) * (2 * q + 2) ^ 4 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hQ p hp
  have hfreq : (2 * q + 2) ^ 4 ≤ (p + C) ^ C := by
    apply le_trans _ hbudget
    nlinarith [pow_nonneg (show 0 ≤ 2 * q + 2 by linarith) 4]
  have hcost : p + A + 4 ≤ (p + C) ^ C := by
    dsimp [A]
    nlinarith [pow_nonneg (show 0 ≤ 2 * q + 2 by linarith) 4]
  refine ⟨a, fun j => (ha j).trans (Real.exp_le_exp.mpr hfreq), ?_⟩
  apply le_trans (Real.exp_le_exp.mpr (neg_le_neg hcost))
  apply le_trans ?_ hscore
  change Real.exp (-(p + A + 4)) ≤ Real.exp (-p) / (2 * Real.exp A)
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.exp A)).mpr
  have he : Real.exp (-(p + A + 4)) * (2 * Real.exp A) =
      2 * Real.exp (-p) / Real.exp 4 := by
    rw [mul_comm (2 : ℝ), ← mul_assoc, ← Real.exp_add]
    have hx : -(p + A + 4) + A = -p - 4 := by ring
    rw [hx, Real.exp_sub]
    ring
  rw [he]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  nlinarith [Real.exp_pos (-p)]

theorem exists_correlating_frequency_product_early :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω : Type*} [Fintype X] [Fintype Ω]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
      (p : ℝ), 0 ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (L : ℝ) ≤ Real.exp p →
      (∀ x, 0 < μ.weight x →
        (fun i => (u x i : ZMod W.modulus)) = residue ∧
          dist (fun i => (u x i : ℝ) / N i) center ≤ Real.exp (-2 * p) / 4) →
      (∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖μ.complexMean (fun x => W.eval N poly (u x) * signal x)‖ →
      ∃ a : (Σ j, J j) → ℤ,
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖μ.complexMean (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) * signal x)‖ := by
  obtain ⟨C, hC, h⟩ := exists_correlating_frequency_early
  refine ⟨C, hC, ?_⟩
  intro X Ω _ _ m J _ periodCap coverCap L W μ u N poly signal residue center p hp hdim hL
    hcell hsignal hcorr
  obtain ⟨a, ha, hc⟩ := h W μ u N poly (fun x => star (signal x)) residue center p hp
    hdim hL hcell (fun x hx => by simpa only [norm_star] using hsignal x hx) (by
      rw [norm_correlation_star_eq_product]
      simpa only [mul_comm] using hcorr)
  refine ⟨a, ha, ?_⟩
  rw [norm_correlation_star_eq_product] at hc
  simpa only [mul_comm] using hc

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3

namespace VectorPolynomial

open _root_.MvPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem normalizedTwistFrequencyPolynomial_top_not_approximation
    (cover : ℕ) (hcover : 0 < cover) (h : Fin m)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : Submodule ℝ (J h → ℝ)) (T : X → ℝ) (R S : ℝ)
    (hT : ∀ i, 0 < T i) (hcost : (cover : ℝ) * S ≤ R)
    (hrank : HasLayerSamplingRank (h.val + 1) T R W (poly h))
    (ha : ∀ i, |(a ⟨h, i⟩ : ℝ)| ≤ R)
    (hw : ∃ w ∈ W, integerRowLinear (fun i => a ⟨h, i⟩) w ≠ 0)
    (htop : homogeneousComponent (h.val + 1)
        (normalizedTwistFrequencyPolynomial cover a poly) =
      C (1 / (cover : ℝ)) * homogeneousComponent (h.val + 1)
        (integerRowPolynomial (fun i => a ⟨h, i⟩) (poly h))) :
    ¬ PolynomialRationalApproximation T S (homogeneousComponent (h.val + 1)
      (normalizedTwistFrequencyPolynomial cover a poly)) := by
  intro happ
  obtain ⟨w, hw, hwa⟩ := hw
  have hwan : ∑ i, (a ⟨h, i⟩ : ℝ) * w i ≠ 0 := by
    simpa only [integerRowLinear_apply] using hwa
  apply hrank (fun i => a ⟨h, i⟩) ha ⟨⟨w, hw⟩, hwan⟩
  have hscaled := (happ.nat_smul cover hcover).mono hcost hT
  rw [htop] at hscaled
  have hcancel (P : MvPolynomial X ℝ) :
      (cover : ℝ) • (C (1 / (cover : ℝ)) * P) = P := by
    rw [smul_eq_C_mul, ← mul_assoc, ← map_mul]
    rw [mul_one_div_cancel (Nat.cast_ne_zero.mpr hcover.ne'), map_one, one_mul]
  rwa [hcancel] at hscaled

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal BigOperators

theorem exists_localized_correlating_frequency :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (signal : (X → ℤ) → ℂ) (p : ℝ),
      0 ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (L : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) →
      (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * signal u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          signal (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ := by
  obtain ⟨C, hC, hfourier⟩ := exists_correlating_frequency_product_early
  refine ⟨C, hC, ?_⟩
  intro X _ _ m J _ periodCap coverCap L W N poly signal p hp hdim hmod hL hN hsignal hcorr
  obtain ⟨start, length, hpos, hlength, hcomparison, hinside, _, hspatial, _, hselected⟩ :=
    exists_correlated_integer_residue_box N W.modulus p hp W.modulus_pos hmod hN
      (fun u => W.eval N poly u * signal u)
  have hnonempty : (integerBox length).Nonempty := by
    refine ⟨0, (mem_integerBox length 0).mpr ?_⟩
    intro i
    simp only [Pi.zero_apply]
    exact ⟨le_rfl, by exact_mod_cast hpos i⟩
  let μ := FiniteProbabilityWeights.uniformFinset (integerBox length) hnonempty
  let u : ↥(integerBox length) → X → ℤ :=
    fun v i => (start i : ℤ) + (W.modulus : ℤ) * v.val i
  have hcell (v : ↥(integerBox length)) (_ : 0 < μ.weight v) :
      (fun i => (u v i : ZMod W.modulus)) = (fun i => (start i : ZMod W.modulus)) ∧
        dist (fun i => (u v i : ℝ) / N i) (fun i => (start i : ℝ) / N i) ≤
          Real.exp (-2 * p) / 4 := by
    constructor
    · funext i
      simp [u]
    · apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      simpa only [u, Real.dist_eq, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        neg_mul] using hspatial v.val v.property i
  have hselected' : Real.exp (-p) ≤ ‖μ.complexMean
      (fun v => W.eval N poly (u v) * signal (u v))‖ := by
    dsimp only [μ, u]
    rw [FiniteProbabilityWeights.uniformFinset_complexMean _ _
      (fun v : X → ℤ => W.eval N poly (fun i => (start i : ℤ) + W.modulus * v i) *
        signal (fun i => (start i : ℤ) + W.modulus * v i))]
    exact hcorr.trans hselected
  obtain ⟨a, ha, hc⟩ := hfourier W μ u N poly (fun v => signal (u v))
    (fun i => (start i : ZMod W.modulus)) (fun i => (start i : ℝ) / N i) p hp hdim hL
    hcell (fun v _ => hsignal _ (hinside v.val v.property)) hselected'
  refine ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, ?_⟩
  dsimp only [μ, u] at hc
  rw [FiniteProbabilityWeights.uniformFinset_complexMean _ _
    (fun v : X → ℤ => (Real.fourierChar (MvPolynomial.eval
      (fun i => (((start i : ℤ) + W.modulus * v i : ℤ) : ℝ))
      (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
      signal (fun i => (start i : ℤ) + W.modulus * v i))] at hc
  simpa only [u, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hc

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

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

noncomputable def lowTaggedRetained (d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (h : Fin d) :
    Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :=
  if hm : h.val < m then
    (W ⟨h.val, hm⟩).map (lowTaggedEmbedding J d ⟨h.val, hm⟩ (by exact Nat.succ_le_of_lt h.isLt))
  else ⊥

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowTaggedGradedSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem le_lowTaggedSubspaceFamily (d : ℕ)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hUK : ∀ h : Fin d, lowTaggedRetained J d U h ≤ K) (j : Fin m) :
    U j ≤ lowTaggedSubspaceFamily J d K j := by
  intro x hx
  by_cases hj : j.val + 1 ≤ d
  · rw [mem_lowTaggedSubspaceFamily_iff J d K j hj]
    let h : Fin d := ⟨j.val, by omega⟩
    apply hUK h
    have heq : lowTaggedRetained J d U h =
        (U j).map (lowTaggedEmbedding J d j hj) := by
      simp only [lowTaggedRetained, h, dif_pos j.isLt]
    rw [heq]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  · simp only [lowTaggedSubspaceFamily, dif_neg hj, Submodule.mem_top]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonLocalAffineFamily
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

theorem exists_local_affine_polynomial_family
    {V : Type} [AddCommGroup V] [Module ℝ V] [Module ℚ V]
    {s r N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p)
    (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (hdense : Real.exp (-p) * N ≤ (J.card : ℝ)) (x : ZMod N → Fin r → ℤ)
    (hx : ∀ h ∈ J, ∀ i, |x h i| ≤ (R i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (x h))
    (P : ZMod N → VectorPolynomial Unit ℚ V) (Γ : VectorPolynomial Unit ℚ V)
    (α : Fin s → V) (β : Fin r → Fin s → V) (U : Fin s → Submodule ℝ V)
    (hα : ∀ d, α d ∈ U d) (hβ : ∀ i d, β i d ∈ U d)
    (hP : ∀ h ∈ J, P h = Γ + positiveUnivariate (fun d => α d + ∑ i, (x h i : ℝ) • β i d)) :
    ∃ K ⊆ J, K.Nonempty ∧ Real.exp (-((p + 4) ^ 7)) * N ≤ (K.card : ℝ) ∧
      ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
        (∀ i j, |(b i : Fin r → ℝ) j| ≤
          properCyclicKernelBasisBound r (Real.exp (-p)) * ((R j : ℝ) + 1)) ∧
        ∃ (t c : Fin r → ℝ) (α' : Fin s → V) (β' : Fin r → Fin s → V),
          (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
          (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
          (∀ i, |c i| ≤ properCyclicCoordinateBound r (Real.exp (-p)) + 1 / 16) ∧
          (∀ d, α' d ∈ U d) ∧ (∀ i d, β' i d ∈ U d) ∧
          ∀ h ∈ K,
            (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ 1 / 16) ∧
            P h = Γ + positiveUnivariate (fun d => α' d +
              ∑ i, affineCyclicTorusLocalLift t c h₀ h i • β' i d) := by
  obtain ⟨b, hb, t, ht, hperiod, K, hKJ, hK, hcard, c, hc, hdata⟩ :=
    exists_localized_cyclic_torus_chart η R hinj h₀ J hJ (Real.exp (-p))
      (Real.exp_pos (-p)) hdense x hx hrep 8 (by norm_num)
  let B := b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)
  let α' := affineBasisConstant B α β c
  let β' := affineBasisCoefficient B β
  refine ⟨K, hKJ, hK, local_cyclic_torus_density hp hr J K hdense hcard,
    b, hb, t, c, α', β', ht, hperiod, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, div_div, show (2 : ℝ) * 8 = 16 by norm_num] using hc
  · exact affineBasisConstant_mem B α β c U hα hβ
  · exact affineBasisCoefficient_mem B β U hβ
  · intro h hh
    obtain ⟨_, hsmall, hcoord⟩ := hdata h hh
    refine ⟨?_, ?_⟩
    · norm_num at hsmall ⊢
      exact hsmall
    · rw [hP h (hKJ hh)]
      have he : (fun d => α d + ∑ i, (x h i : ℝ) • β i d) =
          fun d => α' d + ∑ i, affineCyclicTorusLocalLift t c h₀ h i • β' i d := by
        funext d
        change α d + ∑ i, integerVectorRealMap (x h) i • β i d = _
        rw [hcoord]
        exact affine_basis_change B α β c (affineCyclicTorusLocalLift t c h₀ h) d
      rw [he]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeCommonProjection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_four_projection_norm_le
    {V ι : Type*} [LieRing V] [LieAlgebra ℚ V] [Fintype ι]
    (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] (Fin 4 → V)) (k : Fin 4) :
    ‖(b.baseChange ℝ).equivFun ((LinearMap.proj k).baseChange ℝ x)‖ ≤
      ‖((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  change |(b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x) i| ≤ _
  rw [real_pi_projection_coordinates]
  exact norm_le_pi_norm (((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).equivFun x) ⟨k, i⟩

theorem real_four_projection_grid
    {V ι : Type*} [LieRing V] [LieAlgebra ℚ V] [Fintype ι]
    (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] (Fin 4 → V)) (k : Fin 4) (l : ℕ)
    (hx : ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (b.baseChange ℝ).equivFun ((LinearMap.proj k).baseChange ℝ x) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => z ⟨k, i⟩, funext fun i => ?_⟩
  exact (congrFun hz ⟨k, i⟩).trans (congrArg (fun a : ℝ => (l : ℝ) * a)
    (real_pi_projection_coordinates b x k i).symm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineOrbitFamily
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

theorem affine_petal_decomposition
    {μ ι V : Type*} [Fintype μ] [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (ι → ℚ)) (hker : LinearMap.ker ℓ = K)
    (σ : (ι → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (hσU : ∀ y, σ y ∈ U.baseChange ℝ)
    (hσ : ∀ w ∈ U.baseChange ℝ,
      realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0))
          (σ (realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) w)) =
        realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) w)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ‖(b.baseChange ℝ).equivFun (σ y)‖ ≤ C * ‖y‖)
    {l m : ℕ} (hgrid : ∀ y ∈ realDenominatorGrid l,
      (b.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m)
    {r : ℕ} (α : ι → ℝ) (β : Fin r → ι → ℝ) (x : Fin r → ℤ)
    (w : ℝ ⊗[ℚ] V) (hw : w ∈ U.baseChange ℝ) (q : ι → ℝ)
    (hq : q ∈ realDenominatorGrid l) {ε : ℝ}
    (he : ‖realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) w -
      (α + ∑ j, (x j : ℝ) • β j) - q‖ ≤ ε) :
    ∃ E Q P : ℝ ⊗[ℚ] V, E ∈ U.baseChange ℝ ∧ Q ∈ U.baseChange ℝ ∧
      P ∈ (fourPetalSpace U K).baseChange ℝ ∧
      w = (σ α + ∑ j, (x j : ℝ) • σ (β j)) + E + Q + P ∧
      ‖(b.baseChange ℝ).equivFun E‖ ≤ C * ε ∧
      (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m := by
  let φ := ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)
  let a := realifyCoordinateMap φ w
  let e := a - (α + ∑ j, (x j : ℝ) • β j) - q
  let P := w - σ a
  have hPU : P ∈ U.baseChange ℝ := (U.baseChange ℝ).sub_mem hw (hσU a)
  have hzero : realifyCoordinateMap φ P = 0 := by
    change realifyCoordinateMap φ (w - σ a) = 0
    rw [map_sub, hσ w hw, sub_self]
  have hP : P ∈ (fourPetalSpace U K).baseChange ℝ := by
    apply (mem_real_petal_annihilator_iff U K ℓ hker P).mpr
    refine ⟨hPU, fun j => ?_⟩
    exact congrFun hzero j
  refine ⟨σ e, σ q, P, hσU e, hσU q, hP, ?_, ?_, hgrid q hq⟩
  · dsimp [P, e]
    simp only [map_sub, map_add, map_sum, map_smul]
    abel
  · exact (hbound e).trans (mul_le_mul_of_nonneg_left he hC)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineRefinedCoefficients
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

theorem affine_refined_coefficient_mem {L ι : Type*} [AddCommGroup L] [Module ℚ L]
    [Fintype ι] {s : ℕ} (C D : Fin s → Submodule ℚ L)
    (K : Fin s → Submodule ℚ (Fin 4 → L))
    (G : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (α : Fin s → ℝ ⊗[ℚ] L) (β : ι → Fin s → ℝ ⊗[ℚ] L) (x : ι → ℝ)
    (hG : ∀ d : Fin s, coefficients G (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (C d) (D d) (K d)).map (LinearMap.proj 0)).baseChange ℝ)
    (hα : ∀ d, α d ∈ (D d).baseChange ℝ)
    (hβ : ∀ j d, β j d ∈ (D d).baseChange ℝ) (d : Fin s) :
    coefficients (G + positiveUnivariate (fun d => α d + ∑ j, x j • β j d))
        (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (C d) (D d) (K d)).map (LinearMap.proj 0)).baseChange ℝ := by
  rw [map_add, Finsupp.add_apply, positiveUnivariate_coefficient]
  apply Submodule.add_mem _ (hG d)
  apply Submodule.baseChange_mono ℝ (dependent_le_refined_firstProjection (C d) (D d) (K d))
  exact Submodule.add_mem _ (hα d)
    (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hβ j d)))

end Erdos3.VectorPolynomial

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

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

noncomputable abbrev widths (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Option (LayerSamplerVariables G I n B) × X → ℝ :=
  allocatedExternalCandidateWidths B U b S N τ ξ

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPhasePairFunctionalBounds
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module _root_.MvPolynomial PolynomialTranslationLie

theorem constantCoefficient_injective (s : ℕ) : Function.Injective (constantCoefficient s) := by
  intro x y hxy
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · exact Subsingleton.elim _ _
  · rw [polynomial_eq_constant x.val.polynomial, polynomial_eq_constant y.val.polynomial]
    exact congrArg C hxy

theorem constantCoefficient_eq_zero_iff (s : ℕ) (x : weightedSubalgebra weight s) :
    constantCoefficient s x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact constantCoefficient_injective s (hx.trans (map_zero (constantCoefficient s)).symm)
  · rintro rfl
    exact map_zero _

theorem lie_eq_zero (s : ℕ) (x y : weightedSubalgebra weight s) : ⁅x, y⁆ = 0 := by
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · rfl
  · change scalarDirectionalDerivative x.val.base y.val.polynomial -
      scalarDirectionalDerivative y.val.base x.val.polynomial = 0
    simp [scalarDirectionalDerivative_apply]

theorem constantCoefficient_lie (s : ℕ) (x y : weightedSubalgebra weight s) :
    constantCoefficient s ⁅x, y⁆ = 0 := by
  rw [lie_eq_zero, map_zero]

theorem eq_constantCoefficient_smul_central (s : ℕ) (hs : 0 < s)
    (x : weightedSubalgebra weight s) :
    x = constantCoefficient s x • centralRationalElement weight s hs 1 := by
  apply constantCoefficient_injective s
  rw [map_smul, constantCoefficient_centralRationalElement, smul_eq_mul, mul_one]

theorem frequency_eq_constantCoefficient (s : ℕ) (hs : 0 < s)
    (η : weightedSubalgebra weight s →ₗ[ℚ] ℚ)
    (hη : η (centralRationalElement weight s hs 1) = 1) :
    η = constantCoefficient s := by
  ext x
  conv_lhs => rw [eq_constantCoefficient_smul_central s hs x]
  rw [map_smul, hη, smul_eq_mul, mul_one]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module _root_.MvPolynomial PolynomialTranslationLie VectorPolynomial
open scoped TensorProduct

def constantBasisIndex (s : ℕ) (hs : 0 < s) : WeightedBasisIndex weight s :=
  Sum.inr ⟨0, by change Finsupp.weight weight 0 < s; simpa only [map_zero] using hs⟩

@[simp] theorem constantBasisIndex_grade (s : ℕ) (hs : 0 < s) :
    weightedBasisGrade weight s (constantBasisIndex s hs) = s := by
  simp only [constantBasisIndex, weightedBasisGrade_inr, map_zero, Nat.sub_zero]

theorem constantCoefficient_eq_basis_repr (s : ℕ) (hs : 0 < s)
    (x : weightedSubalgebra weight s) :
    constantCoefficient s x =
      (weightedBasis weight s weight_pos).repr x (constantBasisIndex s hs) := rfl

theorem realify_constantCoefficient_eq_basis_coord (s : ℕ) (hs : 0 < s) :
    realifyFunctional (constantCoefficient s) =
      ((weightedBasis weight s weight_pos).baseChange ℝ).coord (constantBasisIndex s hs) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, Basis.coord_apply, Basis.baseChange_repr_tmul]
    rw [constantCoefficient_eq_basis_repr s hs]
    simp [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem constantCoefficient_coordinate_ofCoordinates {U : Type*}
    (s : ℕ) (hs : 0 < s) [Fintype (WeightedBasisIndex weight s)]
    (P : WeightedBasisIndex weight s → MvPolynomial U ℝ) :
    coordinate (realifyFunctional (constantCoefficient s)).toAddMonoidHom
        (ofCoordinates (R := ℚ) ((weightedBasis weight s weight_pos).baseChange ℝ) P) =
      P (constantBasisIndex s hs) := by
  rw [realify_constantCoefficient_eq_basis_coord s hs, coordinate_ofCoordinates]

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

theorem budget_le_factorizationInputBudget (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    budget s ≤ p + factorizationInputOffset s :=
  (budget_le_factorizationInputOffset s).trans (le_add_of_nonneg_left hp)

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R : Type*} [CommRing R]

theorem rename_lowTaggedRestrict (k : ℕ) (P : MvPolynomial (X ⊕ (Σ j, J j)) R)
    (hP : P ∈ weightedSupportLE (fullTaggedVariableWeight J) k) :
    rename (lowTaggedVariableEmbedding J k) (lowTaggedRestrict J k P) = P := by
  classical
  have hcomp : (rename (R := R) (lowTaggedVariableEmbedding (X := X) J k)).comp
      (lowTaggedRestrict J k) =
      aeval (fun i => rename (lowTaggedVariableEmbedding J k)
        (lowTaggedRestrictionVariables (R := R) J k i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, lowTaggedRestrict, aeval_X]
  change ((rename (lowTaggedVariableEmbedding J k)).comp (lowTaggedRestrict J k)) P = P
  rw [hcomp]
  calc
    _ = aeval (MvPolynomial.X : (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) R) P :=
      aeval_eq_of_weightedSupportLE hP _ _
        (rename_lowTaggedRestrictionVariables_of_weight_le J k)
    _ = P := by simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem abs_coeff_rename_le {σ τ : Type*} (e : σ ↪ τ)
    (P : MvPolynomial σ ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ α, |P.coeff α| ≤ C) (β : τ →₀ ℕ) :
    |(MvPolynomial.rename e P).coeff β| ≤ C := by
  by_cases hz : (MvPolynomial.rename e P).coeff β = 0
  · simpa only [hz, abs_zero] using hC
  · obtain ⟨α, hα, _⟩ := MvPolynomial.coeff_rename_ne_zero e P β hz
    rw [← hα, MvPolynomial.coeff_rename_mapDomain e e.injective]
    exact hP α

end Erdos3

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

theorem narrowSpatial_frame_slope_bound
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (v : Option (G ⊕ J) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (k : G ⊕ J) (x : X) :
    |(v (some k, x) : ℝ)| ≤ τ * (N x : ℝ) / (8 * (1 + W)) := by
  have h := (rectangularWeightIndices_zero_bound _ hv (some k, x)).trans
    (narrowTrimmedSpatialWidths_le hW hτ hξ N hN (some k, x))
  simpa only [trimmedSpatialWidths, centeredSpatialWidths, one_mul, mul_div_assoc] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTagRestrictionBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

theorem polynomialTagRestriction_mass_le_of_coeff_le [Fintype U] [Fintype B]
    (E : B → I → ℝ) (p : MvPolynomial (U ⊕ B) ℝ)
    {L M : ℝ} {s : ℕ} (hM : 0 ≤ M)
    (hE : ∀ b i, |E b i| ≤ L) (hp : p.totalDegree ≤ s)
    (hcoeff : ∀ α, |p.coeff α| ≤ M) :
    realPolynomialMass (aeval (polynomialTagLinearEmbedding E) p) ≤
      (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
        (max 1 ((Fintype.card I : ℝ) * L)) ^ s := by
  have hmass : realPolynomialMass p ≤
      ((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M :=
    monomialArray_abs_sum_le p.support id (fun _ _ _ _ h => h) s
      (fun α hα => (le_totalDegree hα).trans hp) (fun α => p.coeff α) hM
      (fun α _ => hcoeff α)
  exact (polynomialTagRestriction_mass_le E p hE hp).trans
    (mul_le_mul_of_nonneg_right hmass
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) s))

theorem polynomialTagRestriction_coeff_le_of_coeff_le [Fintype U] [Fintype B]
    (E : B → I → ℝ) (p : MvPolynomial (U ⊕ B) ℝ)
    {L M : ℝ} {s : ℕ} (hM : 0 ≤ M)
    (hE : ∀ b i, |E b i| ≤ L) (hp : p.totalDegree ≤ s)
    (hcoeff : ∀ α, |p.coeff α| ≤ M) (α : (U ⊕ I) →₀ ℕ) :
    |(aeval (polynomialTagLinearEmbedding E) p).coeff α| ≤
      (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
        (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  (realPolynomialMass_coeff_le _ α).trans
    (polynomialTagRestriction_mass_le_of_coeff_le E p hM hE hp hcoeff)

theorem polynomialSubspaceRestriction_coeff_le [Fintype U] [Fintype B]
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) {L M : ℝ} {s : ℕ} (hM : 0 ≤ M)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L) (hp : p.totalDegree ≤ s)
    (hcoeff : ∀ α, |p.coeff α| ≤ M) (α : (U ⊕ I) →₀ ℕ) :
    |(polynomialSubspaceRestriction K e p).coeff α| ≤
      (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
        (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  polynomialTagRestriction_coeff_le_of_coeff_le _ p hM (fun b i => he i b) hp hcoeff α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMixedLiftNormalizedMass
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

theorem normalizedMass_homogeneousComponent_projection_le {V : Type*}
    (w : V → ℕ) (n : ℕ) (p : MvPolynomial V ℝ) :
    realPolynomialMass (weightedHomogeneousComponent w n p) ≤ realPolynomialMass p := by
  classical
  have hs : (weightedHomogeneousComponent w n p).support ⊆ p.support := by
    intro α hα
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hα
    split_ifs at hα with h
    · exact mem_support_iff.mpr hα
    · exact False.elim (hα rfl)
  rw [realPolynomialMass_eq_sum_of_support_subset _ _ hs]
  apply Finset.sum_le_sum
  intro α _
  rw [coeff_weightedHomogeneousComponent]
  split_ifs <;> simp only [le_refl, abs_zero, abs_nonneg]

theorem normalizedMass_neg_weightedHomogeneousComponent_le {V : Type*}
    (T : V → ℝ) (w : V → ℕ) (n : ℕ) (p : MvPolynomial V ℝ) :
    realPolynomialMass (scaleMvPolynomialAxes T (-weightedHomogeneousComponent w n p)) ≤
      realPolynomialMass (scaleMvPolynomialAxes T p) := by
  rw [scaleMvPolynomialAxes_neg, normalizedPolynomialMass_neg,
    normalizedAxes_homogeneousComponent_commute]
  exact normalizedMass_homogeneousComponent_projection_le w n _

end Erdos3

end

end OAI
end


