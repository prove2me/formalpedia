-- Prove2me | Definitions.Def_OAIE3v2B136
-- name    : OAIE3v2B136
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:13:35.875975+00:00
-- url     : https://prove2.me/theorems/c4fa0ea8-1871-4638-93bf-a512c9545841
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 138 of 311
-- statement:
--   Definitions bundle 138 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B117`, `OAIE3v2B118`, `OAIE3v2B119`, `OAIE3v2B120`, `OAIE3v2B121`, `OAIE3v2B122`, `OAIE3v2B123` of this split.
--
--   Modules: `Dynamics/ReducedTwistedTranslationBudget.lean`, `Estimates/BoundedSubmoduleIntersection.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/CommonCoefficientFourAnnihilators.lean`, `Estimates/CyclicMixedReflection.lean`, `Estimates/NativeGraphSmallDifference.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/RationalTagConstraintSpaces.lean`, `Estimates/RealSubspaceIntersectionCorrections.lean`, `Estimates/RealSymbolGradeEvaluation.lean`, `Fourier/HomogeneousGradedProjectionFrequency.lean`, `Fourier/NiltestConjugateFrequency.lean`, `Geometry/DependentCoordinateCorrections.lean`, `Geometry/MissingCoordinateDownsets.lean`, `Geometry/NativeCoordinateEstimates.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Geometry/SymbolRepresentativeTransport.lean`, `Geometry/TranslationShearCoordinateSeries.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Linear/CertifiedChartBasisBudget.lean`, `Linear/RationalTagConstraintBasis.lean`, `Linear/RealFourBalancedDual.lean`, `Linear/WeightedTranslationBasisHeight.lean`, `Nilpotent/NiltestAffineProjection.lean`, `Polynomial/RealCoordinatePolynomialSymbol.lean`, `Polynomial/WeightedLinearPolynomialRestriction.lean`, `Sampling/BoundedKernelGridEnumerationBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B117
import Definitions.Def_OAIE3v2B118
import Definitions.Def_OAIE3v2B119
import Definitions.Def_OAIE3v2B120
import Definitions.Def_OAIE3v2B121
import Definitions.Def_OAIE3v2B122
import Definitions.Def_OAIE3v2B123

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem mem_relationSpace (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    (x,P) ∈ relationSpace U ↔ (⟨x,P⟩ : PolynomialTranslationLie σ) ∈ U := Iff.rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem polynomialLinearRestriction_translationPath
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    (polynomialTranslationPath (A z) P).map (polynomialLinearRestriction A).toRingHom =
      polynomialTranslationPath z (polynomialLinearRestriction A P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.map_mul, hp]
    simp [polynomialTranslationPath_linearCoordinatePolynomial]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rational_inclusion_mem_realificationLieSubalgebra_iff (K : LieSubalgebra ℚ L) (a : L) :
    rationalLieInclusion a ∈ realificationLieSubalgebra K ↔ a ∈ K :=
  one_tmul_mem_real_baseChange_iff K.toSubmodule a

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realificationMap_incl_injective (K : LieSubalgebra ℚ L) :
    Function.Injective (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
      (hM := hnil) K.incl) := by
  intro x y hxy
  apply ext
  apply realificationLieHom_incl_injective K
  exact congrArg coord hxy

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)

theorem repr_coefficients_ofCoordinates (α : σ →₀ ℕ) (i : ι) :
    (b.baseChange ℝ).repr (coefficients
      (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) α) i = (P i).coeff α := by
  exact congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α)
    (coordinate_ofCoordinates (R := ℚ) (b.baseChange ℝ) P i)

theorem realSymbolRepresentative_ofCoordinates :
    F.realSymbolRepresentative b ω hlayers v
      (F.realSymbolOfPolynomial b ω hlayers v
        (ofCoordinates (R := ℚ) (b.baseChange ℝ) P)) =
      ofCoordinates (R := ℚ) (b.baseChange ℝ)
        (fun i => weightedHomogeneousComponent v (ω i) (P i)) := by
  classical
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight v α = ω i
  · have hc := F.realSymbolRepresentative_coefficient b ω hlayers v
      (F.realSymbolOfPolynomial b ω hlayers v
        (ofCoordinates (R := ℚ) (b.baseChange ℝ) P)) ⟨(α, i), h⟩
    have hs := F.realSymbolOfPolynomial_coordinate b ω hlayers v
      (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) ⟨(α, i), h⟩
    rw [hc, hs, repr_coefficients_ofCoordinates, repr_coefficients_ofCoordinates,
      coeff_weightedHomogeneousComponent, if_pos h]
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers v _ α i h,
      repr_coefficients_ofCoordinates, coeff_weightedHomogeneousComponent, if_neg h]

end NilpotentLieFiltration

end Erdos3

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

theorem homogeneousAssociatedGradedEquiv_pieceMap
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (j : ℕ) (x : F.layer j) :
    F.homogeneousAssociatedGradedEquiv b ω hF hb (F.associatedGradedPieceMap j x) =
      basisGradeProjection b ω j x.val :=
  F.associatedGradedPieceMap_repr_symm b ω hF j x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realGradedSymbolPolynomial_gradeProjection_coefficient
    (d : ℕ) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x)) α =
      basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
        (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases h : Finsupp.weight w α = ω i
  · rw [F.realGradedSymbolPolynomial_coordinate b ω hlayers w _ ⟨(α, i), h⟩,
      basisGradeProjection_repr,
      F.realGradedSymbolPolynomial_coordinate b ω hlayers w x ⟨(α, i), h⟩]
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w _ α i h,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w x α i h]
    simp

theorem realGradedSymbolPolynomial_gradeProjection
    (d : ℕ) (x : F.RealPolynomialSymbol w) :
    F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x) =
      VectorPolynomial.map
        ((basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ)
          ω d).restrictScalars ℚ)
        (F.realGradedSymbolPolynomial b ω hlayers w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact F.realGradedSymbolPolynomial_gradeProjection_coefficient b ω hlayers w d x α

theorem realGradedSymbolPolynomial_gradeProjection_homogeneous
    (d : ℕ) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ)
    (hα : Finsupp.weight w α ≠ d) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x)) α = 0 := by
  rw [F.realGradedSymbolPolynomial_gradeProjection_coefficient]
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  simp only [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
  split_ifs with hi
  · exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w x α i
      (fun h => hα (h.trans hi))
  · rfl

theorem realGradedSymbolPolynomial_eval₂_gradeProjection
    (d : ℕ) (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x)) =
      basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
        (eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) := by
  rw [F.realGradedSymbolPolynomial_gradeProjection, eval₂_map]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
namespace OAI

section

namespace Erdos3

theorem exists_common_intersection_corrections
    {ι κ ν σ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β e₁ e₂ q₁ q₂ : ι → ℝ),
        β - e₁ - q₁ ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) →
        β - e₂ - q₂ ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) →
        ‖e₁‖ ≤ Real.exp p / monomialScale T α →
        ‖e₂ - e₁‖ ≤ Real.exp p / monomialScale T α →
        q₁ ∈ realDenominatorGrid l → q₂ ∈ realDenominatorGrid l →
        ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β - e - q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ⊓
            LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := by
  obtain ⟨m, hm, hmp, hsolve⟩ := exists_image_intersection_corrections A B hH hl hA hB hp
    hι hcols hHp hlp T hT
  refine ⟨l * m, Nat.mul_pos hl hm, ?_, dvd_mul_right l m, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα β e₁ e₂ q₁ q₂ h₁ h₂ he₁ he₂ hq₁ hq₂
    have hdiff : (β - e₁ - q₁) - (β - e₂ - q₂) = (e₂ - e₁) + (q₂ - q₁) := by abel
    obtain ⟨e, q, _, _, he, hq, hrem⟩ := hsolve α hα (e₂ - e₁) (q₂ - q₁)
      (β - e₁ - q₁) (β - e₂ - q₂) h₁ h₂ he₂
      (realDenominatorGrid_sub l q₂ q₁ hq₂ hq₁) hdiff
    refine ⟨e₁ + e, q₁ + q, ?_, ?_, ?_⟩
    · calc
        ‖e₁ + e‖ ≤ ‖e₁‖ + ‖e‖ := norm_add_le _ _
        _ ≤ Real.exp p / monomialScale T α +
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α :=
          add_le_add he₁ he
        _ = _ := (add_div _ _ _).symm
    · simpa only [sub_neg_eq_add] using
        realDenominatorGrid_sub_product l m q₁ (-q) hq₁ (realDenominatorGrid_neg m hq)
    · have heq : β - (e₁ + e) - (q₁ + q) = (β - e₁ - q₁) - e - q := by abel
      rwa [heq]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_basis_intersection_correction
    {μ κ ν σ L : Type*} [Fintype μ] [Fintype κ] [Fintype ν]
    [LieRing L] [LieAlgebra ℚ L]
    (b : Basis μ ℚ L) (U V : Submodule ℚ L) (v : κ → L) (w : ν → L)
    (hv : Submodule.span ℚ (Set.range v) = U) (hw : Submodule.span ℚ (Set.range w) = V)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a i, RationalHeightLE (b.repr (v a) i) H)
    (hwH : ∀ a i, RationalHeightLE (b.repr (w a) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (x e q : ℝ ⊗[ℚ] L),
        x - e - q ∈ U.baseChange ℝ → x ∈ V.baseChange ℝ →
        ‖(b.baseChange ℝ).equivFun e‖ ≤ Real.exp p / monomialScale T α →
        (b.baseChange ℝ).equivFun q ∈ realDenominatorGrid l →
        ∃ E Q : ℝ ⊗[ℚ] L,
          ‖(b.baseChange ℝ).equivFun E‖ ≤
            (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) / monomialScale T α ∧
          (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m ∧
          x - E - Q ∈ (U ⊓ V).baseChange ℝ := by
  let B := (b.baseChange ℝ).equivFun
  let A : Matrix μ κ ℚ := fun i a => b.repr (v a) i
  let C : Matrix μ ν ℚ := fun i a => b.repr (w a) i
  have hU (x : ℝ ⊗[ℚ] L) : x ∈ U.baseChange ℝ ↔
      B x ∈ LinearMap.range (Matrix.mulVecLin (fun i a => (A i a : ℝ))) := by
    rw [← real_span_rational_family U v hv, real_span_family_mem_iff_coordinates b v,
      real_column_span_mem_iff A]
  have hV (x : ℝ ⊗[ℚ] L) : x ∈ V.baseChange ℝ ↔
      B x ∈ LinearMap.range (Matrix.mulVecLin (fun i a => (C i a : ℝ))) := by
    rw [← real_span_rational_family V w hw, real_span_family_mem_iff_coordinates b w,
      real_column_span_mem_iff C]
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_common_intersection_corrections A C hH hl
    (fun i a => hvH a i) (fun i a => hwH a i) hp hμ hcols hHp hlp T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα x e q hxU hxV he hq
  have hu : B x - B e - B q ∈
      LinearMap.range (Matrix.mulVecLin (fun i a => (A i a : ℝ))) := by
    simpa only [map_sub] using (hU (x - e - q)).mp hxU
  have hz : B x - 0 - 0 ∈
      LinearMap.range (Matrix.mulVecLin (fun i a => (C i a : ℝ))) := by
    simpa only [sub_zero] using (hV x).mp hxV
  obtain ⟨E, Q, hE, hQ, hmem⟩ := hsolve α hα (B x) (B e) 0 (B q) 0 hu hz he
    (by simpa only [zero_sub, norm_neg] using he) hq (realDenominatorGrid_zero l)
  refine ⟨B.symm E, B.symm Q, ?_, ?_, ?_⟩
  · change ‖B (B.symm E)‖ ≤ _
    rw [B.apply_symm_apply]
    exact hE
  · change B (B.symm Q) ∈ _
    rw [B.apply_symm_apply]
    exact hQ
  · rw [realification_inf]
    constructor
    · apply (hU _).mpr
      rw [map_sub, map_sub, B.apply_symm_apply, B.apply_symm_apply]
      exact hmem.1
    · apply (hV _).mpr
      rw [map_sub, map_sub, B.apply_symm_apply, B.apply_symm_apply]
      exact hmem.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem scalarExtension_coordinate_norm_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (q : V →ₗ[ℚ] W) {p : ℝ}
    (hd : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (f.repr (q (e j)) i) ≤ p) (x : ℝ ⊗[ℚ] V) :
    ‖(f.baseChange ℝ).equivFun (q.baseChange ℝ x)‖ ≤
      Real.exp (2 * p) * ‖(e.baseChange ℝ).equivFun x‖ := by
  have h := linearMap_coordinate_norm_le (e.baseChange ℝ) (f.baseChange ℝ) (q.baseChange ℝ)
    ⟨Real.exp p, Real.exp_nonneg p⟩ (fun i j => by
      rw [scalarExtension_basis_coordinates]
      exact (rational_abs_real_le_numerator _).trans ((rationalLogHeight_le_iff _ _).mp (hentries i j)).1) x
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    (Fintype.card ι : ℝ) * Real.exp p ≤ Real.exp p * Real.exp p :=
      mul_le_mul_of_nonneg_right (hd.trans (by linarith [Real.add_one_le_exp p])) (Real.exp_nonneg _)
    _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring

theorem scalarExtension_coordinate_dist_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (q : V →ₗ[ℚ] W) {p : ℝ}
    (hd : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (f.repr (q (e j)) i) ≤ p) (x y : ℝ ⊗[ℚ] V) :
    dist ((f.baseChange ℝ).equivFun (q.baseChange ℝ x))
      ((f.baseChange ℝ).equivFun (q.baseChange ℝ y)) ≤
      Real.exp (2 * p) * dist ((e.baseChange ℝ).equivFun x) ((e.baseChange ℝ).equivFun y) := by
  simpa only [map_sub, ← dist_eq_norm] using scalarExtension_coordinate_norm_le e f q hd hentries (x - y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_eval_integer (T : D.Niltest (fun _ : σ => 1))
    (a : ℤ) (shift x : σ → ℤ) :
    (T.scalarAffinePullback a (fun i => (shift i : ℚ))).eval x =
      T.eval (fun i => a * x i + shift i) := by
  apply T.eval_substitute (scalarAffinePolynomial (a : ℚ) (fun i => (shift i : ℚ)))
    (scalarAffinePolynomial_support _ _) x (fun i => a * x i + shift i)
  intro i
  simp [scalarAffinePolynomial, add_comm]

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)

noncomputable def source : FiniteProbabilityWeights (IntegerScalarCubeBox I s.length) :=
  s.baseLaw.reweight (fun z => s.weight (fun i => (z i : ℝ) / s.length))
    (fun z => (s.weight_range (fun i => (z i : ℝ) / s.length)).1) s.normalized

end NormalizedScalarCubeSource

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReducedTwistedTranslationBudget
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal

theorem exists_weightedTranslationBuffered_scalar_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n N : ℕ) (p L M : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → N ≤ n + (n + 1) ^ d →
      0 ≤ L → 0 ≤ M → L ≤ Real.exp p → M ≤ Real.exp p →
      ((n + (n + 1) ^ d + d.factorial + 2 * d + 1 : ℕ) : ℝ) ≤ (p + C) ^ C ∧
      2 * max (8 * weightedTranslationDisplacementConstant d n N)
        ((L + 2 * Real.pi * (1 + M * n * d)) *
          weightedTranslationDisplacementConstant d n N) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨Z, hZ, hlog⟩ := exists_bchLogMetricConstant_exp_bound d
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + 1) ^ d + Polynomial.C (d.factorial + 2 * d + 1)
  let K := Polynomial.C d *
    (1 + (X + 1) * (Polynomial.C (d + 1) * (X + 2) ^ d) * Polynomial.C d) ^ d
  let P := Q + K + (Q + Polynomial.C Z) ^ Z + 3 * X + Polynomial.C (d + 15)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro n N p L M hp hn hN hL hM hLp hMp
  let q : ℝ := p + (p + 1) ^ d + (d.factorial + 2 * d + 1 : ℕ)
  let k : ℝ := d * (1 + (p + 1) * (((d : ℝ) + 1) * (p + 2) ^ d) * d) ^ d
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have htotal : q + k + (q + Z) ^ Z + 3 * p + (d + 15 : ℕ) ≤ (p + C) ^ C := by
    simpa [X, Q, K, P, q, k, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul] using hbudget p hp
  have hgeom : ((n + (n + 1) ^ d + d.factorial + 2 * d + 1 : ℕ) : ℝ) ≤ q := by
    have hpow : ((n : ℝ) + 1) ^ d ≤ (p + 1) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    dsimp [q]
    push_cast
    linarith
  have hdim : (N : ℝ) ≤ q := by
    apply (Nat.cast_le.mpr hN).trans
    have hh : ((n + (n + 1) ^ d : ℕ) : ℝ) ≤
        ((n + (n + 1) ^ d + d.factorial + 2 * d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n + (n + 1)^d ≤ n + (n+1)^d + d.factorial + 2*d + 1)
    exact hh.trans hgeom
  have hHq : ((2 * d + 1 : ℕ) : ℝ) ≤ q := by
    dsimp [q]
    have hd0 := Nat.cast_nonneg (α := ℝ) d.factorial
    have hpow : 0 ≤ (p + 1) ^ d := by positivity
    push_cast
    linarith
  have hHexp : ((2 * d + 1 : ℕ) : ℝ) ≤ Real.exp q :=
    hHq.trans (by linarith [Real.add_one_le_exp q])
  have hlogbound := hlog N (2 * d + 1) q hq hdim hHexp
  have hshear : (polynomialShearDisplacementBound d (n + 1) 1 : ℝ) ≤ k := by
    dsimp [polynomialShearDisplacementBound, k]
    push_cast
    simp only [one_pow, mul_one]
    simp only [add_assoc, one_add_one_eq_two]
    gcongr
  have hshear1 : (polynomialShearDisplacementBound d (n + 1) 1 : ℝ) + 1 ≤ Real.exp k := by
    linarith [Real.add_one_le_exp k]
  have hv : 0 ≤ (q + Z) ^ Z + 1 := by positivity
  have hlog1 : (bchLogMetricConstant d N (2 * d + 1) 1 : ℝ) + 1 ≤
      Real.exp ((q + Z) ^ Z + 2) := by
    have hh := one_add_le_exp_succ hv hlogbound
    simpa only [add_comm (1 : ℝ), add_assoc, one_add_one_eq_two] using hh
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hdisp : weightedTranslationDisplacementConstant d n N ≤
      Real.exp (k + (q + Z) ^ Z + 3) := by
    unfold weightedTranslationDisplacementConstant
    calc
      _ ≤ Real.exp 1 * Real.exp k * Real.exp ((q + Z) ^ Z + 2) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hnp : (n : ℝ) ≤ Real.exp p := hn.trans (by linarith [Real.add_one_le_exp p])
  have hdp : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hprod : M * (n : ℝ) * d ≤ Real.exp (2 * p + d) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp d := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hprod1 : 1 + M * (n : ℝ) * d ≤ Real.exp (2 * p + d + 1) :=
    one_add_le_exp_succ (by positivity) hprod
  have hpi : 2 * Real.pi ≤ Real.exp 8 := by
    have hp4 := Real.pi_le_four
    linarith [Real.add_one_le_exp (8 : ℝ)]
  have hphase : 2 * Real.pi * (1 + M * (n : ℝ) * d) ≤ Real.exp (2 * p + d + 9) := by
    calc
      _ ≤ Real.exp 8 * Real.exp (2 * p + d + 1) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum : L + 2 * Real.pi * (1 + M * (n : ℝ) * d) ≤ Real.exp (3 * p + d + 10) := by
    have hh := add_le_exp_add_one hp (by positivity : 0 ≤ 2 * p + d + 9) hLp hphase
    convert hh using 1; congr 1; ring
  have height : (8 : ℝ) ≤ Real.exp (3 * p + d + 10) := by
    have hh := Real.add_one_le_exp (3 * p + d + 10)
    have hd0 := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hmax : max (8 * weightedTranslationDisplacementConstant d n N)
      ((L + 2 * Real.pi * (1 + M * n * d)) * weightedTranslationDisplacementConstant d n N) ≤
        Real.exp (3 * p + d + 10) * Real.exp (k + (q + Z) ^ Z + 3) := by
    apply max_le
    · exact mul_le_mul height hdisp (weightedTranslationDisplacementConstant_pos _ _ _).le (Real.exp_nonneg _)
    · exact mul_le_mul hsum hdisp (weightedTranslationDisplacementConstant_pos _ _ _).le (Real.exp_nonneg _)
  constructor
  · apply hgeom.trans
    have hz : 0 ≤ (q + Z) ^ Z := by positivity
    have hd0 := Nat.cast_nonneg (α := ℝ) (d + 15)
    linarith
  · calc
      _ ≤ 2 * (Real.exp (3 * p + d + 10) * Real.exp (k + (q + Z) ^ Z + 3)) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ ≤ Real.exp 1 * (Real.exp (3 * p + d + 10) * Real.exp (k + (q + Z) ^ Z + 3)) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp (k + (q + Z) ^ Z + 3 * p + d + 14) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((p + C) ^ C) := by
        apply Real.exp_le_exp.mpr
        push_cast at htotal
        linarith

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem exists_submodule_intersection_basis_logHeight
    {ι κ J V : Type*} [Fintype ι] [Fintype κ] [Fintype J]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : J → Submodule ℚ V) (v : J → κ → V)
    (hv : ∀ j, Submodule.span ℚ (Set.range (v j)) = U j)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hheight : ∀ j a i, rationalLogHeight (b.repr (v j a) i) ≤ p) :
    ∃ n : ℕ, n ≤ Fintype.card ι ∧ ∃ bw : Basis (Fin n) ℚ ↥(⨅ j, U j : Submodule ℚ V),
      ∀ a i, rationalLogHeight (b.repr (bw a : V) i) ≤ ((p + 2) ^ 2 + 2) ^ 63 := by
  classical
  let A : J → Matrix ι κ ℚ := fun j i k => b.equivFun (v j k) i
  let W := ⨅ j, U j
  let Wc : Submodule ℚ (ι → ℚ) := ⨅ j, LinearMap.range (A j).mulVecLin
  have hA (j : J) : LinearMap.range (A j).mulVecLin = (U j).map b.equivFun.toLinearMap := by
    rw [← hv j, Submodule.map_span, ← Set.range_comp]
    exact Matrix.range_mulVecLin _
  have hmem (x : V) : b.equivFun x ∈ Wc ↔ x ∈ W := by
    simp only [Wc, W, Submodule.mem_iInf]
    constructor
    · intro hx j
      obtain ⟨y, hy, he⟩ := hA j ▸ hx j
      exact b.equivFun.injective he ▸ hy
    · intro hx j
      rw [hA j]
      exact ⟨x, hx j, rfl⟩
  let e : W ≃ₗ[ℚ] Wc :=
    { toFun := fun x => ⟨b.equivFun x, (hmem x).mpr x.property⟩
      invFun := fun x => ⟨b.equivFun.symm x, (hmem _).mp (by
        simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
      map_add' := fun x y => Subtype.ext (b.equivFun.map_add x y)
      map_smul' := fun c x => Subtype.ext (b.equivFun.map_smul c x)
      left_inv := fun x => Subtype.ext (b.equivFun.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (b.equivFun.apply_symm_apply x) }
  let q := (p + 2) ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hp1q : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcols : ((∑ _j : J, Fintype.card κ : ℕ) : ℝ) ≤ q := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
    have hprod := mul_le_mul hJ hκ (Nat.cast_nonneg _) hp
    dsimp [q]
    nlinarith
  obtain ⟨bc, hbc⟩ := exists_image_intersection_basis_exp_height A (one_le_ceil_exp p)
    (fun j i k => rationalHeightLE_ceil_exp (hheight j k i)) hq
    (hJ.trans hpq) (hι.trans hpq) hcols
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1q))
  refine ⟨finrank ℚ Wc, ?_, bc.map e.symm, ?_⟩
  · simpa using Submodule.finrank_le Wc
  · intro a i
    change rationalLogHeight (b.repr (b.equivFun.symm (bc a : ι → ℚ)) i) ≤ _
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    exact (rationalLogHeight_le_iff _ _).mpr (hbc a i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3

theorem halvingPolynomial_support {σ : Type*} (r : σ → ℤ) (i : σ) :
    halvingPolynomial r i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  have hx : (MvPolynomial.X i : MvPolynomial σ ℚ) ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : σ => 1) (Finsupp.single i 1) (1 : ℚ)
  simpa only [halvingPolynomial, zero_add] using
    weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 (1 / 2 : ℚ))
      (Submodule.sub_mem _ hx (weightedSupportLE_C _ 1 (r i : ℚ)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymbolRepresentativeTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ M : Type*} [Fintype ι] [Fintype κ] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration M s) (b : Basis ι ℚ M) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : Basis κ ℚ M)

omit [Fintype κ] in
theorem realSymbolRepresentative_slow_original_coordinates (w : σ → ℕ)
    (T : σ → ℝ) (hT : ∀ j, 0 < T j) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p)
    (E : F.RealPolynomialSymbolGroup w) (hE : F.SymbolSlowBound b ω hF w T (Real.exp p) E)
    (α : σ →₀ ℕ) (i : κ) :
    |(e.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hF w E.coord) α) i| ≤
      Real.exp ((p + 3) ^ 2) / monomialScale T α := by
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hdim' : (Fintype.card ι : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have hbound : (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p ≤ Real.exp ((p + 3) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (3 * p + 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  calc
    _ ≤ (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * (Real.exp p / monomialScale T α) :=
      real_basis_coordinates_bound b e (fun i j => rationalHeightLE_ceil_exp (hentries j i)) _
        (fun j => F.realSymbolRepresentative_slow_coefficients b ω hF w T hT
          (Real.exp_pos p).le E hE α j) i
    _ = ((Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p) / monomialScale T α := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbound (monomialScale_pos T hT α).le

theorem original_coordinate_denominator_bound {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hentries : ∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p)
    (l : ℕ) (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator (fun i j => e.repr (b j) i) * l : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 3 + p) := by
  have hD : (matrixDenominator (fun i j => e.repr (b j) i) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power (fun i j => e.repr (b j) i) hp 1 hκ hι
    intro i j
    exact ((rationalLogHeight_le_iff _ _).mp (hentries j i)).2.trans
      (Real.exp_le_exp.mpr (by simp))
  rw [Nat.cast_mul]
  exact (mul_le_mul hD hl (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MissingCoordinateDownsets
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem missingCoordinateDownset_terminal {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (a : Fin (s + 1) →₀ ℕ)
    (ha : ∀ i, a ∉ missingCoordinateDownset s i) :
    (F.totalDegreeMultifiltration (Fin (s + 1))).layer (fun j => a j) = ⊥ := by
  apply F.layer_eq_bot_above_step
  apply Nat.lt_of_not_ge
  intro h
  obtain ⟨i, hi⟩ := missingCoordinateDownset_covers s a h
  exact ha i hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem conjugate_vertical (T : D.Niltest w) (eta : L →ₗ[ℚ] ℚ)
    (hvert : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      T.observable (z • x) = CircleFourier.character
        ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x)
    (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s) (x : D.Space) :
    T.conjugate.observable (z • x) = CircleFourier.character
      ((realifyFunctional (-eta) z.coord : ℝ) : CircleFourier.Circle) * T.conjugate.observable x := by
  change star (T.observable (z • x)) = _ * star (T.observable x)
  rw [hvert z hz x, star_mul, realifyFunctional_neg, AddCircle.coe_neg, CircleFourier.character_neg]
  exact mul_comm _ _

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTagConstraintSpaces
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem exists_finite_rational_tag_constraints
    (p : ℝ) (_hp : 0 ≤ p) (d : ℕ) (hJ : ∀ j, Fintype.card (J j) ≤ d) :
    ∃ n : ℕ,
      n ≤ m * (⌊p⌋₊ + 1) *
        (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (⌊p⌋₊ * d)) ∧
      ∃ candidate : Fin n → RationalTagConstraint J,
        (∀ i, (candidate i).BudgetLE p) ∧
        ∀ c : RationalTagConstraint J, c.BudgetLE p → ∃ i, candidate i = c := by
  classical
  let N := ⌊p⌋₊
  let H := ⌈Real.exp p⌉₊
  let R := boundedRationalCandidates H
  let Code := Σ j : Fin m, Σ n : Fin (N + 1), (Fin n.val × J j → R)
  let raw : Code → RationalTagConstraint J := fun c =>
    { tag := c.1, count := c.2.1.val,
      generators := fun a i => (c.2.2 (a, i)).val }
  have hR : R.card ≤ (2 * H + 1) * (H + 1) := boundedRationalCandidates_card H
  have hcard : Fintype.card Code ≤
      m * (N + 1) * (((2 * H + 1) * (H + 1)) ^ (N * d)) := by
    dsimp only [Code]
    simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe]
    calc
      _ ≤ ∑ _j : Fin m, ∑ _n : Fin (N + 1),
          ((2 * H + 1) * (H + 1)) ^ (N * d) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro n _
        exact (Nat.pow_le_pow_left hR _).trans
          (Nat.pow_le_pow_right (by positivity)
            (Nat.mul_le_mul (Nat.le_of_lt_succ n.isLt) (hJ j)))
      _ = _ := by simp [Nat.mul_assoc]
  let e := Fintype.equivFin Code
  let candidates := fun i : Fin (Fintype.card Code) => raw (e.symm i)
  have hcover (c : RationalTagConstraint J) (hc : c.BudgetLE p) :
      ∃ i, candidates i = c := by
    have hcN : c.count ≤ N := Nat.le_floor hc.1
    let v : Code := ⟨c.tag, ⟨c.count, Nat.lt_succ_of_le hcN⟩,
      fun a => ⟨c.generators a.1 a.2,
        mem_boundedRationalCandidates (rationalHeightLE_ceil_exp (hc.2 a.1 a.2))⟩⟩
    refine ⟨e v, ?_⟩
    simp only [candidates, Equiv.symm_apply_apply]
    rfl
  obtain ⟨n, hn, candidate, hvalid, _, hcomplete⟩ :=
    exists_filtered_finite_enumeration candidates (fun c => c.BudgetLE p)
  exact ⟨n, hn.trans hcard, candidate, hvalid, fun c hc => hcomplete c hc (hcover c hc)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem exists_finite_rational_tag_constraint_lists
    (p : ℝ) (hp : 0 ≤ p) (N : ℕ)
    (hm : (m : ℝ) ≤ p) (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hN : (N : ℝ) ≤ p) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + 8) ^ 8) ∧
      ∃ candidate : Fin n → List (RationalTagConstraint J),
        (∀ i, (candidate i).length ≤ N) ∧
        (∀ i c, c ∈ candidate i → c.BudgetLE p) ∧
        ∀ cs : List (RationalTagConstraint J), cs.length ≤ N →
          (∀ c ∈ cs, c.BudgetLE p) → ∃ i, candidate i = cs := by
  classical
  let d := Fintype.card (Σ j, J j)
  have hdim (j : Fin m) : Fintype.card (J j) ≤ d :=
    Fintype.card_le_of_injective (Sigma.mk j) sigma_mk_injective
  obtain ⟨M, hM, entries, hentries, hcover⟩ :=
    exists_finite_rational_tag_constraints p hp d hdim
  obtain ⟨n, hn, candidate, hlen, hvalid, hcomplete⟩ :=
    exists_finite_bounded_list_enumeration entries (fun c => c.BudgetLE p) hentries hcover N
  have hcount : (n : ℝ) ≤ Real.exp ((p + 8) ^ 8) := by
    apply le_trans _ (rationalConstraint_list_count_le_exp_of_le M m ⌊p⌋₊ d N
      hp hm (Nat.floor_le hp) hJ hN hM)
    exact_mod_cast hn.trans (Nat.pow_le_pow_right (by omega : 0 < M + 1) (Nat.le_succ N))
  exact ⟨n, hcount, candidate, hlen, hvalid, hcomplete⟩

theorem exists_finite_rational_tagged_certificate_sets
    {X : Type*} (Kinitial : Set ((X ⊕ (Σ j, J j)) → ℝ))
    (p : ℝ) (hp : 0 ≤ p) (N : ℕ)
    (hm : (m : ℝ) ≤ p) (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hN : (N : ℝ) ≤ p) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + 8) ^ 8) ∧
      ∃ candidate : Fin n → Set ((X ⊕ (Σ j, J j)) → ℝ),
        (∀ i, RationalTaggedConstraintCertificate J Kinitial (candidate i) p N) ∧
        ∀ K, RationalTaggedConstraintCertificate J Kinitial K p N →
          ∃ i, candidate i = K := by
  obtain ⟨n, hn, lists, hlen, hvalid, hcomplete⟩ :=
    exists_finite_rational_tag_constraint_lists p hp N hm hJ hN
  let sets := fun i : Fin n => Kinitial ∩ {t | ∀ c ∈ lists i, c.member t}
  refine ⟨n, hn, sets, ?_, ?_⟩
  · intro i
    exact ⟨lists i, hlen i, hvalid i, rfl⟩
  · intro K hK
    obtain ⟨cs, hcs, hbudget, hidentity⟩ := hK
    obtain ⟨i, hi⟩ := hcomplete cs hcs hbudget
    refine ⟨i, ?_⟩
    dsimp only [sets]
    rw [hi]
    exact hidentity.symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem exists_finite_rational_stage_branches {X : Type*}
    (Kinitial : Set ((X ⊕ (Σ j, J j)) → ℝ)) (p qlog : ℝ) (hp : 0 ≤ p)
    (N : ℕ) (hm : (m : ℝ) ≤ p) (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hN : (N : ℝ) ≤ p) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (qlog + (p + 8) ^ 8) ∧
      ∃ candidate : Fin n → ℕ × Set ((X ⊕ (Σ j, J j)) → ℝ),
        (∀ i, 0 < (candidate i).1 ∧ (candidate i).1 ≤ ⌊Real.exp qlog⌋₊ ∧
          RationalTaggedConstraintCertificate J Kinitial (candidate i).2 p N) ∧
        ∀ (q : ℕ) K, 0 < q → (q : ℝ) ≤ Real.exp qlog →
          RationalTaggedConstraintCertificate J Kinitial K p N →
          ∃ i, candidate i = (q, K) := by
  classical
  obtain ⟨nK, hnK, spaces, hspace, hcover⟩ :=
    exists_finite_rational_tagged_certificate_sets Kinitial p hp N hm hJ hN
  let Q : ℕ := ⌊Real.exp qlog⌋₊
  let Index := Fin Q × Fin nK
  let e : Index ≃ Fin (Fintype.card Index) := Fintype.equivFin Index
  let candidate := fun i : Fin (Fintype.card Index) =>
    ((e.symm i).1.val + 1, spaces (e.symm i).2)
  refine ⟨Fintype.card Index, ?_, candidate, ?_, ?_⟩
  · have hQ : (Q : ℝ) ≤ Real.exp qlog := Nat.floor_le (Real.exp_nonneg _)
    change ((Fintype.card (Fin Q × Fin nK) : ℕ) : ℝ) ≤ _
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul hQ hnK (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
      (Real.exp_add _ _).symm
  · intro i
    refine ⟨Nat.succ_pos _, ?_, hspace _⟩
    exact (e.symm i).1.isLt
  · intro q K hq hqcap hK
    obtain ⟨j, hj⟩ := hcover K hK
    have hqQ : q ≤ Q := Nat.le_floor hqcap
    let code : Index := (⟨q - 1, by omega⟩, j)
    refine ⟨e code, ?_⟩
    change ((e.symm (e code)).1.val + 1, spaces (e.symm (e code)).2) = (q, K)
    rw [Equiv.symm_apply_apply]
    exact Prod.ext (by dsimp [code]; omega) hj

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.RationalTagConstraint

open Module

variable {m : ℕ} {J : Fin m → Type*}

noncomputable def rationalSpace (c : RationalTagConstraint J) (j : Fin m) :
    Submodule ℚ (J j → ℚ) :=
  if h : j = c.tag then h.symm ▸ Submodule.span ℚ (Set.range c.generators) else ⊤

@[simp] theorem rationalSpace_self (c : RationalTagConstraint J) :
    c.rationalSpace c.tag = Submodule.span ℚ (Set.range c.generators) := by
  simp [rationalSpace]

theorem rationalSpace_of_ne (c : RationalTagConstraint J) {j : Fin m} (hj : j ≠ c.tag) :
    c.rationalSpace j = ⊤ := by
  simp only [rationalSpace, dif_neg hj]

end Erdos3.VectorPolynomial.RationalTagConstraint

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {η B κ : Type*} [Fintype η] [Fintype B]

theorem realRationalCoordinateSpan_iInf_basis (U : η → Submodule ℚ (B → ℚ))
    (b : Basis κ ℚ ↥(⨅ a, U a)) :
    Submodule.span ℝ (Set.range (fun i j => ((b i : B → ℚ) j : ℝ))) =
      ⨅ a, realRationalCoordinateSpan (U a) := by
  have hb : Submodule.span ℚ (Set.range (fun i => (b i : B → ℚ))) = ⨅ a, U a := by
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def, Submodule.subtype_apply,
      Submodule.map_top, Submodule.range_subtype] using
      congrArg (Submodule.map (⨅ a, U a).subtype) b.span_eq
  exact (realRationalCoordinateSpan_span (fun i => (b i : B → ℚ))).symm.trans
    ((congrArg realRationalCoordinateSpan hb).trans (realRationalCoordinateSpan_iInf U))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def rationalTagConstraintIntersection (cs : List (RationalTagConstraint J))
    (j : Fin m) : Submodule ℚ (J j → ℚ) :=
  ⨅ i : Fin cs.length, (cs.get i).rationalSpace j

theorem constraint_realSpaces_member_iff {X : Type*}
    (c : RationalTagConstraint J) (point : (X ⊕ (Σ j, J j)) → ℝ) :
    (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ realRationalCoordinateSpan (c.rationalSpace j)) ↔
      c.member point := by
  constructor
  · intro h
    simpa only [RationalTagConstraint.rationalSpace_self, realRationalCoordinateSpan_span,
      RationalTagConstraint.member] using h c.tag
  · intro h j
    by_cases hj : j = c.tag
    · subst j
      simpa only [RationalTagConstraint.rationalSpace_self, realRationalCoordinateSpan_span,
        RationalTagConstraint.member] using h
    · rw [c.rationalSpace_of_ne hj, realRationalCoordinateSpan_top]
      trivial

theorem rationalTagConstraintList_basis_member_iff {X : Type*}
    (cs : List (RationalTagConstraint J)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (rationalTagConstraintIntersection cs j))
    (point : (X ⊕ (Σ j, J j)) → ℝ) :
    (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
      Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))) ↔
      ∀ c ∈ cs, c.member point := by
  have hspan (j : Fin m) :
      Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ))) =
        ⨅ k : Fin cs.length, realRationalCoordinateSpan ((cs.get k).rationalSpace j) :=
    realRationalCoordinateSpan_iInf_basis
      (fun k : Fin cs.length => (cs.get k).rationalSpace j) (b j)
  simp_rw [hspan, Submodule.mem_iInf]
  constructor
  · intro h c hc
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hc
    apply (constraint_realSpaces_member_iff c point).mp
    intro j
    simpa only [hk] using h j k
  · intro h j k
    exact (constraint_realSpaces_member_iff (cs.get k) point).mpr
      (h _ (List.get_mem _ _)) j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateEstimates
namespace OAI

section

namespace Erdos3

theorem nativeCoordinate_denominator_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ] (s : ℕ) {P : ℝ} (hP : 0 ≤ P)
    (A : Matrix ι κ ℚ) (l : ℕ) (hl : (l : ℝ) ≤ Real.exp P)
    (hrows : (Fintype.card ι : ℝ) ≤ P) (hcols : (Fintype.card κ : ℝ) ≤ P)
    (hA : ∀ i j, rationalLogHeight (A i j) ≤ (P + 3) ^ 7) :
    ((matrixDenominator A * l : ℕ) : ℝ) ≤ Real.exp (nativeCoordinateInputBudget s P) := by
  obtain ⟨hU, _, hPU, hFU, _, _⟩ := nativeCoordinateBaseBudget_bounds s hP
  have hden : (matrixDenominator A : ℝ) ≤ Real.exp ((nativeCoordinateBaseBudget s P + 2) ^ 3) :=
    matrixDenominator_le_exp_power A hU 1 (hrows.trans hPU) (hcols.trans hPU) (by
      intro i j
      apply ((rationalLogHeight_le_iff (A i j) _).mp (hA i j)).2.trans
      apply Real.exp_le_exp.mpr
      simp only [pow_one]
      linarith)
  rw [Nat.cast_mul]
  calc
    (matrixDenominator A : ℝ) * l ≤
        Real.exp ((nativeCoordinateBaseBudget s P + 2) ^ 3) * Real.exp P :=
      mul_le_mul hden hl (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((nativeCoordinateBaseBudget s P + 2) ^ 3 + P) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (nativeCoordinateInputBudget_bounds s hP).2.1

theorem nativeCoordinate_slow_bound (s : ℕ) {P p : ℝ} (hP : 0 ≤ P) (hpP : p ≤ P)
    (n K : ℕ) (hn : (n : ℝ) ≤ P) (hK : (K : ℝ) ≤ Real.exp ((P + 3) ^ 7 + 1)) :
    2 * (((n : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤
      Real.exp (nativeCoordinateInputBudget s P) := by
  obtain ⟨hU, _, hPU, hFU, _, hSU⟩ := nativeCoordinateBaseBudget_bounds s hP
  let U := nativeCoordinateBaseBudget s P
  have hKU : (K : ℝ) ≤ Real.exp ((U + 2) ^ 1) := by
    apply hK.trans
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  have hfac : ((n : ℝ) + 1) * (K + 1) ≤ Real.exp ((U + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power n hU (hn.trans hPU) 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hKU le_rfl) (by positivity)
  have hSU' : (P + 3) ^ 2 + (s : ℝ) * p ≤ U :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpP (Nat.cast_nonneg s))).trans hSU
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    2 * (((n : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤
        Real.exp 1 * (Real.exp ((U + 2) ^ 3) * Real.exp U) :=
      mul_le_mul htwo (mul_le_mul hfac (Real.exp_le_exp.mpr hSU')
        (Real.exp_pos _).le (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
    _ = Real.exp (1 + (U + 2) ^ 3 + U) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (nativeCoordinateInputBudget_bounds s hP).2.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DependentCoordinateCorrections
namespace OAI

section

namespace Erdos3

theorem exists_coordinate_intersection_corrections
    {ι κ ν σ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (U V : Submodule ℚ (ι → ℚ)) (v : κ → ι → ℚ) (w : ν → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = U) (hw : Submodule.span ℚ (Set.range w) = V)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a i, RationalHeightLE (v a i) H) (hwH : ∀ a i, RationalHeightLE (w a i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β e₁ e₂ q₁ q₂ : ι → ℝ),
        β - e₁ - q₁ ∈ realRationalCoordinateSpan U →
        β - e₂ - q₂ ∈ realRationalCoordinateSpan V →
        ‖e₁‖ ≤ Real.exp p / monomialScale T α →
        ‖e₂ - e₁‖ ≤ Real.exp p / monomialScale T α →
        q₁ ∈ realDenominatorGrid l → q₂ ∈ realDenominatorGrid l →
        ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β - e - q ∈ realRationalCoordinateSpan (U ⊓ V) := by
  simpa only [realRationalCoordinateSpan_inf, realRationalCoordinateSpan_eq_image U v hv,
    realRationalCoordinateSpan_eq_image V w hw] using
    exists_common_intersection_corrections (fun i a => v a i) (fun i a => w a i)
      hH hl (fun i a => hvH a i) (fun i a => hwH a i) hp hι hcols hHp hlp T hT

end Erdos3

end

section

namespace Erdos3

theorem exists_dependent_coordinate_corrections
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (v : κ → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (h₁₂ : (Fintype.card (Σ _ : ({1, 2} : Finset (Fin 4)), ι) : ℝ) ≤ p)
    (h₁₃ : (Fintype.card (Σ _ : ({1, 3} : Finset (Fin 4)), ι) : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ κ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ)
    (hT : ∀ i, Real.exp (separationBudget (p + sparseGeneratorBudget p)) ≤ T i) :
    let P := p + sparseGeneratorBudget p
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (P + ((P + 2) ^ 3 + (P + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β e₁ e₂ q₁ q₂ : ι → ℝ),
        β - e₁ - q₁ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) →
        β - e₂ - q₂ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) →
        ‖e₁‖ ≤ Real.exp P / monomialScale T α →
        ‖e₂ - e₁‖ ≤ Real.exp P / monomialScale T α →
        q₁ ∈ realDenominatorGrid l → q₂ ∈ realDenominatorGrid l →
        ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp P + Real.exp ((P + 2) ^ 3 + (P + 2) ^ 18 + P)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β - e - q ∈ realRationalCoordinateSpan (fourDependentProjection J) := by
  intro P
  have hκ : (Fintype.card κ : ℝ) ≤ p := by
    rw [Fintype.card_sum, Nat.cast_add] at hcols
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card κ)]
  have hpP : p ≤ P := le_add_of_nonneg_right (sparseGeneratorBudget_nonneg hp)
  have hP : 0 ≤ P := hp.trans hpP
  obtain ⟨M₁, hM₁, hM₁p, w₁, hw₁, hw₁H⟩ :=
    exists_sparse_generators_exp_height J {1, 2} v hv hH hvH hp h₁₂ hκ hHp
  obtain ⟨M₂, hM₂, hM₂p, w₂, hw₂, hw₂H⟩ :=
    exists_sparse_generators_exp_height J {1, 3} v hv hH hvH hp h₁₃ hκ hHp
  have hMP : ((max M₁ M₂ : ℕ) : ℝ) ≤ Real.exp P := by
    rw [Nat.cast_max]
    apply (max_le hM₁p hM₂p).trans
    apply Real.exp_le_exp.mpr
    exact le_add_of_nonneg_left hp
  exact exists_coordinate_intersection_corrections
    (fourSparseFirstProjection J {1, 2}) (fourSparseFirstProjection J {1, 3})
    w₁ w₂ hw₁ hw₂ (hM₁.trans (le_max_left _ _)) hl
    (fun a i => (hw₁H a i).mono (le_max_left _ _))
    (fun a i => (hw₂H a i).mono (le_max_right _ _))
    hP (hι.trans hpP) (hcols.trans hpP) hMP
    (hlp.trans (Real.exp_le_exp.mpr hpP)) T hT

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

open Module

theorem fourPetalSpace_eq_inf_ker
    {R V E : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup E] [Module R E] (D : Submodule R V)
    (K : Submodule R (Fin 4 → V)) (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : LinearMap.ker ℓ = K) :
    fourPetalSpace D K = D ⊓ LinearMap.ker
      (ℓ.comp (LinearMap.single R (fun _ : Fin 4 => V) 0)) := by
  rw [LinearMap.ker_comp, hℓ]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGraphSmallDifference
namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G V : Type*} [DecidableEq G] [DecidableEq V]

theorem additiveGraph_image_fst (H : Finset G) (b : G → V) (S : Finset (G × V))
    (hS : S ⊆ additiveGraph H b) : additiveGraph (S.image Prod.fst) b = S := by
  ext x
  rw [mem_additiveGraph_iff]
  constructor
  · rintro ⟨hx, he⟩
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    have hgy := (mem_additiveGraph_iff H b y).mp (hS hy)
    have hxy : x = y := Prod.ext hyx.symm (by rw [he, ← hyx, hgy.2])
    exact hxy.symm ▸ hy
  · intro hx
    exact ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, ((mem_additiveGraph_iff H b x).mp (hS hx)).2⟩

variable [AddCommGroup G] [Fintype G] [AddCommGroup V] [Fintype V]

theorem exists_large_graph_subset_small_difference
    (H : Finset G) (hH : H.Nonempty) (b : G → V) {K : ℝ} (hK : 0 < K)
    (henergy : K⁻¹ * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H b) (additiveGraph H b) : ℝ)) :
    ∃ J ⊆ H, J.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ (J.card : ℝ) ∧
      ((additiveGraph J b - additiveGraph J b).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * J.card := by
  obtain ⟨S, hS, hSn, hsize, hdiff⟩ := BSG.exists_large_subset_small_difference
    (additiveGraph H b) (hH.image _) hK (by simpa only [additiveGraph_card] using henergy)
  let J := S.image Prod.fst
  have hgraph : additiveGraph J b = S := additiveGraph_image_fst H b S hS
  have hcard : S.card = J.card := by rw [← hgraph, additiveGraph_card]
  refine ⟨J, ?_, hSn.image _, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact ((mem_additiveGraph_iff H b y).mp (hS hy)).1
  · simpa only [additiveGraph_card, hcard] using hsize
  · rw [hgraph, ← hcard]
    exact hdiff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFourBalancedDual
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem realFourCoordinateMap_diagonal
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    realFourCoordinateMap ℓ (fourDiagonalMap (R := ℝ) x) =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) x := by
  change realifyCoordinateMap ℓ
    ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm _) = _
  rw [← real_four_diagonal, LinearEquiv.symm_apply_apply, realifyCoordinateMap_comp]

theorem realFourCoordinateMap_single
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (k : Fin 4) (x : ℝ ⊗[ℚ] V) :
    realFourCoordinateMap ℓ (LinearMap.single ℝ (fun _ : Fin 4 => ℝ ⊗[ℚ] V) k x) =
      realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) k)) x := by
  change realifyCoordinateMap ℓ
    ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm _) = _
  rw [← real_four_single, LinearEquiv.symm_apply_apply, realifyCoordinateMap_comp]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicMixedReflection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem tripleCyclicEmbed_expect_le {N : ℕ} [NeZero N]
    (a : ZMod (3 * N)) (g : ZMod (3 * N) → ℝ) (hg : ∀ t, 0 ≤ g t) :
    (𝔼 y : ZMod N, g (a - tripleCyclicEmbed y)) ≤ 3 * (𝔼 t, g t) := by
  classical
  have he : Function.Injective (fun y : ZMod N => a - tripleCyclicEmbed y) := by
    intro x y hxy
    apply tripleCyclicEmbed_injective
    exact sub_right_inj.mp hxy
  have hsum : (∑ y : ZMod N, g (a - tripleCyclicEmbed y)) ≤ ∑ t, g t := by
    calc
      _ = ∑ t ∈ Finset.univ.image (fun y : ZMod N => a - tripleCyclicEmbed y), g t := by
        rw [Finset.sum_image he.injOn]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun t _ _ => hg t)
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, ZMod.card, ZMod.card]
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  calc
    _ ≤ (∑ t, g t) / N := div_le_div_of_nonneg_right hsum hN.le
    _ = _ := by push_cast; field_simp

theorem tripleCyclicEmbed_pair_expect_le {N : ℕ} [NeZero N]
    (z : ZMod N) (g : ZMod (3 * N) → ℝ) (hg : ∀ t, 0 ≤ g t) :
    (𝔼 x : ZMod N, 𝔼 y : ZMod N,
      g (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y)) ≤ 3 * (𝔼 t, g t) := by
  apply (Finset.expect_le_expect (fun x _ =>
    tripleCyclicEmbed_expect_le (tripleCyclicEmbed z - tripleCyclicEmbed x) g hg)).trans_eq
  exact Fintype.expect_const _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_remove_triple_interval {N : ℕ} [NeZero N]
    (z : ZMod N) (a : ZMod (3 * N)) (L : ℕ) (F : ZMod N → ZMod N → ℂ)
    (hF : ∀ x y, ‖F x y‖ ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 x, 𝔼 y, F x y * finiteIndicator (cyclicInterval a L)
      (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y)‖) :
    ∃ χ : AddChar (ZMod (3 * N)) ℂ, ρ ^ 2 / 48 ≤
      ‖𝔼 x, 𝔼 y, F x y * star (χ (tripleCyclicEmbed x)) * star (χ (tripleCyclicEmbed y))‖ := by
  let δ := ρ / 12
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨v, c, _, herr, hmass, hsum⟩ := exists_cyclic_interval_fourier_smoothing a L hδ hδ1
  let D (x y : ZMod N) := tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y
  let I := finiteIndicator (cyclicInterval a L)
  have herror : ‖𝔼 x, 𝔼 y, F x y * (I (D x y) - v (D x y))‖ ≤ 6 * δ := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    calc
      _ ≤ 𝔼 x, 𝔼 y, ‖I (D x y) - v (D x y)‖ := by
        apply Finset.expect_le_expect
        intro x _
        apply (RCLike.norm_expect_le (K := ℂ)).trans
        apply Finset.expect_le_expect
        intro y _
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hF x y)
      _ ≤ 3 * (𝔼 t, ‖I t - v t‖) :=
        tripleCyclicEmbed_pair_expect_le z (fun t => ‖I t - v t‖) (fun _ => norm_nonneg _)
      _ ≤ 6 * δ := by linarith
  have hdiff : ‖(𝔼 x, 𝔼 y, F x y * I (D x y)) - (𝔼 x, 𝔼 y, F x y * v (D x y))‖ ≤ 6 * δ := by
    simpa only [mul_sub, Finset.expect_sub_distrib] using herror
  have htriangle : ‖𝔼 x, 𝔼 y, F x y * I (D x y)‖ ≤
      ‖𝔼 x, 𝔼 y, F x y * v (D x y)‖ +
        ‖(𝔼 x, 𝔼 y, F x y * I (D x y)) - (𝔼 x, 𝔼 y, F x y * v (D x y))‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub
      (𝔼 x, 𝔼 y, F x y * v (D x y)) (𝔼 x, 𝔼 y, F x y * I (D x y))
  have hsmoothed : ρ / 2 ≤ ‖𝔼 x, 𝔼 y, F x y * v (D x y)‖ := by
    change ρ ≤ ‖𝔼 x, 𝔼 y, F x y * I (D x y)‖ at hcorr
    dsimp [δ] at hdiff
    linarith
  have heq : (𝔼 x, 𝔼 y, F x y * v (D x y)) =
      ∑ χ, c χ * (𝔼 x, 𝔼 y, F x y * χ (D x y)) := by
    calc
      _ = 𝔼 x, 𝔼 y, ∑ χ, c χ * (F x y * χ (D x y)) := by
        apply Finset.expect_congr rfl
        intro x _
        apply Finset.expect_congr rfl
        intro y _
        rw [hsum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  obtain ⟨χ, hχ⟩ := exists_large_weighted_term c
    (fun χ => 𝔼 x, 𝔼 y, F x y * χ (D x y)) (by positivity : 0 < ρ / 2)
    (by positivity : 0 < 2 / δ) hmass (by rwa [← heq])
  have hthreshold : (ρ / 2) / (2 / δ) = ρ ^ 2 / 48 := by
    dsimp [δ]
    field_simp
    ring
  rw [hthreshold] at hχ
  have hfactor : (𝔼 x, 𝔼 y, F x y * χ (D x y)) =
      χ (tripleCyclicEmbed z) *
        (𝔼 x, 𝔼 y, F x y * star (χ (tripleCyclicEmbed x)) * star (χ (tripleCyclicEmbed y))) := by
    simp_rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    simp only [D, addChar_sub_star]
    ring
  rw [hfactor, norm_mul, AddChar.norm_apply, one_mul] at hχ
  exact ⟨χ, hχ⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_unwrapped_family_reflected_correlation
    {T : Type*} [Fintype T] [Nonempty T] {N : ℕ} [NeZero N] {p : ℝ}
    (hp : 0 ≤ p) (R S : T → ℤ → ℤ → ℂ)
    (hR : ∀ t x n, ‖R t x n‖ ≤ 1) (hS : ∀ t y n, ‖S t y n‖ ≤ 1)
    (z : ZMod N) (b : T → ZMod N → ℂ) (hb : ∀ t x, ‖b t x‖ ≤ 1)
    (hcorr : Real.exp (-p) ≤ ‖𝔼 t, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      R t x.val (z - x - y).val * star (S t y.val (z - x - y).val) * b t x * star (b t y)‖) :
    ∃ (k : Fin 3) (A B : T → ℤ → ℂ),
      (∀ t n, ‖A t n‖ ≤ 1) ∧ (∀ t n, ‖B t n‖ ≤ 1) ∧
      Real.exp (-(2 * p + 10)) ≤ ‖𝔼 t, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
        R t x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
          star (S t y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) *
            A t x.val * B t y.val‖ := by
  let F (k : Fin 3) (x y : ZMod N) := 𝔼 t,
    R t x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
      star (S t y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * b t x * star (b t y)
  let G (t : T) (x y : ZMod N) :=
    R t x.val (z - x - y).val * star (S t y.val (z - x - y).val) * b t x * star (b t y)
  let D (x y : ZMod N) := tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y
  have hcomm (H : T → ZMod N → ZMod N → ℂ) :
      (𝔼 x, 𝔼 y, 𝔼 t, H t x y) = 𝔼 t, 𝔼 x, 𝔼 y, H t x y := by
    calc
      _ = 𝔼 x, 𝔼 t, 𝔼 y, H t x y := by
        apply Finset.expect_congr rfl
        intro x _
        exact Finset.expect_comm _ _ _
      _ = _ := Finset.expect_comm _ _ _
  have hF (k : Fin 3) (x y : ZMod N) : ‖F k x y‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect (fun t _ => ?_)).trans_eq (Fintype.expect_const (1 : ℝ))
    simp only [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb t y)
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb t x)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR t _ _)).trans (hS t _ _)
  have hterm (k : Fin 3) (x y : ZMod N) :
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y) =
        (𝔼 t, G t x y) * finiteIndicator (tripleCarryInterval N k) (D x y) := by
    by_cases hk : D x y ∈ tripleCarryInterval N k
    · have hr := tripleCarry_representative z x y k hk
      simp only [finiteIndicator, if_pos hk, mul_one, F, G, hr]
    · simp only [finiteIndicator, if_neg hk, mul_zero]
  have hpoint (x y : ZMod N) :
      (∑ k : Fin 3, F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = 𝔼 t, G t x y := by
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_tripleCarry_indicator, mul_one]
  have hsum : (∑ k : Fin 3, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = 𝔼 t, 𝔼 x, 𝔼 y, G t x y := by
    rw [← hcomm G, ← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.expect_sum_comm]
    exact Finset.expect_congr rfl (fun y _ => hpoint x y)
  obtain ⟨k, hk⟩ := exists_large_weighted_term (fun _ : Fin 3 => (1 : ℂ))
    (fun k => 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y))
    (Real.exp_pos (-p)) (by norm_num : (0 : ℝ) < 3) (by norm_num)
    (by simpa only [one_mul, hsum, G] using hcorr)
  have hρ1 : Real.exp (-p) / 3 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)
    linarith only [he]
  obtain ⟨χ, hχ⟩ := exists_remove_triple_interval z (tripleCarryStart N k) N (F k) (hF k)
    (by positivity : 0 < Real.exp (-p) / 3) hρ1 hk
  let A (t : T) (n : ℤ) := b t (n : ZMod N) * star (χ (n : ZMod (3 * N)))
  let B (t : T) (n : ℤ) := star (b t (n : ZMod N)) * star (χ (n : ZMod (3 * N)))
  have hAe (t : T) (x : ZMod N) : A t (x.val : ℤ) = b t x * star (χ (tripleCyclicEmbed x)) := by
    simp [A, tripleCyclicEmbed]
  have hBe (t : T) (y : ZMod N) : B t (y.val : ℤ) = star (b t y) * star (χ (tripleCyclicEmbed y)) := by
    simp [B, tripleCyclicEmbed]
  have hfinal : (𝔼 x, 𝔼 y, F k x y * star (χ (tripleCyclicEmbed x)) * star (χ (tripleCyclicEmbed y))) =
      𝔼 t, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
        R t x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
          star (S t y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * A t x.val * B t y.val := by
    simp_rw [F, Finset.expect_mul, hcomm]
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    rw [hAe, hBe]
    ring
  have htwo : Real.exp (-p) ^ 2 = Real.exp (-(2 * p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hthreshold : (Real.exp (-p) / 3) ^ 2 / 48 = Real.exp (-(2 * p)) / 432 := by
    rw [div_pow, htwo]
    ring
  have h432 : (432 : ℝ) ≤ Real.exp 10 :=
    (by norm_num : (432 : ℝ) ≤ 2 ^ 10).trans (two_pow_le_exp_of_le 10 le_rfl)
  have hsmall : Real.exp (-(2 * p + 10)) ≤ (Real.exp (-p) / 3) ^ 2 / 48 := by
    rw [hthreshold]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 432)).mpr
    calc
      _ ≤ Real.exp (-(2 * p + 10)) * Real.exp 10 :=
        mul_le_mul_of_nonneg_left h432 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨k, A, B, ?_, ?_, ?_⟩
  · intro t n
    simpa only [A, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb t (n : ZMod N)
  · intro t n
    simpa only [B, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb t (n : ZMod N)
  · rw [hfinal] at hχ
    exact hsmall.trans hχ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_cyclic_mixed_reflection (n : ℕ)
    {T : Type} [Fintype T] [Nonempty T] {N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p)
    (K : T → ℤ → ℤ → (Fin n → ℤ) → ℂ) (hK : ∀ t h m u, ‖K t h m u‖ ≤ 1)
    (f : T → ZMod N → ℂ) (hf : ∀ t x, ‖f t x‖ ≤ 1)
    (A : T → Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ)
    (hA : ∀ t i x, ‖A t i x‖ ≤ 1) (hmiss : ∀ t i, MissesBoxCoordinate (A t i) i)
    (hcorr : Real.exp (-p) ≤ ‖𝔼 t, 𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
      f t (m + h + ∑ i, u i) * K t h.val m.val (fun i => (u i).val) *
        ∏ i, A t i (Fin.cons h (Fin.cons m u))‖) :
    ∃ (z : ZMod N) (k : Fin 3) (B : T → Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
      (∀ t i x, ‖B t i x‖ ≤ 1) ∧
      (∀ t i x y, (∀ j, j ≠ i → x j = y j) → B t i x = B t i y) ∧
      let c : ℤ := z.val + (k.val : ℤ) * N
      Real.exp (-(2 * ((2 ^ (n + 1) : ℕ) : ℝ) * p + 10)) ≤
        ‖𝔼 t, 𝔼 u : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
          (K t h.val (c - h.val - h'.val) (fun i => (u i).val) *
            star (K t h'.val (c - h.val - h'.val) (fun i => (u i).val))) *
              ∏ i, B t i (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun j => (u j).val)))‖ := by
  let φ (x : ZMod N) : ℤ := x.val
  let Kcyc (t : T) (h m : ZMod N) (u : Fin n → ZMod N) :=
    K t (φ h) (φ m) (fun i => φ (u i))
  obtain ⟨z, b, hb, hreflect⟩ := exists_mixed_reflected_exp_correlation n Kcyc f A hf hA hmiss hcorr
  let P := ((2 ^ (n + 1) : ℕ) : ℝ) * p
  have hP : 0 ≤ P := mul_nonneg (Nat.cast_nonneg _) hp
  let R (t : T × ((Fin n → ZMod N) × (Fin n → ZMod N))) (h m : ℤ) :=
    mixedTailDifference (K t.1) (fun i => φ (t.2.1 i)) (fun i => φ (t.2.2 i)) h m
  let b' (t : T × ((Fin n → ZMod N) × (Fin n → ZMod N))) (h : ZMod N) :=
    b t.1 t.2.1 t.2.2 h
  have hR : ∀ t h m, ‖R t h m‖ ≤ 1 := fun t h m =>
    mixedTailDifference_norm (K t.1) (hK t.1) _ _ h m
  have hmap (t : T) (u v : Fin n → ZMod N) (h m : ZMod N) :
      mixedTailDifference (Kcyc t) u v h m = R (t, (u, v)) (φ h) (φ m) :=
    mixedTailDifference_map φ (K t) u v h m
  have hinput : Real.exp (-P) ≤
      ‖𝔼 t, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        R t h.val (z - h - h').val * star (R t h'.val (z - h - h').val) *
          b' t h * star (b' t h')‖ := by
    simpa only [P, neg_mul, b', expect_prod_split, hmap, φ] using
      hreflect.trans (Complex.re_le_norm _)
  obtain ⟨k, B₀, C₀, hB₀, hC₀, hunwrapped⟩ :=
    exists_unwrapped_family_reflected_correlation hP R R hR hR z b'
      (fun t h => hb t.1 t.2.1 t.2.2 h) hinput
  let c : ℤ := z.val + (k.val : ℤ) * N
  have hψ (x : ZMod N) : ((φ x : ℤ) : ZMod N) = x := by
    simp [φ]
  have hanchorInput : Real.exp (-(2 * P + 10)) ≤
      ‖𝔼 t, 𝔼 u : Fin n → ZMod N, 𝔼 v : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ h) (c - φ h - φ h') *
          star (mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ h')
            (c - φ h - φ h')) * B₀ (t, (u, v)) (φ h) * C₀ (t, (u, v)) (φ h')‖ := by
    simpa only [R, c, φ, expect_prod_split] using hunwrapped
  obtain ⟨B, hB, hBind, hfinal⟩ := exists_anchored_reflected_family φ
    (fun x : ℤ => (x : ZMod N)) hψ K hK c
    (fun t u v h => B₀ (t, (u, v)) h) (fun t u v h => C₀ (t, (u, v)) h)
    (fun t u v h => hB₀ (t, (u, v)) h) (fun t u v h => hC₀ (t, (u, v)) h) hanchorInput
  refine ⟨z, k, B, hB, hBind, ?_⟩
  simpa only [P, mul_assoc, c, φ] using hfinal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationShearCoordinateSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]
  [Algebra ℚ R] [Algebra ℚ S] {w : σ ⊕ Unit → ℕ}

noncomputable def translationShearCoordinates
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver R σ :=
  (existsUnique_translation_of_shear_exp D b P hb hP).exists.choose

theorem translationShearCoordinates_action
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver.actionMonoidHom (translationShearCoordinates D b P hb hP) =
      (polynomialShearExpAut D).val :=
  (existsUnique_translation_of_shear_exp D b P hb hP).exists.choose_spec

theorem translationShearCoordinates_map_action
    (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver.actionMonoidHom
        (PolynomialTranslationGroupOver.map f (translationShearCoordinates D b P hb hP)) =
      (polynomialShearExpAut (polynomialShearMap f D)).val := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  have he := congrArg
    (fun a : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R => a (X i))
    (translationShearCoordinates_action D b P hb hP)
  change PolynomialTranslationGroupOver.actionHom _ (X i) = polynomialShearExp D (X i) at he
  have hm := PolynomialTranslationGroupOver.map_actionHom f
    (translationShearCoordinates D b P hb hP) (X i)
  rw [he, polynomialShearExp_map, map_X] at hm
  exact hm.symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

theorem translationShearCoordinates_inverse_exp
    (w : σ ⊕ Unit → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    polynomialShearExp (-D) (X (Sum.inr ())) =
      X (Sum.inr ()) - rename Sum.inl (translationShearCoordinates D b P hb hP).polynomial := by
  rw [← polynomialShearExpAut_apply, polynomialShearExpAut_neg_over w d hw]
  have he := translationShearCoordinates_action D b P hb hP
  change ((polynomialShearExpAut D).val).symm (X (Sum.inr ())) = _
  rw [← he]
  exact PolynomialTranslationGroupOver.action_inverse_X_inr _

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

variable [Algebra ℚ R]

theorem translationShearCoordinates_polynomial_series
    (w : σ ⊕ Unit → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    (translationShearCoordinates D b P hb hP).polynomial =
      ∑ k ∈ Finset.range (w (Sum.inr ())),
        ((-1 : ℚ) ^ k / ((k + 1).factorial : ℚ)) •
          ((translationBaseDerivative b).toLinearMap ^ k) P := by
  have he := translationShearCoordinates_inverse_exp w d hw D b P hb hP
  rw [polynomialShearExp_eq_sum (-D) (weightedSupportLE_X w (Sum.inr ())),
    Finset.sum_range_succ'] at he
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    Module.End.one_apply, one_smul] at he
  have hs : (∑ k ∈ Finset.range (w (Sum.inr ())),
      (((k + 1).factorial : ℚ)⁻¹) •
        ((-D).val.toLinearMap ^ (k + 1)) (X (Sum.inr ()))) =
      -rename Sum.inl (∑ k ∈ Finset.range (w (Sum.inr ())),
        ((-1 : ℚ) ^ k / ((k + 1).factorial : ℚ)) •
          ((translationBaseDerivative b).toLinearMap ^ k) P) := by
    rw [map_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [polynomialShear_neg_pow_apply, translationShear_derivation_pow_extra D b P hb hP]
    rw [AlgHom.map_smul_of_tower, smul_smul, ← neg_smul]
    congr 1
    rw [pow_succ]
    ring
  rw [hs] at he
  apply MvPolynomial.rename_injective Sum.inl Sum.inl_injective
  apply neg_injective
  apply add_left_cancel (a := X (Sum.inr ()))
  simpa only [sub_eq_add_neg] using he.symm.trans (add_comm _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CertifiedChartBasisBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

theorem certifiedChartMatrix_budget {ι κ : Type*}
    [Fintype ι] [Fintype κ] (matrix : Matrix ι κ ℚ)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hheight : ∀ i j, rationalLogHeight (matrix i j) ≤ ((p + 2) ^ 2 + 2) ^ 63) :
    (∀ i j, |(matrix i j : ℝ)| ≤ Real.exp (((p + 2) ^ 2 + 2) ^ 63)) ∧
    0 < matrixDenominator matrix ∧
    (matrixDenominator matrix : ℝ) ≤ Real.exp ((p + 2) ^ 254) ∧
    ∀ i j, ∃ z : ℤ, (z : ℝ) = (matrixDenominator matrix : ℝ) * (matrix i j : ℝ) := by
  have hcost : ((p + 2) ^ 2 + 2) ^ 63 ≤ (p + 2) ^ 252 := by
    simpa using shifted_power_budget_le hp 2 63
  refine ⟨fun i j => (rational_abs_real_le_numerator (matrix i j)).trans
    ((rationalLogHeight_le_iff _ _).mp (hheight i j)).1,
    matrixDenominator_pos matrix, ?_, ?_⟩
  · apply matrixDenominator_le_exp_power matrix hp 252 hι hκ
    intro i j
    exact ((rationalLogHeight_le_iff _ _).mp (hheight i j)).2.trans
      (Real.exp_le_exp.mpr hcost)
  · intro i j
    obtain ⟨z, hz⟩ := matrixDenominator_mul_entry_real_integral matrix i j
    exact ⟨z, hz.symm⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BoundedKernelGridEnumerationBudget
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup
open Module

variable {ι L G : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [LieAlgebra ℝ L] [Group G]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_kernel_grid_enumeration [IsScalarTower ℚ ℝ L] (b : Basis ι ℝ L)
    (π : NilpotentLieBCHGroup L s hnil →* G) (m N : ℕ) (hm : 0 < m)
    {B : ℝ} (hB : 0 ≤ B) (hN : (m : ℝ) * B ≤ N) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (2 * N + 1) ^ Fintype.card ι ∧
      ∃ center : Fin n → NilpotentLieBCHGroup L s hnil,
        (∀ j, π (center j) = 1 ∧ (∀ i, |b.repr (center j).coord i| ≤ B) ∧
          b.equivFun (center j).coord ∈ realDenominatorGrid m) ∧
        ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
          (∀ i, |b.repr g.coord i| ≤ B) →
          b.equivFun g.coord ∈ realDenominatorGrid m → ∃ j, center j = g := by
  classical
  let A : Set (ι → ℝ) := {x | x ∈ realDenominatorGrid m ∧ ∀ i, |x i| ≤ B}
  obtain ⟨hAfin, hAcard⟩ := finite_card_real_grid_box A m N hm
    (fun _ hx => hx.1) (fun _ hx => hx.2) hN
  let S : Set (NilpotentLieBCHGroup L s hnil) :=
    {g | π g = 1 ∧ (∀ i, |b.repr g.coord i| ≤ B) ∧
      b.equivFun g.coord ∈ realDenominatorGrid m}
  let f : NilpotentLieBCHGroup L s hnil → (ι → ℝ) := fun g => b.equivFun g.coord
  have hf : Function.Injective f := by
    intro g h hgh
    apply NilpotentLieBCHGroup.ext
    exact b.equivFun.injective hgh
  have hmaps : Set.MapsTo f S A := by
    intro g hg
    exact ⟨hg.2.2, by simpa only [f, Basis.equivFun_apply] using hg.2.1⟩
  have hSfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn hAfin
  have hScard : S.ncard ≤ (2 * N + 1) ^ Fintype.card ι :=
    (Set.ncard_le_ncard_of_injOn f hmaps hf.injOn hAfin).trans hAcard
  let : Fintype S := hSfin.fintype
  have hone : (1 : NilpotentLieBCHGroup L s hnil) ∈ S := by
    refine ⟨map_one π, ?_, ?_⟩
    · simpa only [coord_one, map_zero, Finsupp.zero_apply, abs_zero] using fun _ : ι => hB
    · simpa only [coord_one, map_zero] using realDenominatorGrid_zero (ι := ι) m
  let : Nonempty S := ⟨⟨1, hone⟩⟩
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, Fintype.card_pos, ?_, fun j => (e.symm j).val,
    fun j => (e.symm j).property, ?_⟩
  · simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hScard
  · intro g hmark hbound hgrid
    let x : S := ⟨g, hmark, hbound, hgrid⟩
    exact ⟨e x, congrArg Subtype.val (e.symm_apply_apply x)⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

namespace NilpotentLieBCHGroup
open Module

variable {ι L G : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L] [Group G]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_kernel_grid_enumeration_exp (b : Basis ι ℝ L)
    (π : NilpotentLieBCHGroup L s hnil →* G) (m : ℕ) (hm : 0 < m)
    {B p : ℝ} (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∃ center : Fin n → NilpotentLieBCHGroup L s hnil,
        (∀ j, π (center j) = 1 ∧ (∀ i, |b.repr (center j).coord i| ≤ B) ∧
          b.equivFun (center j).coord ∈ realDenominatorGrid m) ∧
        ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
          (∀ i, |b.repr g.coord i| ≤ B) →
          b.equivFun g.coord ∈ realDenominatorGrid m → ∃ j, center j = g := by
  obtain ⟨n, hn, hcard, center, hcenters, hcover⟩ :=
    exists_bounded_kernel_grid_enumeration b π m ⌈(m : ℝ) * B⌉₊ hm hB0 (Nat.le_ceil _)
  refine ⟨n, hn, ?_, center, hcenters, hcover⟩
  exact (Nat.cast_le.mpr hcard).trans
    (real_grid_integer_box_count_bound (Fintype.card ι) m hp hB0 hd hmp hB)

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end


