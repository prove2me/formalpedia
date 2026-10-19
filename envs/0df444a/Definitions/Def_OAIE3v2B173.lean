-- Prove2me | Definitions.Def_OAIE3v2B173
-- name    : OAIE3v2B173
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:42:11.332331+00:00
-- url     : https://prove2.me/theorems/3a524e2b-4316-4ad1-8f3b-97f7524e5c45
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 175 of 311
-- statement:
--   Definitions bundle 175 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B155`, `OAIE3v2B158` of this split.
--
--   Modules: `Dynamics/ResetFromCommonQuotient.lean`, `Estimates/AdaptedDiagramNativeExternalNet.lean`, `Estimates/CommonRefilteredFactorization.lean`, `Estimates/FrozenMarkedLeftOrbitBound.lean`, `Estimates/NativeFrozenMarkedLocalMark.lean`, `Estimates/RealifiedTopQuotient.lean`, `Estimates/RefilteredPointwiseSplitting.lean`, `Estimates/SimultaneousSymbolSplitting.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Estimates/SymbolCommonCorrections.lean`, `Fourier/HomogeneousGradedProjectionFrequency.lean`, `Linear/ActualOrdinaryPointwiseSpanning.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Linear/RefilteredKernelConstantBounds.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Polynomial/ControlledPolynomialGroupMapBounds.lean`, `Polynomial/NativeMarkedPolynomialFreezing.lean`, `Polynomial/PrescribedFastPolynomialFactorization.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`, `Polynomial/RefilteredPolynomialProjection.lean`, `Polynomial/SimultaneousPolynomialSymbolSplitting.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B155
import Definitions.Def_OAIE3v2B158

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolCommonCorrections
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem controlled_compatible_factors_mod_layer (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (k : ℕ) (hk : k ≤ s + 1)
    (E P R E' P' R' : F.realification.Group)
    (hP : P.coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k)
    (hP' : P'.coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k)
    (hidentity : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (E * P * R) =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (E' * P' * R'))
    (ha : ‖(e.baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hd : (e.baseChange ℝ).equivFun (R' * R⁻¹).coord ∈ realDenominatorGrid l) :
    (E⁻¹ * E').coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k ∧
      (R' * R⁻¹).coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k := by
  apply F.realification.compatible_factors_mem_mod_layer_of_separation
    (realLieSubalgebraOverRat (realificationLieSubalgebra U)) k hk E P R E' P' R' hP hP' hidentity
  intro j _ _ hsum
  exact F.controlled_separation_at_layer e ω hlayers U v hspan hH hl hv hp hι hκ hHp hlp (j + 1)
    (E⁻¹ * E').coord (R' * R⁻¹).coord ha hd hsum

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_symbol_comparison_mod_layer (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ k : ℕ, k ≤ s + 1 → ∀ E P R E' P' R' : F.RealPolynomialSymbolGroup w,
      F.realSymbolGradeQuotientHom w k P ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) →
      F.realSymbolGradeQuotientHom w k P' ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) →
      F.realSymbolGradeQuotientHom w k (E * P * R) = F.realSymbolGradeQuotientHom w k (E' * P' * R') →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E' →
      F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R' →
      F.realSymbolGradeQuotientHom w k (E⁻¹ * E') ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) ∧
      F.realSymbolGradeQuotientHom w k (R' * R⁻¹) ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) := by
  obtain ⟨cs, _, hslow⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨cr, _, hrat⟩ := exists_symbol_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) +
    (Polynomial.X + Polynomial.C cs) ^ cs + (Polynomial.X + Polynomial.C cr) ^ cr + Polynomial.X + 2
  let B : Polynomial ℕ := (2 * Q + 2) ^ 48 + (2 * Q + 2) ^ 24 + 2 * Q + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
    T hT k hk E P R E' P' R' hP hP' heq hE hE' hR hR'
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let q : ℝ := (p + (s + 2)) ^ (s + 2) + (p + cs) ^ cs + (p + cr) ^ cr + p + 2
  have hd0 : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  have hs0 : 0 ≤ (p + cs) ^ cs := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsq : (p + cs) ^ cs ≤ q := by dsimp [q]; linarith
  have hrq : (p + cr) ^ cr ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    ((Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)).trans
          (by dsimp [q]; linarith)
  have hcutoff : separationBudget (2 * q) ≤ (p + C) ^ C := by
    simpa [B, Q, q, separationBudget, Polynomial.eval₂_pow] using hbound p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hAslow : F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + cs) ^ cs)) (E⁻¹ * E') := by
    have hinputs : ∀ g ∈ [E⁻¹, E'], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hlayers w T _ E).mpr hE
      · exact hE'
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hslow F b ω hlayers w hw H p hH hp hι hσ hHp hb T hTpos [E⁻¹, E'] (by simp) hinputs
  obtain ⟨m, hm, hmp, _, hproducts⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  have hDgrid : F.SymbolRationalGrid b ω hlayers w m (R' * R⁻¹) := by
    have hinputs : ∀ g ∈ [R', R⁻¹], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hR'
      · exact F.symbolRationalGrid_inv b ω hlayers w l hR
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [R', R⁻¹] (by simp) hinputs
  have hAnorm : ‖((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * q) / Real.exp (separationBudget (2 * q)) := by
    have hnorm := F.symbolSlowBound_log_norm b ω hlayers w T
      (Real.one_le_exp (separationBudget_nonneg (by positivity : 0 ≤ 2 * q)))
      (fun i => (Real.exp_le_exp.mpr hcutoff).trans (hT i)) (Real.exp_nonneg _) (E⁻¹ * E') hAslow
    exact hnorm.trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (hsq.trans (by linarith))) (Real.exp_nonneg _))
  have hresult := (F.polynomialSymbolFiltration w).controlled_compatible_factors_mod_layer
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) U v hspan hH hm hv hq hdim (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hmp.trans (Real.exp_le_exp.mpr hrq)) k hk
    E P R E' P' R' ((F.realSymbolGradeQuotient_mem_iff w U k P).mp hP)
      ((F.realSymbolGradeQuotient_mem_iff w U k P').mp hP') heq hAnorm hDgrid
  exact ⟨(F.realSymbolGradeQuotient_mem_iff w U k _).mpr hresult.1,
    (F.realSymbolGradeQuotient_mem_iff w U k _).mpr hresult.2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ResetFromCommonQuotient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_reset_from_common_quotient (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
        Submodule.span ℚ (Set.range v) = U.toSubmodule →
        BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule →
        (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v i) z) H) →
        ∀ k : ℕ, k ≤ s + 1 → ∀ E P R E₀ P₀ R₀ : F.RealPolynomialSymbolGroup w,
        P.coord ∈ realificationLieSubalgebra U →
        F.realSymbolGradeQuotientHom w k P₀ ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w k) →
        F.realSymbolGradeQuotientHom w k (E₀ * P₀ * R₀) = F.realSymbolGradeQuotientHom w k (E * P * R) →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
        F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R₀ →
        let A := F.truncateRealSymbol b ω hlayers w k (E₀⁻¹ * E)
        let D := F.truncateRealSymbol b ω hlayers w k (R * R₀⁻¹)
        (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
          (A * P * D).coord ∈ realificationLieSubalgebra U ∧
          F.realSymbolGradeQuotientHom w k (E * A⁻¹) = F.realSymbolGradeQuotientHom w k E₀ ∧
          F.realSymbolGradeQuotientHom w k (D⁻¹ * R) = F.realSymbolGradeQuotientHom w k R₀ ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) ∧
          F.SymbolRationalGrid b ω hlayers w m (D⁻¹ * R) := by
  obtain ⟨cc, hcc, hcompare⟩ := exists_controlled_symbol_comparison_mod_layer s a
  obtain ⟨cr, hcr, hreset⟩ := exists_controlled_symbol_reset s a
  refine ⟨max cc cr, hcc.trans (le_max_left _ _), ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hκ hHp hlp hb T hT
  have hc : (p + cc) ^ cc ≤ (p + (max cc cr : ℕ)) ^ max cc cr :=
    shifted_power_self_mono hp (by omega) (le_max_left _ _)
  have hr : (p + cr) ^ cr ≤ (p + (max cc cr : ℕ)) ^ max cc cr :=
    shifted_power_self_mono hp (by omega) (le_max_right _ _)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨m, hm, hmp, hlm, hresetm⟩ := hreset F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hTpos
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hr), hlm, ?_⟩
  intro U v hspan hU hv k hk E P R E₀ P₀ R₀ hP hP₀ hidentity hE hE₀ hR hR₀
  have hPq : F.realSymbolGradeQuotientHom w k P ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w k) :=
    Subgroup.mem_map.mpr ⟨P, hP, rfl⟩
  obtain ⟨hleft, hright⟩ := hcompare F b ω hlayers w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv T
    (fun i => (Real.exp_le_exp.mpr hc).trans (hT i)) k hk E₀ P₀ R₀ E P R hP₀ hPq hidentity hE₀ hE hR₀ hR
  obtain ⟨hprod, hmid, hEq, hRq, hslow, hgrid⟩ := hresetm U hU k E P R E₀ R₀ hP hE hE₀ hR hR₀ hleft hright
  exact ⟨hprod, hmid, hEq, hRq,
    F.symbolSlowBound_mono b ω hlayers w T hTpos (Real.exp_le_exp.mpr hr) _ hslow, hgrid⟩

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

theorem gradedFrequency_comap_top_zero (η : M →ₗ[ℚ] ℚ)
    (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hzero : ∀ y ∈ U, basisGradeProjection (G.associatedGradedBasis f ν hG) ν s y = y →
      G.gradedFrequency f ν hG η y = 0) :
    ∀ x ∈ U.comap (F.associatedGradedMap G φ hφ),
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω s x = x →
        F.gradedFrequency e ω hF (η.comp φ.toLinearMap) x = 0 := by
  intro x hx hpure
  rw [F.gradedFrequency_top_natural G e ω hF f ν hG φ hφ η x hpure]
  apply hzero _ hx
  exact (F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ s x).symm.trans
    (congrArg (F.associatedGradedMap G φ hφ) hpure)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SimultaneousSymbolSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_terminal_symbol_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ E P R E' P' R' : F.RealPolynomialSymbolGroup w,
      P.coord ∈ realificationLieSubalgebra U →
      P'.coord ∈ realificationLieSubalgebra U →
      E * P * R = E' * P' * R' →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E' →
      F.SymbolRationalGrid b ω hlayers w l R →
      F.SymbolRationalGrid b ω hlayers w l R' →
      (E⁻¹ * E').coord ∈ realificationLieSubalgebra U ∧
        (R' * R⁻¹).coord ∈ realificationLieSubalgebra U := by
  obtain ⟨C, hC, hcompare⟩ := exists_controlled_symbol_comparison_mod_layer s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw U v hspan H l p hH hl hp
    hι hσ hκ hHp hlp hb hv T hT E P R E' P' R' hP hP' heq hE hE' hR hR'
  have hresult := hcompare F b ω hlayers w hw U v hspan H l p hH hl hp
    hι hσ hκ hHp hlp hb hv T hT (s + 1) le_rfl E P R E' P' R'
    ((F.realSymbolGradeQuotient_mem_terminal_iff w U P).mpr hP)
    ((F.realSymbolGradeQuotient_mem_terminal_iff w U P').mpr hP')
    (congrArg (F.realSymbolGradeQuotientHom w (s + 1)) heq) hE hE' hR hR'
  exact ⟨(F.realSymbolGradeQuotient_mem_terminal_iff w U (E⁻¹ * E')).mp hresult.1,
    (F.realSymbolGradeQuotient_mem_terminal_iff w U (R' * R⁻¹)).mp hresult.2⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_simultaneous_symbol_extension (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : η → κ → F.PolynomialSymbol w),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w)
        (fun z => z.val.1) (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ j i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v j i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        ∀ k : ℕ, k ≤ s → ∀ (X E₀ R₀ : F.RealPolynomialSymbolGroup w)
          (E P R : η → F.RealPolynomialSymbolGroup w),
        (∀ j, E j * P j * R j = X) →
        (∀ j, (P j).coord ∈ realificationLieSubalgebra (U j)) →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
        (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
        F.SymbolRationalGrid b ω hlayers w l R₀ →
        (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
        (∀ j, F.realSymbolGradeQuotientHom w k (E₀⁻¹ * X * R₀⁻¹) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U j)).map
            (F.realSymbolGradeQuotientHom w k)) →
        ∃ E₁ R₁ : F.RealPolynomialSymbolGroup w,
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ C)) E₁ ∧
          F.SymbolRationalGrid b ω hlayers w m R₁ ∧
          F.realSymbolGradeQuotientHom w k E₁ = F.realSymbolGradeQuotientHom w k E₀ ∧
          F.realSymbolGradeQuotientHom w k R₁ = F.realSymbolGradeQuotientHom w k R₀ ∧
          ∀ j, F.realSymbolGradeQuotientHom w (k + 1) (E₁⁻¹ * X * R₁⁻¹) ∈
            (NilpotentLieBCHGroup.realificationSubgroup
              (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U j)).map
              (F.realSymbolGradeQuotientHom w (k + 1)) := by
  obtain ⟨c₀, _, hreset⟩ := exists_symbol_reset_from_common_quotient s a
  obtain ⟨c₁, _, hslowprod⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨c₂, _, hratprod⟩ := exists_symbol_rational_product_bound s 2
  obtain ⟨c₃, _, hcommon⟩ := exists_common_symbol_grade_corrections s 1
  obtain ⟨c₄, _, hstep⟩ := exists_controlled_symbol_grade_step s 1
  obtain ⟨C, hC, hbudget⟩ := exists_symbol_extension_budget a c₀ c₁ c₂ c₃ c₄
  refine ⟨C, hC, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT
  let q₁ : ℝ := (p + c₀) ^ c₀ + (p + 2) ^ a + p + 2
  let q₂ : ℝ := (q₁ + c₁) ^ c₁ + (q₁ + c₂) ^ c₂ + q₁ + 2
  let q₃ : ℝ := (q₂ + c₃) ^ c₃ + q₂ + 2
  have h₀ : 0 ≤ (p + c₀) ^ c₀ := by positivity
  have ha : 0 ≤ (p + 2) ^ a := by positivity
  have hq₁ : 0 ≤ q₁ := by dsimp [q₁]; positivity
  have hp₁ : p ≤ q₁ := by dsimp [q₁]; linarith
  have hreset₁ : (p + c₀) ^ c₀ ≤ q₁ := by dsimp [q₁]; linarith
  have ha₁ : (p + 2) ^ a ≤ q₁ := by dsimp [q₁]; linarith
  have hs₁ : 0 ≤ (q₁ + c₁) ^ c₁ := by positivity
  have hr₁ : 0 ≤ (q₁ + c₂) ^ c₂ := by positivity
  have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
  have h₁₂ : q₁ ≤ q₂ := by dsimp [q₂]; linarith
  have hs₂ : (q₁ + c₁) ^ c₁ ≤ q₂ := by dsimp [q₂]; linarith
  have hr₂ : (q₁ + c₂) ^ c₂ ≤ q₂ := by dsimp [q₂]; linarith
  have hc₂ : 0 ≤ (q₂ + c₃) ^ c₃ := by positivity
  have hq₃ : 0 ≤ q₃ := by dsimp [q₃]; positivity
  have h₂₃ : q₂ ≤ q₃ := by dsimp [q₃]; linarith
  have hc₃ : (q₂ + c₃) ^ c₃ ≤ q₃ := by dsimp [q₃]; linarith
  have hp₂ : p ≤ q₂ := hp₁.trans h₁₂
  have hp₃ : p ≤ q₃ := hp₂.trans h₂₃
  have hf : 0 ≤ (q₃ + c₄) ^ c₄ := by positivity
  have htotal : (p + c₀) ^ c₀ + (q₂ + c₃) ^ c₃ + (q₃ + c₄) ^ c₄ ≤ (p + 2) ^ C := hbudget p hp
  have hcut₀ : (p + c₀) ^ c₀ ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right hc₂).trans ((le_add_of_nonneg_right hf).trans htotal)
  have hcut₃ : (q₂ + c₃) ^ c₃ ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left h₀).trans ((le_add_of_nonneg_right hf).trans htotal)
  have hfinal : (q₃ + c₄) ^ c₄ ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left (add_nonneg h₀ hc₂)).trans htotal
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  have hgraded (j : η) : BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
      (fun z => ω z.val.2) (U j).toSubmodule := by
    have heq : (fun z : SymbolBasisIndex w ω => ω z.val.2) = (fun z => Finsupp.weight w z.val.1) :=
      funext (fun z => z.property.symm)
    rw [heq]
    exact (hblock j).graded _ _ _ (Finsupp.weight w)
  obtain ⟨m₁, hm₁, hm₁p, hlm₁, hresetm⟩ := hreset F b ω hlayers w hw H l p hH hl hp hι hσ hκ hHp hlp hb
    T (fun i => (Real.exp_le_exp.mpr hcut₀).trans (hT i))
  obtain ⟨m₂, hm₂, hm₂p, hm₁m₂, hproductsm⟩ := hratprod F b ω hlayers w hw H q₁ hH hq₁
    (hι.trans hp₁) (hσ.trans hp₁) (hHp.trans (Real.exp_le_exp.mpr hp₁)) hb m₁ hm₁
    (hm₁p.trans (Real.exp_le_exp.mpr hreset₁))
  obtain ⟨m₃, hm₃, hm₃p, hm₂m₃, hcommonm⟩ := hcommon F b ω hlayers w hw U v hspan hblock H m₂ q₂
    hH hm₂ hq₂ (hι.trans hp₂) (hσ.trans hp₂) (hκ.trans hp₂) (hη.trans hp₂)
    (hHp.trans (Real.exp_le_exp.mpr hp₂)) (hm₂p.trans (Real.exp_le_exp.mpr hr₂)) hv
    T (fun i => (Real.exp_le_exp.mpr hcut₃).trans (hT i))
  obtain ⟨m₄, hm₄, hm₄p, hm₃m₄, hstepm⟩ := hstep F b ω hlayers w hw H m₃ q₃ hH hm₃ hq₃
    (hι.trans hp₃) (hσ.trans hp₃) (hHp.trans (Real.exp_le_exp.mpr hp₃))
    (hm₃p.trans (Real.exp_le_exp.mpr hc₃)) hb T hTpos
  have hlm₃ : l ∣ m₃ := hlm₁.trans (hm₁m₂.trans hm₂m₃)
  refine ⟨m₄, hm₄, hm₄p.trans (Real.exp_le_exp.mpr hfinal), hlm₃.trans hm₃m₄, ?_⟩
  intro k hk X E₀ R₀ E P R hX hP hE₀ hE hR₀ hR hY
  let Y := E₀⁻¹ * X * R₀⁻¹
  let A₀ := fun j => F.truncateRealSymbol b ω hlayers w k (E₀⁻¹ * E j)
  let D₀ := fun j => F.truncateRealSymbol b ω hlayers w k (R j * R₀⁻¹)
  let E' := fun j => E j * (A₀ j)⁻¹
  let P' := fun j => A₀ j * P j * D₀ j
  let R' := fun j => (D₀ j)⁻¹ * R j
  have hdata (j : η) : E' j * P' j * R' j = X ∧
      (P' j).coord ∈ realificationLieSubalgebra (U j) ∧
      F.realSymbolGradeQuotientHom w k (E' j) = F.realSymbolGradeQuotientHom w k E₀ ∧
      F.realSymbolGradeQuotientHom w k (R' j) = F.realSymbolGradeQuotientHom w k R₀ ∧
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + c₀) ^ c₀)) (E' j) ∧
      F.SymbolRationalGrid b ω hlayers w m₁ (R' j) := by
    have hprod : E₀ * Y * R₀ = E j * P j * R j := by
      calc
        E₀ * Y * R₀ = X := by dsimp [Y]; group
        _ = E j * P j * R j := (hX j).symm
    obtain ⟨hprod', hmid, hEq, hRq, hslow, hgrid⟩ := hresetm (U j) (v j) (hspan j) (hgraded j) (hv j)
      k (by omega) (E j) (P j) (R j) E₀ Y R₀ (hP j) (hY j)
      (congrArg (F.realSymbolGradeQuotientHom w k) hprod) (hE j) hE₀ (hR j) hR₀
    exact ⟨hprod'.trans (hX j), hmid, hEq, hRq, hslow, hgrid⟩
  let A := fun j => E₀⁻¹ * E' j
  let D := fun j => R' j * R₀⁻¹
  have hAs (j : η) : F.SymbolSlowBound b ω hlayers w T (Real.exp ((q₁ + c₁) ^ c₁)) (A j) := by
    have hi : ∀ g ∈ [E₀⁻¹, E' j], F.SymbolSlowBound b ω hlayers w T (Real.exp ((q₁ + 2) ^ 1)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · apply (F.symbolSlowBound_inv_iff b ω hlayers w T _ _).mpr
        exact F.symbolSlowBound_mono b ω hlayers w T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using ha₁.trans (le_add_of_nonneg_right (by norm_num)))) _ hE₀
      · exact F.symbolSlowBound_mono b ω hlayers w T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using hreset₁.trans (le_add_of_nonneg_right (by norm_num)))) _
          (hdata j).2.2.2.2.1
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hslowprod F b ω hlayers w hw H q₁ hH hq₁
      (hι.trans hp₁) (hσ.trans hp₁) (hHp.trans (Real.exp_le_exp.mpr hp₁)) hb T hTpos [E₀⁻¹, E' j] (by simp) hi
  have hDg (j : η) : F.SymbolRationalGrid b ω hlayers w m₂ (D j) := by
    have hi : ∀ g ∈ [R' j, R₀⁻¹], F.SymbolRationalGrid b ω hlayers w m₁ g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (hdata j).2.2.2.2.2
      · exact F.symbolRationalGrid_inv b ω hlayers w m₁ (F.symbolRationalGrid_mono b ω hlayers w hl hlm₁ _ hR₀)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproductsm [R' j, R₀⁻¹] (by simp) hi
  let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ) (fun z => ω z.val.2) k
  have hlin (j : η) : π Y.coord - π (A j).coord - π (D j).coord ∈ realificationLieSubalgebra (U j) := by
    have h := F.symbol_current_grade_residual_mem b ω hlayers w (U j) (hgraded j) k
      (E' j) (P' j) (R' j) E₀ R₀ (hdata j).2.1 (hdata j).2.2.1.symm (hdata j).2.2.2.1
    change π (E₀⁻¹ * (E' j * P' j * R' j) * R₀⁻¹).coord - π (A j).coord - π (D j).coord ∈ _ at h
    rw [(hdata j).1] at h
    exact h
  obtain ⟨Ac, Dc, hAc, hDc, hAcs, hDcg, hres⟩ := hcommonm k Y.coord A D
    (fun j => F.symbolSlowBound_mono b ω hlayers w T hTpos
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hs₂.trans (le_add_of_nonneg_right (by norm_num)))) _ (hAs j))
    hDg hlin
  obtain ⟨_, hEq, hRq, hnext, hslow, hgrid⟩ := hstepm U hgraded k X E₀ R₀ Ac Dc hY hAc hDc hres
    (F.symbolSlowBound_mono b ω hlayers w T hTpos
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using
        ((ha₁.trans (h₁₂.trans h₂₃)).trans (le_add_of_nonneg_right (by norm_num))))) _ hE₀)
    (F.symbolSlowBound_mono b ω hlayers w T hTpos
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hc₃.trans (le_add_of_nonneg_right (by norm_num)))) _ hAcs)
    (F.symbolRationalGrid_mono b ω hlayers w hl hlm₃ _ hR₀) hDcg
  refine ⟨E₀ * Ac, Dc * R₀, F.symbolSlowBound_mono b ω hlayers w T hTpos
    (Real.exp_le_exp.mpr hfinal) _ hslow, hgrid, hEq, hRq, ?_⟩
  intro j
  have hnorm : (E₀ * Ac)⁻¹ * X * (Dc * R₀)⁻¹ = Ac⁻¹ * (E₀⁻¹ * X * R₀⁻¹) * Dc⁻¹ := by group
  rw [hnorm]
  exact hnext j

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_simultaneous_symbol_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : η → κ → F.PolynomialSymbol w),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w)
        (fun z => z.val.1) (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ j i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v j i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ (X : F.RealPolynomialSymbolGroup w) (E P R : η → F.RealPolynomialSymbolGroup w),
      (∀ j, E j * P j * R j = X) →
      (∀ j, (P j).coord ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (E₀ P₀ R₀ : F.RealPolynomialSymbolGroup w),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        E₀ * P₀ * R₀ = X ∧
        P₀.coord ∈ realificationLieSubalgebra (⨅ j, U j) ∧
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ C)) E₀ ∧
        F.SymbolRationalGrid b ω hlayers w m R₀ := by
  obtain ⟨K, hK, hextend⟩ := exists_simultaneous_symbol_extension s 1
  let C := max 2 ((a + 4) * budgetDepthExponent K s)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT X E P R hX hP hE hR
  let q₀ : ℝ := (p + 2) ^ a + p
  let Q := iteratedPowerBudget K q₀
  have hq₀ : 0 ≤ q₀ := by dsimp [q₀]; positivity
  have hp₀ : p ≤ q₀ := le_add_of_nonneg_left (by positivity)
  have ha₀ : (p + 2) ^ a ≤ q₀ := le_add_of_nonneg_right hp
  have hK₁ : 1 ≤ K := by omega
  have hQnonneg : ∀ n, 0 ≤ Q n := iteratedPowerBudget_nonneg K hq₀
  have hQmono : Monotone Q := iteratedPowerBudget_monotone hK₁ hq₀
  have hpQ (n : ℕ) : p ≤ Q n := hp₀.trans (iteratedPowerBudget_ge hK₁ hq₀ n)
  have haQ (n : ℕ) : (p + 2) ^ a ≤ Q n := ha₀.trans (iteratedPowerBudget_ge hK₁ hq₀ n)
  have hstart : q₀ ≤ (p + 2) ^ (a + 2) := by
    have hbase : 1 ≤ p + 2 := by linarith
    have hpow : (p + 2) ^ a ≤ (p + 2) ^ (a + 1) := pow_le_pow_right₀ hbase (by omega)
    have hpp : p ≤ (p + 2) ^ (a + 1) := le_power_budget hp (by omega)
    calc
      q₀ ≤ (p + 2) ^ (a + 1) + (p + 2) ^ (a + 1) := add_le_add hpow hpp
      _ = 2 * (p + 2) ^ (a + 1) := by ring
      _ ≤ (p + 2) * (p + 2) ^ (a + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (p + 2) ^ (a + 2) := (pow_succ' (p + 2) (a + 1)).symm
  have hQfinal : Q s ≤ (p + 2) ^ C := by
    have hbound := polynomial_budget_comp hp hq₀ (a + 2) (budgetDepthExponent K s)
      hstart (iteratedPowerBudget_le_power K hq₀ s)
    apply hbound.trans
    apply pow_le_pow_right₀ (by linarith : 1 ≤ p + 2)
    exact le_max_right _ _
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTstage (n : ℕ) (hn : n < s) : ∀ i, Real.exp ((Q n + 2) ^ K) ≤ T i := by
    intro i
    apply (Real.exp_le_exp.mpr ?_).trans (hT i)
    change Q (n + 1) ≤ (p + 2) ^ C
    exact (hQmono (by omega)).trans hQfinal
  have hind : ∀ n : ℕ, n ≤ s →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (Q n) ∧ l ∣ m ∧
        ∃ E₀ R₀ : F.RealPolynomialSymbolGroup w,
          F.SymbolSlowBound b ω hlayers w T (Real.exp (Q n)) E₀ ∧
          F.SymbolRationalGrid b ω hlayers w m R₀ ∧
          ∀ j, F.realSymbolGradeQuotientHom w (n + 1) (E₀⁻¹ * X * R₀⁻¹) ∈
            (NilpotentLieBCHGroup.realificationSubgroup
              (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U j)).map
              (F.realSymbolGradeQuotientHom w (n + 1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨l, hl, hlp.trans (Real.exp_le_exp.mpr (hpQ 0)), dvd_refl l, 1, 1,
        F.symbolSlowBound_one b ω hlayers w T hTpos (Real.exp_nonneg _),
        F.symbolRationalGrid_one b ω hlayers w l, ?_⟩
      intro j
      rw [F.realSymbolGradeQuotientHom_first w]
      exact Subgroup.one_mem _
    | succ n ih =>
      intro hn
      obtain ⟨m, hm, hmp, hlm, E₀, R₀, hE₀, hR₀, hY⟩ := ih (by omega)
      obtain ⟨m', hm', hmp', hmm', hstep⟩ := hextend F b ω hlayers w hw U v hspan hblock H m (Q n)
        hH hm (hQnonneg n) (hι.trans (hpQ n)) (hσ.trans (hpQ n)) (hκ.trans (hpQ n)) (hη.trans (hpQ n))
        (hHp.trans (Real.exp_le_exp.mpr (hpQ n))) hmp hb hv T (hTstage n (by omega))
      have hEn : F.SymbolSlowBound b ω hlayers w T (Real.exp ((Q n + 2) ^ 1)) E₀ :=
        F.symbolSlowBound_mono b ω hlayers w T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using
            (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2) : Q n ≤ Q n + 2))) _ hE₀
      have hEi : ∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((Q n + 2) ^ 1)) (E j) := by
        intro j
        apply F.symbolSlowBound_mono b ω hlayers w T hTpos _ _ (hE j)
        apply Real.exp_le_exp.mpr
        simpa only [pow_one] using (haQ n).trans (le_add_of_nonneg_right (by norm_num))
      have hRi : ∀ j, F.SymbolRationalGrid b ω hlayers w m (R j) :=
        fun j => F.symbolRationalGrid_mono b ω hlayers w hl hlm _ (hR j)
      obtain ⟨E₁, R₁, hE₁, hR₁, _, _, hY₁⟩ := hstep (n + 1) hn X E₀ R₀ E P R hX hP hEn hEi hR₀ hRi hY
      exact ⟨m', hm', hmp', hlm.trans hmm', E₁, R₁, hE₁, hR₁, hY₁⟩
  obtain ⟨m, hm, hmp, hlm, E₀, R₀, hE₀, hR₀, hY⟩ := hind s le_rfl
  refine ⟨m, E₀, E₀⁻¹ * X * R₀⁻¹, R₀, hm, hmp.trans (Real.exp_le_exp.mpr hQfinal), hlm,
    by group, ?_, F.symbolSlowBound_mono b ω hlayers w T hTpos (Real.exp_le_exp.mpr hQfinal) _ hE₀, hR₀⟩
  rw [realificationLieSubalgebra_iInf, lieSubalgebra_mem_iInf]
  intro j
  exact (F.realSymbolGradeQuotient_mem_terminal_iff w (U j) _).mp (hY j)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SimultaneousPolynomialSymbolSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_simultaneous_polynomial_symbol_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : η → κ → F.PolynomialSymbol w),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w)
        (fun z => z.val.1) (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ j i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v j i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : η → F.RealPolynomialSymbolGroup w),
      (∀ j, E j * P j * R j = F.realPolynomialSymbolHom b ω hlayers w g) →
      (∀ j, (P j).coord ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        e₀ * p₀ * r₀ = g ∧
        (F.realPolynomialSymbolHom b ω hlayers w p₀).coord ∈
          realificationLieSubalgebra (⨅ j, U j) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈
            realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨C, hC, hsplit⟩ := exists_simultaneous_symbol_splitting s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT g E P R hX hP hE hR
  obtain ⟨m, E₀, P₀, R₀, hm, hmp, hlm, hprod, hmid, hslow, hrat⟩ :=
    hsplit F b ω hlayers w hw U v hspan hblock H l p hH hl hp
      hι hσ hκ hη hHp hlp hb hv T hT (F.realPolynomialSymbolHom b ω hlayers w g)
      E P R hX hP hE hR
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨e₀, p₀, r₀, hepr, hp₀, he, hr, he0, hr0, hp0⟩ :=
    F.exists_realPolynomial_controlled_symbol_factorization b ω hlayers w T hTpos
      (Real.exp_nonneg _) m g E₀ P₀ R₀ hprod hslow hrat
  refine ⟨m, e₀, p₀, r₀, hm, hmp, hlm, hepr, ?_, he, hr, he0, hr0, hp0⟩
  rw [hp₀]
  exact hmid

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredPointwiseSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem pointwise_refiltered_values_mem (hw : ∀ i, 0 < w i)
    (p : F.realification.adaptedLieSubalgebra w)
    (hzero : coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    (hU : ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra U) :
    ∀ t : σ → ℝ, eval₂ t (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
      realificationLieSubalgebra (F.gradedRefiltrationSubalgebra U) := by
  apply (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (F.gradedRefiltrationSubalgebra U)).toSubmodule _).mpr
  exact F.normalized_refiltration_coefficients_mem_first w U hw p
    ((F.real_symbol_values_iff_refiltration_coefficients b ω hlayers w U p).mp hU) hzero

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_pointwise_polynomial_symbol_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ F.AssociatedGraded) (v : η → κ → F.AssociatedGraded),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ j i k, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j i) k) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : η → F.RealPolynomialSymbolGroup w),
      (∀ j, E j * P j * R j = F.realPolynomialSymbolHom b ω hlayers w g) →
      (∀ j, ∀ t : σ → ℝ,
        eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w (P j).coord) ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
          (F.realPolynomialSymbolHom b ω hlayers w p₀).coord) ∈ realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨K, hK, hsplit⟩ := exists_simultaneous_polynomial_symbol_splitting s a
  let C := max 2 (((s + 4) * (s + 3) + 2) * K)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hgraded H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT g E P R hX hP hE hR
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let V := fun j => F.symbolPointwiseSubalgebra b ω hlayers w (U j)
  let v' := fun j => F.pointwiseSymbolSpanningFamily b ω hlayers w (v j)
  let q : ℝ := (p + (s + 3)) ^ (s + 3)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := symbol_spanning_parameter_ge s hp
  have hcount : (Fintype.card (SymbolBasisIndex w ω × κ) : ℝ) ≤ q := by
    have hnat : Fintype.card (SymbolBasisIndex w ω × κ) ≤
        Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s * Fintype.card κ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ω s hw
        (F.adaptedBasis_weight_le_step b ω hlayers))
    exact (Nat.cast_le.mpr hnat).trans
      (symbol_spanning_count_bound s _ _ _ hp hι hσ hκ)
  have hcost : (q + 2) ^ K ≤ (p + 2) ^ C := by
    apply (symbol_spanning_parameter_power_bound s K hp).trans
    apply pow_le_pow_right₀ (by linarith only [hp] : 1 ≤ p + 2)
    exact le_max_right _ _
  have hcostexp := Real.exp_le_exp.mpr hcost
  have hTq : ∀ i, Real.exp ((q + 2) ^ K) ≤ T i := fun i => hcostexp.trans (hT i)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hP' : ∀ j, (P j).coord ∈ realificationLieSubalgebra (V j) := by
    intro j
    exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w (U j) _).mpr (hP j)
  have hE' : ∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((q + 2) ^ a)) (E j) := by
    intro j
    apply F.symbolSlowBound_mono b ω hlayers w T hTpos _ (E j) (hE j)
    exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl 2)) a)
  obtain ⟨m, e₀, p₀, r₀, hm, hmp, hlm, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hsplit F b ω hlayers w hw V v'
      (fun j => F.pointwiseSymbolSpanningFamily_span b ω hlayers w (U j) (hgraded j) (v j) (hspan j))
      (fun j => F.symbolPointwiseSubalgebra_blockInvariant b ω hlayers w (U j))
      H l q hH hl hq (hι.trans hpq) (hσ.trans hpq) hcount (hη.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq)) hb
      (fun j => F.pointwiseSymbolSpanningFamily_height b ω hlayers w (v j) hH (hv j))
      T hTq g E P R hX hP' hE' hR
  refine ⟨m, e₀, p₀, r₀, hm, hmp.trans hcostexp, hlm, hepr, ?_, ?_, hr, he0, hr0, hp0⟩
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w (⨅ j, U j) _).mp
    rw [F.symbolPointwiseSubalgebra_iInf]
    exact hmid
  · intro α i
    exact (he α i).trans
      (div_le_div_of_nonneg_right hcostexp (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_common_polynomial_step_drop_factors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (eta : J → L →ₗ[ℚ] ℚ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.ControlledSymbolFactorization b ω hF (eta j) T
        (F.realPolynomialSymbolHom b ω hF (fun _ => 1) g) p) →
      ∃ (U : J → LieSubalgebra ℚ F.AssociatedGraded) (v : J → ι → F.AssociatedGraded)
        (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) ∧
        (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω (U j).toSubmodule) ∧
        (∀ j i k, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j i) k) ≤ p) ∧
        (∀ j x, x ∈ (⨅ j, U j) → basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
          F.gradedFrequency b ω hF (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hF (fun _ => 1)
          (F.realPolynomialSymbolHom b ω hF (fun _ => 1) p₀).coord) ∈
            realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨K, hK, hsplit⟩ := exists_pointwise_polynomial_symbol_splitting s 1
  refine ⟨2 * K, by omega, ?_⟩
  intro σ ι J L _ _ _ _ _ F b ω hF eta p hp hι hσ hJ hstructure T hT g hfactor
  classical
  choose m E P R U v hm hmp hprod hE hR hv hU hheight hfreq hP using hfactor
  let l := ∏ j, m j
  have hl : 0 < l := Finset.prod_pos (fun j _ => hm j)
  have hdvd (j : J) : m j ∣ l := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let q := p ^ 2 + p + 2
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hq : 0 ≤ q := hp.trans hpq
  have hq1 : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcost : (q + 2) ^ K ≤ (p + 2) ^ (2 * K) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    dsimp [q]
    nlinarith
  have hlq : (l : ℝ) ≤ Real.exp q :=
    (product_denominator_le_budget m hp hJ hmp).trans
      (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hq1)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hslow : ∀ j, F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp ((q + 2) ^ 1)) (E j) := by
    intro j
    apply F.symbolSlowBound_mono b ω hF (fun _ => 1) T hTpos _ (E j) (hE j)
    exact Real.exp_le_exp.mpr (by simpa only [pow_one] using hpq.trans (by linarith : q ≤ q + 2))
  have hrat : ∀ j, F.SymbolRationalGrid b ω hF (fun _ => 1) l (R j) :=
    fun j => F.symbolRationalGrid_mono b ω hF (fun _ => 1) (hm j) (hdvd j) (R j) (hR j)
  obtain ⟨m₀, e₀, p₀, r₀, hm₀, hm₀q, _, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hsplit F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) U v hv hU H l q hH hl hq
      (hι.trans hpq) (hσ.trans hpq) (hι.trans hpq) (hJ.trans hpq) hHq hlq
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (fun j i k => rationalHeightLE_ceil_exp (hheight j i k)) T
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hT i)) g E P R hprod
      (fun j => (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF (fun _ => 1) (U j) _).mp (hP j))
      hslow hrat
  refine ⟨U, v, m₀, e₀, p₀, r₀, hv, hU, hheight, ?_, hm₀,
    hm₀q.trans (Real.exp_le_exp.mpr hcost), hepr, hmid, ?_, hr, he0, hr0, hp0⟩
  · intro j x hx hxgrade
    exact hfreq j x ((lieSubalgebra_mem_iInf U x).mp hx j) hxgrade
  · intro α i
    exact (he α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost)
      (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_outer_polynomial_product_bounds (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ qs rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
        qs.length ≤ k → rs.length ≤ k →
        (∀ q ∈ qs, q.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ q ∈ qs, CoefficientBound (b.baseChange ℝ) (fun _ => 1)
          (Real.exp ((p + 2) ^ a)) q.coord) →
        (∀ r ∈ rs, CoefficientGrid (b.baseChange ℝ) l r.coord) →
        CoefficientBound (b.baseChange ℝ) (fun _ => 1)
          (Real.exp ((p + C) ^ C)) qs.prod.coord ∧
        CoefficientGrid (b.baseChange ℝ) m rs.reverse.prod.coord := by
  obtain ⟨Cs, hCs, hslow⟩ := exists_formal_polynomial_product_bound s a k
  obtain ⟨Cr, hCr, hrat⟩ := exists_formal_polynomial_product_grid s k
  refine ⟨max Cs Cr, hCs.trans (le_max_left _ _), ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  have hbs : (p + Cs) ^ Cs ≤ (p + (max Cs Cr : ℕ)) ^ max Cs Cr :=
    shifted_power_self_mono hp (by omega) (le_max_left _ _)
  have hbr : (p + Cr) ^ Cr ≤ (p + (max Cs Cr : ℕ)) ^ max Cs Cr :=
    shifted_power_self_mono hp (by omega) (le_max_right _ _)
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ := hrat F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hbr), hlm, ?_⟩
  intro qs rs hqs hrs hqa hra hqb hrb
  constructor
  · have h := hslow F b ω hF H p hH hp hι hσ hHp hstructure
      (fun _ => 1) (fun _ => zero_lt_one) qs hqs hqa hqb
    intro α i
    exact (h α i).trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr hbs) (monomialScale_pos (fun _ => 1) (fun _ => zero_lt_one) α).le)
  · exact hgrid rs.reverse (by simpa only [List.length_reverse] using hrs)
      (fun r hr => hra r (List.mem_reverse.mp hr))
      (fun r hr => hrb r (List.mem_reverse.mp hr))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

attribute [local instance] OAI.Erdos3.OrdinaryPolynomialPhase.phaseBasisFintype
theorem two_le_budget (s : ℕ) : 2 ≤ budget s := by
  apply le_trans _ (le_max_left _ _)
  have hf := Nat.factorial_pos s
  have hn : 2 ≤ 0 + (0 + 1)^s + s.factorial + 2*s + 1 := by
    simp only [zero_add, one_pow]
    omega
  exact_mod_cast hn

end Erdos3.OrdinaryPolynomialPhase

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

theorem refiltration_coefficients_mem_first_of_constant
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hconstant : coefficients p 0 ∈ F.realGradedRefiltrationLayer W 1) :
    ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W 1 := by
  intro α
  by_cases hα : α = 0
  · simpa only [hα] using hconstant
  · exact F.realGradedRefiltrationLayer_antitone W
      (positive_weight_of_ne_zero w hw hα) (hp α)

theorem exists_native_refiltered_orbit_of_constant
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hconstant : coefficients p 0 ∈ F.realGradedRefiltrationLayer W 1) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p := by
  have hfirst := F.refiltration_coefficients_mem_first_of_constant W w hw p hp hconstant
  have hcoeff : ∀ α, coefficients p α ∈ (F.realGradedRefiltrationSubalgebra W).toSubmodule := by
    intro α
    exact (F.mem_realGradedRefiltrationSubalgebra W _).mpr (hfirst α)
  let q₀ := restrictCoefficients (F.realGradedRefiltrationSubalgebra W).toSubmodule p hcoeff
  have hq₀ : VectorPolynomial.map
      (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap q₀ = p :=
    map_restrictCoefficients (F.realGradedRefiltrationSubalgebra W).toSubmodule p hcoeff
  let H := F.gradedRefiltrationSubalgebra W
  let inc := (realLieHomToRat (realificationLieHom H.incl)).toLinearMap
  let lift : F.realGradedRefiltrationSubalgebra W →ₗ[ℚ] (ℝ ⊗[ℚ] H) :=
    (realificationSubmoduleEquiv H.toSubmodule).symm.toLinearMap.restrictScalars ℚ
  have hcomp : inc.comp lift = (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap := by
    ext x
    exact congrArg Subtype.val ((realificationSubmoduleEquiv H.toSubmodule).apply_symm_apply x)
  let q := VectorPolynomial.map lift q₀
  have hmap : VectorPolynomial.map inc q = p := by
    apply coefficients.injective
    ext α
    dsimp only [q]
    rw [coefficients_map, coefficients_map]
    change (inc.comp lift) (coefficients q₀ α) = coefficients p α
    rw [hcomp]
    simpa only [coefficients_map] using congrArg (fun r => coefficients r α) hq₀
  have hadapted : (F.gradedRefiltration W).realification.Adapted w q := by
    apply ((F.gradedRefiltration W).realification.adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_native_refiltration_layer]
    have h := congrArg (fun r => coefficients r α) hmap
    rw [coefficients_map] at h
    change inc (coefficients q α) ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α)
    rw [h]
    exact hp α
  exact ⟨polynomialOrbitOfLog q hadapted, hmap⟩

theorem exists_native_refiltered_orbit_real_values_of_constant
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hconstant : coefficients p 0 ∈ F.realGradedRefiltrationLayer W 1) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
          (⟨eval₂ t p⟩ : F.realification.Group) := by
  obtain ⟨q, hq⟩ := F.exists_native_refiltered_orbit_of_constant W w hw p hp hconstant
  exact ⟨q, hq, fun t => F.native_refiltered_orbit_real_value W w q p hq t⟩

theorem exists_native_pointwise_refiltered_orbit_of_constant
    {ι : Type*} (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : F.realification.adaptedLieSubalgebra w)
    (hconstant : coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1)
    (hW : ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra W) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
          (⟨eval₂ t (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))⟩ : F.realification.Group) :=
  F.exists_native_refiltered_orbit_real_values_of_constant W w hw p
    ((F.real_symbol_values_iff_refiltration_coefficients b ω hlayers w W p).mp hW) hconstant

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ)

noncomputable def filteredRealPolynomialSection (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (g : (G.realification.adaptedPolynomialFiltration w).Group) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  ⟨⟨map ((S.baseChange ℝ).restrictScalars ℚ)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)), by
    intro α
    rw [coefficients_map]
    exact baseChange_mem_of_mapsTo (G.layer (Finsupp.weight w α))
      (F.layer (Finsupp.weight w α)) S (hS _) (g.coord.property α)⟩⟩

variable (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realPolynomialGroupMap_filteredSection (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)
    (g : (G.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialGroupMap G φ hφ w (F.filteredRealPolynomialSection G w S hS g) = g := by
  have hcomp : φ.toLinearMap.comp S = LinearMap.id := LinearMap.ext hsection
  have hcompR := congrArg
    (fun f : M →ₗ[ℚ] M => f.baseChange ℝ) hcomp
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hcompR
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  apply coefficients.injective
  ext α
  change coefficients (map ((φ.toLinearMap.baseChange ℝ).restrictScalars ℚ)
    (map ((S.baseChange ℝ).restrictScalars ℚ)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)))) α = _
  rw [coefficients_map, coefficients_map]
  exact DFunLike.congr_fun hcompR _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTopQuotient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_quotient_marked_layer_lift
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y)
    (j : ℕ) (a : L ⧸ F.layerIdeal s) (b : M)
    (ha : a ∈ (F.layer j).map (lieQuotientMap (F.layerIdeal s)).toLinearMap)
    (hb : b ∈ G.layer j)
    (hcompat : lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) a =
      lieQuotientMap (G.layerIdeal s) b) :
    ∃ x ∈ F.layer j, lieQuotientMap (F.layerIdeal s) x = a ∧ φ x = b := by
  by_cases hjs : j ≤ s
  · obtain ⟨z, hz, hza⟩ := ha
    have hδ : b - φ z ∈ G.layer s := by
      apply (lieQuotientMap_eq_zero (G.layerIdeal s) _).mp
      rw [map_sub, sub_eq_zero]
      exact hcompat.symm.trans
        (congrArg (lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s)) hza.symm)
    obtain ⟨t, ht, hφt⟩ := honto (b - φ z) hδ
    refine ⟨z + t, (F.layer j).add_mem hz (F.antitone hjs ht), ?_, ?_⟩
    · rw [map_add, (lieQuotientMap_eq_zero (F.layerIdeal s) t).mpr ht, add_zero]
      exact hza
    · rw [map_add, hφt]
      abel
  · have hj : s + 1 ≤ j := by omega
    have ha0 : a = 0 := by
      obtain ⟨z, hz, rfl⟩ := ha
      have hz0 : z = 0 := by
        have h := F.antitone hj hz
        rw [F.terminal] at h
        exact h
      rw [hz0, map_zero]
    have hb0 : b = 0 := by
      have h := G.antitone hj hb
      rw [G.terminal] at h
      exact h
    exact ⟨0, (F.layer j).zero_mem, by rw [map_zero, ha0], by rw [map_zero, hb0]⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_adapted_quotient_fiber_polynomial_lift
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y)
    (w : σ → ℕ) (pbar : VectorPolynomial σ ℚ (L ⧸ F.layerIdeal s))
    (q : VectorPolynomial σ ℚ M)
    (hcompat : map (lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s)).toLinearMap
      pbar = map (lieQuotientMap (G.layerIdeal s)).toLinearMap q)
    (hpbar : ∀ a, coefficients pbar a ∈
      (F.layer (Finsupp.weight w a)).map (lieQuotientMap (F.layerIdeal s)).toLinearMap)
    (hq : G.Adapted w q) :
    ∃ p : VectorPolynomial σ ℚ L,
      F.Adapted w p ∧ map (lieQuotientMap (F.layerIdeal s)).toLinearMap p = pbar ∧
        map φ.toLinearMap p = q := by
  classical
  have hc (a : σ →₀ ℕ) :
      lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) (coefficients pbar a) =
        lieQuotientMap (G.layerIdeal s) (coefficients q a) := by
    simpa only [coefficients_map, LieHom.coe_toLinearMap] using
      congrArg (fun P => coefficients P a) hcompat
  have hex (a : σ →₀ ℕ) : ∃ x ∈ F.layer (Finsupp.weight w a),
      lieQuotientMap (F.layerIdeal s) x = coefficients pbar a ∧ φ x = coefficients q a :=
    F.exists_quotient_marked_layer_lift G φ hφ honto (Finsupp.weight w a)
      (coefficients pbar a) (coefficients q a) (hpbar a)
      ((G.adapted_iff_coefficients w q).mp hq a) (hc a)
  let v (a : σ →₀ ℕ) : L :=
    if coefficients pbar a = 0 ∧ coefficients q a = 0 then 0 else Classical.choose (hex a)
  have hv (a : σ →₀ ℕ) : v a ∈ F.layer (Finsupp.weight w a) ∧
      lieQuotientMap (F.layerIdeal s) (v a) = coefficients pbar a ∧
        φ (v a) = coefficients q a := by
    dsimp only [v]
    split_ifs with hz
    · exact ⟨(F.layer _).zero_mem, (map_zero _).trans hz.1.symm,
        (map_zero _).trans hz.2.symm⟩
    · exact Classical.choose_spec (hex a)
  let c : (σ →₀ ℕ) →₀ L := Finsupp.onFinset
    ((coefficients pbar).support ∪ (coefficients q).support) v (by
      intro a ha
      apply Finset.mem_union.mpr
      by_cases hp0 : coefficients pbar a = 0
      · right
        apply Finsupp.mem_support_iff.mpr
        intro hq0
        exact ha (by simp only [v, hp0, hq0, and_self, ite_true])
      · exact Or.inl (Finsupp.mem_support_iff.mpr hp0))
  let p : VectorPolynomial σ ℚ L := coefficients.symm c
  have hcoef (a : σ →₀ ℕ) : coefficients p a = v a := by
    simp only [p, LinearEquiv.apply_symm_apply, c, Finsupp.onFinset_apply]
  refine ⟨p, ?_, ?_, ?_⟩
  · apply (F.adapted_iff_coefficients w p).mpr
    intro a
    rw [hcoef]
    exact (hv a).1
  · apply coefficients.injective
    ext a
    rw [coefficients_map, hcoef]
    exact (hv a).2.1
  · apply coefficients.injective
    ext a
    rw [coefficients_map, hcoef]
    exact (hv a).2.2

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (b : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

include b ν hG in

theorem gradedRefiltrationLayer_map (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) (j : ℕ) :
    (F.gradedRefiltrationLayer U j).map φ.toLinearMap =
      G.gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) j := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxF, hxU⟩ := (F.mem_gradedRefiltrationLayer U j x).mp hx
    apply (G.mem_gradedRefiltrationLayer _ j (φ x)).mpr
    refine ⟨hφ j x hxF, F.associatedGradedPieceMap j ⟨x, hxF⟩, hxU, ?_⟩
    exact F.associatedGradedMap_piece G φ hφ j ⟨x, hxF⟩
  · intro y hy
    obtain ⟨hyG, hyU⟩ := (G.mem_gradedRefiltrationLayer _ j y).mp hy
    obtain ⟨a, ha, haeq⟩ := hyU
    change F.associatedGradedMap G φ hφ a = G.associatedGradedPieceMap j ⟨y, hyG⟩ at haeq
    let a' := basisGradeProjection (F.associatedGradedBasis e ω hF) ω j a
    have ha'U : a' ∈ U := hU j a ha
    have ha'pure : basisGradeProjection (F.associatedGradedBasis e ω hF) ω j a' = a' := by
      apply (F.associatedGradedBasis e ω hF).repr.injective
      ext i
      simp only [a', basisGradeProjection_repr]
      split_ifs <;> rfl
    obtain ⟨x, hx⟩ := F.exists_associatedGradedPieceMap_of_pure e ω hF j a' ha'pure
    have hgraded : F.associatedGradedMap G φ hφ (F.associatedGradedPieceMap j x) =
        G.associatedGradedPieceMap j ⟨y, hyG⟩ := by
      rw [hx]
      change F.associatedGradedMap G φ hφ
        (basisGradeProjection (F.associatedGradedBasis e ω hF) ω j a) = _
      rw [F.associatedGradedMap_gradeProjection G e ω hF b ν hG φ hφ, haeq]
      exact G.associatedGradedPieceMap_grade_fixed b ν hG j ⟨y, hyG⟩
    have hδ : y - φ x ∈ G.layer (j + 1) := by
      apply (G.associatedGradedPieceMap_eq_zero_iff j
        ⟨y - φ x, (G.layer j).sub_mem hyG (hφ j x x.property)⟩).mp
      change G.associatedGradedPieceMap j
        (⟨y, hyG⟩ - ⟨φ x, hφ j x x.property⟩) = 0
      rw [map_sub, ← F.associatedGradedMap_piece G φ hφ j x, hgraded, sub_self]
    obtain ⟨z, hz, hzeq⟩ := hsurj (j + 1) (y - φ x) hδ
    refine ⟨(x : L) + z, (F.gradedRefiltrationLayer U j).add_mem ?_
      (F.layer_succ_le_gradedRefiltrationLayer U j hz), ?_⟩
    · exact (F.mem_gradedRefiltrationLayer U j x).mpr ⟨x.property, hx.symm ▸ ha'U⟩
    · change φ ((x : L) + z) = y
      rw [map_add, hzeq]
      abel

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RefilteredKernelConstantBounds
namespace OAI

section

namespace Erdos3
open Module
open scoped TensorProduct BigOperators

namespace NilpotentLieFiltration

variable {ι L M : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (H : Submodule ℚ L) (hH : F.layer 2 ≤ H)
    (b : Basis ι ℚ (LinearMap.ker φ.toLinearMap))

include hH

theorem exists_kernel_constant_factors (g : F.realification.Group)
    (hg : realificationLieHom φ g.coord ∈ (H.map φ.toLinearMap).baseChange ℝ) :
    ∃ (e : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap) (r : LinearMap.ker φ.toLinearMap),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr e i ∧ (b.baseChange ℝ).repr e i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr r i = z) ∧
      let kE : F.realification.Group := ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e⟩
      let kR : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (r : L)⟩
      NilpotentLieBCHGroup.realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ kE = 1 ∧
      NilpotentLieBCHGroup.realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ kR = 1 ∧
      (kE⁻¹ * g * kR⁻¹).coord ∈ H.baseChange ℝ := by
  obtain ⟨e, r, he, hr, hlin⟩ :=
    exists_fractional_integer_kernel_correction φ.toLinearMap H b g.coord hg
  refine ⟨e, r, he, hr, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    change φ.toLinearMap.baseChange ℝ
      ((LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e) = 0
    have hm : (LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e ∈
        (LinearMap.ker φ.toLinearMap).baseChange ℝ := ⟨e, rfl⟩
    rwa [realification_ker, LinearMap.mem_ker] at hm
  · apply NilpotentLieBCHGroup.ext
    change φ.toLinearMap.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] (r : L)) = 0
    rw [LinearMap.baseChange_tmul, show φ.toLinearMap (r : L) = 0 from r.property,
      TensorProduct.tmul_zero]
  · let a := (LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e
    let c := (1 : ℝ) ⊗ₜ[ℚ] (r : L)
    have hbch := F.realification.bch_triple_sub_sum_mem_next_layer 1 (-a) g.coord (-c)
      (by rw [F.realification.one_eq_top]; trivial)
      (by rw [F.realification.one_eq_top]; trivial)
    have hm : lieBCH s (lieBCH s (-a) g.coord) (-c) - (-a + g.coord + -c) ∈
        H.baseChange ℝ := Submodule.baseChange_mono ℝ hH hbch
    have hlin' : -a + g.coord + -c ∈ H.baseChange ℝ := by
      convert hlin using 1
      dsimp [a, c]
      abel
    have hh := (H.baseChange ℝ).add_mem hm hlin'
    simpa only [sub_add_cancel, NilpotentLieBCHGroup.coord_mul,
      NilpotentLieBCHGroup.coord_inv] using hh

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_common_refiltered_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (eta : J → L →ₗ[ℚ] ℚ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.ControlledSymbolFactorization b w hF (eta j) T
        (F.realPolynomialSymbolHom b w hF (fun _ => 1) g) p) →
      ∃ (W : LieSubalgebra ℚ F.AssociatedGraded) (v : Fin (Fintype.card ι) → F.AssociatedGraded)
        (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis b w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v i) k) ≤
          ((p + 2) ^ 2 + 2) ^ 63 + 1) ∧
        (∀ j x, x ∈ F.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b w hF (fun _ => 1)
          (F.realPolynomialSymbolHom b w hF (fun _ => 1) p₀).coord) ∈ realificationLieSubalgebra W) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∧
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
          ∀ t : σ → ℝ, eval₂ t (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
            realificationLieSubalgebra (F.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨C, hC, hcommon⟩ := exists_common_polynomial_step_drop_factors s
  refine ⟨C, hC, ?_⟩
  intro σ ι J L _ _ _ _ _ F b w hF eta p hp hι hσ hJ hstructure T hT g hfactor
  obtain ⟨U, v, m, e₀, p₀, r₀, hv, hU, hheight, hfreq, hm, hmp, hepr,
      hmid, he, hr, he0, hr0, hp0⟩ :=
    hcommon F b w hF eta p hp hι hσ hJ hstructure T hT g hfactor
  let W := ⨅ j, U j
  obtain ⟨v₀, hv₀, hheight₀⟩ := exists_intersection_spanning_logHeight
    (F.associatedGradedBasis b w hF) U v hv hp hι hι hJ hheight
  have hW : BasisGradedSubmodule (F.associatedGradedBasis b w hF) w W.toSubmodule := by
    intro k x hx
    apply (lieSubalgebra_mem_iInf U _).mpr
    intro j
    exact hU j k x ((lieSubalgebra_mem_iInf U x).mp hx j)
  refine ⟨W, v₀, m, e₀, p₀, r₀, hv₀, hW, hheight₀, ?_, hm, hmp, hepr,
    hmid, he, hr, he0, hr0, hp0, ?_⟩
  · intro j
    exact F.real_frequency_zero_on_refiltered_top b w hF W (eta j) (hfreq j)
  · intro hzero
    exact F.pointwise_refiltered_values_mem b w hF (fun _ => 1) W (fun _ => Nat.zero_lt_one)
      p₀.coord (hp0.trans hzero) hmid

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrescribedFastPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_polynomial_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ) (Γ : Subgroup F.Group) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ →
      (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
      ∃ (r γ : F.realification.Group) (q : (F.realification.adaptedPolynomialFiltration w).Group),
        (∀ i, |(b.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom ∧
        F.realification.adaptedConstantGroupHom w r * q *
          F.realification.adaptedConstantGroupHom w γ = g ∧
        coefficients (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        F.realPolynomialSymbolHom b ω hlayers w q = F.realPolynomialSymbolHom b ω hlayers w g := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ _ _ F b ω hlayers w Γ l H p hl hinner hb hp hd hH hlp g
  obtain ⟨r, hr, γ, hγ, hconst⟩ := hrep b F.lowerCentralSeries_eq_bot Γ l H p hl hinner hb hp hd hH hlp
    (F.realification.adaptedPolynomialConstantHom w g)
  obtain ⟨q, hfactor, hzero, hsymbol⟩ := F.realification.exists_constant_normalized_polynomial w g r γ hconst
  refine ⟨r, γ, q, hr, hγ, hfactor, hzero, ?_⟩
  apply NilpotentLieBCHGroup.ext
  exact congrArg (F.realPolynomialSymbolQuotientEquiv b ω hlayers w)
    (congrArg NilpotentLieBCHGroup.coord hsymbol)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

noncomputable def realFilteredSymbolGroupMap :
    F.RealPolynomialSymbolGroup w →* G.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.filteredPolynomialSymbolMap G φ hφ w)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def nativeRefiltrationLayerEquiv (j : ℕ) (hj : 1 ≤ j) :
    (F.gradedRefiltration W).layer j ≃ₗ[ℚ] F.gradedRefiltrationLayer W j :=
  Submodule.comapSubtypeEquivOfLe (F.gradedRefiltrationLayer_antitone W hj)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeMarkedPolynomialFreezing
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module NilpotentLieBCHGroup
open scoped TensorProduct
variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

variable (w : σ → ℕ)

noncomputable def frozenMarkedLeft (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (EF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kE : F.realification.Group) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  F.realification.adaptedConstantGroupHom w kE *
    F.filteredRealPolynomialSection G w S hS EF

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenMarkedLeftOrbitBound
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)

noncomputable def frozenMarkedLeftOrbit
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group) :
    F.realification.PolynomialOrbit w :=
  (F.realification.polynomialOrbitCoordinates w).symm
    (F.frozenMarkedLeft G w S hS
      (G.realification.polynomialOrbitCoordinates w marked) center)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]

theorem sectionCorrectedPolynomial_map (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (hS : Function.RightInverse S φ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) :
    map ((φ.baseChange ℝ).restrictScalars ℚ) (sectionCorrectedPolynomial φ S p q) = q := by
  apply coefficients.injective
  ext a
  rw [coefficients_map, sectionCorrectedPolynomial_coefficients]
  change φ.baseChange ℝ (coefficients p a -
    S.baseChange ℝ (φ.baseChange ℝ (coefficients p a) - coefficients q a)) = _
  rw [map_sub, linearMap_baseChange_rightInverse φ S hS]
  abel

namespace NilpotentLieFiltration

variable {ι κ : Type*} {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)

theorem real_projected_discrepancy_mem_shifted
    (p : F.realification.adaptedLieSubalgebra w)
    (q : G.realification.adaptedLieSubalgebra w)
    (hcompat : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
      (F.realPolynomialSymbolMap b ω hF w p) = G.realPolynomialSymbolMap c τ hG w q) :
    F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ))
      (F.realificationLieHom_mem_layer G φ hφ) w p - q ∈
        G.realification.shiftedAdaptedIdeal w := by
  let r : G.realification.adaptedLieSubalgebra w :=
    F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ))
      (F.realificationLieHom_mem_layer G φ hφ) w p
  have he : G.realSymbolOfPolynomial c τ hG w r.val =
      G.realSymbolOfPolynomial c τ hG w q.val := by
    calc
      _ = G.realSymbolOfPolynomial c τ hG w
        (map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) p.val) :=
        congrArg (G.realSymbolOfPolynomial c τ hG w)
          (F.realification.filteredPolynomialMap_coe G.realification
            (realLieHomToRat (realificationLieHom φ))
            (F.realificationLieHom_mem_layer G φ hφ) w p)
      _ = (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) :=
        (F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c τ hG w p).symm
      _ = _ := hcompat
  have h := (G.realSymbolOfPolynomial_eq_iff_symbolMap_eq c τ hG w r q).mp he
  exact (G.realification.polynomialSymbolMap_eq_iff w r q).mp h

theorem sectionCorrectedPolynomial_prescribed_symbol
    (S : M →ₗ[ℚ] L) (hS : Function.RightInverse S φ)
    (hSlayer : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (x : F.RealPolynomialSymbol w) (q : G.realification.adaptedLieSubalgebra w)
    (hcompat : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ x =
      G.realPolynomialSymbolMap c τ hG w q) :
    ∃ p : F.realification.adaptedLieSubalgebra w,
      p.val = sectionCorrectedPolynomial φ.toLinearMap S
        (F.realSymbolRepresentative b ω hF w x) q.val ∧
      F.realPolynomialSymbolMap b ω hF w p = x ∧
      F.realification.filteredPolynomialMap G.realification
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ) w p = q := by
  let p₀ : F.realification.adaptedLieSubalgebra w :=
    F.realAdaptedSymbolRepresentative b ω hF w x
  have hp₀ : F.realPolynomialSymbolMap b ω hF w p₀ = x := by
    dsimp only [p₀]
    exact F.realPolynomialSymbolMap_representative b ω hF w x
  let φR : (ℝ ⊗[ℚ] L) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] M) := realLieHomToRat (realificationLieHom φ)
  let hφR := F.realificationLieHom_mem_layer G φ hφ
  let δ : G.realification.adaptedLieSubalgebra w :=
    F.realification.filteredPolynomialMap G.realification φR hφR w p₀ - q
  have hδ : δ ∈ G.realification.shiftedAdaptedIdeal w := by
    apply F.real_projected_discrepancy_mem_shifted G φ hφ b ω hF c τ hG w p₀ q
    rw [hp₀]
    exact hcompat
  have hd (a : σ →₀ ℕ) :
      coefficients (map ((S.baseChange ℝ).restrictScalars ℚ) δ.val) a ∈
        F.realification.layer (Finsupp.weight w a + 1) := by
    rw [coefficients_map]
    exact baseChange_mem_of_mapsTo (G.layer (Finsupp.weight w a + 1))
      (F.layer (Finsupp.weight w a + 1)) S (hSlayer _) (hδ a)
  let d : F.realification.adaptedLieSubalgebra w :=
    ⟨map ((S.baseChange ℝ).restrictScalars ℚ) δ.val,
      fun a => F.realification.antitone (Nat.le_succ _) (hd a)⟩
  have hdz : F.realPolynomialSymbolMap b ω hF w d = 0 := by
    apply (F.realPolynomialSymbolMap_eq_zero_iff b ω hF w d).mpr
    exact (F.realification.polynomialSymbolMap_eq_zero_iff w d).mpr hd
  refine ⟨p₀ - d, rfl, ?_, ?_⟩
  · rw [map_sub, hdz, sub_zero]
    exact hp₀
  · apply Subtype.ext
    exact sectionCorrectedPolynomial_map φ.toLinearMap S hS
      (F.realSymbolRepresentative b ω hF w x) q.val

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

theorem exists_filtered_linear_section
    (c : Basis κ ℚ M) (v : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ v k}))
    (φ : L →ₗ[ℚ] M)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) :
    ∃ S : M →ₗ[ℚ] L, Function.RightInverse S φ ∧
      ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j := by
  classical
  have hmem (k : κ) : c k ∈ G.layer (v k) := by
    rw [hG]
    exact Submodule.subset_span ⟨k, (show v k ≤ v k from le_rfl), rfl⟩
  choose x hx hφx using fun k => hsurj (v k) (c k) (hmem k)
  let S := c.constr ℚ x
  have hS (k : κ) : S (c k) = x k := c.constr_basis ℚ x k
  refine ⟨S, ?_, ?_⟩
  · have heq : φ.comp S = LinearMap.id := by
      apply c.ext
      intro k
      change φ (S (c k)) = c k
      rw [hS, hφx]
    intro y
    exact congrArg (fun f : M →ₗ[ℚ] M => f y) heq
  · intro j y hy
    have hle : G.layer j ≤ (F.layer j).comap S := by
      rw [hG]
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change S (c k) ∈ F.layer j
      rw [hS]
      exact F.antitone hk (hx k)
    exact hle hy

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem externalCandidate_stepZero_coord_eq_zero (F : NilpotentLieFiltration L 0)
    (x : L) : x = 0 := by
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  simpa only [F.terminal, Submodule.mem_bot] using hx

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem associatedGradedMap_basis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hφH : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p) (i : ι) (j : κ) :
    rationalLogHeight ((G.associatedGradedBasis f ν hG).repr
      (F.associatedGradedMap G φ hφ (F.associatedGradedBasis e ω hF i)) j) ≤ p := by
  classical
  rw [F.associatedGradedMap_basis_repr G e ω hF f ν hG φ hφ]
  split_ifs
  · exact hφH i j
  · simpa [rationalLogHeight] using hp

theorem exists_associatedGradedMap_comap_bounded_spanning [Fintype ι] [Fintype κ]
    (U : LieSubalgebra ℚ G.AssociatedGraded) (v : κ → G.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ a j, rationalLogHeight ((G.associatedGradedBasis f ν hG).repr (v a) j) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p) :
    ∃ u : ι → F.AssociatedGraded,
      Submodule.span ℚ (Set.range u) =
        (U.comap (F.associatedGradedMap G φ hφ)).toSubmodule ∧
      ∀ a i, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (u a) i) ≤
        preimageBasisBudget p + 1 := by
  classical
  let eA := F.associatedGradedBasis e ω hF
  let fA := G.associatedGradedBasis f ν hG
  let T := (F.associatedGradedMap G φ hφ).toLinearMap
  let K := U.toSubmodule.comap T
  have heH (a i : ι) : rationalLogHeight (eA.repr (eA a) i) ≤ p := by
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simpa [rationalLogHeight] using hp
  obtain ⟨b, hb⟩ := exists_preimage_basis_logHeight eA fA ⊤ U.toSubmodule T eA v
    eA.span_eq hv hp hκ hι hκ heH hvH
    (F.associatedGradedMap_basis_logHeight G e ω hF f ν hG φ hφ hp hφH)
  have hspan : Submodule.span ℚ (Set.range (fun a => (b a : F.AssociatedGraded))) = K := by
    change Submodule.span ℚ (Set.range ((⊤ ⊓ K).subtype ∘ b)) = K
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype, top_inf_eq]
  obtain ⟨z, hz, hzH⟩ := exists_bounded_submodule_ambient_spanning eA K
    (fun a => (b a : F.AssociatedGraded)) hspan (one_le_ceil_exp (preimageBasisBudget p))
    (fun a i => rationalHeightLE_ceil_exp (hb a i))
  refine ⟨fun a => z (Fintype.equivFin ι a), ?_, fun a i => ?_⟩
  · change Submodule.span ℚ (Set.range (z ∘ Fintype.equivFin ι)) = K
    rw [Set.range_comp, (Fintype.equivFin ι).surjective.range_eq, Set.image_univ]
    exact hz
  · exact rationalLogHeight_le_of_height (hzH _ i)
      (ceil_exp_le_exp_add_one (preimageBasisBudget_nonneg hp))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ γ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def gradedImageSpanningFamily (v : γ → F.AssociatedGraded) :
    γ → G.AssociatedGraded := fun a => F.associatedGradedMap G φ hφ (v a)

theorem gradedImageSpanningFamily_span (W : LieSubalgebra ℚ F.AssociatedGraded)
    (v : γ → F.AssociatedGraded) (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (F.gradedImageSpanningFamily G φ hφ v)) =
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule := by
  change Submodule.span ℚ (Set.range ((F.associatedGradedMap G φ hφ).toLinearMap ∘ v)) =
    W.toSubmodule.map (F.associatedGradedMap G φ hφ).toLinearMap
  rw [Set.range_comp, ← Submodule.map_span, hv]

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem gradedImageSpanningFamily_logHeight [Fintype ι]
    (v : γ → F.AssociatedGraded) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) (a : γ) (j : κ) :
    rationalLogHeight ((G.associatedGradedBasis c ν hG).repr
      (F.gradedImageSpanningFamily G φ hφ v a) j) ≤ (p + 2) ^ 4 := by
  exact linearMap_coordinate_logHeight (F.associatedGradedBasis e ω hF)
    (G.associatedGradedBasis c ν hG) (F.associatedGradedMap G φ hφ).toLinearMap hp hι
    (F.associatedGradedMap_basis_logHeight G e ω hF c ν hG φ hφ hp hφH) (v a) (hvH a) j

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realificationLieSubalgebra_comap {L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (U : LieSubalgebra ℚ M) (φ : L →ₗ⁅ℚ⁆ M) :
    realificationLieSubalgebra (U.comap φ) =
      (realificationLieSubalgebra U).comap (realificationLieHom φ) := by
  apply LieSubalgebra.toSubmodule_injective
  exact realification_comap U.toSubmodule φ.toLinearMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPolynomialGroupMapBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ)

theorem polynomialRationalGrid_iff_coefficients [Finite ι] (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialRationalGrid b w l g ↔ ∀ α,
      (b.baseChange ℝ).equivFun
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) ∈
          realDenominatorGrid l := by
  classical
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext fun i => congrFun ha (α, i)⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext fun z => congrFun (ha z.1) z.2⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (b : Basis ι ℚ L) (c : Basis κ ℚ M)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)

theorem realPolynomialGroupMap_slow_exp
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hsource : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T A g) :
    G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ 3) * A)
      (F.realPolynomialGroupMap G φ hφ w g) := by
  classical
  let Q := LinearMap.toMatrix b c φ.toLinearMap
  have hQ : ∀ i j, RationalHeightLE (Q i j) H := by
    simpa only [Q, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using hentries
  have hnum : ∀ i j, ((Q i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 1) := by
    intro i j
    exact (Nat.cast_le.mpr (hQ i j).1).trans
      (hHp.trans (Real.exp_le_exp.mpr (by simp)))
  intro α i
  change |(c.baseChange ℝ).repr (coefficients
    ((F.realPolynomialGroupMap G φ hφ w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) α) i| ≤ _
  rw [F.realPolynomialGroupMap_log G φ hφ w, coefficients_map]
  change |(c.baseChange ℝ).equivFun (φ.toLinearMap.baseChange ℝ
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α)) i| ≤ _
  exact rational_coordinate_map_weighted_exp (b.baseChange ℝ) (c.baseChange ℝ)
    (φ.toLinearMap.baseChange ℝ) Q (realified_linear_coordinate_matrix b c φ.toLinearMap)
    (fun _ : ι => ()) (fun _ : κ => ()) (fun _ _ h => (h rfl).elim)
    hp hsource 1 (by decide) hnum (fun _ : Unit => monomialScale T α)
    (fun _ => monomialScale_pos T hT α) hA
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) (hg α) i

theorem exists_realPolynomialGroupMap_grid
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hsource : (Fintype.card ι : ℝ) ≤ p)
    (htarget : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
        F.PolynomialRationalGrid b w l g →
        G.PolynomialRationalGrid c w m (F.realPolynomialGroupMap G φ hφ w g) := by
  classical
  let Q := LinearMap.toMatrix b c φ.toLinearMap
  have hQ : ∀ i j, RationalHeightLE (Q i j) H := by
    simpa only [Q, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using hentries
  refine ⟨l * matrixDenominator Q, Nat.mul_pos hl (matrixDenominator_pos Q),
    matrixDenominator_allowance_le_exp Q l H hQ hp htarget hsource hHp hlp,
    dvd_mul_right l (matrixDenominator Q), ?_⟩
  intro g hg
  rw [G.polynomialRationalGrid_iff_coefficients]
  intro α
  have hc := (F.polynomialRationalGrid_iff_coefficients b w l g).mp hg α
  have ho := realified_linear_coordinate_grid b c φ.toLinearMap l _ hc
  rw [F.realPolynomialGroupMap_log G φ hφ w, coefficients_map]
  change (c.baseChange ℝ).equivFun (φ.toLinearMap.baseChange ℝ
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α)) ∈
      realDenominatorGrid (l * matrixDenominator Q)
  simpa only [Q, Nat.mul_comm] using ho

end Erdos3.NilpotentLieFiltration

end

end OAI
end


