-- Prove2me | Definitions.Def_OAIErdos3B116
-- name    : OAIErdos3B116
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T22:38:06.244757+00:00
-- url     : https://prove2.me/theorems/63ad7148-748a-4555-a1e4-540246402a24
-- title:
--   OpenAI Erdős-3 split, definitions bundle 117 of 125
-- statement:
--   Definitions bundle 117 of 125 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B115`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 117 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_terminal_symbol_comparison`, `OAI.Erdos3.NilpotentLieFiltration.exists_simultaneous_symbol_extension`, `OAI.Erdos3.NilpotentLieFiltration.exists_simultaneous_symbol_splitting`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotientHom_first`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotient_mem_terminal_iff`, `OAI.Erdos3.NilpotentLieFiltration.symbolRationalGrid_one`, `OAI.Erdos3.NilpotentLieFiltration.symbolSlowBound_one`, `OAI.Erdos3.PolynomialTranslationGroup.fromInteger`, `OAI.Erdos3.PolynomialTranslationGroup.fromInteger_base`, `OAI.Erdos3.PolynomialTranslationGroup.fromInteger_polynomial`, `OAI.Erdos3.PolynomialTranslationGroup.integralGroup`, `OAI.Erdos3.PolynomialTranslationGroup.integralGroup_action_integral`, `OAI.Erdos3.PolynomialTranslationGroup.mem_integralGroup_iff`, `OAI.Erdos3.PolynomialTranslationGroup.mem_integralGroup_iff_action`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationElement`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationElement_action`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_action`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_injective`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_rational`, `OAI.Erdos3.PolynomialTranslationLie.bchTranslationHom`, `OAI.Erdos3.PolynomialTranslationLie.bchTranslationHom_action`, `OAI.Erdos3.PolynomialTranslationLie.bchTranslationHom_apply`, `OAI.Erdos3.PolynomialTranslationLie.bchTranslationHom_mem_integralGroup_iff`, `OAI.Erdos3.PolynomialTranslationLie.bchTranslation_integral_comap`, `OAI.Erdos3.PolynomialTranslationLie.existsUnique_bchRealTranslation`, `OAI.Erdos3.PolynomialTranslationLie.exponentialElement_action_eq_shear`, `OAI.Erdos3.PolynomialTranslationLie.mem_weightedTranslationLattice`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_denominatorGrid_iff`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_integralVector_iff`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_integral_iff`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_scaledGrid_normalize`, `OAI.Erdos3.PolynomialTranslationLie.weightedOrderedBasis_inner_grid`, `OAI.Erdos3.PolynomialTranslationLie.weightedOrderedBasis_outer_grid`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearEmbedding_integral_iff`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationLattice`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationLattice_eq_integral_preimage`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationLattice_inner_grid`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationLattice_outer_grid`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationNilmanifold`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationNilmanifold_complexity`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationNilmanifold_complexity_budget`, `OAI.Erdos3.polynomialExponentialCoordinate_eval_potential_on_submodule`, `_private.Geometry.WeightedTranslationIntegralCoordinates.0.OAI.Erdos3.integral_C_iff`, `_private.Geometry.WeightedTranslationIntegralCoordinates.0.OAI.Erdos3.integral_rename_iff`, `_private.Nilpotent.WeightedTranslationRealBCHCoordinates.0.OAI.Erdos3.eval_translate_rational`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B031

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SimultaneousSymbolSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem symbolSlowBound_one (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M) :
    F.SymbolSlowBound b ω hlayers w T M 1 := by
  intro z
  change |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr 0 z| ≤ _
  simp only [map_zero, Finsupp.zero_apply, abs_zero]
  exact div_nonneg hM (monomialScale_pos T hT z.val.1).le

theorem symbolRationalGrid_one (l : ℕ) : F.SymbolRationalGrid b ω hlayers w l 1 := by
  change (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr 0 z) ∈ realDenominatorGrid l
  have hzero : (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr 0 z) =
      (0 : SymbolBasisIndex w ω → ℝ) := by
    funext z
    simp only [map_zero, Finsupp.zero_apply, Pi.zero_apply]
  rw [hzero]
  exact realDenominatorGrid_zero l

theorem realSymbolGradeQuotientHom_first (g : F.RealPolynomialSymbolGroup w) :
    F.realSymbolGradeQuotientHom w 1 g = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply (lieQuotientMap_eq_zero ((F.polynomialSymbolFiltration w).realification.layerIdeal 1) _).mpr
  change g.coord ∈ (F.polynomialSymbolFiltration w).realification.layer 1
  rw [(F.polynomialSymbolFiltration w).realification.one_eq_top]
  exact Submodule.mem_top

theorem realSymbolGradeQuotient_mem_terminal_iff
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (g : F.RealPolynomialSymbolGroup w) :
    F.realSymbolGradeQuotientHom w (s + 1) g ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
        (F.realSymbolGradeQuotientHom w (s + 1)) ↔ g.coord ∈ realificationLieSubalgebra U := by
  rw [F.realSymbolGradeQuotient_mem_iff w U (s + 1) g,
    (F.polynomialSymbolFiltration w).realification.terminal, sup_bot_eq]
  rfl

end Erdos3.NilpotentLieFiltration

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedTranslationIntegralCoordinates
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

theorem integral_C_iff {τ : Type*} (c : ℚ) :
    (C c : MvPolynomial τ ℚ) ∈ integerCoefficientPolynomials τ ↔
      ∃ z : ℤ, c = (z : ℚ) := by
  classical
  constructor
  · intro h
    simpa [MvPolynomial.coeff_C] using
      (mem_integerCoefficientPolynomials_iff _).mp h 0
  · rintro ⟨z, rfl⟩
    exact integerCoefficientPolynomials_C z

theorem integral_rename_iff {σ τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ ℚ) :
    rename f P ∈ integerCoefficientPolynomials τ ↔
      P ∈ integerCoefficientPolynomials σ := by
  constructor
  · intro h
    apply (mem_integerCoefficientPolynomials_iff _).mpr
    intro a
    simpa only [coeff_rename_mapDomain f hf] using
      (mem_integerCoefficientPolynomials_iff _).mp h (a.mapDomain f)
  · intro h
    obtain ⟨Q, hQ⟩ := (mem_integerCoefficientPolynomials P).mp h
    apply (mem_integerCoefficientPolynomials _).mpr
    refine ⟨rename f Q, ?_⟩
    rw [MvPolynomial.map_rename, hQ]

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]
variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)

theorem weightedShearEmbedding_integral_iff (x : weightedSubalgebra w d) :
    (∀ i, (weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit)) ↔
    (∀ i, ∃ z : ℤ, x.val.base i = (z : ℚ)) ∧
      x.val.polynomial ∈ integerCoefficientPolynomials σ := by
  have hgen (i : σ ⊕ Unit) : (weightedShearEmbedding w d x).val (X i) =
      shearDerivation x.val (X i) := rfl
  simp only [hgen]
  constructor
  · intro h
    constructor
    · intro i
      exact (integral_C_iff (τ := σ ⊕ Unit) _).mp (by simpa only [shearDerivation_X_inl] using h (Sum.inl i))
    · exact (integral_rename_iff (Sum.inl : σ → σ ⊕ Unit) Sum.inl_injective _).mp (by
        simpa only [shearDerivation_X_inr] using h (Sum.inr ()))
  · rintro ⟨hb, hp⟩ i
    cases i with
    | inl i =>
        rw [shearDerivation_X_inl]
        exact (integral_C_iff _).mpr (hb i)
    | inr u =>
        rw [shearDerivation_X_inr]
        exact (integral_rename_iff Sum.inl Sum.inl_injective _).mpr hp

theorem weightedBasis_integral_iff (x : weightedSubalgebra w d) :
    (∀ i, (weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit)) ↔
      ∀ a, ∃ z : ℤ, (weightedBasis w d hw).repr x a = (z : ℚ) := by
  rw [weightedShearEmbedding_integral_iff]
  constructor
  · rintro ⟨hb, hp⟩ a
    cases a with
    | inl i => simpa only [weightedBasis_repr_inl] using hb i
    | inr a => exact (mem_integerCoefficientPolynomials_iff _).mp hp a.val
  · intro h
    constructor
    · intro i
      simpa only [weightedBasis_repr_inl] using h (Sum.inl i)
    · apply (mem_integerCoefficientPolynomials_iff _).mpr
      intro a
      by_cases ha : Finsupp.weight w a < d
      · exact h (Sum.inr ⟨a, ha⟩)
      · refine ⟨0, ?_⟩
        apply not_ne_iff.mp
        intro hc
        have hs := x.property.2 (MvPolynomial.mem_support_iff.mpr hc)
        change Finsupp.weight w a + 1 ≤ d at hs
        omega

variable [Finite (WeightedBasisIndex w d)]

theorem weightedBasis_integralVector_iff (x : weightedSubalgebra w d) :
    (∀ i, (weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit)) ↔
      IntegralVector ((weightedBasis w d hw).equivFun x) := by
  rw [weightedBasis_integral_iff w d hw]
  constructor
  · intro h
    choose z hz using h
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩ a
    exact ⟨z a, hz a⟩

theorem weightedBasis_denominatorGrid_iff (B : ℕ) (x : weightedSubalgebra w d) :
    (weightedBasis w d hw).equivFun x ∈ denominatorGrid B ↔
      ∀ i, ((B : ℚ) • weightedShearEmbedding w d x).val (X i) ∈
        integerCoefficientPolynomials (σ ⊕ Unit) := by
  change IntegralVector ((B : ℚ) • (weightedBasis w d hw).equivFun x) ↔ _
  rw [← map_smul]
  simpa only [map_smul] using (weightedBasis_integralVector_iff w d hw ((B : ℚ) • x)).symm

theorem weightedBasis_scaledGrid_normalize (B : ℕ) (hB : 0 < B)
    (x : weightedSubalgebra w d)
    (hx : (weightedBasis w d hw).equivFun x ∈ scaledIntegerGrid B) :
    ∀ i, ((B : ℚ)⁻¹ • weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit) := by
  obtain ⟨z, hz⟩ := hx
  have hBq : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  have hi : IntegralVector ((weightedBasis w d hw).equivFun ((B : ℚ)⁻¹ • x)) := by
    refine ⟨z, ?_⟩
    have hv : (weightedBasis w d hw).equivFun ((B : ℚ)⁻¹ • x) =
        fun i => (z i : ℚ) := by
      rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hBq, one_smul]
    exact congrFun hv
  simpa only [map_smul] using (weightedBasis_integralVector_iff w d hw _).mpr hi

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationRealBCHCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem exponentialElement_action_eq_shear (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) :
    PolynomialTranslationGroup.actionMonoidHom
      (PolynomialTranslationGroup.exponentialElement x.val.base x.val.polynomial) =
      (polynomialShearExpAut (weightedShearEmbedding w d x)).val := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
      change PolynomialTranslationGroup.actionHom _ (X (Sum.inl i)) =
        (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inl i))
      rw [PolynomialTranslationGroup.actionHom_X_inl, weightedShearExp_X_inl]
      rfl
  | inr u =>
      cases u
      change PolynomialTranslationGroup.actionHom _ (X (Sum.inr ())) =
        (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inr ()))
      rw [PolynomialTranslationGroup.actionHom_X_inr,
        weightedShearExp_X_inr w d x (d+1) (Nat.le_succ d)]
      congr 2
      exact polynomialTranslate_exponentialCoordinate_series w hw x.val.base
        (weightedSupportDrop_le x.property.2)

noncomputable def bchTranslationHom (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).Group →* PolynomialTranslationGroup σ where
  toFun g := PolynomialTranslationGroup.exponentialElement g.coord.val.base g.coord.val.polynomial
  map_one' := by
    apply PolynomialTranslationGroup.actionMonoidHom_injective
    change PolynomialTranslationGroup.actionMonoidHom
      (PolynomialTranslationGroup.exponentialElement (0 : weightedSubalgebra w d).val.base
        (0 : weightedSubalgebra w d).val.polynomial) = PolynomialTranslationGroup.actionMonoidHom 1
    rw [exponentialElement_action_eq_shear w d hw 0]
    change (weightedShearGroupHom w d hwd 1).val = PolynomialTranslationGroup.actionMonoidHom 1
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply PolynomialTranslationGroup.actionMonoidHom_injective
    rw [map_mul, exponentialElement_action_eq_shear w d hw,
      exponentialElement_action_eq_shear w d hw, exponentialElement_action_eq_shear w d hw]
    change (weightedShearGroupHom w d hwd (g*h)).val =
      (weightedShearGroupHom w d hwd g).val * (weightedShearGroupHom w d hwd h).val
    rw [map_mul]
    rfl

@[simp] theorem bchTranslationHom_apply (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    bchTranslationHom w d hw hwd g =
      PolynomialTranslationGroup.exponentialElement g.coord.val.base g.coord.val.polynomial := rfl

@[simp] theorem bchTranslationHom_action (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    PolynomialTranslationGroup.actionMonoidHom (bchTranslationHom w d hw hwd g) =
      (weightedShearGroupHom w d hwd g).val :=
  exponentialElement_action_eq_shear w d hw g.coord

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem eval_translate_rational {σ : Type*} (z h : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    eval z (polynomialTranslate h P) = eval (z + h) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Pi.add_apply]

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

namespace PolynomialTranslationLie

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

theorem existsUnique_bchRealTranslation (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    ∃! q : PolynomialTranslationGroupOver ℝ σ,
      PolynomialTranslationGroupOver.actionMonoidHom q = (weightedShearRealGroupHom w d hwd g).val := by
  obtain ⟨b, P, hb, hP⟩ := realShearEmbedding_shape w d g.coord
  exact existsUnique_translation_of_shear_exp (realShearEmbedding w d g.coord) b P hb hP

noncomputable def bchRealTranslationElement (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    PolynomialTranslationGroupOver ℝ σ :=
  (existsUnique_bchRealTranslation w d hwd g).exists.choose

theorem bchRealTranslationElement_action (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    PolynomialTranslationGroupOver.actionMonoidHom (bchRealTranslationElement w d hwd g) =
      (weightedShearRealGroupHom w d hwd g).val :=
  (existsUnique_bchRealTranslation w d hwd g).exists.choose_spec

noncomputable def bchRealTranslationHom (w : σ → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).realification.Group →* PolynomialTranslationGroupOver ℝ σ where
  toFun := bchRealTranslationElement w d hwd
  map_one' := by
    apply PolynomialTranslationGroupOver.actionMonoidHom_injective
    rw [bchRealTranslationElement_action, map_one, map_one]
    rfl
  map_mul' g h := by
    apply PolynomialTranslationGroupOver.actionMonoidHom_injective
    rw [map_mul, bchRealTranslationElement_action, bchRealTranslationElement_action,
      bchRealTranslationElement_action, map_mul]
    rfl

@[simp] theorem bchRealTranslationHom_action (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    PolynomialTranslationGroupOver.actionMonoidHom (bchRealTranslationHom w d hwd g) =
      (weightedShearRealGroupHom w d hwd g).val :=
  bchRealTranslationElement_action w d hwd g

theorem bchRealTranslationHom_injective (w : σ → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d) :
    Function.Injective (bchRealTranslationHom w d hwd) := by
  intro g h heq
  apply weightedShearRealGroupHom_injective w d hwd
  apply Subtype.ext
  rw [← bchRealTranslationHom_action, ← bchRealTranslationHom_action, heq]

theorem bchRealTranslationHom_rational (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    bchRealTranslationHom w d hwd (NilpotentLieBCHGroup.realificationHom g) =
      PolynomialTranslationGroupOver.map (algebraMap ℚ ℝ)
        (PolynomialTranslationGroupOver.rationalEquiv (bchTranslationHom w d hw hwd g)) := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [bchRealTranslationHom_action]
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  have hrat : PolynomialTranslationGroupOver.actionMonoidHom
      (PolynomialTranslationGroupOver.rationalEquiv (bchTranslationHom w d hw hwd g)) =
      (weightedShearGroupHom w d hwd g).val := by
    rw [PolynomialTranslationGroupOver.rationalEquiv_action, bchTranslationHom_action]
  have hmap := PolynomialTranslationGroupOver.map_actionHom (algebraMap ℚ ℝ)
    (PolynomialTranslationGroupOver.rationalEquiv (bchTranslationHom w d hw hwd g)) (X i)
  have hreal := weightedShearRealGroupHom_rational w d hwd g (X i)
  simp only [MvPolynomial.map_X] at hmap hreal
  change (weightedShearRealGroupHom w d hwd
    (NilpotentLieBCHGroup.realificationHom g)).val (X i) =
    PolynomialTranslationGroupOver.actionHom _ (X i)
  rw [hreal, ← hmap]
  congr 1
  exact (congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ]
    MvPolynomial (σ ⊕ Unit) ℚ => f (X i)) hrat).symm

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationIntegralAction
namespace OAI

section

namespace Erdos3.PolynomialTranslationGroup

open _root_.MvPolynomial
variable {σ : Type*}

noncomputable def fromInteger :
    PolynomialTranslationGroupOver ℤ σ →* PolynomialTranslationGroup σ :=
  PolynomialTranslationGroupOver.rationalEquiv.symm.toMonoidHom.comp
    (PolynomialTranslationGroupOver.map (Int.castRingHom ℚ))

@[simp] theorem fromInteger_base (g : PolynomialTranslationGroupOver ℤ σ) (i : σ) :
    (fromInteger g).base i = (g.base i : ℚ) := rfl

@[simp] theorem fromInteger_polynomial (g : PolynomialTranslationGroupOver ℤ σ) :
    (fromInteger g).polynomial = MvPolynomial.map (Int.castRingHom ℚ) g.polynomial := rfl

noncomputable def integralGroup : Subgroup (PolynomialTranslationGroup σ) := fromInteger.range

theorem mem_integralGroup_iff (g : PolynomialTranslationGroup σ) :
    g ∈ integralGroup ↔ (∀ i, ∃ z : ℤ, g.base i = (z : ℚ)) ∧
      g.polynomial ∈ integerCoefficientPolynomials σ := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨fun i => ⟨h.base i, rfl⟩, ⟨h.polynomial, rfl⟩⟩
  · rintro ⟨hb, P, hP⟩
    choose b hb using hb
    refine ⟨⟨b, P⟩, ?_⟩
    apply PolynomialTranslationGroup.ext
    · exact (funext hb).symm
    · exact hP

theorem integralGroup_action_integral {g : PolynomialTranslationGroup σ}
    (hg : g ∈ integralGroup) (i : σ ⊕ Unit) :
    actionMonoidHom g (X i) ∈ integerCoefficientPolynomials (σ ⊕ Unit) := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨PolynomialTranslationGroupOver.actionHom h (X i), ?_⟩
  change MvPolynomial.map (Int.castRingHom ℚ)
    (PolynomialTranslationGroupOver.actionHom h (X i)) = _
  rw [PolynomialTranslationGroupOver.map_actionHom, MvPolynomial.map_X]
  rfl

theorem mem_integralGroup_iff_action (g : PolynomialTranslationGroup σ) :
    g ∈ integralGroup ↔
      ∀ i, actionMonoidHom g (X i) ∈ integerCoefficientPolynomials (σ ⊕ Unit) := by
  refine ⟨fun hg => integralGroup_action_integral hg, ?_⟩
  intro hg
  apply (mem_integralGroup_iff g).mpr
  have hb : ∀ i, ∃ z : ℤ, g.base i = (z : ℚ) := by
    intro i
    apply (integerCoefficientPolynomials_C_iff (σ := σ ⊕ Unit) (g.base i)).mp
    have h := (integerCoefficientPolynomials (σ ⊕ Unit)).sub_mem
      (hg (Sum.inl i)) (integerCoefficientPolynomials_X (Sum.inl i))
    change actionHom g (X (Sum.inl i)) - X (Sum.inl i) ∈ _ at h
    simpa only [actionHom_X_inl, add_sub_cancel_left] using h
  refine ⟨hb, ?_⟩
  apply (integerCoefficientPolynomials_translate_iff g.base hb g.polynomial).mp
  apply (integerCoefficientPolynomials_rename_iff Sum.inl Sum.inl_injective _).mp
  have h := (integerCoefficientPolynomials (σ ⊕ Unit)).sub_mem
    (hg (Sum.inr ())) (integerCoefficientPolynomials_X (Sum.inr ()))
  change actionHom g (X (Sum.inr ())) - X (Sum.inr ()) ∈ _ at h
  simpa only [actionHom_X_inr, add_sub_cancel_left] using h

end Erdos3.PolynomialTranslationGroup

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem bchTranslationHom_mem_integralGroup_iff (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    bchTranslationHom w d hw hwd g ∈ PolynomialTranslationGroup.integralGroup ↔
      weightedShearGroupHom w d hwd g ∈ integerWeightedLoweringSubgroup (shearWeight w d) := by
  rw [PolynomialTranslationGroup.mem_integralGroup_iff_action, bchTranslationHom_action]
  rfl

theorem bchTranslation_integral_comap (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    PolynomialTranslationGroup.integralGroup.comap (bchTranslationHom w d hw hwd) =
      (integerWeightedLoweringSubgroup (shearWeight w d)).comap (weightedShearGroupHom w d hwd) := by
  ext g
  exact bchTranslationHom_mem_integralGroup_iff w d hw hwd g

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedTranslationLattice
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def weightedTranslationLattice (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) : Subgroup (weightedFiltration w d hwd).Group :=
  (integerWeightedLoweringSubgroup (shearWeight w d)).comap (weightedShearGroupHom w d hwd)

@[simp] theorem mem_weightedTranslationLattice (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).Group) :
    g ∈ weightedTranslationLattice w d hwd ↔
      polynomialShearExpAut (weightedShearEmbedding w d g.coord) ∈
        integerWeightedLoweringSubgroup (shearWeight w d) := Iff.rfl

theorem weightedTranslationLattice_eq_integral_preimage (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    weightedTranslationLattice w d hwd =
      PolynomialTranslationGroup.integralGroup.comap (bchTranslationHom w d hw hwd) :=
  (bchTranslation_integral_comap w d hw hwd).symm

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationLattice_inner_grid :
    scaledIntegerGrid d.factorial ⊆
      bchSubgroupCoordinates (weightedBasis w d hw) (weightedTranslationLattice w d hwd) := by
  intro x hx
  let X := (weightedBasis w d hw).equivFun.symm x
  have hX : (weightedBasis w d hw).equivFun X ∈ scaledIntegerGrid d.factorial := by
    simpa only [X,LinearEquiv.apply_symm_apply] using hx
  have hI := weightedBasis_scaledGrid_normalize w d hw d.factorial (Nat.factorial_pos d) X hX
  have he := polynomialShear_factorial_exp_integral d (shearWeight_le w d hwd)
    ((d.factorial : ℚ)⁻¹ • weightedShearEmbedding w d X) hI
  have hc : (d.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  rw [smul_smul,mul_inv_cancel₀ hc,one_smul] at he
  exact he

theorem weightedTranslationLattice_outer_grid :
    bchSubgroupCoordinates (weightedBasis w d hw) (weightedTranslationLattice w d hwd) ⊆
      denominatorGrid d.factorial := by
  intro x hx
  let X := (weightedBasis w d hw).equivFun.symm x
  have hE : polynomialShearExpAut (weightedShearEmbedding w d X) ∈
      integerWeightedLoweringSubgroup (shearWeight w d) := hx
  have hI (i : σ ⊕ Unit) := polynomialShear_factorial_log_integral d (shearWeight_le w d hwd)
    (polynomialShearExpAut (weightedShearEmbedding w d X)) hE i
  simp only [polynomialShearLog_exp] at hI
  have h := (weightedBasis_denominatorGrid_iff w d hw d.factorial X).mpr hI
  simpa only [X,LinearEquiv.apply_symm_apply] using h

end Erdos3.PolynomialTranslationLie

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

theorem weightedOrderedBasis_inner_grid :
    scaledIntegerGrid d.factorial ⊆
      bchSubgroupCoordinates (weightedOrderedBasis w d hw) (weightedTranslationLattice w d hwd) :=
  bchSubgroup_inner_grid_reindex (weightedBasis w d hw) (weightedIndexOrder w d) _
    (weightedTranslationLattice_inner_grid w d hw hwd)

theorem weightedOrderedBasis_outer_grid :
    bchSubgroupCoordinates (weightedOrderedBasis w d hw) (weightedTranslationLattice w d hwd) ⊆
      denominatorGrid d.factorial :=
  bchSubgroup_outer_grid_reindex (weightedBasis w d hw) (weightedIndexOrder w d) _
    (weightedTranslationLattice_outer_grid w d hw hwd)

noncomputable def weightedTranslationNilmanifold :
    RationalFilteredNilmanifold (weightedSubalgebra w d) d (Fintype.card (WeightedBasisIndex w d)) where
  filtration := weightedFiltration w d hwd
  basis := weightedOrderedBasis w d hw
  layerBasis i := weightedLayerFinBasis w d hw hwd (i.val+1)
  lattice := weightedTranslationLattice w d hwd
  grid := d.factorial
  grid_pos := Nat.factorial_pos d
  inner_grid := weightedOrderedBasis_inner_grid w d hw hwd
  outer_grid := weightedOrderedBasis_outer_grid w d hw hwd

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


