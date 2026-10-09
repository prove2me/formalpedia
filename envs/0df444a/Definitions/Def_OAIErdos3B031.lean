-- Prove2me | Definitions.Def_OAIErdos3B031
-- name    : OAIErdos3B031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T20:27:37.788494+00:00
-- url     : https://prove2.me/theorems/6e0e3ca7-85f0-43df-9496-ecc17f128e4b
-- title:
--   OpenAI Erdős-3 split, definitions bundle 32 of 108
-- statement:
--   Definitions bundle 32 of 108 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B030`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 32 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.FirstCoefficientGrid`, `OAI.Erdos3.NilpotentLieFiltration.FirstCoefficientSlowBound`, `OAI.Erdos3.NilpotentLieFiltration.LayerOneBasisIndex`, `OAI.Erdos3.NilpotentLieFiltration.exists_fast_coefficient_generators_exp`, `OAI.Erdos3.NilpotentLieFiltration.exists_firstCoefficient_adjoint_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_firstCoefficient_coordinate_derivative_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_firstCoefficient_operation_grid`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_polynomial_operation_grid`, `OAI.Erdos3.NilpotentLieFiltration.exists_real_adapted_dual_grid`, `OAI.Erdos3.NilpotentLieFiltration.exists_symbol_reset_from_common_quotient`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientAdjoint_bound_of_polynomial_bound`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientAdjoint_grid_of_polynomial_grid`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGrid_map`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientHorizontal_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientHorizontal_projector_repr`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRealEquiv_basis`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRealEquiv_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientSlowBound_map`, `OAI.Erdos3.NilpotentLieFiltration.horizontalCoefficientIndex`, `OAI.Erdos3.NilpotentLieFiltration.horizontalCoefficientIndex_of_constant`, `OAI.Erdos3.NilpotentLieFiltration.layerOneBasis`, `OAI.Erdos3.NilpotentLieFiltration.layerOneBasis_repr_mk`, `OAI.Erdos3.NilpotentLieFiltration.layerOneIndexOfConstant`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedAdjoint_tensor`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedConstant`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedConstant_mem_first`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedConstant_tensor`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedLogDerivative_mul`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialTensor_injective`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientBasis`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientBasis_matrix`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientBasis_repr_basis`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientBasis_symm`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientHorizontalEquiv`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientHorizontalEquiv_projection`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientHorizontal_projector`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientHorizontal_projector_repr`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientConstant`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientConstant_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientConstant_grid`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientConstant_slow`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientDirectionMap_mul`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientDirectionMap_mul_rat`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientDirectionMap_triple_rat`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientHorizontal_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientHorizontal_projector`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientHorizontal_projector_repr`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial_adjoint`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial_adjoint_constant`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial_constant`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial_logDerivative`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial_normalizedRelativeLog`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientSection`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientSection_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientSection_coordinate_zero`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientSection_grid`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientSection_rightInverse`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientSection_slow`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientSection_surviving_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeCoefficient_eq_map`, `OAI.Erdos3.NilpotentLieFiltration.realReducedSquareCoefficientMap`, `OAI.Erdos3.NilpotentLieFiltration.realReducedSquareCoefficientMap_grid`, `OAI.Erdos3.NilpotentLieFiltration.realReducedSquareCoefficientMap_matrix`, `OAI.Erdos3.NilpotentLieFiltration.realReducedSquareCoefficientMap_relative`, `OAI.Erdos3.NilpotentLieFiltration.realReducedSquareCoefficientMap_slow`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalIndex`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalSymbolIndex`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalSymbolMap_basis_height`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalSymbolMap_monomial_blocks`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalSymbolMap_real_matrix`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonal_basis`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonal_basis_height`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealDiagonalHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealDiagonalHom_grid`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealDiagonalHom_slow`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealSymbolHom_grid`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealSymbolHom_repr`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealSymbolHom_slow`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap_basis_repr`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap_repr`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSnd_basis_repr`, `OAI.Erdos3.descended_linear_map_coordinate_height`, `OAI.Erdos3.extendInitialCoordinates`, `OAI.Erdos3.extendInitialCoordinates_castLE`, `OAI.Erdos3.extendInitialCoordinates_grid`, `OAI.Erdos3.fastCoefficientGeneratorHeight_le_exp`, `OAI.Erdos3.fastCoefficientGeneratorHeight_pos`, `OAI.Erdos3.fastKernelGeneratorHeight_le_exp`, `OAI.Erdos3.initialHorizontalEquiv`, `OAI.Erdos3.initialHorizontalEquiv_projection`, `OAI.Erdos3.initialHorizontalEquiv_symm_projection`, `OAI.Erdos3.intervalAuxiliaryCell`, `OAI.Erdos3.intervalAuxiliaryCellEquiv`, `OAI.Erdos3.intervalAuxiliaryCell_eq_iff`, `OAI.Erdos3.norm_extendInitialCoordinates_le`, `OAI.Erdos3.realDenominatorGrid_single`, `OAI.Erdos3.realLinearMap_eq_of_rat_directions`, `OAI.Erdos3.realSupportedQuotientSection_coordinate`, `OAI.Erdos3.realSupportedQuotientSection_coordinate_zero`, `OAI.Erdos3.realSupportedQuotientSection_norm`, `OAI.Erdos3.realSupportedQuotientSection_rightInverse`, `OAI.Erdos3.supportedQuotientSection`, `OAI.Erdos3.supportedQuotientSection_basis`, `OAI.Erdos3.supportedQuotientSection_coordinate`, `OAI.Erdos3.supportedQuotientSection_coordinate_zero`, `OAI.Erdos3.supportedQuotientSection_rightInverse`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B099

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastCoefficientGeneratorBudget
namespace OAI

section

namespace Erdos3

theorem fastCoefficientGeneratorHeight_pos (n m r H : ℕ) (hH : 1 ≤ H) :
    0 < fastCoefficientGeneratorHeight n m r H := by
  have hHp : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
  have hB : 1 ≤ (n + 1) * H ^ n := Nat.succ_le_of_lt (by positivity)
  have hK := rationalKernelHeight_pos r hB
  unfold fastCoefficientGeneratorHeight fastKernelGeneratorHeight
  positivity

theorem fastKernelGeneratorHeight_le_exp (n m r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (fastKernelGeneratorHeight n m r H : ℝ) ≤ Real.exp ((p + 2) ^ 38) := by
  have hp1 : p ≤ (p + 2) ^ 1 := le_power_budget hp (by decide)
  have hB : (((n + 1) * H ^ n : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    exact rational_sum_cost_le_exp n H hp 1 1
      (hH.trans (Real.exp_le_exp.mpr hp1)) (hn.trans hp1)
  have hK : (rationalKernelHeight r ((n + 1) * H ^ n) : ℝ) ≤
      Real.exp ((p + 2) ^ 35) := by
    have hk := rationalKernelHeight_le_budget r ((n + 1) * H ^ n)
      (by positivity : 0 ≤ (p + 2) ^ 3)
      (hr.trans (le_power_budget hp (by decide : 1 ≤ 3))) hB
    exact exponential_budget_comp hp (by positivity) 3 7 le_rfl hk
  have hH' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 35) :=
    hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 35)))
  have hprod : ((rationalKernelHeight r ((n + 1) * H ^ n) * H : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 36) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 35) * Real.exp ((p + 2) ^ 35) :=
        mul_le_mul hK hH' (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (2 * (p + 2) ^ 35) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          2 * (p + 2) ^ 35 ≤ (p + 2) * (p + 2) ^ 35 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (p + 2) ^ 36 := by rw [pow_succ (p + 2) 35]; ring
  exact rational_sum_cost_le_exp m _ hp 36 1 hprod (hm.trans hp1)

theorem fastCoefficientGeneratorHeight_le_exp (n m r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (fastCoefficientGeneratorHeight n m r H : ℝ) ≤ Real.exp ((p + 2) ^ 40) :=
  rational_sum_cost_le_exp n _ hp 38 1
    (fastKernelGeneratorHeight_le_exp n m r H hp hn hm hr hH)
    (hn.trans (le_power_budget hp (by decide : 1 ≤ 1)))

namespace NilpotentLieFiltration

open Module

theorem exists_fast_coefficient_generators_exp
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 40) ∧
      ∃ z : κ → F.FirstCoefficientModule w,
        Submodule.span ℚ (Set.range z) = F.firstCoefficientFastSubmodule w hw U ∧
        ∀ i j, RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (z i) j) H' := by
  have he := F.exists_bounded_fast_coefficient_generators e ω hF w hw U v hspan hH hv
  obtain ⟨r, hr, z, hz, hzh⟩ := he
  refine ⟨_, fastCoefficientGeneratorHeight_pos _ _ _ _ hH, ?_, z, hz, hzh⟩
  exact fastCoefficientGeneratorHeight_le_exp _ _ _ _ hp hn hm
    ((Nat.cast_le.mpr hr).trans hq) hHp

end NilpotentLieFiltration
end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AuxiliaryIntervalCells
namespace OAI

section

namespace Erdos3

noncomputable def intervalAuxiliaryCell (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (M d : ℕ) (hd : 0 < d) (u r b : ℤ)
    (hbase : ∀ x : ℤ, x ≡ b [ZMOD r] → x ≡ u [ZMOD (M : ℤ)])
    (x : ↥(Finset.filter (fun x => x ≡ b [ZMOD r]) (Finset.Ico a (a + N)))) :
    P.Label × CompatibleAuxResidue M d u :=
  (intervalResidueCell a P r b x,
    compatibleAuxResidueOfPoint M d hd u x.val (hbase x.val (Finset.mem_filter.mp x.property).2))

theorem intervalAuxiliaryCell_eq_iff (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (M d : ℕ) (hd : 0 < d) (u r b : ℤ)
    (hbase : ∀ x : ℤ, x ≡ b [ZMOD r] → x ≡ u [ZMOD (M : ℤ)])
    (x : ↥(Finset.filter (fun x => x ≡ b [ZMOD r]) (Finset.Ico a (a + N))))
    (k : P.Label × CompatibleAuxResidue M d u) :
    intervalAuxiliaryCell a P M d hd u r b hbase x = k ↔
      (intervalCellLower a P k.1 ≤ x.val ∧ x.val < intervalCellUpper a P k.1) ∧
        x.val ≡ (k.2.val.val : ℤ) [ZMOD (d : ℤ)] := by
  rcases k with ⟨j, v⟩
  simp only [intervalAuxiliaryCell, Prod.mk.injEq, intervalResidueCell_eq_iff a P hstep,
    compatibleAuxResidueOfPoint_eq_iff]

noncomputable def intervalAuxiliaryCellEquiv (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (hpos : ∀ k, 0 < P.length k)
    (M d : ℕ) (hd : 0 < d) (u r b : ℤ)
    (hbase : ∀ x : ℤ, x ≡ b [ZMOD r] → x ≡ u [ZMOD (M : ℤ)])
    (k : P.Label × CompatibleAuxResidue M d u) (R c : ℤ)
    (hcombine : ∀ x : ℤ,
      (x ≡ b [ZMOD r] ∧ x ≡ (k.2.val.val : ℤ) [ZMOD (d : ℤ)]) ↔ x ≡ c [ZMOD R]) :
    {x : ↥(Finset.filter (fun x => x ≡ b [ZMOD r]) (Finset.Ico a (a + N))) //
      intervalAuxiliaryCell a P M d hd u r b hbase x = k} ≃
      ↥(Finset.filter (fun x => x ≡ c [ZMOD R])
        (Finset.Ico (intervalCellLower a P k.1) (intervalCellUpper a P k.1))) where
  toFun x := by
    have hx := (intervalAuxiliaryCell_eq_iff a P hstep M d hd u r b hbase x.val k).mp x.property
    exact ⟨x.val.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hx.1,
      (hcombine x.val.val).mp ⟨(Finset.mem_filter.mp x.val.property).2, hx.2⟩⟩⟩
  invFun x := by
    have hx := Finset.mem_filter.mp x.property
    have hinterval := Finset.mem_Ico.mp hx.1
    have hr := (hcombine x.val).mpr hx.2
    have hend := P.end_le_of_step_one hstep k.1 (hpos k.1)
    have hend' : (P.start k.1 : ℤ) + P.length k.1 ≤ N := by exact_mod_cast hend
    have hstart : (0 : ℤ) ≤ P.start k.1 := Int.natCast_nonneg _
    have houter : x.val ∈ Finset.Ico a (a + N) := by
      simp only [intervalCellLower, intervalCellUpper] at hinterval
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    let y : ↥(Finset.filter (fun z => z ≡ b [ZMOD r]) (Finset.Ico a (a + N))) :=
      ⟨x.val, Finset.mem_filter.mpr ⟨houter, hr.1⟩⟩
    exact ⟨y, (intervalAuxiliaryCell_eq_iff a P hstep M d hd u r b hbase y k).mpr
      ⟨hinterval, hr.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DescendedLinearMapBounds
namespace OAI

section

namespace Erdos3

open Module

variable {L M Z ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [AddCommGroup Z] [Module ℚ Z]
  [Fintype ι] [Fintype κ]

theorem descended_linear_map_coordinate_height
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (b : Basis ν ℚ Z)
    (π : L →ₗ[ℚ] M) (hπ : Function.Surjective π) (φ : M →ₗ[ℚ] Z)
    {Q H : ℕ} (hQ : 1 ≤ Q)
    (hproj : ∀ i j, RationalHeightLE (f.repr (π (e j)) i) Q)
    (hcomp : ∀ i j, RationalHeightLE (b.repr (φ (π (e j))) i) H) (i : ν) (j : κ) :
    RationalHeightLE (b.repr (φ (f j)) i)
      ((Fintype.card ι + 1) * (rationalSolveHeight (Fintype.card κ) Q * H) ^ Fintype.card ι) := by
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_section e f π hπ hQ hproj
  have h := linearMap_coordinate_height e b (φ.comp π) (fun j i => hcomp i j)
    (σ (f j)) (fun k => hσH k j) i
  simpa only [LinearMap.comp_apply, hσ (f j)] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedQuotientSection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

section Algebra

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
  (hP : P = Submodule.span K (b '' S))

noncomputable def supportedQuotientSection : (V ⧸ P) →ₗ[K] V :=
  (supportedQuotientBasis b P S hP).constr K (fun i => b i.val)

@[simp] theorem supportedQuotientSection_basis (i : {i // i ∉ S}) :
    supportedQuotientSection b P S hP (supportedQuotientBasis b P S hP i) = b i.val :=
  Basis.constr_basis _ _ _ i

theorem supportedQuotientSection_rightInverse (x : V ⧸ P) :
    P.mkQ (supportedQuotientSection b P S hP x) = x := by
  have he : P.mkQ.comp (supportedQuotientSection b P S hP) = LinearMap.id := by
    apply (supportedQuotientBasis b P S hP).ext
    intro i
    change P.mkQ (supportedQuotientSection b P S hP
      (supportedQuotientBasis b P S hP i)) = supportedQuotientBasis b P S hP i
    rw [supportedQuotientSection_basis, supportedQuotientBasis_apply]
  exact DFunLike.congr_fun he x

theorem supportedQuotientSection_coordinate (x : V ⧸ P) (i : {i // i ∉ S}) :
    b.repr (supportedQuotientSection b P S hP x) i =
      (supportedQuotientBasis b P S hP).repr x i := by
  rw [← supportedQuotientBasis_repr_mk b P S hP, supportedQuotientSection_rightInverse]

theorem supportedQuotientSection_coordinate_zero (x : V ⧸ P) (i : ι) (hi : i ∈ S) :
    b.repr (supportedQuotientSection b P S hP x) i = 0 := by
  have he : (b.coord i).comp (supportedQuotientSection b P S hP) = 0 := by
    apply (supportedQuotientBasis b P S hP).ext
    intro j
    change b.repr (supportedQuotientSection b P S hP
      (supportedQuotientBasis b P S hP j)) i = 0
    rw [supportedQuotientSection_basis, b.repr_self]
    apply Finsupp.single_eq_of_ne
    exact fun hij => j.property (hij ▸ hi)
  exact DFunLike.congr_fun he x

end Algebra

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (P : Submodule ℚ V) (S : Set ι)
  (hP : P = Submodule.span ℚ (b '' S))

theorem realSupportedQuotientSection_rightInverse (x : ℝ ⊗[ℚ] (V ⧸ P)) :
    P.mkQ.baseChange ℝ ((supportedQuotientSection b P S hP).baseChange ℝ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      supportedQuotientSection_rightInverse]

theorem realSupportedQuotientSection_coordinate
    (x : ℝ ⊗[ℚ] (V ⧸ P)) (i : {i // i ∉ S}) :
    (b.baseChange ℝ).repr ((supportedQuotientSection b P S hP).baseChange ℝ x) i =
      ((supportedQuotientBasis b P S hP).baseChange ℝ).repr x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, supportedQuotientSection_coordinate]

theorem realSupportedQuotientSection_coordinate_zero
    (x : ℝ ⊗[ℚ] (V ⧸ P)) (i : ι) (hi : i ∈ S) :
    (b.baseChange ℝ).repr ((supportedQuotientSection b P S hP).baseChange ℝ x) i = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      supportedQuotientSection_coordinate_zero b P S hP x i hi]
    exact zero_smul ℚ r

theorem realSupportedQuotientSection_norm [Fintype ι] [DecidablePred (· ∈ S)]
    (x : ℝ ⊗[ℚ] (V ⧸ P)) :
    ‖(b.baseChange ℝ).equivFun ((supportedQuotientSection b P S hP).baseChange ℝ x)‖ =
      ‖((supportedQuotientBasis b P S hP).baseChange ℝ).equivFun x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    by_cases hi : i ∈ S
    · rw [Basis.equivFun_apply, realSupportedQuotientSection_coordinate_zero b P S hP x i hi,
        norm_zero]
      exact norm_nonneg _
    · rw [Basis.equivFun_apply,
        realSupportedQuotientSection_coordinate b P S hP x ⟨i, hi⟩]
      exact norm_le_pi_norm (((supportedQuotientBasis b P S hP).baseChange ℝ).equivFun x) ⟨i, hi⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [Basis.equivFun_apply, ← realSupportedQuotientSection_coordinate b P S hP x i]
    exact norm_le_pi_norm ((b.baseChange ℝ).equivFun
      ((supportedQuotientSection b P S hP).baseChange ℝ x)) i.val

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDerivativeDifferences
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_real_adapted_dual_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x →
          ∀ h : σ → ℤ, F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) m
            (F.realAdaptedLogDerivative (fun i => (h i : ℚ)) x)) ∧
        (∀ (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
          (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l g.coord →
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x →
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) m (dualAdjoint g x)) := by
  have hgridExists := exists_real_dual_operation_grid s
  obtain ⟨D, _, hgrid⟩ := hgridExists
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let B : Polynomial ℕ := (Q + Polynomial.C D) ^ D
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  let : Fintype (AdaptedBasisIndex (fun _ : σ => 1) ω) :=
    adaptedBasisIndexFintype (fun _ => 1) ω s (by simp) (F.adaptedBasis_weight_le_step b ω hF)
  let q := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ (s + 2))).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le (fun _ : σ => 1) ω s (by simp)
      (F.adaptedBasis_weight_le_step b ω hF))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hfinal : (q + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hdata := hgrid (F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)) H q
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot
    hH hq hdim (hHp.trans (Real.exp_le_exp.mpr hpq))
    (F.adaptedMonomialBasis_bracket_height b ω hF (fun _ => 1) hH hc)
    l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_, ?_⟩
  · intro x hx h
    have hout := hlog (F.realAdaptedPolynomialJet (fun i => (h i : ℚ)) x)
      (by simpa only [F.realAdaptedPolynomialJet_base, RealAdaptedCoefficientGrid,
        Basis.equivFun_apply] using hx)
      (by simpa only [F.realAdaptedPolynomialJet_tangent, RealAdaptedCoefficientGrid,
        Basis.equivFun_apply] using F.realAdaptedDirectionalDerivative_grid b ω hF l x hx h)
    simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply, realAdaptedLogDerivative] using hout
  · intro g x hg hx
    have hout := had g x
      (by simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply] using hg)
      (by simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply] using hx)
    simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply] using hout

theorem realAdaptedAdjoint_tensor {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedPolynomialTensor w (dualAdjoint g x) =
      dualAdjoint (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialTensor w x) := by
  let φ := F.realAdaptedPolynomialTensor w
  exact dualLinearLift_adjoint (F.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (⊤ : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)) φ φ.toLinearMap
    (fun u v _ => φ.map_lie u v) g x (by trivial)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_polynomial_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          CoefficientGrid (b.baseChange ℝ) l A.coord →
          ∀ i : σ, CoefficientGrid (b.baseChange ℝ) m (formalLogDerivative i A)) ∧
        (∀ (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
          (Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
          A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          Q ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          CoefficientGrid (b.baseChange ℝ) l A.coord →
          CoefficientGrid (b.baseChange ℝ) l Q →
          CoefficientGrid (b.baseChange ℝ) m (dualAdjoint A Q)) := by
  obtain ⟨C, hC, hgrid⟩ := exists_real_adapted_dual_grid s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  classical
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · intro A hA hAgrid i
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    have hxgrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l x := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l x).mpr
      rwa [hx]
    have hout := (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ m _).mp
      (hlog x hxgrid (Pi.single i 1))
    have hsingle : (fun j => ((Pi.single i 1 : σ → ℤ) j : ℚ)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [hsingle, F.realAdaptedLogDerivative_eq_formal, hx] at hout
    exact hout
  · intro A Q hA hQ hAgrid hQgrid
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    obtain ⟨y, hy⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) Q hQ
    let G : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) := ⟨x⟩
    have hG : F.realFullPolynomialHom (fun _ : σ => 1) G = A := NilpotentLieBCHGroup.ext hx
    have hxgrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l x := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l x).mpr
      rwa [hx]
    have hygrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l y := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l y).mpr
      rwa [hy]
    have hout := (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ m _).mp (had G y hxgrid hygrid)
    rw [F.realAdaptedAdjoint_eq_formal, hG, hy] at hout
    exact hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realAdaptedPolynomialTensor_injective (w : σ → ℕ) :
    Function.Injective (F.realAdaptedPolynomialTensor w) := by
  intro x y hxy
  apply ((F.adaptedMonomialBasis e ω hF w).baseChange ℝ).repr.injective
  apply Finsupp.ext
  intro z
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra w =>
    (e.baseChange ℝ).repr (VectorPolynomial.coefficients p.val z.val.1) z.val.2) hxy
  exact (F.realAdaptedPolynomialTensor_coordinates w e ω hF x z).symm.trans
    (hc.trans (F.realAdaptedPolynomialTensor_coordinates w e ω hF y z))

variable [Fintype σ]

theorem realAdaptedLogDerivative_mul (h : σ → ℚ)
    (P Q : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realAdaptedLogDerivative h (P * Q).coord =
      F.realAdaptedLogDerivative h P.coord + dualAdjoint P (F.realAdaptedLogDerivative h Q.coord) := by
  apply F.realAdaptedPolynomialTensor_injective e ω hF (fun _ => 1)
  rw [map_add, F.realAdaptedLogDerivative_tensor, F.realAdaptedLogDerivative_tensor,
    F.realAdaptedAdjoint_tensor, F.realAdaptedLogDerivative_tensor]
  have hh := F.realification.adaptedLogDerivative_mul h
    (F.realAdaptedPolynomialGroupHom (fun _ => 1) P)
    (F.realAdaptedPolynomialGroupHom (fun _ => 1) Q)
  rw [← map_mul] at hh
  exact hh

theorem realFirstCoefficientDirectionMap_mul_rat (h : σ → ℚ)
    (P Q : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientDirectionMap (P * Q).coord (fun i => (h i : ℝ)) =
      F.realFirstCoefficientDirectionMap P.coord (fun i => (h i : ℝ)) +
        F.realFirstCoefficientAdjoint (fun _ => 1) P
          (F.realFirstCoefficientDirectionMap Q.coord (fun i => (h i : ℝ))) := by
  rw [F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientDirectionMap_rat,
    F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientAdjoint_map, ← map_add]
  apply congrArg (F.realFirstCoefficientMap (fun _ => 1))
  exact Subtype.ext (F.realAdaptedLogDerivative_mul e ω hF h P Q)

theorem realFirstCoefficientDirectionMap_triple_rat (h : σ → ℚ)
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientDirectionMap (A * B * D).coord (fun i => (h i : ℝ)) =
      F.realFirstCoefficientDirectionMap A.coord (fun i => (h i : ℝ)) +
        F.realFirstCoefficientAdjoint (fun _ => 1) A
          (F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ))) +
        F.realFirstCoefficientAdjoint (fun _ => 1) (A * B)
          (F.realFirstCoefficientDirectionMap D.coord (fun i => (h i : ℝ))) := by
  rw [F.realFirstCoefficientDirectionMap_mul_rat e ω hF,
    F.realFirstCoefficientDirectionMap_mul_rat e ω hF]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem realLinearMap_eq_of_rat_directions {σ E : Type*} [Fintype σ]
    [AddCommGroup E] [Module ℝ E] (f g : (σ → ℝ) →ₗ[ℝ] E)
    (h : ∀ v : σ → ℚ, f (fun i => (v i : ℝ)) = g (fun i => (v i : ℝ))) : f = g := by
  classical
  apply (Pi.basisFun ℝ σ).ext
  intro i
  have he : (fun j => ((Pi.single i (1 : ℚ) : σ → ℚ) j : ℝ)) = Pi.basisFun ℝ σ i := by
    funext j
    by_cases hij : j = i <;> simp [Pi.basisFun_apply, hij]
  simpa only [he] using h (Pi.single i 1)

end Erdos3

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFirstCoefficientDirectionMap_mul
    (P Q : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ) :
    F.realFirstCoefficientDirectionMap (P * Q).coord h =
      F.realFirstCoefficientDirectionMap P.coord h +
        F.realFirstCoefficientAdjoint (fun _ => 1) P
          (F.realFirstCoefficientDirectionMap Q.coord h) := by
  have he := realLinearMap_eq_of_rat_directions
    (F.realFirstCoefficientDirectionMap (P * Q).coord)
    (F.realFirstCoefficientDirectionMap P.coord +
      (F.realFirstCoefficientAdjoint (fun _ => 1) P).toLinearMap.comp
        (F.realFirstCoefficientDirectionMap Q.coord))
    (F.realFirstCoefficientDirectionMap_mul_rat e ω hF · P Q)
  exact DFunLike.congr_fun he h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def FirstCoefficientSlowBound (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (x : F.RealFirstCoefficientModule w) : Prop :=
  ∀ z : FirstCoefficientIndex w ω,
    |(F.realFirstCoefficientBasis b ω hF w).repr x z| ≤ M / monomialScale T z.val.1

def FirstCoefficientGrid (w : σ → ℕ) (l : ℕ) (x : F.RealFirstCoefficientModule w) : Prop :=
  (fun z : FirstCoefficientIndex w ω => (F.realFirstCoefficientBasis b ω hF w).repr x z) ∈
    realDenominatorGrid l

theorem firstCoefficientSlowBound_map (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (x : F.realShiftedCoefficientSubmodule w 1)
    (hx : F.RealAdaptedCoefficientBound b ω hF w T M x.val) :
    F.FirstCoefficientSlowBound b ω hF w T M (F.realFirstCoefficientMap w x) := by
  intro z
  rw [F.realFirstCoefficientBasis_repr_map]
  exact hx ((firstCoefficientSurvivorEquiv w ω).symm z).val.val

theorem firstCoefficientGrid_map (w : σ → ℕ) (l : ℕ)
    (x : F.realShiftedCoefficientSubmodule w 1)
    (hx : F.RealAdaptedCoefficientGrid b ω hF w l x.val) :
    F.FirstCoefficientGrid b ω hF w l (F.realFirstCoefficientMap w x) := by
  obtain ⟨v, hv⟩ := hx
  refine ⟨fun z => v ((firstCoefficientSurvivorEquiv w ω).symm z).val.val, ?_⟩
  funext z
  change (v ((firstCoefficientSurvivorEquiv w ω).symm z).val.val : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w x) z
  rw [F.realFirstCoefficientBasis_repr_map]
  exact congrFun hv ((firstCoefficientSurvivorEquiv w ω).symm z).val.val

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realFirstCoefficientSection :
    F.RealFirstCoefficientModule w →ₗ[ℝ] F.realShiftedCoefficientSubmodule w 1 :=
  supportedQuotientSection (F.realShiftedMonomialBasis b ω hF w 1)
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype)
    {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
    (F.realShiftedCoefficient_next_eq_span b ω hF w 1)

theorem realFirstCoefficientSection_rightInverse (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientMap w (F.realFirstCoefficientSection b ω hF w x) = x :=
  supportedQuotientSection_rightInverse _ _ _ _ x

theorem realFirstCoefficientSection_surviving_coordinate (x : F.RealFirstCoefficientModule w)
    (z : FirstCoefficientIndex w ω) :
    ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr
      (F.realFirstCoefficientSection b ω hF w x).val
      ((firstCoefficientSurvivorEquiv w ω).symm z).val.val =
      (F.realFirstCoefficientBasis b ω hF w).repr x z := by
  have h := F.realFirstCoefficientBasis_repr_map b ω hF w
    (F.realFirstCoefficientSection b ω hF w x) z
  rw [F.realFirstCoefficientSection_rightInverse] at h
  exact h.symm

theorem realFirstCoefficientSection_coordinate_zero (x : F.RealFirstCoefficientModule w)
    (z : AdaptedBasisIndex w ω) (hz : Finsupp.weight w z.val.1 + 1 ≠ ω z.val.2) :
    ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr
      (F.realFirstCoefficientSection b ω hF w x).val z = 0 := by
  by_cases hshift : Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2
  · have hnext : Finsupp.weight w z.val.1 + 2 ≤ ω z.val.2 := by omega
    calc
      _ = (F.realShiftedMonomialBasis b ω hF w 1).repr
          (F.realFirstCoefficientSection b ω hF w x) ⟨z, hshift⟩ :=
        (F.realShiftedMonomialBasis_repr b ω hF w 1 _ ⟨z, hshift⟩).symm
      _ = 0 := supportedQuotientSection_coordinate_zero
        (F.realShiftedMonomialBasis b ω hF w 1)
        ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype)
        {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
        (F.realShiftedCoefficient_next_eq_span b ω hF w 1) x ⟨z, hshift⟩ hnext
  · have hx := (F.realFirstCoefficientSection b ω hF w x).property
    exact (basis_mem_span_image_iff ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ)
      {z | Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2} _).mp
        ((F.realShiftedCoefficient_eq_span b ω hF w 1).le hx) z hshift

theorem realFirstCoefficientSection_coordinate (x : F.RealFirstCoefficientModule w)
    (z : AdaptedBasisIndex w ω) :
    ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr
      (F.realFirstCoefficientSection b ω hF w x).val z =
      if hz : Finsupp.weight w z.val.1 + 1 = ω z.val.2 then
        (F.realFirstCoefficientBasis b ω hF w).repr x ⟨z.val, hz⟩ else 0 := by
  split_ifs with hz
  · exact F.realFirstCoefficientSection_surviving_coordinate b ω hF w x ⟨z.val, hz⟩
  · exact F.realFirstCoefficientSection_coordinate_zero b ω hF w x z hz

theorem realFirstCoefficientSection_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound b ω hF w T M x) :
    F.RealAdaptedCoefficientBound b ω hF w T M (F.realFirstCoefficientSection b ω hF w x).val := by
  intro z
  rw [F.realFirstCoefficientSection_coordinate]
  split_ifs with hz
  · exact hx ⟨z.val, hz⟩
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT _).le

theorem realFirstCoefficientSection_grid (l : ℕ) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid b ω hF w l x) :
    F.RealAdaptedCoefficientGrid b ω hF w l (F.realFirstCoefficientSection b ω hF w x).val := by
  classical
  obtain ⟨v, hv⟩ := hx
  refine ⟨fun z => if hz : Finsupp.weight w z.val.1 + 1 = ω z.val.2 then v ⟨z.val, hz⟩ else 0, ?_⟩
  funext z
  change ((if hz : Finsupp.weight w z.val.1 + 1 = ω z.val.2 then v ⟨z.val, hz⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr
      (F.realFirstCoefficientSection b ω hF w x).val z
  rw [F.realFirstCoefficientSection_coordinate]
  split_ifs with hz
  · exact congrFun hv ⟨z.val, hz⟩
  · simp only [Int.cast_zero, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realAdaptedConstant :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
  (F.adaptedConstantLieHom w).toLinearMap.baseChange ℝ

theorem realAdaptedConstant_mem_first (x : ℝ ⊗[ℚ] L) :
    F.realAdaptedConstant w x ∈ F.realShiftedCoefficientSubmodule w 1 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul r x =>
    exact Submodule.tmul_mem_baseChange_of_mem r (F.adaptedConstant_mem_shiftedIdeal w x)

theorem realAdaptedConstant_tensor (x : ℝ ⊗[ℚ] L) :
    F.realAdaptedPolynomialTensor w (F.realAdaptedConstant w x) =
      F.realification.adaptedConstant w x := by
  classical
  change F.realAdaptedPolynomialTensor w (F.realAdaptedConstant w x) =
    F.realification.adaptedConstantLieHom w x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    apply Subtype.ext
    apply coefficients.injective
    ext α
    change coefficients (F.realAdaptedPolynomialMap w (r ⊗ₜ[ℚ] F.adaptedConstant w x)) α =
      coefficients (monomial 0 (r ⊗ₜ[ℚ] x)) α
    rw [F.realAdaptedPolynomialMap_coefficient_tmul]
    change r ⊗ₜ[ℚ] coefficients (monomial 0 x) α = _
    simp only [coefficients_monomial, Finsupp.single_apply]
    split_ifs <;> simp

noncomputable def realFirstCoefficientConstant :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  (F.realFirstCoefficientMap w).comp
    ((F.realAdaptedConstant w).codRestrict (F.realShiftedCoefficientSubmodule w 1)
      (F.realAdaptedConstant_mem_first w))

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientOfPolynomial_constant (x : ℝ ⊗[ℚ] L) :
    F.realFirstCoefficientOfPolynomial b ω hF w (monomial 0 x) =
      F.realFirstCoefficientConstant w x := by
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra w => p.val)
    (F.realAdaptedConstant_tensor w x)
  change F.realAdaptedPolynomialMap w (F.realAdaptedConstant w x) = monomial 0 x at hc
  rw [← hc]
  exact F.realFirstCoefficientOfPolynomial_map b ω hF w
    ⟨F.realAdaptedConstant w x, F.realAdaptedConstant_mem_first w x⟩

theorem realFirstCoefficientConstant_coordinate [DecidableEq σ] (x : ℝ ⊗[ℚ] L)
    (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientConstant w x) z =
      if z.val.1 = 0 then (b.baseChange ℝ).repr x z.val.2 else 0 := by
  classical
  rw [← F.realFirstCoefficientOfPolynomial_constant w b ω hF,
    F.realFirstCoefficientOfPolynomial_coordinate, coefficients_monomial]
  by_cases hz : z.val.1 = 0
  · simp only [hz, Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne hz, map_zero, Finsupp.zero_apply, if_neg hz]

theorem realFirstCoefficientConstant_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M : ℝ) (hM : 0 ≤ M) (x : ℝ ⊗[ℚ] L)
    (hx : ∀ i, |(b.baseChange ℝ).repr x i| ≤ M) :
    F.FirstCoefficientSlowBound b ω hF w T M (F.realFirstCoefficientConstant w x) := by
  classical
  intro z
  rw [F.realFirstCoefficientConstant_coordinate w b ω hF]
  split_ifs with hz
  · simpa only [hz, monomialScale_zero, div_one] using hx z.val.2
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT _).le

theorem realFirstCoefficientConstant_grid (l : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : (fun i => (b.baseChange ℝ).repr x i) ∈ realDenominatorGrid l) :
    F.FirstCoefficientGrid b ω hF w l (F.realFirstCoefficientConstant w x) := by
  classical
  obtain ⟨a, ha⟩ := hx
  refine ⟨fun z => if z.val.1 = 0 then a z.val.2 else 0, ?_⟩
  funext z
  change ((if z.val.1 = 0 then a z.val.2 else 0 : ℤ) : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientConstant w x) z
  rw [F.realFirstCoefficientConstant_coordinate w b ω hF]
  split_ifs
  · exact congrFun ha z.val.2
  · simp only [Int.cast_zero, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

section Transfer

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientAdjoint_bound_of_polynomial_bound (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (g : F.RealAdaptedPolynomialGroup w) (C : ℝ)
    (hpoly : ∀ y, F.RealAdaptedCoefficientBound b ω hF w T 1 y →
      F.RealAdaptedCoefficientBound b ω hF w T C (dualAdjoint g y))
    {M : ℝ} (hM : 0 ≤ M) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound b ω hF w T M x) :
    F.FirstCoefficientSlowBound b ω hF w T (C * M) (F.realFirstCoefficientAdjoint w g x) := by
  refine weighted_linear_bound_of_unit (F.realFirstCoefficientBasis b ω hF w)
    (F.realFirstCoefficientBasis b ω hF w) (fun z => monomialScale T z.val.1)
    (fun z => monomialScale T z.val.1) (F.realFirstCoefficientAdjoint w g).toLinearMap C ?_ hM x hx
  intro y hy
  change F.FirstCoefficientSlowBound b ω hF w T C (F.realFirstCoefficientAdjoint w g y)
  rw [← F.realFirstCoefficientSection_rightInverse b ω hF w y, F.realFirstCoefficientAdjoint_map]
  apply F.firstCoefficientSlowBound_map
  exact hpoly _ (F.realFirstCoefficientSection_slow b ω hF w T hT zero_le_one y hy)

theorem firstCoefficientAdjoint_grid_of_polynomial_grid
    (g : F.RealAdaptedPolynomialGroup w) (l m : ℕ)
    (hpoly : ∀ y, F.RealAdaptedCoefficientGrid b ω hF w l y →
      F.RealAdaptedCoefficientGrid b ω hF w m (dualAdjoint g y))
    (x : F.RealFirstCoefficientModule w) (hx : F.FirstCoefficientGrid b ω hF w l x) :
    F.FirstCoefficientGrid b ω hF w m (F.realFirstCoefficientAdjoint w g x) := by
  rw [← F.realFirstCoefficientSection_rightInverse b ω hF w x, F.realFirstCoefficientAdjoint_map]
  apply F.firstCoefficientGrid_map
  exact hpoly _ (F.realFirstCoefficientSection_grid b ω hF w l x hx)

end Transfer

theorem exists_firstCoefficient_adjoint_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g : F.RealAdaptedPolynomialGroup w,
      F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) g.coord →
      ∀ (M : ℝ), 0 ≤ M → ∀ x : F.RealFirstCoefficientModule w,
      F.FirstCoefficientSlowBound b ω hF w T M x →
      F.FirstCoefficientSlowBound b ω hF w T (Real.exp ((p + C) ^ C) * M)
        (F.realFirstCoefficientAdjoint w g x) := by
  have hex := exists_scaled_polynomial_dual_bound s a
  obtain ⟨C, hC, hbound⟩ := hex
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc T hT g hg M hM x hx
  have had := (hbound F b ω hF w hw H p hH hp hι hσ hHp hc T hT).2
  apply F.firstCoefficientAdjoint_bound_of_polynomial_bound b ω hF w T hT g
    (Real.exp ((p + C) ^ C)) ?_ hM x hx
  intro y hy
  exact had g y hg (F.realAdaptedCoefficientBound_mono b ω hF w T hT
    (Real.one_le_exp (by positivity)) y hy)

theorem exists_firstCoefficient_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
          (x : F.RealFirstCoefficientModule (fun _ : σ => 1)),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l g.coord →
          F.FirstCoefficientGrid b ω hF (fun _ => 1) l x →
          F.FirstCoefficientGrid b ω hF (fun _ => 1) m (F.realFirstCoefficientAdjoint (fun _ => 1) g x)) ∧
        (∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x →
          ∀ h : σ → ℤ, F.FirstCoefficientGrid b ω hF (fun _ => 1) m
            (F.realFirstCoefficientDirectionMap x (fun i => (h i : ℝ)))) := by
  have hex := exists_real_adapted_dual_grid s
  obtain ⟨C, hC, hgrid⟩ := hex
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  have hdata := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · intro g x hg hx
    exact F.firstCoefficientAdjoint_grid_of_polynomial_grid b ω hF (fun _ => 1)
      g l m (fun y hy => had g y hg hy) x hx
  · intro x hx h
    have he := F.realFirstCoefficientDirectionMap_rat x (fun i => (h i : ℚ))
    simp only [Rat.cast_intCast] at he
    rw [he]
    exact F.firstCoefficientGrid_map b ω hF (fun _ => 1) m _ (hlog x hx h)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientOfPolynomial_adjoint (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientOfPolynomial b ω hF w
      (dualAdjoint (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialTensor w x.val)).val =
      F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientMap w x) := by
  rw [← F.realAdaptedAdjoint_tensor, F.realFirstCoefficientAdjoint_map]
  let y : F.realShiftedCoefficientSubmodule w 1 :=
    ⟨dualAdjoint g x.val, dualAdjoint_real_mem_of_invariant ⊤ _
      (fun a _ c hc => F.realShiftedCoefficient_lie_mem w 1 a c hc) g (by trivial) x.val x.property⟩
  change F.realFirstCoefficientOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w y.val) =
    F.realFirstCoefficientMap w y
  exact F.realFirstCoefficientOfPolynomial_map b ω hF w y

theorem realFirstCoefficientOfPolynomial_adjoint_constant (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] L) :
    F.realFirstCoefficientOfPolynomial b ω hF w
      (dualAdjoint (F.realAdaptedPolynomialGroupHom w g) (F.realification.adaptedConstant w x)).val =
      F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientConstant w x) := by
  rw [← F.realAdaptedConstant_tensor]
  exact F.realFirstCoefficientOfPolynomial_adjoint b ω hF w g
    ⟨F.realAdaptedConstant w x, F.realAdaptedConstant_mem_first w x⟩

variable [Fintype σ]

theorem realFirstCoefficientOfPolynomial_logDerivative (h : σ → ℚ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
      (F.realification.adaptedLogDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val =
      F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) := by
  rw [← F.realAdaptedLogDerivative_tensor, F.realFirstCoefficientDirectionMap_rat]
  let y : F.realShiftedCoefficientSubmodule (fun _ : σ => 1) 1 :=
    ⟨F.realAdaptedLogDerivative h g.coord, F.realAdaptedLogDerivative_mem_first h g.coord⟩
  change F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
    (F.realAdaptedPolynomialMap (fun _ => 1) y.val) = F.realFirstCoefficientMap (fun _ => 1) y
  exact F.realFirstCoefficientOfPolynomial_map b ω hF (fun _ => 1) y

theorem realFirstCoefficientOfPolynomial_normalizedRelativeLog (h : σ → ℚ)
    (e m : ℝ ⊗[ℚ] L) (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
      (F.realification.normalizedRelativeLog h e m
        (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val =
      F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
        F.realFirstCoefficientConstant (fun _ => 1) e -
        F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) := by
  have he := F.realification.filteredFirstJet_normalizedRelativeLog h e m
    (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)
  rw [F.realFirstCoefficientOfPolynomial_eq_of_firstJet b ω hF (fun _ => 1) _ _ he]
  change F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
    ((F.realification.adaptedLogDerivative h
        (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val - monomial 0 e -
      (dualAdjoint (F.realAdaptedPolynomialGroupHom (fun _ => 1) g)
        (F.realification.adaptedConstant (fun _ => 1) m)).val) = _
  rw [map_sub, map_sub, F.realFirstCoefficientOfPolynomial_logDerivative,
    F.realFirstCoefficientOfPolynomial_constant, F.realFirstCoefficientOfPolynomial_adjoint_constant]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_firstCoefficient_coordinate_derivative_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + 2) ^ a)) x →
      ∀ i : σ, F.FirstCoefficientSlowBound b ω hF (fun _ => 1) T
        (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
        (F.realFirstCoefficientDirectionMap x (Pi.single i 1)) := by
  have hex := exists_scaled_polynomial_dual_bound s a
  obtain ⟨C, hC, hbound⟩ := hex
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT x hx i
  let Φ := dualRealLogarithmicDifferential
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot) x
  have hunit : ∀ y, F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T 1 y →
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C)) (Φ y) := by
    intro y hy
    have hy' := F.realAdaptedCoefficientBound_mono b ω hF (fun _ : σ => 1) T hT
      (Real.one_le_exp (by positivity : 0 ≤ (p + 2) ^ a)) y hy
    have hlog := (hbound F b ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
      H p hH hp hι hσ hHp hc T hT).1
    change F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
      (dualLogDerivative ⟨dualConstantLie x + dualInfinitesimal y⟩)
    apply hlog
    · simpa only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero] using hx
    · simpa only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add] using hy'
  have hderiv := F.realAdaptedDirectionalDerivative_single_bound b ω hF T hT
    (Real.exp_nonneg _) x hx i
  have hout : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
      (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
      (F.realAdaptedLogDerivative (Pi.single i 1) x) := by
    change F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
      (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
      (Φ (F.realAdaptedDirectionalDerivative (Pi.single i 1) x))
    exact weighted_linear_bound_of_unit
      ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
      ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
      (fun z => monomialScale T z.val.1) (fun z => monomialScale T z.val.1)
      Φ (Real.exp ((p + C) ^ C)) hunit
      (div_nonneg (mul_nonneg (Nat.cast_nonneg s) (Real.exp_nonneg _)) (hT i).le) _ hderiv
  have hsingle : (fun j => ((Pi.single i (1 : ℚ) : σ → ℚ) j : ℝ)) = Pi.single i 1 := by
    ext j
    by_cases hji : j = i <;> simp [hji]
  rw [← hsingle, F.realFirstCoefficientDirectionMap_rat]
  exact F.firstCoefficientSlowBound_map b ω hF (fun _ => 1) T _ _ hout

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {K E H : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup H] [Module K H] {a d : ℕ}

def extendInitialCoordinates : (Fin a → K) →ₗ[K] (Fin d → K) where
  toFun x j := if h : j.val < a then x ⟨j.val, h⟩ else 0
  map_add' x y := by funext j; by_cases h : j.val < a <;> simp [h]
  map_smul' c x := by funext j; by_cases h : j.val < a <;> simp [h]

@[simp] theorem extendInitialCoordinates_castLE (ha : a ≤ d) (x : Fin a → K) (i : Fin a) :
    extendInitialCoordinates x (Fin.castLE ha i) = x i := by
  simp [extendInitialCoordinates, i.isLt]

noncomputable def initialHorizontalEquiv (ha : a ≤ d) (b : Basis (Fin d) K E)
    (P : E →ₗ[K] H) (S : H →ₗ[K] E)
    (hsection : ∀ x, P (S x) = x)
    (hproj : ∀ x j, b.equivFun (S (P x)) j =
      if j.val < a then b.equivFun x j else 0) : (Fin a → K) ≃ₗ[K] H where
  toFun y := P (b.equivFun.symm (extendInitialCoordinates y))
  invFun x i := b.equivFun (S x) (Fin.castLE ha i)
  left_inv y := by
    funext i
    change b.equivFun (S (P (b.equivFun.symm (extendInitialCoordinates y))))
      (Fin.castLE ha i) = y i
    rw [hproj]
    simp only [LinearEquiv.apply_symm_apply, Fin.val_castLE, i.isLt, ite_true,
      extendInitialCoordinates_castLE]
  right_inv x := by
    have he : b.equivFun.symm
        (extendInitialCoordinates (fun i => b.equivFun (S x) (Fin.castLE ha i))) = S x := by
      apply b.equivFun.injective
      funext j
      rw [LinearEquiv.apply_symm_apply]
      change (if h : j.val < a then
        b.equivFun (S x) (Fin.castLE ha ⟨j.val, h⟩) else 0) = b.equivFun (S x) j
      split_ifs with hj
      · rfl
      · have h := hproj (S x) j
        simpa only [hsection, hj, ite_false] using h.symm
    change P (b.equivFun.symm
      (extendInitialCoordinates (fun i => b.equivFun (S x) (Fin.castLE ha i)))) = x
    rw [he, hsection]
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [map_smul, RingHom.id_apply]

theorem initialHorizontalEquiv_symm_projection (ha : a ≤ d) (b : Basis (Fin d) K E)
    (P : E →ₗ[K] H) (S : H →ₗ[K] E)
    (hsection : ∀ x, P (S x) = x)
    (hproj : ∀ x j, b.equivFun (S (P x)) j =
      if j.val < a then b.equivFun x j else 0) (x : E) :
    (initialHorizontalEquiv ha b P S hsection hproj).symm (P x) =
      fun i => b.equivFun x (Fin.castLE ha i) := by
  funext i
  change b.equivFun (S (P x)) (Fin.castLE ha i) = _
  rw [hproj]
  simp only [Fin.val_castLE, i.isLt, ite_true]

theorem initialHorizontalEquiv_projection (ha : a ≤ d) (b : Basis (Fin d) K E)
    (P : E →ₗ[K] H) (S : H →ₗ[K] E)
    (hsection : ∀ x, P (S x) = x)
    (hproj : ∀ x j, b.equivFun (S (P x)) j =
      if j.val < a then b.equivFun x j else 0) (x : E) :
    initialHorizontalEquiv ha b P S hsection hproj
      (fun i => b.equivFun x (Fin.castLE ha i)) = P x := by
  rw [← initialHorizontalEquiv_symm_projection ha b P S hsection hproj x,
    LinearEquiv.apply_symm_apply]

end Erdos3

end

section

namespace Erdos3

theorem realDenominatorGrid_single {ι : Type*} [DecidableEq ι] (l : ℕ) (i : ι) :
    Pi.single i (1 : ℝ) ∈ realDenominatorGrid l := by
  refine ⟨Pi.single i (l : ℤ), ?_⟩
  funext j
  change ((Pi.single i (l : ℤ) : ι → ℤ) j : ℝ) =
    (l : ℝ) * (Pi.single i (1 : ℝ) : ι → ℝ) j
  by_cases h : j = i <;> simp [h]

theorem extendInitialCoordinates_grid {a d : ℕ} (l : ℕ) (x : Fin a → ℝ)
    (hx : x ∈ realDenominatorGrid l) :
    (extendInitialCoordinates x : Fin d → ℝ) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => if hi : i.val < a then z ⟨i.val, hi⟩ else 0, ?_⟩
  funext i
  change ((if hi : i.val < a then z ⟨i.val, hi⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * (if hi : i.val < a then x ⟨i.val, hi⟩ else 0)
  by_cases hi : i.val < a
  · simpa only [hi, dite_true, Pi.smul_apply, smul_eq_mul] using congrFun hz ⟨i.val, hi⟩
  · simp only [hi, dite_false, Int.cast_zero, mul_zero]

theorem norm_extendInitialCoordinates_le {a d : ℕ} (x : Fin a → ℝ) :
    ‖(extendInitialCoordinates x : Fin d → ℝ)‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  change ‖if hi : i.val < a then x ⟨i.val, hi⟩ else 0‖ ≤ ‖x‖
  split_ifs with hi
  · exact norm_le_pi_norm x ⟨i.val, hi⟩
  · simpa only [norm_zero] using norm_nonneg x

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientHorizontal_projector_repr
    (x : F.FirstCoefficientModule w) (z : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis b ω hF w).repr
        (F.firstCoefficientHorizontalSection w (F.firstCoefficientHorizontal w x)) z =
      if z.val.1 = 0 then (F.firstCoefficientBasis b ω hF w).repr x z else 0 := by
  classical
  obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientHorizontal_map, F.firstCoefficientHorizontalSection_mk]
  change (F.firstCoefficientBasis b ω hF w).repr
      (F.firstCoefficientMap w ⟨F.adaptedConstant w (coefficients p.val.val 0), _⟩) z = _
  rw [F.firstCoefficientBasis_repr_map, F.firstCoefficientBasis_repr_map]
  change b.repr (coefficients (monomial 0 (coefficients p.val.val 0)) z.val.1) z.val.2 = _
  by_cases hz : z.val.1 = 0
  · simp [hz, coefficients_monomial]
  · simp [hz, coefficients_monomial, Finsupp.single_eq_of_ne hz]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientRealEquiv_coordinates (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w)
    (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.firstCoefficientRealEquiv w x) z =
      ((F.firstCoefficientBasis b ω hF w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r x =>
    obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
    have ht : r ⊗ₜ[ℚ] F.firstCoefficientMap w p =
        (F.firstCoefficientMap w).baseChange ℝ (r ⊗ₜ[ℚ] p) := rfl
    rw [ht, F.firstCoefficientRealEquiv_map]
    let q : F.realShiftedCoefficientSubmodule w 1 :=
      ⟨r ⊗ₜ[ℚ] p.val, Submodule.tmul_mem_baseChange_of_mem r p.property⟩
    change (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w q) z =
      ((F.firstCoefficientBasis b ω hF w).baseChange ℝ).repr (r ⊗ₜ[ℚ] F.firstCoefficientMap w p) z
    rw [F.realFirstCoefficientBasis_repr_map]
    change ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr (r ⊗ₜ[ℚ] p.val)
        ((firstCoefficientSurvivorEquiv w ω).symm z).val.val =
      ((F.firstCoefficientBasis b ω hF w).baseChange ℝ).repr (r ⊗ₜ[ℚ] F.firstCoefficientMap w p) z
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      F.adaptedMonomialBasis_repr, F.firstCoefficientBasis_repr_map]
    rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realFirstCoefficientHorizontal_projector_repr
    (x : F.RealFirstCoefficientModule w) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr
        (F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x)) z =
      if z.val.1 = 0 then (F.realFirstCoefficientBasis b ω hF w).repr x z else 0 := by
  classical
  obtain ⟨x, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  change (F.realFirstCoefficientBasis b ω hF w).repr
    (F.firstCoefficientRealEquiv w ((F.firstCoefficientHorizontalSection w).baseChange ℝ
      ((F.firstCoefficientHorizontal w).baseChange ℝ
        ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w x))))) z = _
  rw [LinearEquiv.symm_apply_apply, F.firstCoefficientRealEquiv_coordinates,
    F.firstCoefficientRealEquiv_coordinates]
  exact baseChange_coordinate_projector_repr (F.firstCoefficientBasis b ω hF w)
    (F.firstCoefficientHorizontal w) (F.firstCoefficientHorizontalSection w)
    (fun z => z.val.1 = 0) (F.firstCoefficientHorizontal_projector_repr b ω hF w) x z

theorem realFirstCoefficientHorizontal_projector (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x) =
      basisCoordinateProjection (F.realFirstCoefficientBasis b ω hF w) {z | z.val.1 = 0} x := by
  classical
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.realFirstCoefficientHorizontal_projector_repr, basisCoordinateProjection_repr]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (rows : Fin d → FirstCoefficientIndex w ω)
  (hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
    b.repr ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
      (F.realFirstCoefficientBasis e ω hF w i)) j = 0)

include hblock

theorem realFastCoefficientHorizontal_projector
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :
    F.realFastCoefficientHorizontalSection w hw U (F.realFastCoefficientHorizontal w hw U x) =
      basisCoordinateProjection b {j | (rows j).val.1 = 0} x := by
  classical
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw U).mkQ_surjective x
  change (F.realFirstCoefficientFastSubmodule w hw U).mkQ
    (F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x)) = _
  rw [F.realFirstCoefficientHorizontal_projector e ω hF w]
  exact basisBlockMap_commutes (F.realFirstCoefficientBasis e ω hF w) b
    (fun i => i.val.1) (fun j => (rows j).val.1)
    (F.realFirstCoefficientFastSubmodule w hw U).mkQ hblock 0 x

theorem realFastCoefficientHorizontal_projector_repr
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U)
    (j : Fin d) :
    b.repr (F.realFastCoefficientHorizontalSection w hw U
      (F.realFastCoefficientHorizontal w hw U x)) j =
      if (rows j).val.1 = 0 then b.repr x j else 0 := by
  rw [F.realFastCoefficientHorizontal_projector e ω hF w hw U b rows hblock]
  exact basisCoordinateProjection_repr b {j | (rows j).val.1 = 0} x j

noncomputable def realFastCoefficientHorizontalEquiv {a : ℕ} (ha : a ≤ d)
    (hprefix : ∀ j, j.val < a ↔ (rows j).val.1 = 0) :
    (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :=
  initialHorizontalEquiv ha b (F.realFastCoefficientHorizontal w hw U)
    (F.realFastCoefficientHorizontalSection w hw U)
    (F.realFastCoefficientHorizontal_section w hw U) (fun x j => by
      change b.repr (F.realFastCoefficientHorizontalSection w hw U
        (F.realFastCoefficientHorizontal w hw U x)) j = _
      rw [F.realFastCoefficientHorizontal_projector_repr e ω hF w hw U b rows hblock]
      simp only [← hprefix j, Basis.equivFun_apply])

theorem realFastCoefficientHorizontalEquiv_projection {a : ℕ} (ha : a ≤ d)
    (hprefix : ∀ j, j.val < a ↔ (rows j).val.1 = 0)
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :
    F.realFastCoefficientHorizontalEquiv e ω hF w hw U b rows hblock ha hprefix
      (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x :=
  initialHorizontalEquiv_projection ha b (F.realFastCoefficientHorizontal w hw U)
    (F.realFastCoefficientHorizontalSection w hw U)
    (F.realFastCoefficientHorizontal_section w hw U) _ x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

section Ambient

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientRealEquiv_basis (i : FirstCoefficientIndex w ω) :
    F.firstCoefficientRealEquiv w ((F.firstCoefficientBasis e ω hF w).baseChange ℝ i) =
      F.realFirstCoefficientBasis e ω hF w i := by
  apply (F.realFirstCoefficientBasis e ω hF w).repr.injective
  ext j
  rw [F.firstCoefficientRealEquiv_coordinates]
  simp only [Basis.repr_self]

end Ambient

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def realFastCoefficientBasis
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U)) :
    Basis κ ℝ (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :=
  realTransportedQuotientBasis (F.firstCoefficientFastSubmodule w hw U)
    (F.firstCoefficientRealEquiv w) b

theorem realFastCoefficientBasis_repr_basis
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U))
    (i : FirstCoefficientIndex w ω) (j : κ) :
    (F.realFastCoefficientBasis w hw U b).repr
        ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
          (F.realFirstCoefficientBasis e ω hF w i)) j =
      (b.repr ((F.firstCoefficientFastSubmodule w hw U).mkQ
        (F.firstCoefficientBasis e ω hF w i)) j : ℝ) := by
  rw [← F.firstCoefficientRealEquiv_basis e ω hF w i]
  exact realTransportedQuotientBasis_repr_basis _ _ _ b i j

theorem realFastCoefficientBasis_matrix
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U)) :
    LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w)
        (F.realFastCoefficientBasis w hw U b) (F.realFirstCoefficientFastSubmodule w hw U).mkQ =
      (LinearMap.toMatrix (F.firstCoefficientBasis e ω hF w) b
        (F.firstCoefficientFastSubmodule w hw U).mkQ).map (Rat.castHom ℝ) := by
  ext j i
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply]
  exact F.realFastCoefficientBasis_repr_basis w hw U e ω hF b i j

theorem realFastCoefficientBasis_symm
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U))
    (D : Matrix κ (FirstCoefficientIndex w ω) ℚ)
    (S : Matrix (FirstCoefficientIndex w ω) κ ℚ)
    (hD : LinearMap.toMatrix (F.firstCoefficientBasis e ω hF w) b
      (F.firstCoefficientFastSubmodule w hw U).mkQ = D)
    (hDS : D * S = 1) (y : κ → ℝ) :
    (F.realFastCoefficientBasis w hw U b).equivFun.symm y =
      (F.realFirstCoefficientFastSubmodule w hw U).mkQ
        ((F.realFirstCoefficientBasis e ω hF w).equivFun.symm
          (S.map (Rat.castHom ℝ) *ᵥ y)) := by
  apply quotient_basis_representative (F.realFirstCoefficientBasis e ω hF w)
    (F.realFastCoefficientBasis w hw U b) _ (D.map (Rat.castHom ℝ)) _ ?_
    (real_matrix_right_inverse D S hDS) y
  rw [F.realFastCoefficientBasis_matrix, hD]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealReducedCoefficientMap
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def realReducedSquareCoefficientMap (w : σ → ℕ) :
    (ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w) →ₗ[ℝ]
      F.RealFirstCoefficientModule w :=
  (F.firstCoefficientRealEquiv w).toLinearMap.comp
    ((F.reducedSquareCoefficientMap w).baseChange ℝ)

theorem realReducedSquareCoefficientMap_relative (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realReducedSquareCoefficientMap w (F.realReducedRelativeSquareSymbolMap w hw x) =
      F.realNormalizedFirstCoefficientMap w x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    change F.firstCoefficientRealEquiv w
      (r ⊗ₜ[ℚ] F.reducedSquareCoefficientMap w (F.reducedRelativeSquareSymbolMap w hw x)) =
      F.firstCoefficientRealEquiv w (r ⊗ₜ[ℚ] F.normalizedFirstCoefficientMap w x)
    rw [F.reducedSquareCoefficientMap_relative]

theorem realReducedRelativeCoefficient_eq_map (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.realReducedRelativeCoefficient w hw g =
      F.realReducedSquareCoefficientMap w (F.reducedSquareRealRelativePart w g).coord := by
  obtain ⟨x, hx⟩ := F.reducedSquareRealRelativePart_exists_preimage w hw g
  rw [← hx, F.realReducedSquareCoefficientMap_relative]
  exact (F.realReducedRelativeCoefficient_of_preimage w hw g x hx).symm

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (FirstCoefficientIndex w ω)]

theorem realReducedSquareCoefficientMap_matrix [DecidableEq (ReducedSquareSymbolIndex s w ω)] :
    LinearMap.toMatrix ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
      (F.realFirstCoefficientBasis e ω hF w) (F.realReducedSquareCoefficientMap w) =
      (LinearMap.toMatrix (F.reducedSquareSymbolBasis e ω hF w)
        (F.firstCoefficientBasis e ω hF w) (F.reducedSquareCoefficientMap w)).map
          (Rat.castHom ℝ) := by
  exact scalarExtension_equiv_matrix (F.reducedSquareSymbolBasis e ω hF w)
    (F.firstCoefficientBasis e ω hF w) (F.realFirstCoefficientBasis e ω hF w)
    (F.reducedSquareCoefficientMap w) (F.firstCoefficientRealEquiv w)
    (F.firstCoefficientRealEquiv_coordinates e ω hF w)

theorem realReducedSquareCoefficientMap_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M : ℝ) (hM : 0 ≤ M) (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T M g) :
    F.FirstCoefficientSlowBound e ω hF w T
      (((Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) + 1) * 2 * M)
      (F.realReducedSquareCoefficientMap w g.coord) := by
  classical
  let D := LinearMap.toMatrix (F.reducedSquareSymbolBasis e ω hF w)
    (F.firstCoefficientBasis e ω hF w) (F.reducedSquareCoefficientMap w)
  intro i
  have h := rational_coordinate_map_weighted
    ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
    (F.realFirstCoefficientBasis e ω hF w) (F.realReducedSquareCoefficientMap w)
    D (F.realReducedSquareCoefficientMap_matrix e ω hF w)
    (fun j => j.val.1) (fun j => j.val.1)
    (fun i j hij => by simpa only [D, LinearMap.toMatrix_apply] using
      F.reducedSquareCoefficientMap_monomial_blocks e ω hF w j i hij)
    1 (fun i j => by
      dsimp only [D]
      rw [LinearMap.toMatrix_apply]
      exact_mod_cast (F.reducedSquareCoefficientMap_basis_height e ω hF w j i).1)
    (monomialScale T) (monomialScale_pos T hT) hM g.coord hg i
  simpa only [Basis.equivFun_apply, NNReal.coe_one, one_add_one_eq_two] using h

theorem realReducedSquareCoefficientMap_grid (l : ℕ)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l g) :
    F.FirstCoefficientGrid e ω hF w l (F.realReducedSquareCoefficientMap w g.coord) := by
  classical
  let D := LinearMap.toMatrix (F.reducedSquareSymbolBasis e ω hF w)
    (F.firstCoefficientBasis e ω hF w) (F.reducedSquareCoefficientMap w)
  have hden : matrixDenominator D = 1 := by
    apply Nat.le_antisymm
    · have hb : ∀ i j, RationalHeightLE (D i j) 1 := by
        intro i j
        simpa only [D, LinearMap.toMatrix_apply] using
          F.reducedSquareCoefficientMap_basis_height e ω hF w j i
      simpa using matrixDenominator_le D hb
    · exact matrixDenominator_pos D
  have h := rational_coordinate_map_grid
    ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
    (F.realFirstCoefficientBasis e ω hF w) (F.realReducedSquareCoefficientMap w)
    D (F.realReducedSquareCoefficientMap_matrix e ω hF w) l g.coord hg
  simpa only [hden, one_mul, FirstCoefficientGrid, Basis.equivFun_apply] using h

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReducedProjectionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

def reducedSquareDiagonalIndex (s : ℕ) (ω : ι → ℕ)
    (i : QuotientTopBasisIndex s ω) : ReducedSquareBasisIndex s ω :=
  ⟨Sum.inl i.val, i.property⟩

def reducedSquareDiagonalSymbolIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ)
    (z : QuotientTopSymbolIndex s w ω) : ReducedSquareSymbolIndex s w ω :=
  ⟨(z.val.1, reducedSquareDiagonalIndex s ω z.val.2), z.property⟩

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem reducedSquareSnd_basis_repr [DecidableEq ι]
    (a : ReducedSquareBasisIndex s ω) (b : QuotientTopBasisIndex s ω) :
    (F.quotientTopBasis e ω hF).repr
      (F.reducedSquareSnd (F.reducedSquareBasis e ω hF a)) b =
      if a = reducedSquareDiagonalIndex s ω b then 1 else 0 := by
  classical
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareSnd_mk,
    F.quotientTopBasis_repr_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl i =>
    change e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inl i)).val.2) b.val = _
    rw [F.adaptedSquareBasis_inl]
    simp [reducedSquareDiagonalIndex, Basis.repr_self, Finsupp.single_apply,
      Subtype.ext_iff]
  | inr i =>
    change e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inr i)).val.2) b.val = _
    rw [F.adaptedSquareBasis_inr]
    simp [reducedSquareDiagonalIndex, Subtype.ext_iff]

theorem reducedSquareSndSymbolMap_basis_repr [DecidableEq σ] [DecidableEq ι] (w : σ → ℕ)
    (a : ReducedSquareSymbolIndex s w ω) (b : QuotientTopSymbolIndex s w ω) :
    (F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b =
      if a = reducedSquareDiagonalSymbolIndex s w ω b then 1 else 0 := by
  classical
  change (F.quotientTop.polynomialSymbolBasis _ _ _ w).repr
    (F.squareFiltration.quotientTop.filteredPolynomialSymbolMap F.quotientTop
      F.reducedSquareSnd F.reducedSquareSnd_mem w
      (F.squareFiltration.quotientTop.polynomialSymbolBasis _ _ _ w a)) b = _
  rw [filteredPolynomialSymbolMap_basis_repr, F.reducedSquareSnd_basis_repr e ω hF]
  simp [reducedSquareDiagonalSymbolIndex, Subtype.ext_iff, Prod.ext_iff, ite_and]

theorem reducedSquareSndSymbolMap_repr (w : σ → ℕ)
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w)
    (b : QuotientTopSymbolIndex s w ω) :
    (F.quotientTopSymbolBasis e ω hF w).repr (F.reducedSquareSndSymbolMap w x) b =
      (F.reducedSquareSymbolBasis e ω hF w).repr x
        (reducedSquareDiagonalSymbolIndex s w ω b) := by
  classical
  have h : ((F.quotientTopSymbolBasis e ω hF w).coord b).comp
      (F.reducedSquareSndSymbolMap w).toLinearMap =
      (F.reducedSquareSymbolBasis e ω hF w).coord
        (reducedSquareDiagonalSymbolIndex s w ω b) := by
    apply (F.reducedSquareSymbolBasis e ω hF w).ext
    intro a
    change (F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b = _
    rw [F.reducedSquareSndSymbolMap_basis_repr e ω hF]
    simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  exact DFunLike.congr_fun h x

theorem reducedSquareRealSymbolHom_repr (w : σ → ℕ)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (b : QuotientTopSymbolIndex s w ω) :
    ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).repr
        (F.reducedSquareRealSymbolHom w g).coord b =
      ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).repr g.coord
        (reducedSquareDiagonalSymbolIndex s w ω b) := by
  classical
  have h : (((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).coord b).comp
      ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) =
      ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).coord
        (reducedSquareDiagonalSymbolIndex s w ω b) := by
    apply ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).ext
    intro a
    change ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).repr
      ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
        (((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ) a)) b = _
    rw [linearMap_baseChange_basis]
    change ((F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b : ℝ) = _
    rw [F.reducedSquareSndSymbolMap_basis_repr e ω hF]
    simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> norm_num
  exact DFunLike.congr_fun h g.coord

theorem reducedSquareRealSymbolHom_slow (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T M g) :
    F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T M
      (F.reducedSquareRealSymbolHom w g) := by
  intro b
  change |((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).repr
    (F.reducedSquareRealSymbolHom w g).coord b| ≤ _
  rw [F.reducedSquareRealSymbolHom_repr e ω hF]
  exact hg (reducedSquareDiagonalSymbolIndex s w ω b)

theorem reducedSquareRealSymbolHom_grid (w : σ → ℕ) (l : ℕ)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l g) :
    F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l
      (F.reducedSquareRealSymbolHom w g) := by
  obtain ⟨z, hz⟩ := hg
  refine ⟨fun b => z (reducedSquareDiagonalSymbolIndex s w ω b), ?_⟩
  funext b
  change (z (reducedSquareDiagonalSymbolIndex s w ω b) : ℝ) =
    (l : ℝ) * ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).repr
      (F.reducedSquareRealSymbolHom w g).coord b
  rw [F.reducedSquareRealSymbolHom_repr e ω hF]
  exact congrFun hz (reducedSquareDiagonalSymbolIndex s w ω b)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedDiagonalBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem reducedSquareDiagonal_basis (a : QuotientTopBasisIndex s ω) :
    F.reducedSquareDiagonal (F.quotientTopBasis e ω hF a) =
      F.reducedSquareBasis e ω hF (reducedSquareDiagonalIndex s ω a) := by
  rw [F.quotientTopBasis_apply, F.reducedSquareDiagonal_mk]
  change _ = F.squareFiltration.quotientTopBasis (F.adaptedSquareBasis e ω (hF 2))
    (squareBasisWeight ω) (F.adaptedSquareBasis_layers e ω hF) _
  rw [F.squareFiltration.quotientTopBasis_apply]
  congr 1
  apply Subtype.ext
  exact (F.adaptedSquareBasis_inl e ω (hF 2) a.val).symm

theorem reducedSquareDiagonal_basis_height
    (a : QuotientTopBasisIndex s ω) (b : ReducedSquareBasisIndex s ω) :
    RationalHeightLE ((F.reducedSquareBasis e ω hF).repr
      (F.reducedSquareDiagonal (F.quotientTopBasis e ω hF a)) b) 1 := by
  rw [F.reducedSquareDiagonal_basis]
  exact basis_repr_height_one (F.reducedSquareBasis e ω hF) _ _

theorem reducedSquareDiagonalSymbolMap_basis_height (w : σ → ℕ)
    (a : QuotientTopSymbolIndex s w ω) (b : ReducedSquareSymbolIndex s w ω) :
    RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr
      (F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolBasis e ω hF w a)) b) 1 :=
  filteredPolynomialSymbolMap_basis_height F.quotientTop F.squareFiltration.quotientTop
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF) F.reducedSquareDiagonal F.reducedSquareDiagonal_mem
    w le_rfl (fun i j => F.reducedSquareDiagonal_basis_height e ω hF j i) a b

theorem reducedSquareDiagonalSymbolMap_monomial_blocks (w : σ → ℕ)
    (a : QuotientTopSymbolIndex s w ω) (b : ReducedSquareSymbolIndex s w ω)
    (hab : b.val.1 ≠ a.val.1) :
    (F.reducedSquareSymbolBasis e ω hF w).repr
      (F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolBasis e ω hF w a)) b = 0 :=
  filteredPolynomialSymbolMap_monomial_blocks F.quotientTop F.squareFiltration.quotientTop
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF) F.reducedSquareDiagonal F.reducedSquareDiagonal_mem
    w a b hab

variable (w : σ → ℕ) [Fintype (QuotientTopSymbolIndex s w ω)]
  [Fintype (ReducedSquareSymbolIndex s w ω)]

theorem reducedSquareRealDiagonalHom_coord
    (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareRealDiagonalHom w g).coord =
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ g.coord := rfl

theorem reducedSquareDiagonalSymbolMap_real_matrix
    [DecidableEq (QuotientTopSymbolIndex s w ω)] :
    LinearMap.toMatrix ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ)
      ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
        ((F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ) =
      (LinearMap.toMatrix (F.quotientTopSymbolBasis e ω hF w)
        (F.reducedSquareSymbolBasis e ω hF w) (F.reducedSquareDiagonalSymbolMap w).toLinearMap).map
          (Rat.castHom ℝ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, linearMap_baseChange_basis]
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply, Rat.coe_castHom]

theorem reducedSquareRealDiagonalHom_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M : ℝ) (hM : 0 ≤ M) (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T M g) :
    F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
      (((Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) + 1) * 2 * M)
      (F.reducedSquareRealDiagonalHom w g) := by
  classical
  let D := LinearMap.toMatrix (F.quotientTopSymbolBasis e ω hF w)
    (F.reducedSquareSymbolBasis e ω hF w) (F.reducedSquareDiagonalSymbolMap w).toLinearMap
  intro i
  have h := rational_coordinate_map_weighted
    ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ)
    ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
    ((F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ)
    D (F.reducedSquareDiagonalSymbolMap_real_matrix e ω hF w)
    (fun j => j.val.1) (fun j => j.val.1)
    (fun i j hij => by
      dsimp only [D]
      rw [LinearMap.toMatrix_apply]
      exact F.reducedSquareDiagonalSymbolMap_monomial_blocks e ω hF w j i hij)
    1 (fun i j => by
      dsimp only [D]
      rw [LinearMap.toMatrix_apply]
      exact_mod_cast (F.reducedSquareDiagonalSymbolMap_basis_height e ω hF w j i).1)
    (monomialScale T) (monomialScale_pos T hT) hM g.coord hg i
  change |((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).repr
    (F.reducedSquareRealDiagonalHom w g).coord i| ≤ _
  rw [F.reducedSquareRealDiagonalHom_coord]
  simpa only [Basis.equivFun_apply, NNReal.coe_one, one_add_one_eq_two] using h

theorem reducedSquareRealDiagonalHom_grid (l : ℕ)
    (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l g) :
    F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l
      (F.reducedSquareRealDiagonalHom w g) := by
  change (fun z => ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).repr
    (F.reducedSquareRealDiagonalHom w g).coord z) ∈
      realDenominatorGrid l
  rw [F.reducedSquareRealDiagonalHom_coord]
  exact scalarExtension_grid_of_height_one (F.quotientTopSymbolBasis e ω hF w)
    (F.reducedSquareSymbolBasis e ω hF w) (F.reducedSquareDiagonalSymbolMap w).toLinearMap
    (fun i j => F.reducedSquareDiagonalSymbolMap_basis_height e ω hF w j i) l g.coord hg

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LayerOneCoefficientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

abbrev LayerOneBasisIndex (ω : ι → ℕ) := {i : ι // ¬ 2 ≤ ω i}

noncomputable def layerOneBasis : Basis (LayerOneBasisIndex ω) ℚ (L ⧸ F.layer 2) :=
  supportedQuotientBasis e (F.layer 2) {i | 2 ≤ ω i} (hF 2)

theorem layerOneBasis_repr_mk (x : L) (i : LayerOneBasisIndex ω) :
    (F.layerOneBasis e ω hF).repr ((F.layer 2).mkQ x) i = e.repr x i :=
  supportedQuotientBasis_repr_mk e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x i

def horizontalCoefficientIndex (w : σ → ℕ) (i : LayerOneBasisIndex ω) :
    FirstCoefficientIndex w ω :=
  ⟨(0, i.val), by
    have hp := F.adaptedBasis_weight_pos e ω hF i.val
    have hi := i.property
    simp only [map_zero, Nat.zero_add]
    omega⟩

def layerOneIndexOfConstant (w : σ → ℕ) (z : FirstCoefficientIndex w ω)
    (hz : z.val.1 = 0) : LayerOneBasisIndex ω :=
  ⟨z.val.2, by
    have h := z.property
    rw [hz, map_zero] at h
    omega⟩

theorem horizontalCoefficientIndex_of_constant (w : σ → ℕ)
    (z : FirstCoefficientIndex w ω) (hz : z.val.1 = 0) :
    F.horizontalCoefficientIndex e ω hF w (layerOneIndexOfConstant ω w z hz) = z := by
  apply Subtype.ext
  exact Prod.ext hz.symm rfl

theorem firstCoefficientHorizontal_coordinates (w : σ → ℕ)
    (x : F.FirstCoefficientModule w) (i : LayerOneBasisIndex ω) :
    (F.layerOneBasis e ω hF).repr (F.firstCoefficientHorizontal w x) i =
      (F.firstCoefficientBasis e ω hF w).repr x (F.horizontalCoefficientIndex e ω hF w i) := by
  obtain ⟨x, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientHorizontal_map, F.layerOneBasis_repr_mk,
    F.firstCoefficientBasis_repr_map]
  rfl

theorem realFirstCoefficientHorizontal_coordinates (w : σ → ℕ)
    (x : F.RealFirstCoefficientModule w) (i : LayerOneBasisIndex ω) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).repr (F.realFirstCoefficientHorizontal w x) i =
      (F.realFirstCoefficientBasis e ω hF w).repr x
        (F.horizontalCoefficientIndex e ω hF w i) := by
  obtain ⟨x, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  change ((F.layerOneBasis e ω hF).baseChange ℝ).repr
    ((F.firstCoefficientHorizontal w).baseChange ℝ
      ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w x))) i = _
  rw [LinearEquiv.symm_apply_apply, F.firstCoefficientRealEquiv_coordinates]
  exact baseChange_coordinate_eq (F.firstCoefficientBasis e ω hF w)
    (F.layerOneBasis e ω hF) (F.firstCoefficientHorizontal w)
    (F.horizontalCoefficientIndex e ω hF w)
    (F.firstCoefficientHorizontal_coordinates e ω hF w) x i

end Erdos3.NilpotentLieFiltration

end

end OAI

end


