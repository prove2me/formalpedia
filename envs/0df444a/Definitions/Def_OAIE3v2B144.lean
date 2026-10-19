-- Prove2me | Definitions.Def_OAIE3v2B144
-- name    : OAIE3v2B144
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:10:33.462061+00:00
-- url     : https://prove2.me/theorems/774e0be7-4bf0-4ff6-bf19-e863432fee80
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 146 of 311
-- statement:
--   Definitions bundle 146 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B128`, `OAIE3v2B129`, `OAIE3v2B130`, `OAIE3v2B131`, `OAIE3v2B132`, `OAIE3v2B133`, `OAIE3v2B134` of this split.
--
--   Modules: `Dynamics/RationalConstraintCountBudget.lean`, `Estimates/BoundedRealifiedSquareOrbit.lean`, `Estimates/BoundedSubmoduleIntersection.lean`, `Estimates/CommonIntegralModelEquivalences.lean`, `Estimates/FastCoefficientImage.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/NativeCentralSeed.lean`, `Estimates/ProjectedPointwiseCoefficient.lean`, `Estimates/RealFirstCoefficientHorizontal.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/ReducedSquareSymbol.lean`, `Estimates/ReducedSymbolDimensions.lean`, `Estimates/SquareRationalModel.lean`, `Estimates/SquareStructureHeight.lean`, `Estimates/SymbolCommonCorrections.lean`, `Estimates/SymbolFastMembership.lean`, `Geometry/CoordinateDerivativeBounds.lean`, `Linear/RationalSpanDerivativeSystem.lean`, `Linear/RealDualRationalBounds.lean`, `Linear/ReindexGradedBasis.lean`, `Linear/ReindexQuotientBasis.lean`, `Linear/SquareBasisGeometry.lean`, `Nilpotent/NiltestVerticalBounds.lean`, `Nilpotent/RationalBCHProducts.lean`, `Polynomial/FormalPolynomialCorrectionStep.lean`, `Polynomial/PolynomialDerivativeBounds.lean`, `Polynomial/PolynomialDerivativeDifferences.lean`, `Polynomial/ShiftedGradedPolynomial.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129
import Definitions.Def_OAIE3v2B130
import Definitions.Def_OAIE3v2B131
import Definitions.Def_OAIE3v2B132
import Definitions.Def_OAIE3v2B133
import Definitions.Def_OAIE3v2B134

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RationalBCHProducts
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_bch_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (lieStructureConstants e i j z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (NilpotentLieBCHGroup L s hnil), rs.length ≤ k →
          (∀ r ∈ rs, e.equivFun r.coord ∈ denominatorGrid l) →
          e.equivFun rs.prod.coord ∈ denominatorGrid m := by
  have hrealExists := exists_real_bch_rational_product_bound s k
  obtain ⟨C, hC, hreal⟩ := hrealExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
  have hproductsExists := hreal e H p hnil hp hd hH hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hproductsExists
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro rs hlen hrs
  have hinputs : ∀ r ∈ rs.map (realificationHom (hnil := hnil)),
      (e.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid l := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
    exact hrs q hq
  have hout := hproducts (rs.map (realificationHom (hnil := hnil)))
    (by simpa only [List.length_map] using hlen) hinputs
  rw [← map_list_prod, realificationHom_coordinates, real_cast_mem_denominatorGrid_iff] at hout
  exact hout

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem squareObservable_mk (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (g : F.squareFiltration.Group) :
    F.squareObservable Γ ε u (QuotientGroup.mk g) =
      u (QuotientGroup.mk (ε * F.squareFstHom g)) * star (u (QuotientGroup.mk (F.squareSndHom g))) := rfl

theorem squareObservable_top_invariant (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (χ : F.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.subgroup s, ∀ x, u (z • x) = character (χ z) * u x)
    (k : F.squareFiltration.Group) (hk : k ∈ F.squareFiltration.subgroup s)
    (x : F.squareFiltration.Group ⧸ F.squareLattice Γ) :
    F.squareObservable Γ ε u (k • x) = F.squareObservable Γ ε u x := by
  obtain ⟨hz, heq⟩ := F.square_top_projections hk
  let z := F.squareFstHom k
  have hε : ∀ y : F.Group ⧸ Γ, ε • (z • y) = z • (ε • y) := by
    intro y
    rw [← mul_smul, ← mul_smul, (F.top_commutes z hz ε).eq]
  simp only [squareObservable, cosetMap_smul, ← heq]
  rw [hε, hu z hz, hu z hz, star_mul]
  have hc : character (χ z) * star (character (χ z)) = 1 := by
    rw [← character_neg, ← character_add, add_neg_cancel, character_zero]
  calc
    _ = (character (χ z) * star (character (χ z))) *
        (u (ε • cosetMap (F.squareLattice Γ) Γ F.squareFstHom (F.squareLattice_le_fst Γ) x) *
          star (u (cosetMap (F.squareLattice Γ) Γ F.squareSndHom (F.squareLattice_le_snd Γ) x))) := by ring
    _ = _ := by rw [hc, one_mul]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealDualRationalBounds
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_rational_dual_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      1 ≤ H → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ z : DualGroup hnil,
          e.equivFun (dualBaseLinear z.coord) ∈ denominatorGrid l →
          e.equivFun (dualTangentLinear z.coord) ∈ denominatorGrid l →
          e.equivFun (dualLogDerivative z) ∈ denominatorGrid m) ∧
        (∀ (g : NilpotentLieBCHGroup L s hnil) (x : L),
          e.equivFun g.coord ∈ denominatorGrid l → e.equivFun x ∈ denominatorGrid l →
          e.equivFun (dualAdjoint g x) ∈ denominatorGrid m) := by
  have hproductsExists := exists_bch_rational_product_bound s 3
  obtain ⟨D, _, hproducts⟩ := hproductsExists
  let B : Polynomial ℕ := (2 * Polynomial.X + Polynomial.C D) ^ D
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hH hp hd hHp hc l hl hlp
  have hp2 : p ≤ 2 * p := by linarith
  have hdim : (Fintype.card (ι ⊕ ι) : ℝ) ≤ 2 * p := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  have hdata := hproducts (rationalDualBasis e) H (2 * p) (dualLie_lowerCentralSeries_eq_bot hnil)
    (by positivity) hdim (hHp.trans (Real.exp_le_exp.mpr hp2))
    (rationalDualBasis_structure_height e hH hc) l hl (hlp.trans (Real.exp_le_exp.mpr hp2))
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hdata
  have hfinal : (2 * p + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbound p hp
  have hzero : (0 : ι → ℚ) ∈ denominatorGrid l := ⟨0, by intro i; simp⟩
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_, ?_⟩
  · intro z hb ht
    have hz := (rationalDualBasis_grid_iff e l z.coord).mpr ⟨hb, ht⟩
    have hconst : (rationalDualBasis e).equivFun (dualConstantHom (dualBaseHom z)).coord ∈
        denominatorGrid l := by
      apply (rationalDualBasis_grid_iff e l _).mpr
      change e.equivFun (dualBaseLinear (dualConstantLie (dualBaseLinear z.coord))) ∈ _ ∧
        e.equivFun (dualTangentLinear (dualConstantLie (dualBaseLinear z.coord))) ∈ _
      simpa only [dualBaseLinear_constant, dualTangentLinear_constant, map_zero] using And.intro hb hzero
    have hinv : (rationalDualBasis e).equivFun ((dualConstantHom (dualBaseHom z))⁻¹).coord ∈
        denominatorGrid l := by
      simpa only [coord_inv, map_neg] using denominatorGrid_neg l hconst
    have hinputs : ∀ r ∈ [z, (dualConstantHom (dualBaseHom z))⁻¹],
        (rationalDualBasis e).equivFun r.coord ∈ denominatorGrid l := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hz
      · exact hinv
    have hout := (rationalDualBasis_grid_iff e m _).mp
      (hprod [z, (dualConstantHom (dualBaseHom z))⁻¹] (by simp) hinputs)
    simpa only [List.prod_cons, List.prod_nil, mul_one, dualLogDerivative] using hout.2
  · intro g x hg hx
    have hleft : (rationalDualBasis e).equivFun (dualConstantHom g).coord ∈ denominatorGrid l := by
      apply (rationalDualBasis_grid_iff e l _).mpr
      change e.equivFun (dualBaseLinear (dualConstantLie g.coord)) ∈ _ ∧
        e.equivFun (dualTangentLinear (dualConstantLie g.coord)) ∈ _
      simpa only [dualBaseLinear_constant, dualTangentLinear_constant, map_zero] using And.intro hg hzero
    have hmiddle : (rationalDualBasis e).equivFun (dualTangentElement (hnil := hnil) x).coord ∈
        denominatorGrid l := by
      apply (rationalDualBasis_grid_iff e l _).mpr
      change e.equivFun (dualBaseLinear (dualInfinitesimal x)) ∈ _ ∧
        e.equivFun (dualTangentLinear (dualInfinitesimal x)) ∈ _
      simpa only [dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal, map_zero] using And.intro hzero hx
    have hright : (rationalDualBasis e).equivFun ((dualConstantHom g)⁻¹).coord ∈ denominatorGrid l := by
      simpa only [coord_inv, map_neg] using denominatorGrid_neg l hleft
    have hinputs : ∀ r ∈ [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹],
        (rationalDualBasis e).equivFun r.coord ∈ denominatorGrid l := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hleft
      · exact hmiddle
      · exact hright
    have hout := (rationalDualBasis_grid_iff e m _).mp
      (hprod [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹] (by simp) hinputs)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← mul_assoc, dualAdjoint] using hout.2

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_real_dual_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      1 ≤ H → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ z : DualGroup (realification_lowerCentralSeries_eq_bot hnil),
          (e.baseChange ℝ).equivFun (dualBaseLinear z.coord) ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (dualTangentLinear z.coord) ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (dualLogDerivative z) ∈ realDenominatorGrid m) ∧
        (∀ (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
          (x : ℝ ⊗[ℚ] L),
          (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (dualAdjoint g x) ∈ realDenominatorGrid m) := by
  have hratExists := exists_rational_dual_operation_grid s
  obtain ⟨C, hC, hrat⟩ := hratExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hH hp hd hHp hc l hl hlp
  have hdata := hrat e H p hnil hH hp hd hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  exact ⟨m, hm, hmp, hlm, real_dual_log_grid_of_rational e l m hl hlog,
    real_dual_adjoint_grid_of_rational e l m hl had⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedGradedPolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem shiftedGradedPolynomial_zero (p : F.adaptedLieSubalgebra w) :
    F.shiftedGradedPolynomial b ω hlayers w 0 p.val =
      F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolMap w p) := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  apply Finsupp.ext
  intro i
  rw [F.shiftedGradedPolynomial_coefficient, Nat.add_zero, F.gradedPieceProjection_coordinate]
  by_cases hd : Finsupp.weight w α = ω i
  · rw [if_pos hd.symm]
    exact ((F.gradedSymbolPolynomial_coefficient b ω hlayers w (F.polynomialSymbolMap w p)
      ⟨(α, i), hd⟩).trans (F.polynomialSymbolBasis_repr_map b ω hlayers w p ⟨(α, i), hd⟩)).symm
  · rw [if_neg (Ne.symm hd)]
    exact (F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ α i hd).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem polynomialLayer_eq_coefficientSubmodule {s : ℕ} (F : NilpotentLieFiltration L s) (j : ℕ) :
    (F.polynomialFiltration (σ := σ)).layer j = coefficientSubmodule (F.layer j) := by
  ext P
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem gradedSymbolPolynomial_filteredMap_coefficient (x : F.PolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (G.gradedSymbolPolynomial f ν hG w (F.filteredPolynomialSymbolMap G φ hφ w x)) α =
      F.associatedGradedMap G φ hφ (coefficients (F.gradedSymbolPolynomial e ω hF w x) α) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.filteredPolynomialSymbolMap_symbol, G.gradedSymbolPolynomial_coefficient_symbol,
    F.gradedSymbolPolynomial_coefficient_symbol, F.associatedGradedMap_piece]
  congr 1
  apply Subtype.ext
  exact F.filteredPolynomialMap_coefficient G φ hφ w p α

theorem gradedSymbolPolynomial_filteredMap (x : F.PolynomialSymbol w) :
    G.gradedSymbolPolynomial f ν hG w (F.filteredPolynomialSymbolMap G φ hφ w x) =
      VectorPolynomial.map (F.associatedGradedMap G φ hφ).toLinearMap
        (F.gradedSymbolPolynomial e ω hF w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α

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
open scoped BigOperators

theorem monomialScale_const_mul {σ : Type*} (S : σ → ℝ) (c : ℝ) (α : σ →₀ ℕ) :
    monomialScale (fun i => c * S i) α =
      c ^ Finsupp.weight (fun _ => 1) α * monomialScale S α := by
  classical
  simp only [monomialScale, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_one]

theorem monomialScale_le_exp_mul {σ : Type*} (S T : σ → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) {q : ℝ} (hq : 0 ≤ q)
    (hST : ∀ i, T i ≤ Real.exp q * S i) (α : σ →₀ ℕ) {s : ℕ}
    (hα : Finsupp.weight (fun _ => 1) α ≤ s) :
    monomialScale T α ≤ Real.exp ((s : ℝ) * q) * monomialScale S α := by
  classical
  calc
    monomialScale T α ≤ monomialScale (fun i => Real.exp q * S i) α := by
      apply Finset.prod_le_prod
      · intro i _
        exact pow_nonneg (hT i).le _
      · intro i _
        exact pow_le_pow_left₀ (hT i).le (hST i) _
    _ = Real.exp q ^ Finsupp.weight (fun _ => 1) α * monomialScale S α :=
      monomialScale_const_mul S (Real.exp q) α
    _ ≤ Real.exp q ^ s * monomialScale S α :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Real.one_le_exp hq) hα)
        (monomialScale_pos S hS α).le
    _ = Real.exp ((s : ℝ) * q) * monomialScale S α := by rw [Real.exp_nat_mul]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolSlowBound_rescale (S T : σ → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    {p q : ℝ} (hq : 0 ≤ q) (hST : ∀ i, Real.exp (-q) * T i ≤ S i)
    (E : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ => 1) S (Real.exp p) E) :
    F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp (p + (s : ℝ) * q)) E := by
  have hratio (i : σ) : T i ≤ Real.exp q * S i := by
    calc
      T i = Real.exp q * (Real.exp (-q) * T i) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp q * S i := mul_le_mul_of_nonneg_left (hST i) (Real.exp_pos _).le
  intro z
  apply (hE z).trans
  apply (div_le_div_iff₀ (monomialScale_pos S hS z.val.1)
    (monomialScale_pos T hT z.val.1)).mpr
  have hscale := monomialScale_le_exp_mul S T hS hT hq hratio z.val.1
    (z.property.le.trans (F.adaptedBasis_weight_le_step b ω hF z.val.2))
  calc
    Real.exp p * monomialScale T z.val.1 ≤
        Real.exp p * (Real.exp ((s : ℝ) * q) * monomialScale S z.val.1) :=
      mul_le_mul_of_nonneg_left hscale (Real.exp_pos _).le
    _ = Real.exp (p + (s : ℝ) * q) * monomialScale S z.val.1 := by
      rw [Real.exp_add, mul_assoc]

theorem ControlledSymbolFactorization.rescale {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η S X p)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    (hq : 0 ≤ q) (hST : ∀ i, Real.exp (-q) * T i ≤ S i) :
    F.ControlledSymbolFactorization b ω hF η T X (p + (s : ℝ) * q) := by
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hh, hη, hP⟩ := h
  have hpq : p ≤ p + (s : ℝ) * q := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) hq)
  exact ⟨m, E, P, R, W, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    F.symbolSlowBound_rescale b ω hF S T hS hT hq hST E hE,
    hR, hv, hW, (fun i j => (hh i j).trans hpq), hη, hP⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem ControlledSymbolFactorization.exists_in {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η T X p) :
    ∃ (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded) (u : ι → F.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule ∧
      (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p) ∧
      (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
        F.gradedFrequency b ω hF η x = 0) ∧
      F.SymbolFactorizationIn b ω hF T X p l W := by
  obtain ⟨l, E, P, R, W, u, hl, hlp, hprod, hE, hR, hu, hW, hh, hη, hP⟩ := h
  exact ⟨l, W, u, hl, hlp, hu, hW, hh, hη, E, P, R, hprod, hE, hR, hP⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem SymbolFactorizationIn.exists_fast_factors {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.SymbolFactorizationIn b ω hF T X p l W) :
    ∃ E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      E * P * R = X ∧ F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
      F.SymbolFastIn (fun _ => 1) (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W) P := h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSquareSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

variable (F : NilpotentLieFiltration L (s + 1))

theorem quotientTopGradedMap_piece_eq_zero_iff (j : ℕ) (hj : j ≤ s) (x : F.layer j) :
    F.quotientTopGradedMap (F.associatedGradedPieceMap j x) = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  have hle : (F.layerIdeal (s + 1)).toSubmodule ≤ F.layer (j + 1) :=
    F.antitone (Nat.add_le_add_right hj 1)
  have h := F.quotientGradedMap_piece_eq_zero_iff (F.layerIdeal (s + 1)) (t := s) le_rfl j x
  rw [sup_eq_left.mpr hle] at h
  convert h using 1
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareGradedRelativePiece (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTopGradedMap.toLinearMap.comp (F.squareGradedRelativePiece j hj)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem squareLattice_eq_pair_comap (Γ : Subgroup F.Group) :
    F.squareLattice Γ =
      (piBCHSubgroup (fun _ : Bool => F) (fun _ => Γ)).comap
        (map (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
          (hM := (pi (fun _ : Bool => F)).lowerCentralSeries_eq_bot) F.squarePairMap) := by
  ext g
  rw [F.mem_squareLattice, Subgroup.mem_comap, mem_piBCHSubgroup]
  constructor
  · intro h i
    cases i
    · exact h.2
    · exact h.1
  · intro h
    exact ⟨h true, h false⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem reducedSquareSnd_basis_height
    (a : ReducedSquareBasisIndex s ω) (b : QuotientTopBasisIndex s ω) :
    RationalHeightLE ((F.quotientTopBasis e ω hF).repr
      (F.reducedSquareSnd (F.reducedSquareBasis e ω hF a)) b) 1 := by
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareSnd_mk, F.quotientTopBasis_repr_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl i =>
    change RationalHeightLE (e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inl i)).val.2) b.val) 1
    rw [F.adaptedSquareBasis_inl]
    exact basis_repr_height_one e i b.val
  | inr i =>
    change RationalHeightLE (e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inr i)).val.2) b.val) 1
    rw [F.adaptedSquareBasis_inr, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def quotientTopSymbolBasis :
    Basis (QuotientTopSymbolIndex s w ω) ℚ (F.quotientTop.PolynomialSymbol w) :=
  F.quotientTop.polynomialSymbolBasis (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedSquareBasis_structure_bound (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : 2 * (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (i j k : ι ⊕ {i // 2 ≤ w i}) :
    rationalLogHeight (lieStructureConstants (F.adaptedSquareBasis b w h) i j k) ≤
      (p + 2) ^ 11 := by
  classical
  have hB (i j) : RationalHeightLE
      (LinearMap.toMatrix (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
        F.squarePairMap.toLinearMap i j) H := by
    rw [LinearMap.toMatrix_apply]
    exact (F.adaptedSquareBasis_pairMap_height b w h i j).mono hH
  obtain ⟨_, _, _, hbr⟩ := exists_bounded_lie_embedding_retraction
    (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
    F.squarePairMap F.squarePairMap_injective hH
    (lie_pi_structure_height (fun _ : Bool => b) hH (fun _ => hc))
    hB
  apply rationalLogHeight_le_of_height (hbr i j k)
  apply rationalLieStructureHeight_inverse_budget _ _ _ hp
  · simpa only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ,
      Fintype.card_bool, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hd
  · exact (Nat.cast_le.mpr (card_squareBasis_index_le w)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)
  · exact hHp

theorem exists_adaptedSquareBasis_grid (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    (Γ : Subgroup F.Group) {l : ℕ} (hl : 0 < l)
    (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : 2 * (Fintype.card ι : ℝ) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (F.adaptedSquareBasis b w h) (F.squareLattice Γ) ∧
      bchSubgroupCoordinates (F.adaptedSquareBasis b w h) (F.squareLattice Γ) ⊆
        denominatorGrid N := by
  classical
  have hB (i j) : RationalHeightLE
      (LinearMap.toMatrix (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
        F.squarePairMap.toLinearMap i j) 1 := by
    rw [LinearMap.toMatrix_apply]
    exact F.adaptedSquareBasis_pairMap_height b w h i j
  rw [F.squareLattice_eq_pair_comap]
  apply exists_bchSubgroup_comap_grid_exp_bound
    (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
    F.squarePairMap F.squarePairMap_injective _ (H := 1) le_rfl hl
    hB
    (piBCHSubgroup_inner_grid (fun _ : Bool => F) (fun _ => b) (fun _ => Γ) l
      (fun _ => hin))
    (piBCHSubgroup_outer_grid (fun _ : Bool => F) (fun _ => b) (fun _ => Γ) l
      (fun _ => hout)) hp
  · simpa only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ,
      Fintype.card_bool, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hd
  · exact (Nat.cast_le.mpr (card_squareBasis_index_le w)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · exact hlp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedRealifiedSquareOrbit
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem squareLayer_eq_ker_constraint (j : ℕ) :
    F.squareFiltration.layer j = LinearMap.ker (F.squareLayerConstraint j) := by
  ext x
  rw [F.mem_squareFiltration_layer, F.mem_squareLayer_iff_second_and_difference]
  change (x.val.2 ∈ F.layer j ∧ x.val.1 - x.val.2 ∈ F.layer (j + 1)) ↔
    ((F.layer j).mkQ x.val.2, (F.layer (j + 1)).mkQ (x.val.1 - x.val.2)) = 0
  simp only [Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem realifiedSquareEquiv_mem_layer (j : ℕ) (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    x ∈ F.squareFiltration.realification.layer j ↔
      F.realifiedSquareEquiv x ∈ F.realification.squareFiltration.layer j := by
  change x ∈ (F.squareFiltration.layer j).baseChange ℝ ↔ _
  rw [F.squareLayer_eq_ker_constraint, realification_ker, LinearMap.mem_ker,
    F.realification.mem_squareFiltration_layer,
    F.realification.mem_squareLayer_iff_second_and_difference]
  change (F.squareLayerConstraint j).baseChange ℝ x = 0 ↔
    F.realification.squareSnd (F.realifiedSquareEquiv x) ∈ F.realification.layer j ∧
      F.realification.squareFst (F.realifiedSquareEquiv x) -
        F.realification.squareSnd (F.realifiedSquareEquiv x) ∈ F.realification.layer (j + 1)
  rw [F.realifiedSquareEquiv_snd, F.realifiedSquareEquiv_fst]
  simp only [squareLayerConstraint, realification_prod_eq_zero_iff,
    LinearMap.baseChange_comp, LinearMap.comp_apply, realification_mkQ_eq_zero_iff,
    LinearMap.baseChange_sub, LinearMap.sub_apply]
  rfl

theorem realifiedSquareEquiv_symm_mem_layer (j : ℕ) (x : F.realification.squareLieSubalgebra) :
    F.realifiedSquareEquiv.symm x ∈ F.squareFiltration.realification.layer j ↔
      x ∈ F.realification.squareFiltration.layer j := by
  rw [F.realifiedSquareEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareObservable_mk (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (g : F.squareFiltration.realification.Group) :
    F.realSquareObservable Γ ε u (QuotientGroup.mk g) =
      F.realification.squareObservable (Γ.map realificationHom) ε u
        (QuotientGroup.mk (F.realifiedSquareGroupEquiv g)) := by
  rw [F.realification.squareObservable_mk, F.realifiedSquareGroupEquiv_fst,
    F.realifiedSquareGroupEquiv_snd]
  rfl

theorem realSquareObservable_top_invariant (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup s, ∀ x, u (z • x) = character (χ z) * u x)
    (k : F.squareFiltration.realification.Group) (hk : k ∈ F.squareFiltration.realification.subgroup s)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) :
    F.realSquareObservable Γ ε u (k • x) = F.realSquareObservable Γ ε u x := by
  induction x using Quotient.inductionOn with
  | h g =>
    change F.realSquareObservable Γ ε u (QuotientGroup.mk (k * g)) = _
    rw [F.realSquareObservable_mk, F.realSquareObservable_mk, map_mul]
    exact F.realification.squareObservable_top_invariant _ ε u χ hu
      (F.realifiedSquareGroupEquiv k) ((F.realifiedSquareEquiv_mem_layer s k.coord).mp hk)
      (QuotientGroup.mk (F.realifiedSquareGroupEquiv g))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]

theorem exists_lipschitz_realSquare_descent
    (b : Basis ι ℚ F.squareLieSubalgebra)
    (c : Basis κ ℚ (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hin : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid l)
    (hout : bchSubgroupCoordinates c ((F.squareLattice Γ).map
      (F.squareFiltration.quotientStepHom (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)) ⊆
        denominatorGrid m)
    (he : ∀ i j, RationalHeightLE
      (c.repr (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (b j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants c i j k) H)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (A B : ℝ≥0)
    (hLip : letI := realificationQuotientMetricSpace b (F.squareLattice Γ) l hl hin
      LipschitzWith A (F.realSquareObservable Γ ε u))
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let I := F.squareFiltration.layerIdeal (s + 1)
    let Δ := (F.squareLattice Γ).map (F.squareFiltration.quotientStepHom I (t := s) le_rfl)
    letI := realificationQuotientMetricSpace c Δ m hm hout
    ∃ v : F.squareFiltration.quotientTop.realification.Group ⧸ Δ.map realificationHom → ℂ,
      (∀ g, v (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom I (t := s) le_rfl g)) =
        F.realSquareObservable Γ ε u (QuotientGroup.mk g)) ∧
      LipschitzWith (rationalReconstructionLipschitzBound s (Fintype.card ι) (Fintype.card κ) H A (B ^ 2)) v ∧
      ∀ x, ‖v x‖ ≤ (B : ℝ) ^ 2 := by
  dsimp only
  refine exists_lipschitz_realification_reconstruction b c
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))) (lieQuotientMap_surjective _)
    (F.squareLattice Γ) _ le_rfl l m H hl hm hH hin hout he hc
    (F.realSquareObservable Γ ε u) ?_ A (B ^ 2) hLip ?_
  · intro k hk x
    exact F.realSquareObservable_top_invariant Γ ε u χ hu k
      ((F.squareFiltration.mem_realQuotientStepHom_ker _ le_rfl k).mp hk)
      (QuotientGroup.mk x)
  · simpa only [NNReal.coe_pow] using F.realSquareObservable_norm_le Γ ε u B.coe_nonneg hb

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem squareObservable_recovers_product (ε γ a b : F.Group) (hγ : γ ∈ Γ)
    (u : F.Group ⧸ Γ → ℂ) (q : F.squareFiltration.Group)
    (hfst : F.squareFstHom q = ε⁻¹ * a * γ⁻¹) (hsnd : F.squareSndHom q = b) :
    F.squareObservable Γ ε u (QuotientGroup.mk q) =
      u (QuotientGroup.mk a) * star (u (QuotientGroup.mk b)) := by
  rw [F.squareObservable_mk, hfst, hsnd]
  have heq : (QuotientGroup.mk (ε * (ε⁻¹ * a * γ⁻¹)) : F.Group ⧸ Γ) = QuotientGroup.mk a := by
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, inv_inv, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_assoc, inv_mul_cancel, mul_one] using hγ
  rw [heq]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareObservable_recovers_product (ε γ a b : F.realification.Group)
    (hγ : γ ∈ Γ.map realificationHom)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (q : F.squareFiltration.realification.Group)
    (hfst : F.realSquareFstHom q = ε⁻¹ * a * γ⁻¹) (hsnd : F.realSquareSndHom q = b) :
    F.realSquareObservable Γ ε u (QuotientGroup.mk q) =
      u (QuotientGroup.mk a) * star (u (QuotientGroup.mk b)) := by
  rw [F.realSquareObservable_mk]
  exact F.realification.squareObservable_recovers_product (Γ.map realificationHom)
    ε γ a b hγ u (F.realifiedSquareGroupEquiv q)
    ((F.realifiedSquareGroupEquiv_fst q).trans hfst)
    ((F.realifiedSquareGroupEquiv_snd q).trans hsnd)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCentralSeed
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

theorem realify_basisFrequency_direction {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (hN : 0 < N) (n : S → ℤ) (j : S) :
    realifyFunctional (basisFrequency b S N n) ((N : ℝ) • b.baseChange ℝ j) = n j := by
  simp only [map_smul, Basis.baseChange_apply, realifyFunctional_tmul,
    basisFrequency_basis, one_mul, smul_eq_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  exact mul_div_cancel₀ _ (by exact_mod_cast hN.ne')

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientImage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def firstCoefficientBasis (w : σ → ℕ) :
    Basis (FirstCoefficientIndex w ω) ℚ (F.FirstCoefficientModule w) :=
  (supportedQuotientBasis (F.shiftedMonomialBasis b ω hF w 1)
    ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
      (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype)
    {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
    (F.shiftedPolynomial_next_eq_span b ω hF w 1)).reindex (firstCoefficientSurvivorEquiv w ω)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDerivativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_integral_coordinate
    (f : L →ₗ[ℚ] ℝ) (p : VectorPolynomial σ ℚ L) (l : ℕ)
    (hp : ∀ β, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * f (coefficients p β))
    (h : σ → ℤ) (α : σ →₀ ℕ) :
    ∃ z : ℤ, (z : ℝ) = (l : ℝ) *
      f (coefficients (directionalDerivative (fun i => (h i : ℚ)) p) α) := by
  classical
  let z : σ → ℤ := fun i => Classical.choose (hp (α + Finsupp.single i 1))
  have hz (i : σ) : (z i : ℝ) = (l : ℝ) * f (coefficients p (α + Finsupp.single i 1)) :=
    Classical.choose_spec (hp (α + Finsupp.single i 1))
  refine ⟨∑ i, h i * (α i + 1 : ℤ) * z i, ?_⟩
  rw [directionalDerivative_coordinate, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, Rat.cast_intCast]
  apply Finset.sum_congr rfl
  intro i _
  rw [hz]
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem realAdaptedDirectionalDerivative_polynomial
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialMap (fun _ => 1) (F.realAdaptedDirectionalDerivative h x) =
      directionalDerivative h (F.realAdaptedPolynomialMap (fun _ => 1) x) := by
  apply coefficients.injective
  ext α
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      ((F.adaptedDirectionalDerivative h).baseChange ℝ (r ⊗ₜ[ℚ] p))) α = _
    rw [LinearMap.baseChange_tmul, F.realAdaptedPolynomialMap_coefficient_tmul,
      F.adaptedDirectionalDerivative_coe, coefficients_directionalDerivative,
      coefficients_directionalDerivative]
    simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      F.realAdaptedPolynomialMap_coefficient_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem realAdaptedDirectionalDerivative_tensor
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialTensor (fun _ => 1) (F.realAdaptedDirectionalDerivative h x) =
      F.realification.adaptedDirectionalDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) x) := by
  apply Subtype.ext
  exact F.realAdaptedDirectionalDerivative_polynomial h x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
  (b : Basis ι ℚ L)

section Lie

variable {A : Type*} [LieRing A] [LieAlgebra ℚ A] (e : Basis ι ℚ A)

noncomputable def heightBoundedLieSubalgebras (m H : ℕ) : Set (LieSubalgebra ℚ A) :=
  {K | K.toSubmodule ∈ heightBoundedSubspaces e m H}

theorem finite_card_heightBoundedLieSubalgebras (m H : ℕ) :
    (heightBoundedLieSubalgebras e m H).Finite ∧
      (heightBoundedLieSubalgebras e m H).ncard ≤
        ((2 * H + 1) * (H + 1)) ^ (m * Fintype.card ι) := by
  classical
  obtain ⟨hfin, hcard⟩ := finite_card_heightBoundedSubspaces e m H
  let f : heightBoundedLieSubalgebras e m H → heightBoundedSubspaces e m H :=
    fun K => ⟨K.val.toSubmodule, K.property⟩
  have hf : Function.Injective f := by
    intro K J h
    exact Subtype.ext (LieSubalgebra.toSubmodule_injective (congrArg Subtype.val h))
  let : Fintype (heightBoundedSubspaces e m H) := hfin.fintype
  let : Finite (heightBoundedLieSubalgebras e m H) := Finite.of_injective f hf
  have hc := Nat.card_le_card_of_injective f hf
  refine ⟨Set.toFinite _, ?_⟩
  exact (show (heightBoundedLieSubalgebras e m H).ncard ≤ (heightBoundedSubspaces e m H).ncard by
    simpa only [Nat.card_coe_set_eq] using hc).trans hcard

end Lie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalConstraintCountBudget
namespace OAI

section

namespace Erdos3

open Module

theorem heightBoundedLieSubalgebras_ncard_exp_bound
    {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).ncard : ℝ) ≤
      Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
  have hc := (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).2
  have he := rational_log_height_count_exp_bound (m * Fintype.card ι) hA
  have hr := (Nat.cast_le.mpr hc).trans he
  simpa only [Nat.cast_mul, mul_assoc] using hr

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

theorem bracket_mem_subalgebra_sup_layer_succ (U : LieSubalgebra ℚ L)
    {j : ℕ} (hj : 1 ≤ j) {a b : L}
    (ha : a ∈ U.toSubmodule ⊔ F.layer j) (hb : b ∈ U.toSubmodule ⊔ F.layer j) :
    ⁅a, b⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
  obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨v, hv, y, hy, rfl⟩ := Submodule.mem_sup.mp hb
  have hu1 : u ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hv1 : v ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have huv : ⁅u, v⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer (j + 1)) (U.lie_mem hu hv)
  have huy : ⁅u, y⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
    apply (le_sup_right : F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer (j + 1))
    simpa only [Nat.add_comm 1 j] using F.lie_mem hu1 hy
  have hxv : ⁅x, v⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_right : F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer (j + 1)) (F.lie_mem hx hv1)
  have hxy : ⁅x, y⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_right : F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer (j + 1))
      (F.antitone (by omega : j + 1 ≤ j + j) (F.lie_mem hx hy))
  rw [add_lie, lie_add, lie_add]
  exact Submodule.add_mem _ (Submodule.add_mem _ huv huy) (Submodule.add_mem _ hxv hxy)

theorem bch_triple_remainder_mem_subalgebra_sup_layer (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) {j : ℕ} (hj : 1 ≤ j) (a b c : L)
    (ha : a ∈ U.toSubmodule ⊔ F.layer j)
    (hb : b ∈ U.toSubmodule ⊔ F.layer j)
    (hc : c ∈ U.toSubmodule ⊔ F.layer j) :
    lieBCH s (lieBCH s a b) c - (a + b + c) ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
  lieBCH_triple_sub_sum_mem_submodule hs _ _
    (sup_le_sup_left (F.antitone (Nat.le_succ j)) _)
    (fun _ hx _ hy => F.bracket_mem_subalgebra_sup_layer_succ U hj hx hy) a b c ha hb hc

theorem outer_sum_mem_subalgebra_sup_layer (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) {j : ℕ} (hj : 1 ≤ j) (a d p p' : L)
    (ha : a ∈ U.toSubmodule ⊔ F.layer j)
    (hd : d ∈ U.toSubmodule ⊔ F.layer j)
    (hp : p ∈ U) (hp' : p' ∈ U)
    (heq : p = lieBCH s (lieBCH s a p') d) :
    a + d ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
  have hrem := F.bch_triple_remainder_mem_subalgebra_sup_layer hs U hj a p' d ha
    ((le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer j) hp') hd
  rw [← heq] at hrem
  have hpW : p ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer (j + 1)) hp
  have hp'W : p' ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer (j + 1)) hp'
  convert Submodule.sub_mem _ (Submodule.sub_mem _ hpW hp'W) hrem using 1
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem outer_factors_mem_of_separation (U : LieSubalgebra ℚ L)
    (A D P P' : F.Group) (hP : P.coord ∈ U) (hP' : P'.coord ∈ U)
    (hidentity : P = A * P' * D)
    (hseparate : ∀ j : ℕ, 1 ≤ j → j ≤ s →
      A.coord + D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      A.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧
        D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    A.coord ∈ U ∧ D.coord ∈ U := by
  have hind : ∀ n : ℕ, n ≤ s →
      A.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) ∧
        D.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.zero_add, F.one_eq_top, sup_top_eq]
      exact ⟨Submodule.mem_top, Submodule.mem_top⟩
    | succ n ih =>
      intro hn
      obtain ⟨ha, hd⟩ := ih (by omega)
      apply hseparate (n + 1) (by omega) hn
      apply F.outer_sum_mem_subalgebra_sup_layer (by omega) U (by omega)
        A.coord D.coord P.coord P'.coord ha hd hP hP'
      exact congrArg NilpotentLieBCHGroup.coord hidentity
  change A.coord ∈ U.toSubmodule ∧ D.coord ∈ U.toSubmodule
  simpa only [F.terminal, sup_bot_eq] using hind s le_rfl

theorem comparison_middle_identity (E P R E' P' R' : F.Group)
    (h : E * P * R = E' * P' * R') :
    P = (E⁻¹ * E') * P' * (R' * R⁻¹) := by
  have heq := congrArg (fun x : F.Group => E⁻¹ * x * R⁻¹) h
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using heq

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem controlled_outer_factors_mem (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (A D P P' : F.realification.Group)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP' : P'.coord ∈ realificationLieSubalgebra U)
    (hidentity : P = A * P' * D)
    (ha : ‖(e.baseChange ℝ).equivFun A.coord‖ ≤ Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hd : (e.baseChange ℝ).equivFun D.coord ∈ realDenominatorGrid l) :
    A.coord ∈ realificationLieSubalgebra U ∧ D.coord ∈ realificationLieSubalgebra U := by
  let W := realLieSubalgebraOverRat (realificationLieSubalgebra U)
  change A.coord ∈ W ∧ D.coord ∈ W
  apply F.realification.outer_factors_mem_of_separation W A D P P' hP hP' hidentity
  intro j _ _ hsum
  let M : Matrix ι (κ ⊕ ι) ℚ := fun i z => e.repr (subalgebraLayerFamily e v ω (j + 1) z) i
  have hM : ∀ i z, RationalHeightLE (M i z) H :=
    fun i z => subalgebraLayerFamily_height e v ω (j + 1) hH hv z i
  have hcols : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hsum' : (e.baseChange ℝ).equivFun A.coord + (e.baseChange ℝ).equivFun D.coord ∈
      Submodule.span ℝ (Set.range (fun z i => (M i z : ℝ))) := by
    rw [← map_add]
    exact (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan (j + 1) _).mp hsum
  obtain ⟨ha', hd'⟩ := controlled_small_vector_separation M hH hl hM (by linarith)
    (hι.trans (by linarith)) hcols
    (hHp.trans (Real.exp_le_exp.mpr (by linarith)))
    (hlp.trans (Real.exp_le_exp.mpr (by linarith))) _ _ ha hd hsum'
  exact ⟨(F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan (j + 1) _).mpr ha',
    (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan (j + 1) _).mpr hd'⟩

theorem controlled_compatible_factors_mem (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (E P R E' P' R' : F.realification.Group)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP' : P'.coord ∈ realificationLieSubalgebra U)
    (hidentity : E * P * R = E' * P' * R')
    (ha : ‖(e.baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hd : (e.baseChange ℝ).equivFun (R' * R⁻¹).coord ∈ realDenominatorGrid l) :
    (E⁻¹ * E').coord ∈ realificationLieSubalgebra U ∧
      (R' * R⁻¹).coord ∈ realificationLieSubalgebra U :=
  F.controlled_outer_factors_mem e ω hlayers U v hspan hH hl hv hp hι hκ hHp hlp
    (E⁻¹ * E') (R' * R⁻¹) P P' hP hP'
    (F.realification.comparison_middle_identity E P R E' P' R' hidentity) ha hd

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_symbol_comparison (s a : ℕ) :
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
      ∀ E P R E' P' R' : F.RealPolynomialSymbolGroup w,
      P.coord ∈ realificationLieSubalgebra U → P'.coord ∈ realificationLieSubalgebra U →
      E * P * R = E' * P' * R' →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E' →
      F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R' →
      (E⁻¹ * E').coord ∈ realificationLieSubalgebra U ∧
        (R' * R⁻¹).coord ∈ realificationLieSubalgebra U := by
  obtain ⟨cs, _, hslow⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨cr, _, hrat⟩ := exists_symbol_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) +
    (Polynomial.X + Polynomial.C cs) ^ cs + (Polynomial.X + Polynomial.C cr) ^ cr + Polynomial.X + 2
  let B : Polynomial ℕ := (2 * Q + 2) ^ 48 + (2 * Q + 2) ^ 24 + 2 * Q + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
    T hT E P R E' P' R' hP hP' heq hE hE' hR hR'
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
  exact (F.polynomialSymbolFiltration w).controlled_compatible_factors_mem
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) U v hspan hH hm hv hq hdim (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hmp.trans (Real.exp_le_exp.mpr hrq))
    E P R E' P' R' hP hP' heq hAnorm hDgrid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_bounded_symbol_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF w).repr (v i) z) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
        ∀ E₀ P₀ R₀ E P R : F.RealPolynomialSymbolGroup w,
          P₀.coord ∈ realificationLieSubalgebra U → P.coord ∈ realificationLieSubalgebra U →
          E₀ * P₀ * R₀ = E * P * R →
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E₀ →
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
          F.SymbolRationalGrid b ω hF w l R₀ → F.SymbolRationalGrid b ω hF w l R →
          (E₀⁻¹ * E).coord ∈ realificationLieSubalgebra U ∧
          (R * R₀⁻¹).coord ∈ realificationLieSubalgebra U ∧
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + C) ^ C)) (E₀⁻¹ * E) ∧
          F.SymbolRationalGrid b ω hF w m (R * R₀⁻¹) := by
  have hcompExists := exists_controlled_symbol_comparison s a
  obtain ⟨cc, _, hcomp⟩ := hcompExists
  have hslowExists := exists_symbol_slow_product_bound s a 2
  obtain ⟨cs, _, hslow⟩ := hslowExists
  have hratExists := exists_symbol_rational_product_bound s 2
  obtain ⟨cr, _, hrat⟩ := hratExists
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C cc) ^ cc +
    (Polynomial.X + Polynomial.C cs) ^ cs + (Polynomial.X + Polynomial.C cr) ^ cr
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
  have hsum : (p + cc) ^ cc + (p + cs) ^ cs + (p + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbound p hp
  have hc0 : 0 ≤ (p + cc) ^ cc := by positivity
  have hs0 : 0 ≤ (p + cs) ^ cs := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hcb : (p + cc) ^ cc ≤ (p + C) ^ C := by linarith
  have hsb : (p + cs) ^ cs ≤ (p + C) ^ C := by linarith
  have hrb : (p + cr) ^ cr ≤ (p + C) ^ C := by linarith
  have hproductsExists := hrat F b ω hF w hw H p hH hp hι hσ hHp hb l hl hlp
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hproductsExists
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrb), hlm, ?_⟩
  intro T hT E₀ P₀ R₀ E P R hP₀ hP heq hE₀ hE hR₀ hR
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hmem := hcomp F b ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
    T (fun i => (Real.exp_le_exp.mpr hcb).trans (hT i)) E₀ P₀ R₀ E P R
    hP₀ hP heq hE₀ hE hR₀ hR
  refine ⟨hmem.1, hmem.2, ?_, ?_⟩
  · have hinputs : ∀ x ∈ [E₀⁻¹, E], F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hF w T _ E₀).mpr hE₀
      · exact hE
    have hpair : F.SymbolSlowBound b ω hF w T (Real.exp ((p + cs) ^ cs)) (E₀⁻¹ * E) := by
      simpa only [List.prod_cons, List.prod_nil, mul_one] using
        hslow F b ω hF w hw H p hH hp hι hσ hHp hb T hTpos [E₀⁻¹, E] (by simp) hinputs
    exact F.symbolSlowBound_mono b ω hF w T hTpos (Real.exp_le_exp.mpr hsb) _ hpair
  · have hinputs : ∀ x ∈ [R, R₀⁻¹], F.SymbolRationalGrid b ω hF w l x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hR
      · exact F.symbolRationalGrid_inv b ω hF w l hR₀
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hproducts [R, R₀⁻¹] (by simp) hinputs

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonIntegralModelEquivalences
namespace OAI

section

namespace Erdos3

open Module

variable {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty) (K : α → LieSubalgebra ℚ L)

include hS in
theorem exists_common_height_bounded_subalgebra (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ a ∈ S, K a ∈ heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-(3 * (m : ℝ) * Fintype.card ι * (A + 2))) * S.card ≤ (T.card : ℝ) := by
  obtain ⟨U, _, T, hTS, hT, hU, hlarge⟩ := exists_exponential_constant_fiber S hS K
    (heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊)
    (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).1 hK
    (heightBoundedLieSubalgebras_ncard_exp_bound e m hA)
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀, fun a ha => (hU a ha).trans (hU a₀ ha₀).symm, hlarge⟩

include hS in
theorem exists_common_log_height_subalgebra (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ A) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-(3 * (m : ℝ) * Fintype.card ι * (A + 2))) * S.card ≤ (T.card : ℝ) := by
  apply exists_common_height_bounded_subalgebra e S hS K m hA
  intro a ha
  obtain ⟨v, hv, hh⟩ := hK a ha
  exact (mem_heightBoundedSubspaces e m ⌈Real.exp A⌉₊ (K a).toSubmodule).mpr
    ⟨v, hv, fun i j => rationalHeightLE_ceil_exp (hh i j)⟩

include hS in
theorem exists_common_fast_subalgebra (m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-((p + 2) ^ 5)) * S.card ≤ (T.card : ℝ) := by
  obtain ⟨a₀, ha₀, T, hTS, haT, hcommon, hlarge⟩ :=
    exists_common_log_height_subalgebra e S hS K m hp hK
  refine ⟨a₀, ha₀, T, hTS, haT, hcommon, ?_⟩
  apply le_trans _ hlarge
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (common_subalgebra_cost_le_budget m (Fintype.card ι) hp hm hd hp le_rfl)

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_common_fast_subalgebra_and_denominator
    {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty)
    (K : α → LieSubalgebra ℚ L) (n : α → ℕ) (m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p)
    (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, K a = K a₀ ∧ n a = n a₀) ∧
      Real.exp (-((p + 2) ^ 5 + p)) * S.card ≤ (T.card : ℝ) := by
  obtain ⟨b, _, U, hUS, hbU, hKsame, hUlarge⟩ :=
    exists_common_fast_subalgebra e S hS K m hp hm hd hK
  obtain ⟨a₀, haU, T, hTU, haT, hnsame, hTlarge⟩ :=
    exists_common_positive_nat U ⟨b, hbU⟩ n (fun a ha => hn a (hUS ha))
  refine ⟨a₀, hUS haU, T, hTU.trans hUS, haT, ?_, ?_⟩
  · intro a ha
    exact ⟨(hKsame a (hTU ha)).trans (hKsame a₀ haU).symm, hnsame a ha⟩
  · calc
      Real.exp (-((p + 2) ^ 5 + p)) * S.card =
          Real.exp (-p) * (Real.exp (-((p + 2) ^ 5)) * S.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-p) * U.card := mul_le_mul_of_nonneg_left hUlarge (Real.exp_pos _).le
      _ ≤ T.card := hTlarge

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem normalizedRelativeSubmodule_lie_mem (a p : F.adaptedLieSubalgebra w)
    (hp : p ∈ F.normalizedRelativeSubmodule w) :
    ⁅a, p⁆ ∈ F.normalizedRelativeSubmodule w := by
  refine ⟨(F.shiftedAdaptedIdeal w).lie_mem hp.1, ?_⟩
  change coefficients ⁅a.val, p.val⁆ 0 ∈ F.layer 2
  rw [← eval_zero_eq_coefficient]
  change evalLie (0 : σ → ℚ) ⁅a.val, p.val⁆ ∈ F.layer 2
  rw [LieHom.map_lie]
  apply (F.layerIdeal 2).lie_mem
  change eval (fun _ : σ => 0) p.val ∈ F.layer 2
  rw [eval_zero_eq_coefficient]
  exact hp.2

noncomputable def normalizedRelativeIdeal : LieIdeal ℚ (F.adaptedLieSubalgebra w) :=
  { F.normalizedRelativeSubmodule w with
    lie_mem := fun {a p} hp => F.normalizedRelativeSubmodule_lie_mem w a p hp }

theorem relativeSquareLift_lie (hw : ∀ i, 0 < w i)
    (a : F.adaptedLieSubalgebra w) (p : F.normalizedRelativeSubmodule w) :
    F.relativeSquareLift w hw ⟨⁅a, p.val⁆, F.normalizedRelativeSubmodule_lie_mem w a p.val p.property⟩ =
      ⁅F.squareDiagonalPolynomialMap w a, F.relativeSquareLift w hw p⁆ := by
  apply F.square_polynomial_ext w
  · rw [F.squareFstPolynomialMap_relative, LieHom.map_lie,
      F.squareFstPolynomialMap_diagonal, F.squareFstPolynomialMap_relative]
  · rw [F.squareSndPolynomialMap_relative, LieHom.map_lie,
      F.squareSndPolynomialMap_relative, lie_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSymbolDimensions
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hF hw in
theorem quotientTopSymbolIndex_finite : Finite (QuotientTopSymbolIndex s w ω) :=
  symbolBasisIndex_finite w (fun i : QuotientTopBasisIndex s ω => ω i.val) s hw
    (F.quotientTop.adaptedBasis_weight_le_step (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF))

include hF hw in
theorem quotientTopSymbolIndex_card_le [Fintype (QuotientTopSymbolIndex s w ω)] :
    Fintype.card (QuotientTopSymbolIndex s w ω) ≤
      Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  have h := symbolBasisIndex_card_le w (fun i : QuotientTopBasisIndex s ω => ω i.val) s hw
    (F.quotientTop.adaptedBasis_weight_le_step (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF))
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareRationalModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem exists_square_rational_model (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
    (Γ : Subgroup F.Group) {l H : ℕ} (hl : 0 < l) (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : 2 * (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (N : ℕ) (hN : 0 < N)
      (hinner : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (F.squareFinBasis b w (hlayers 2)) (F.squareLattice Γ))
      (houter : bchSubgroupCoordinates (F.squareFinBasis b w (hlayers 2))
        (F.squareLattice Γ) ⊆ denominatorGrid N),
      (F.squareFiltration.ofAdaptedBasis (F.squareFinBasis b w (hlayers 2))
        (squareFinWeight w) (F.squareFinBasis_layers b w hlayers)
        (F.squareLattice Γ) N hN hinner houter).GeometryComplexityLE ((p + 2) ^ 11) := by
  obtain ⟨N, hN, hNp, hinner, houter⟩ :=
    F.exists_adaptedSquareBasis_grid b w (hlayers 2) Γ hl hin hout hp hd hlp
  have hin' := bchSubgroup_inner_grid_reindex _ (Fintype.equivFin _) _ hinner
  have hout' := bchSubgroup_outer_grid_reindex _ (Fintype.equivFin _) _ houter
  refine ⟨N, hN, hin', hout', ?_⟩
  apply F.squareFiltration.ofAdaptedBasis_geometry _ _ _ _ _ _ hin' hout' (by positivity)
  · exact ((Nat.cast_le.mpr (card_squareBasis_index_le w)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)).trans
        (le_power_budget hp (by decide : 1 ≤ 11))
  · exact hNp.trans (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 9 ≤ 11)))
  · intro i j k
    change rationalLogHeight
      (lieStructureConstants (F.squareFinBasis b w (hlayers 2)) i j k) ≤ (p + 2) ^ 11
    rw [squareFinBasis, lieStructureConstants_reindex]
    exact F.adaptedSquareBasis_structure_bound b w (hlayers 2) hH hc hp hd hHp _ _ _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareStructureHeight
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : F.layer 2 = Submodule.span ℚ (e '' {i | 2 ≤ ω i}))

theorem adaptedSquareBasis_bracket_repr_inl (x y : F.squareLieSubalgebra) (k : ι) :
    (F.adaptedSquareBasis e ω hF).repr ⁅x, y⁆ (Sum.inl k) = e.repr ⁅x.val.2, y.val.2⁆ k := by
  change (F.squareBasis e _).repr ⁅x, y⁆ (Sum.inl k) = _
  rw [F.squareBasis_repr_inl]
  rfl

theorem adaptedSquareBasis_bracket_repr_inr (x y : F.squareLieSubalgebra) (k : {i // 2 ≤ ω i}) :
    (F.adaptedSquareBasis e ω hF).repr ⁅x, y⁆ (Sum.inr k) =
      e.repr (⁅x.val.1, y.val.1⁆ - ⁅x.val.2, y.val.2⁆) k.val := by
  change (F.squareBasis e _).repr ⁅x, y⁆ (Sum.inr k) = _
  rw [F.squareBasis_repr_inr, supportedSubmoduleBasis_repr]
  rfl

theorem adaptedSquareBasis_structure_height {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (a b k : ι ⊕ {i // 2 ≤ ω i}) :
    RationalHeightLE ((F.adaptedSquareBasis e ω hF).repr
      ⁅F.adaptedSquareBasis e ω hF a, F.adaptedSquareBasis e ω hF b⁆ k) H := by
  rcases a with i | i <;> rcases b with j | j <;> rcases k with k | k
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inl]
    exact hc i j k
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inl]
    simpa only [sub_self, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, sub_zero] using hc i j.val k.val
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inl]
    simpa only [zero_lie, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inl]
    simpa only [zero_lie, sub_zero] using hc i.val j k.val
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, sub_zero] using hc i.val j.val k.val

variable (F : NilpotentLieFiltration L (s + 1))

theorem reducedSquareBasis_structure_height
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    {H : ℕ} (hH : 1 ≤ H) (hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (a b k : ReducedSquareBasisIndex s ω) :
    RationalHeightLE ((F.reducedSquareBasis e ω hF).repr
      ⁅F.reducedSquareBasis e ω hF a, F.reducedSquareBasis e ω hF b⁆ k) H := by
  change RationalHeightLE (lieStructureConstants (F.reducedSquareBasis e ω hF) a b k) H
  have hspan : (F.squareFiltration.layerIdeal (s + 1)).toSubmodule = Submodule.span ℚ
      (F.adaptedSquareBasis e ω (hF 2) '' {i | s + 1 ≤ squareBasisWeight ω i}) :=
    F.adaptedSquareBasis_layers e ω hF (s + 1)
  have he : lieStructureConstants (F.reducedSquareBasis e ω hF) a b k =
      lieStructureConstants (F.adaptedSquareBasis e ω (hF 2)) a.val b.val k.val :=
    supportedQuotientBasis_lieStructure (F.adaptedSquareBasis e ω (hF 2))
      (F.squareFiltration.layerIdeal (s + 1)) {i | s + 1 ≤ squareBasisWeight ω i} hspan a b k
  rw [he]
  exact F.adaptedSquareBasis_structure_height e ω (hF 2) hH hc a.val b.val k.val

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateDerivativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_single_coordinate (f : L →ₗ[ℚ] ℝ)
    (p : VectorPolynomial σ ℚ L) (i : σ) (α : σ →₀ ℕ) :
    f (coefficients (directionalDerivative (Pi.single i 1) p) α) =
      (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1)) := by
  rw [directionalDerivative_coordinate]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem directionalDerivative_single_scaled_bound
    (f : L →ₗ[ℚ] ℝ) (p : VectorPolynomial σ ℚ L)
    (d : ℕ) (hdegree : ∀ (β : σ →₀ ℕ) (i : σ), d < β i → f (coefficients p β) = 0)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ β, |f (coefficients p β)| ≤ M / monomialScale T β) (i : σ) (α : σ →₀ ℕ) :
    |f (coefficients (directionalDerivative (Pi.single i 1) p) α)| ≤
      ((d : ℝ) * M / T i) / monomialScale T α := by
  rw [directionalDerivative_single_coordinate]
  by_cases hd : d < α i + 1
  · rw [hdegree _ i (by simpa using hd), mul_zero, abs_zero]
    exact div_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hM) (hT i).le)
      (monomialScale_pos T hT α).le
  · have hdi : (α i + 1 : ℝ) ≤ d := by exact_mod_cast Nat.le_of_not_gt hd
    have hscale : monomialScale T (α + Finsupp.single i 1) = monomialScale T α * T i := by
      rw [monomialScale_add]
      simp [monomialScale]
    have hcoef := hp (α + Finsupp.single i 1)
    rw [hscale] at hcoef
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α i + 1)]
    calc
      _ ≤ (d : ℝ) * (M / (monomialScale T α * T i)) :=
        mul_le_mul hdi hcoef (abs_nonneg _) (Nat.cast_nonneg d)
      _ = _ := by ring

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem realAdaptedDirectionalDerivative_single_bound
    {σ ι L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T M x) (i : σ) :
    F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T ((s : ℝ) * M / T i)
      (F.realAdaptedDirectionalDerivative (Pi.single i 1) x) := by
  have hp := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1) T hT hM
    (⟨x⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp hx
  intro z
  rw [← F.realAdaptedPolynomialTensor_coordinates (fun _ => 1) b ω hF,
    F.realAdaptedDirectionalDerivative_polynomial]
  let f := ((b.baseChange ℝ).coord z.val.2).restrictScalars ℚ
  have hdegree : ∀ (β : σ →₀ ℕ) (j : σ), s < β j →
      f (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) β) = 0 := by
    intro β j hj
    have hβ := Finsupp.le_weight (fun _ : σ => 1) (s := j) (by decide) β
    have hi := F.adaptedBasis_weight_le_step b ω hF z.val.2
    have hni : ¬Finsupp.weight (fun _ : σ => 1) β ≤ ω z.val.2 := by omega
    exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
      ((F.realification.adapted_iff_coefficients (fun _ => 1) _).mp
        (F.realAdaptedPolynomialMap_adapted (fun _ => 1) x) β) z.val.2 hni
  exact directionalDerivative_single_scaled_bound f
    (F.realAdaptedPolynomialMap (fun _ => 1) x) s hdegree T hT M hM
    (fun β => hp β z.val.2) i z.val.1

end Erdos3.NilpotentLieFiltration

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalSpanDerivativeSystem
namespace OAI

section

namespace Erdos3

open Module

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def basisWeightedCoordinates (b : Basis ι ℝ E) (scale : ι → ℝ) :
    E →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi (fun i => scale i • b.coord i)

@[simp] theorem basisWeightedCoordinates_apply (b : Basis ι ℝ E) (scale : ι → ℝ)
    (x : E) (i : ι) :
    basisWeightedCoordinates b scale x i = scale i * b.repr x i := rfl

theorem basisWeightedCoordinates_norm_le_iff [Fintype ι]
    (b : Basis ι ℝ E) (scale : ι → ℝ) (hscale : ∀ i, 0 < scale i)
    {M : ℝ} (hM : 0 ≤ M) (x : E) :
    ‖basisWeightedCoordinates b scale x‖ ≤ M ↔ ∀ i, |b.equivFun x i| ≤ M / scale i := by
  constructor
  · intro hx i
    apply (le_div_iff₀ (hscale i)).mpr
    have hi := (norm_le_pi_norm (basisWeightedCoordinates b scale x) i).trans hx
    simpa only [basisWeightedCoordinates_apply, Real.norm_eq_abs, abs_mul,
      abs_of_pos (hscale i), Basis.equivFun_apply, mul_comm] using hi
  · intro hx
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro i
    have hi := (le_div_iff₀ (hscale i)).mp (hx i)
    simpa only [basisWeightedCoordinates_apply, Real.norm_eq_abs, abs_mul,
      abs_of_pos (hscale i), Basis.equivFun_apply, mul_comm] using hi

theorem basisWeightedCoordinates_operator_bound [Fintype ι]
    (b : Basis ι ℝ E) (scale : ι → ℝ) (hscale : ∀ i, 0 < scale i)
    (A : E →ₗ[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ M, 0 ≤ M → ∀ x, (∀ i, |b.equivFun x i| ≤ M / scale i) →
      ∀ i, |b.equivFun (A x) i| ≤ C * M / scale i) (x : E) :
    ‖basisWeightedCoordinates b scale (A x)‖ ≤ C * ‖basisWeightedCoordinates b scale x‖ := by
  apply (basisWeightedCoordinates_norm_le_iff b scale hscale
    (mul_nonneg hC (norm_nonneg _)) (A x)).mpr
  exact hA _ (norm_nonneg _) x
    ((basisWeightedCoordinates_norm_le_iff b scale hscale (norm_nonneg _) x).mp le_rfl)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReindexGradedBasis
namespace OAI

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))

theorem gradedFrequency_reindex (η : L →ₗ[ℚ] ℚ) :
    F.gradedFrequency (b.reindex e) (fun k => ω (e.symm k)) hF' η =
      F.gradedFrequency b ω hF η := by
  apply LinearMap.ext
  intro x
  change η ((b.reindex e).repr.symm
      ((F.associatedGradedBasis (b.reindex e) (fun k => ω (e.symm k)) hF').repr x)) =
    η (b.repr.symm ((F.associatedGradedBasis b ω hF).repr x))
  rw [F.associatedGradedBasis_reindex b ω hF e hF']
  apply congrArg η
  apply (b.reindex e).repr.injective
  ext k
  simp only [LinearEquiv.apply_symm_apply, Basis.repr_reindex_apply]

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_controlled_vertical_decomposition {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) :
    letI := D.metricSpace
    ∀ (f : D.Space → ℂ) (K B : ℝ≥0), LipschitzWith K f → (∀ x, ‖f x‖ ≤ B) →
      (K : ℝ) ≤ Real.exp p → ∀ δ : ℝ, 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (η : J → L →ₗ[ℚ] ℚ) (v : J → D.Space → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, LipschitzWith K (v j) ∧ (∀ x, ‖v j x‖ ≤ B)) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        v j (z • x) = character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * v j x) ∧
      (∀ (z : D.RealGroup) (c : ℂ), (∀ x, f (z • x) = c * f x) →
        ∀ j x, v j (z • x) = c * v j x) ∧
      ∀ x, ‖(∑ j, v j x) - f x‖ ≤ δ := by
  classical
  let := D.metricSpace
  intro f K B hf hb hK δ hδ hδp
  obtain ⟨b, w, N, hlayers, _, hbinv, hN, hNp, _, _, A, hcomm, horbit, hact⟩ :=
    D.exists_controlled_central_actions hp hD
  let S : Set (Fin (finrank ℚ L)) := {j | s ≤ w j}
  let q := centralActionBudget p
  have hq : 0 ≤ q := centralActionBudget_nonneg hp
  have hpq : p ≤ q := le_centralActionBudget hp
  have hd : (Fintype.card S : ℝ) ≤ p := by
    apply (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hD.1
  let O : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos q).le⟩
  obtain ⟨J, inst, ν, v, hcard, hν, hv, hchar, hpres, herr⟩ :=
    exists_controlled_commuting_circle_decomposition A hcomm f K B O hf hb horbit δ q hδ hq
      (hd.trans hpq) (hK.trans (Real.exp_le_exp.mpr hpq)) le_rfl
      (hδp.trans (Real.exp_le_exp.mpr hpq))
  let η : J → L →ₗ[ℚ] ℚ := fun j => basisFrequency b S N (ν j)
  let R : ℝ := (2 * q + 2) ^ 4 + q + (p + 3) ^ 5
  have hpow : 0 ≤ (p + 3) ^ 5 := by positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hqR : q ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hfreq : (2 * q + 2) ^ 4 ≤ R := by dsimp [R]; linarith
  have hbas : (p + 3) ^ 5 ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hNq : (p + 3) ^ 9 ≤ q := by dsimp [q, centralActionBudget]; linarith
  have hterm : 2 * q * (2 * q + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ _ + (R + 2) ^ 4
    exact le_add_of_nonneg_right (by positivity)
  have hheight : (R + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ 2 * q * (2 * q + 2) ^ 4 + _
    have h : 0 ≤ 2 * q * (2 * q + 2) ^ 4 := by positivity
    linarith
  have hcentral (i : S) (z : L) : ⁅b i, z⁆ = 0 := by
    apply D.filtration.top_layer_central
    rw [hlayers s]
    exact Submodule.subset_span ⟨i, i.property, rfl⟩
  have hucentral (i : S) (z : ℝ ⊗[ℚ] L) : ⁅(N : ℝ) • b.baseChange ℝ i, z⁆ = 0 :=
    scaled_real_basis_central b i (hcentral i) N z
  refine ⟨J, inst, η, v, hcard.trans (Real.exp_le_exp.mpr hterm), ?_, hv, ?_, ?_, herr⟩
  · intro j i
    exact (basisFrequency_logHeight_le D.basis b S N hN (ν j) hR (hd.trans (hpq.trans hqR))
      (hNp.trans (Real.exp_le_exp.mpr (hNq.trans hqR)))
      (fun a => (hν j a).trans (Real.exp_le_exp.mpr hfreq))
      (fun a c => (hbinv a c).trans hbas) i).trans hheight
  · intro j z hz x
    apply central_span_character (fun i : S => (N : ℝ) • b.baseChange ℝ i) hucentral
      (realifyFunctional (η j)) (v j) ?_ ?_ x
    · intro i r y
      have h := hchar j i (r : CircleFourier.Circle) y
      rw [hact] at h
      change _ = character ((r * realifyFunctional (basisFrequency b S N (ν j))
        ((N : ℝ) • b.baseChange ℝ i) : ℝ) : CircleFourier.Circle) * _
      rw [realify_basisFrequency_direction b S N hN (ν j) i]
      simpa only [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm] using h
    · exact D.filtration.realLayer_le_span_scaled_basis b s S (hlayers s) N hN hz
  · intro z c hc
    apply hpres (fun x => z • x) c ?_ hc
    intro i t x
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [hact, hact, ← mul_smul, ← mul_smul]
    rw [(realBCHLine_commute _ (hucentral i) r z).eq]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_controlled_square_geometry {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b w (hlayers 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hlayers 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) := by
  obtain ⟨b, w, l, _, _, hlayers, hb, _, hc, hl, hlp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let q : ℝ := (p + 3) ^ 11 + 2 * p + 3
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqbr : (p + 3) ^ 11 + 1 ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hD.1
  have h2dim : 2 * (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ q := by
    have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
    dsimp [q]
    linarith
  have hH : (⌈Real.exp ((p + 3) ^ 11)⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one (by positivity)).trans (Real.exp_le_exp.mpr hqbr)
  have hgrid : (l : ℝ) ≤ Real.exp q := by
    apply hlp.trans (Real.exp_le_exp.mpr _)
    have hpow := pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (by decide : 9 ≤ 11)
    dsimp [q]
    linarith
  obtain ⟨N, hN, hinner, houter, hgeom⟩ := D.filtration.exists_square_rational_model
    b w hlayers D.lattice hl (one_le_ceil_exp _)
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k)) hin hout hq h2dim hH hgrid
  refine ⟨b, w, hlayers, N, hN, hinner, houter, hb, ?_⟩
  have he : q + 2 = (p + 3) ^ 11 + 2 * p + 5 := by dsimp [q]; ring
  simpa only [he, squareGeometryBudget] using hgeom

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_controlled_vertical_decomposition (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (δ : ℝ) (hδ : 0 < δ) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (η : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      (∀ j, (∃ x, (U j).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (η j) z.coord = n) ∧
      (∀ (z : D.RealGroup) (c : ℂ), (∀ x, T.observable (z • x) = c * T.observable x) →
        ∀ j x, (U j).observable (z • x) = c * (U j).observable x) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ δ) ∧
      ∀ x : σ → ℤ, ‖(∑ j, (U j).eval x) - T.eval x‖ ≤ δ := by
  let := D.metricSpace
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := observable_budget hT
    have hB := T.normBound.coe_nonneg
    linarith
  obtain ⟨J, inst, η, v, hcard, hheight, hv, hchar, hpres, herr⟩ :=
    D.exists_controlled_vertical_decomposition hp hT.1 T.observable T.lipBound T.normBound
      T.lipschitz T.norm_le hK δ hδ hδp
  let U : J → D.Niltest w := fun j =>
    { orbit := T.orbit
      observable := v j
      normBound := T.normBound
      lipBound := T.lipBound
      norm_le := (hv j).2
      lipschitz := (hv j).1 }
  refine ⟨J, inst, η, U, hcard, hheight, fun j => ⟨hT, rfl⟩, hchar, ?_, hpres, herr, ?_⟩
  · intro j hne z hz hΓ
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (η j) (v j)
      (hchar j) hne z hz hΓ
  · intro x
    exact herr (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReindexQuotientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ : Type*}

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

variable [Fintype ι]

noncomputable def reducedSquareFinIndexEquiv (s : ℕ) (ω : ι → ℕ) :
    ReducedSquareBasisIndex s ω ≃
      Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i}) :=
  (reindexWeightSurvivors s (squareBasisWeight ω) (Fintype.equivFin _)).trans (Fintype.equivFin _)

end Erdos3.NilpotentLieFiltration

end

end OAI
end


