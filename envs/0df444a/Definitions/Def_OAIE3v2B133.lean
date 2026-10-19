-- Prove2me | Definitions.Def_OAIE3v2B133
-- name    : OAIE3v2B133
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:56:01.299602+00:00
-- url     : https://prove2.me/theorems/8ee70416-f86a-4dae-9dd7-9949c9a28a69
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 135 of 311
-- statement:
--   Definitions bundle 135 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B119`, `OAIE3v2B120` of this split.
--
--   Modules: `Estimates/BoundedRealifiedSquareOrbit.lean`, `Estimates/GradedPieceRepresentative.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/ProjectedPointwiseCoefficient.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/ReducedSquareSymbol.lean`, `Estimates/ShiftedGradedCalculus.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Fourier/VerticalFrequencyIdentification.lean`, `Geometry/FilteredSubalgebraCoordinates.lean`, `Geometry/RealifiedSquareCoordinates.lean`, `Geometry/RealifiedSquareMetric.lean`, `Linear/ChosenBasisGeometryBounds.lean`, `Linear/OrdinarySymbolBasisDimension.lean`, `Linear/ReindexGradedBasis.lean`, `Linear/ReindexQuotientBasis.lean`, `Linear/SquareBasisGeometry.lean`, `Nilpotent/RationalBCHProducts.lean`, `Polynomial/PolynomialDerivativeBounds.lean`, `Polynomial/ScaledPolynomialDualBounds.lean`, `Polynomial/SquarePolynomialCoordinates.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B119
import Definitions.Def_OAIE3v2B120

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RationalBCHProducts
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_real_bch_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (lieStructureConstants e i j z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)),
          rs.length ≤ k →
          (∀ r ∈ rs, (e.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid l) →
          (e.baseChange ℝ).equivFun rs.prod.coord ∈ realDenominatorGrid m := by
  induction k with
  | zero =>
    refine ⟨2, by omega, ?_⟩
    intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
    refine ⟨l, hl, hlp.trans (Real.exp_le_exp.mpr (le_power_budget hp (by omega))), dvd_refl l, ?_⟩
    intro rs hlen hrs
    have hrs0 : rs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst rs
    simpa only [List.prod_nil, NilpotentLieBCHGroup.coord_one, map_zero] using
      (realDenominatorGrid_zero (ι := ι) l)
  | succ k ih =>
    obtain ⟨K, hK, hprod⟩ := ih
    obtain ⟨J, _, hmul⟩ := exists_real_bch_rational_closure s
    let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C K) ^ K + Polynomial.C J) ^ J
    obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
    refine ⟨C, hC, ?_⟩
    intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
    obtain ⟨m₁, hm₁, hm₁p, hlm₁, hprod₁⟩ := hprod e H p hnil hp hd hH hc l hl hlp
    let q : ℝ := (p + K) ^ K
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hpq : p ≤ q := by
      apply (show p ≤ p + K from le_add_of_nonneg_right (Nat.cast_nonneg K)).trans
      have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
      simpa only [pow_one] using pow_le_pow_right₀
        (show (1 : ℝ) ≤ p + K by linarith) (show 1 ≤ K by omega)
    obtain ⟨m₂, hm₂, hm₂p, hm₁m₂, hmul₂, _⟩ := hmul e H q hnil hq (hd.trans hpq)
      (hH.trans (Real.exp_le_exp.mpr hpq)) hc m₁ hm₁ hm₁p
    have hpoly : (q + J) ^ J ≤ (p + C) ^ C := by
      simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
    refine ⟨m₂, hm₂, hm₂p.trans (Real.exp_le_exp.mpr hpoly), hlm₁.trans hm₁m₂, ?_⟩
    intro rs hlen hrs
    cases rs with
    | nil =>
      simpa only [List.prod_nil, NilpotentLieBCHGroup.coord_one, map_zero] using
        (realDenominatorGrid_zero (ι := ι) m₂)
    | cons r rs =>
      rw [List.prod_cons]
      apply hmul₂
      · exact realDenominatorGrid_subset_of_dvd hl hlm₁ (hrs r (List.mem_cons_self))
      · apply hprod₁ rs (Nat.le_of_succ_le_succ hlen)
        exact fun x hx => hrs x (List.mem_cons_of_mem r hx)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module

theorem exists_symbol_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (F.RealPolynomialSymbolGroup w), rs.length ≤ k →
          (∀ r ∈ rs, F.SymbolRationalGrid b ω hlayers w l r) →
          F.SymbolRationalGrid b ω hlayers w m rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_real_bch_rational_product_bound s k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.polynomialSymbolBasis b ω hlayers w
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j z, RationalHeightLE (lieStructureConstants B i j z) H :=
    F.polynomialSymbolBasis_bracket_height b ω hlayers w hH hb
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hK B H q
    (F.polynomialSymbol_lowerCentralSeries_eq_bot w) hq hdim
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hstruct l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpoly), hlm, hprod⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_rational_inv_mul_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ D R : F.RealPolynomialSymbolGroup w,
          F.SymbolRationalGrid b ω hF w l D → F.SymbolRationalGrid b ω hF w l R →
          F.SymbolRationalGrid b ω hF w m (D⁻¹ * R) := by
  obtain ⟨C, hC, hprod⟩ := exists_symbol_rational_product_bound s 2
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hprod F b ω hF w hw H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro D R hD hR
  have hinputs : ∀ x ∈ [D⁻¹, R], F.SymbolRationalGrid b ω hF w l x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact F.symbolRationalGrid_inv b ω hF w l hD
    · exact hR
  simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [D⁻¹, R] (by simp) hinputs

end Erdos3.NilpotentLieFiltration

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

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationSubgroup (K : LieSubalgebra ℚ L) :
    Subgroup (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :=
  realLieSubgroup (realificationLieSubalgebra K)

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem realificationLieSubalgebra_map {L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (U : LieSubalgebra ℚ L) (f : L →ₗ⁅ℚ⁆ M) :
    realificationLieSubalgebra (U.map f) =
      (realificationLieSubalgebra U).map (realificationLieHom f) := by
  apply LieSubalgebra.toSubmodule_injective
  exact realification_map U.toSubmodule f.toLinearMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedCoefficientBound_mono (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hx : F.RealAdaptedCoefficientBound b ω hF w T M x) :
    F.RealAdaptedCoefficientBound b ω hF w T N x := by
  intro z
  exact (hx z).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT z.val.1).le)

theorem realAdaptedCoefficientBound_polynomial_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (g : F.RealAdaptedPolynomialGroup w) :
    F.RealAdaptedCoefficientBound b ω hF w T M g.coord ↔
      F.PolynomialSlowBound b w T M (F.realAdaptedPolynomialGroupHom w g) :=
  (F.polynomialSlowBound_groupHom_iff b w ω hF T hT hM g).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_normalized_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℚ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ r : VectorPolynomial σ ℚ D.filtration.realification.squareLieSubalgebra,
          D.filtration.realification.squareFiltration.Adapted w r ∧
          VectorPolynomial.map D.filtration.realification.squareFst.toLinearMap r =
            normalizedShiftLog s h (-ε.coord) (-γ.coord) f.log ∧
          VectorPolynomial.map D.filtration.realification.squareSnd.toLinearMap r = f.log := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  let H := ⌈Real.exp p⌉₊
  let u : D.RealGroup := ⟨eval h f.log⟩
  let v : D.RealGroup := ⟨eval (fun _ => 0) f.log⟩
  obtain ⟨ε, hε, γ, hγ, heq⟩ := hrep D.basis D.filtration.lowerCentralSeries_eq_bot
    D.lattice D.grid H (p + 1) D.grid_pos D.inner_grid
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) (u * v⁻¹)
  refine ⟨ε, γ, hγ, hε, ?_⟩
  exact D.filtration.realification.exists_normalized_shift_square w hw h (-ε.coord) (-γ.coord)
    f.log f.adapted (D.filtration.realification.normalizedShift_horizontal_zero h f.log ε γ heq)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedGradedCalculus
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem filteredFirstJetMap_eq_iff (p q : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetMap w p = F.filteredFirstJetMap w q ↔
      ∀ α, coefficients (p.val - q.val) α ∈ F.layer (Finsupp.weight w α + 2) := by
  rw [← sub_eq_zero, ← map_sub, F.filteredFirstJetMap_eq_zero_iff]
  rfl

theorem filteredFirstJet_lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ (F.FilteredFirstJet w) (F.FilteredFirstJet w) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def taylorRemainder (h : σ → ℚ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ L :=
  (scalarTaylorRemainder h).rTensor L

theorem taylorRemainder_apply (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    taylorRemainder h p = translate h p - p - directionalDerivative h p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q x =>
    change scalarTaylorRemainder h q ⊗ₜ[ℚ] x = _
    rw [scalarTaylorRemainder_apply, TensorProduct.sub_tmul, TensorProduct.sub_tmul,
      translate_tmul, directionalDerivative_tmul, scalarDirectionalDerivative_apply, TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    abel

theorem coefficients_taylorRemainder_monomial (h : σ → ℚ) (α β : σ →₀ ℕ) (x : L) :
    coefficients (taylorRemainder h (monomial α x)) β =
      (scalarTaylorRemainder h (MvPolynomial.monomial α 1)).coeff β • x := by
  change coefficients (scalarTaylorRemainder h (MvPolynomial.monomial α 1) ⊗ₜ[ℚ] x) β = _
  exact coefficients_tmul _ _ _

theorem coefficients_taylorRemainder (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (taylorRemainder h p) α = ∑ β ∈ (coefficients p).support,
      (scalarTaylorRemainder h (MvPolynomial.monomial β 1)).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, coefficients_taylorRemainder_monomial]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem taylorRemainder_mem_shifted (h : σ → ℚ) (k : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k) :
    translate h p - p - directionalDerivative h p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) (k + 2) := by
  rw [← taylorRemainder_apply]
  intro α
  rw [coefficients_taylorRemainder]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (scalarTaylorRemainder h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ (hp β)
    have hd := scalarTaylorRemainder_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 2 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    omega

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem filteredFirstJet_translate (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1)
      ⟨translate h p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
        (F.adapted_translate (fun _ => 1) (by simp) h
          ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩ =
      F.filteredFirstJetMap (fun _ => 1) p +
        F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p) := by
  rw [F.symbolFirstDerivative_map, ← map_add]
  apply (F.filteredFirstJetMap_eq_iff (fun _ => 1) _ _).mpr
  have hp : p.val ∈ F.shiftedAdaptedSubmodule (fun _ => 1) 0 := by
    intro α
    simpa only [Nat.add_zero] using p.property α
  have hr := F.taylorRemainder_mem_shifted h 0 hp
  change ∀ α, coefficients (translate h p.val - (p.val + directionalDerivative h p.val)) α ∈ _
  rw [show translate h p.val - (p.val + directionalDerivative h p.val) =
      translate h p.val - p.val - directionalDerivative h p.val by abel]
  exact hr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem filteredFirstJet_normalizedShift [Fintype σ] (h : σ → ℚ) (a b : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1)
      ⟨normalizedShiftLog s h a b p.val,
        (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
          (F.normalizedShiftLog_adapted (fun _ => 1) (by simp) h a b
            ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩ =
      lieBCH s (F.filteredFirstJetMap (fun _ => 1) (F.adaptedConstant (fun _ => 1) a))
        (lieBCH s (F.filteredFirstJetMap (fun _ => 1) p +
          F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p))
            (F.filteredFirstJetMap (fun _ => 1) (F.adaptedConstant (fun _ => 1) b))) := by
  let q : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
    ⟨translate h p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
      (F.adapted_translate (fun _ => 1) (by simp) h
        ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩
  have he : (⟨normalizedShiftLog s h a b p.val,
        (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
          (F.normalizedShiftLog_adapted (fun _ => 1) (by simp) h a b
            ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩ :
      F.adaptedLieSubalgebra (fun _ : σ => 1)) =
      lieBCH s (F.adaptedConstant (fun _ => 1) a)
        (lieBCH s q (F.adaptedConstant (fun _ => 1) b)) := by
    apply Subtype.ext
    change normalizedShiftLog s h a b p.val =
      (F.adaptedLieSubalgebra (fun _ : σ => 1)).incl
        (lieBCH s (F.adaptedConstant (fun _ => 1) a) (lieBCH s q (F.adaptedConstant (fun _ => 1) b)))
    rw [map_lieBCH, map_lieBCH]
    rfl
  rw [he, map_lieBCH, map_lieBCH]
  have ht : F.filteredFirstJetMap (fun _ => 1) q = F.filteredFirstJetMap (fun _ => 1) p +
      F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p) := F.filteredFirstJet_translate h p
  rw [ht]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def normalizedShiftAdapted (a b : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  ⟨normalizedShiftLog s h a b p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
    (F.normalizedShiftLog_adapted (fun _ => 1) (by simp) h a b
      ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩

noncomputable def normalizedRelativeLog (e m : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)

noncomputable def adaptedLogDerivative (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedLieSubalgebra (fun _ : σ => 1) := dualLogDerivative (F.adaptedPolynomialJet h p)

theorem filteredFirstJet_normalizedRelativeLog (e m : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1) (F.normalizedRelativeLog h e m p) =
      F.filteredFirstJetMap (fun _ => 1)
        (F.adaptedLogDerivative h p - F.adaptedConstant (fun _ => 1) e -
          dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
            (F.adaptedConstant (fun _ => 1) m)) := by
  have hbracket : ∀ x ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
      ∀ y ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
        ⁅x, y⁆ ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
    intro x hx y hy
    exact F.shiftedPolynomialIdeal_lie_mem (fun _ => 1) (i := 1) (j := 1) hx hy
  have hz : dualTangentLinear (F.adaptedPolynomialJet h p).coord ∈
      F.shiftedPolynomialIdeal (fun _ : σ => 1) 1 := by
    rw [F.adaptedPolynomialJet_tangent]
    exact F.directionalDerivative_mem_next h p
  have hid := dualBCH_insertion_quotient
    (F.shiftedPolynomialIdeal (fun _ : σ => 1) 1) (F.shiftedPolynomialIdeal (fun _ : σ => 1) 2)
    hbracket (F.adaptedPolynomialJet h p)
    (F.adaptedConstant (fun _ => 1) e) (F.adaptedConstant (fun _ => 1) m) hz
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) e)
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) m)
  rw [F.adaptedPolynomialJet_base, F.adaptedPolynomialJet_tangent,
    F.adaptedPolynomialJet_baseHom] at hid
  change F.filteredFirstJetMap (fun _ => 1)
    (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)) = _
  rw [map_lieBCH, map_neg]
  have hn := F.filteredFirstJet_normalizedShift h (-e) (-m) p
  change F.filteredFirstJetMap (fun _ => 1) (F.normalizedShiftAdapted h (-e) (-m) p) = _ at hn
  rw [hn, F.symbolFirstDerivative_map]
  have hc (a : L) : F.adaptedConstant (fun _ : σ => 1) (-a) =
      -F.adaptedConstant (fun _ : σ => 1) a := (F.adaptedConstantLieHom (fun _ => 1)).map_neg a
  rw [hc e, hc m, map_neg, map_neg,
    ← lieBCH_assoc (F.filteredFirstJet_lowerCentralSeries_eq_bot (fun _ : σ => 1))]
  rw [map_add] at hid
  exact hid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_tangent (x : L) :
    dualLogDerivative (hnil := hnil) (dualTangentElement x) = x := by
  simpa only [map_one, mul_one] using
    dualLogDerivative_tangent_mul_constant x (1 : NilpotentLieBCHGroup L s hnil)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarePolynomialCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem square_polynomial_ext {r q : F.squareFiltration.adaptedLieSubalgebra w}
    (hf : F.squareFstPolynomialMap w r = F.squareFstPolynomialMap w q)
    (hs : F.squareSndPolynomialMap w r = F.squareSndPolynomialMap w q) : r = q := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply Subtype.ext
  apply Prod.ext
  · have he := congrArg (fun p : F.adaptedLieSubalgebra w => coefficients p.val α) hf
    simpa only [F.squareFstPolynomialMap_coefficient] using he
  · have he := congrArg (fun p : F.adaptedLieSubalgebra w => coefficients p.val α) hs
    simpa only [F.squareSndPolynomialMap_coefficient] using he

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

theorem quotientLie_mem_iff (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (j : ℕ) (x : L) :
    lieQuotientMap I x ∈ (F.quotientLie I hI).layer j ↔ x ∈ F.layer j ⊔ I.toSubmodule := by
  change x ∈ ((F.layer j).map I.toSubmodule.mkQ).comap I.toSubmodule.mkQ ↔ _
  rw [Submodule.comap_map_mkQ, sup_comm]

theorem quotientGradedMap_piece_eq_zero_iff (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) (j : ℕ) (x : F.layer j) :
    F.quotientGradedMap I hI (F.associatedGradedPieceMap j x) = 0 ↔
      (x : L) ∈ F.layer (j + 1) ⊔ I.toSubmodule := by
  rw [F.quotientGradedMap_piece, associatedGradedPieceMap_eq_zero_iff,
    F.quotientLie_mem_iff]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

theorem normalizedRelativeLog_shifted :
    F.normalizedRelativeLog h e m p ∈ F.shiftedAdaptedIdeal (fun _ : σ => 1) := by
  apply (F.polynomialSymbolMap_eq_zero_iff (fun _ => 1) _).mp
  change F.polynomialSymbolMap (fun _ => 1)
    (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)) = 0
  rw [map_lieBCH, map_neg]
  have he : F.polynomialSymbolMap (fun _ => 1) (F.normalizedShiftAdapted h (-e) (-m) p) =
      F.polynomialSymbolMap (fun _ => 1) p := by
    apply (F.polynomialSymbolMap_eq_iff (fun _ => 1) _ _).mpr
    exact F.normalizedShiftLog_sub_coefficient_mem (fun _ => 1) (by simp) h (-e) (-m)
      ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property)
  rw [he]
  exact congrArg NilpotentLieBCHGroup.coord
    (mul_inv_cancel (⟨F.polynomialSymbolMap (fun _ => 1) p⟩ :
      F.PolynomialSymbolGroup (fun _ : σ => 1)))

theorem normalizedRelativeLog_horizontal
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    coefficients (F.normalizedRelativeLog h e m p).val 0 ∈ F.layer 2 := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mp
  rw [← eval_zero_eq_coefficient]
  change lieQuotientMap (F.layerIdeal 2)
    (eval (0 : σ → ℚ) ((F.adaptedLieSubalgebra (fun _ => 1)).incl
      (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)))) = 0
  rw [map_lieBCH, eval_lieBCH, F.horizontal_bch, map_neg, map_neg, map_neg]
  have hz := (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mpr hzero
  rw [← eval_zero_eq_coefficient, map_sub, map_sub] at hz
  rw [sub_eq_add_neg] at hz
  exact hz

theorem normalizedRelativeLog_mem
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    F.normalizedRelativeLog h e m p ∈ F.normalizedRelativeSubmodule (fun _ : σ => 1) :=
  ⟨F.normalizedRelativeLog_shifted h e m p, F.normalizedRelativeLog_horizontal h e m p hzero⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem quotientTopBasis_repr_mk (x : L) (i : QuotientTopBasisIndex s ω) :
    (F.quotientTopBasis e ω hF).repr (lieQuotientMap (F.layerIdeal (s + 1)) x) i = e.repr x i.val :=
  supportedQuotientBasis_repr_mk e _ _ _ x i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable [Fintype ι]

omit [Fintype ι] in

theorem adaptedSquareBasis_pairMap_height (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    (k : Σ _ : Bool, ι) (j : ι ⊕ {i // 2 ≤ w i}) :
    RationalHeightLE ((Pi.basis (fun _ : Bool => b)).repr
      (F.squarePairMap (F.adaptedSquareBasis b w h j)) k) 1 := by
  rcases k with ⟨flag, i⟩
  rw [Pi.basis_repr]
  cases j with
  | inl j =>
    cases flag <;>
      simpa only [squarePairMap_false, squarePairMap_true, adaptedSquareBasis_inl] using
        basis_repr_height_one b j i
  | inr j =>
    cases flag
    · simp only [squarePairMap_false, adaptedSquareBasis_inr, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero le_rfl
    · simpa only [squarePairMap_true, adaptedSquareBasis_inr] using basis_repr_height_one b j i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev QuotientTopSymbolIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ) :=
  SymbolBasisIndex w (fun i : QuotientTopBasisIndex s ω => ω i.val)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedSquareCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realifiedSquareEquiv :
    (ℝ ⊗[ℚ] F.squareLieSubalgebra) ≃ₗ[ℚ] F.realification.squareLieSubalgebra :=
  let e := ((F.squareCoordinates.baseChange ℚ ℝ _ _).trans
    (TensorProduct.prodRight ℚ ℝ ℝ L (F.layer 2))).trans
      ((LinearEquiv.refl ℝ (ℝ ⊗[ℚ] L)).prodCongr (realificationSubmoduleEquiv (F.layer 2)))
  (e.restrictScalars ℚ).trans F.realification.squareCoordinates.symm

theorem realifiedSquareEquiv_tmul (r : ℝ) (x : F.squareLieSubalgebra) :
    (F.realifiedSquareEquiv (r ⊗ₜ[ℚ] x)).val =
      (r ⊗ₜ[ℚ] x.val.1, r ⊗ₜ[ℚ] x.val.2) := by
  apply Prod.ext
  · change r ⊗ₜ[ℚ] x.val.2 + r ⊗ₜ[ℚ] (x.val.1 - x.val.2) = r ⊗ₜ[ℚ] x.val.1
    rw [← TensorProduct.tmul_add]
    congr 1
    abel
  · rfl

theorem realifiedSquareEquiv_fst (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    F.realification.squareFst (F.realifiedSquareEquiv x) = realificationLieHom F.squareFst x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => exact congrArg Prod.fst (F.realifiedSquareEquiv_tmul r x)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realifiedSquareEquiv_snd (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    F.realification.squareSnd (F.realifiedSquareEquiv x) = realificationLieHom F.squareSnd x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => exact congrArg Prod.snd (F.realifiedSquareEquiv_tmul r x)
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realifiedSquareLieEquiv :
    (ℝ ⊗[ℚ] F.squareLieSubalgebra) ≃ₗ⁅ℚ⁆ F.realification.squareLieSubalgebra where
  toFun := F.realifiedSquareEquiv
  invFun := F.realifiedSquareEquiv.symm
  left_inv := F.realifiedSquareEquiv.left_inv
  right_inv := F.realifiedSquareEquiv.right_inv
  map_add' := F.realifiedSquareEquiv.map_add
  map_smul' := F.realifiedSquareEquiv.map_smul
  map_lie' := by
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · change F.realification.squareFst (F.realifiedSquareEquiv ⁅x, y⁆) =
        F.realification.squareFst ⁅F.realifiedSquareEquiv x, F.realifiedSquareEquiv y⁆
      simp only [realifiedSquareEquiv_fst, LieHom.map_lie]
    · change F.realification.squareSnd (F.realifiedSquareEquiv ⁅x, y⁆) =
        F.realification.squareSnd ⁅F.realifiedSquareEquiv x, F.realifiedSquareEquiv y⁆
      simp only [realifiedSquareEquiv_snd, LieHom.map_lie]

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

def squareLayerConstraint (j : ℕ) : F.squareLieSubalgebra →ₗ[ℚ]
    ((L ⧸ F.layer j) × (L ⧸ F.layer (j + 1))) :=
  ((F.layer j).mkQ.comp F.squareSnd.toLinearMap).prod
    ((F.layer (j + 1)).mkQ.comp (F.squareFst.toLinearMap - F.squareSnd.toLinearMap))

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realifiedSquareGroupEquiv :
    F.squareFiltration.realification.Group ≃* F.realification.squareFiltration.Group where
  toFun g := ⟨F.realifiedSquareEquiv g.coord⟩
  invFun g := ⟨F.realifiedSquareEquiv.symm g.coord⟩
  left_inv g := NilpotentLieBCHGroup.ext (F.realifiedSquareEquiv.symm_apply_apply g.coord)
  right_inv g := NilpotentLieBCHGroup.ext (F.realifiedSquareEquiv.apply_symm_apply g.coord)
  map_mul' g h := NilpotentLieBCHGroup.ext
    (map_lieBCH_of_nilpotent_steps F.realifiedSquareLieEquiv.toLieHom
      F.squareFiltration.realification.lowerCentralSeries_eq_bot
      F.realification.squareFiltration.lowerCentralSeries_eq_bot g.coord h.coord)

noncomputable def realSquareFstHom : F.squareFiltration.realification.Group →* F.realification.Group :=
  realificationMap (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) F.squareFst

noncomputable def realSquareSndHom : F.squareFiltration.realification.Group →* F.realification.Group :=
  realificationMap (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) F.squareSnd

theorem realifiedSquareGroupEquiv_fst (g : F.squareFiltration.realification.Group) :
    F.realification.squareFstHom (F.realifiedSquareGroupEquiv g) = F.realSquareFstHom g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realifiedSquareEquiv_fst g.coord

theorem realifiedSquareGroupEquiv_snd (g : F.squareFiltration.realification.Group) :
    F.realification.squareSndHom (F.realifiedSquareGroupEquiv g) = F.realSquareSndHom g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realifiedSquareEquiv_snd g.coord

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareLattice_le_fst :
    (F.squareLattice Γ).map realificationHom ≤
      (Γ.map realificationHom).comap F.realSquareFstHom := by
  apply realificationMap_subgroup F.squareFst
  exact F.squareLattice_le_fst Γ

theorem realSquareLattice_le_snd :
    (F.squareLattice Γ).map realificationHom ≤
      (Γ.map realificationHom).comap F.realSquareSndHom := by
  apply realificationMap_subgroup F.squareSnd
  exact F.squareLattice_le_snd Γ

noncomputable def realSquareObservable (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) : ℂ :=
  u (ε • cosetMap _ _ F.realSquareFstHom (F.realSquareLattice_le_fst Γ) x) *
    star (u (cosetMap _ _ F.realSquareSndHom (F.realSquareLattice_le_snd Γ) x))

theorem realSquareObservable_norm_le (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ x, ‖u x‖ ≤ B)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) :
    ‖F.realSquareObservable Γ ε u x‖ ≤ B ^ 2 := by
  rw [realSquareObservable, norm_mul, norm_star, pow_two]
  exact mul_le_mul (hu _) (hu _) (norm_nonneg _) hB

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedPieceRepresentative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_associatedGradedPieceMap_of_pure
    {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (j : ℕ) (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x = x) :
    ∃ v : F.layer j, F.associatedGradedPieceMap j v = x := by
  have hm := basisCoordinateProjection_mem_span (F.associatedGradedBasis e ω hF)
    {i | ω i = j} x
  change basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x ∈ _ at hm
  rw [hx, ← F.associatedGradedPieceMap_range e ω hF j] at hm
  exact hm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem homogeneousSymbolLift_coordinate [DecidableEq σ] (α : σ →₀ ℕ)
    (v : F.AssociatedGraded) (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr (F.homogeneousSymbolLift b ω hlayers w α v) z =
      if α = z.val.1 then (F.associatedGradedBasis b ω hlayers).repr v z.val.2 else 0 := by
  rw [F.homogeneousSymbolLift_apply, F.gradedPolynomialSymbol_coordinate, coefficients_monomial]
  by_cases h : α = z.val.1 <;> simp [h]

theorem gradedSymbolPolynomial_homogeneousSymbolLift (α : σ →₀ ℕ) (v : F.AssociatedGraded) :
    F.gradedSymbolPolynomial b ω hlayers w (F.homogeneousSymbolLift b ω hlayers w α v) =
      monomial α (basisGradeProjection (F.associatedGradedBasis b ω hlayers) ω (Finsupp.weight w α) v) := by
  classical
  apply coefficients.injective
  ext β
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [coefficients_monomial]
  by_cases hα : α = β
  · subst β
    rw [Finsupp.single_eq_same, basisGradeProjection_repr]
    by_cases hd : Finsupp.weight w α = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(α, i), hd⟩,
        F.homogeneousSymbolLift_coordinate]
      simp only [hd, ite_true]
    · rw [F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ α i hd]
      exact (if_neg (Ne.symm hd)).symm
  · rw [Finsupp.single_eq_of_ne (Ne.symm hα), map_zero, Finsupp.zero_apply]
    by_cases hd : Finsupp.weight w β = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(β, i), hd⟩,
        F.homogeneousSymbolLift_coordinate]
      exact if_neg hα
    · exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ β i hd

theorem homogeneousSymbolLift_coefficient (α : σ →₀ ℕ) (x : F.PolynomialSymbol w) :
    F.homogeneousSymbolLift b ω hlayers w α (coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α) =
      basisCoordinateProjection (F.polynomialSymbolBasis b ω hlayers w) {z | z.val.1 = α} x := by
  classical
  apply (F.polynomialSymbolBasis b ω hlayers w).repr.injective
  ext z
  rw [F.homogeneousSymbolLift_coordinate, basisCoordinateProjection_repr]
  simp only [Set.mem_ofPred_eq]
  by_cases h : z.val.1 = α
  · rw [if_pos h, if_pos h.symm, ← h]
    exact F.gradedSymbolPolynomial_coefficient b ω hlayers w x z
  · rw [if_neg h, if_neg (Ne.symm h)]

end Erdos3.NilpotentLieFiltration

end

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

theorem associatedGradedMap_basis_repr (i : ι) (j : κ) :
    (G.associatedGradedBasis f ν hG).repr
      (F.associatedGradedMap G φ hφ (F.associatedGradedBasis e ω hF i)) j =
      if ω i = ν j then f.repr (φ (e i)) j else 0 := by
  rw [G.associatedGradedBasis_repr, F.associatedGradedBasis_apply]
  change (G.polynomialSymbolBasis f ν hG (fun _ : Unit => 1)).repr
    (F.filteredPolynomialSymbolMap G φ hφ (fun _ : Unit => 1)
      (F.polynomialSymbolBasis e ω hF (fun _ : Unit => 1) _)) _ = _
  rw [F.filteredPolynomialSymbolMap_basis_repr G e ω hF f ν hG φ hφ]
  simp only [unitMonomial_injective.eq_iff]

theorem associatedGradedMap_gradeProjection (j : ℕ) (x : F.AssociatedGraded) :
    F.associatedGradedMap G φ hφ (basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x) =
      basisGradeProjection (G.associatedGradedBasis f ν hG) ν j (F.associatedGradedMap G φ hφ x) := by
  apply basisBlockMap_commutes (F.associatedGradedBasis e ω hF) (G.associatedGradedBasis f ν hG)
    ω ν (F.associatedGradedMap G φ hφ).toLinearMap
  intro i k hik
  change (G.associatedGradedBasis f ν hG).repr
    (F.associatedGradedMap G φ hφ (F.associatedGradedBasis e ω hF i)) k = 0
  rw [F.associatedGradedMap_basis_repr G e ω hF f ν hG φ hφ, if_neg (Ne.symm hik)]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareObservable_relative_character (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup s, ∀ x, u (z • x) = character (χ z) * u x)
    (k : F.squareFiltration.realification.Group)
    (hk : F.realSquareFstHom k ∈ F.realification.subgroup s)
    (hs : F.realSquareSndHom k = 1)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) :
    F.realSquareObservable Γ ε u (k • x) =
      character (χ (F.realSquareFstHom k)) * F.realSquareObservable Γ ε u x := by
  have hcomm (y : F.realification.Group ⧸ Γ.map realificationHom) :
      ε • (F.realSquareFstHom k • y) = F.realSquareFstHom k • (ε • y) := by
    rw [← mul_smul, ← mul_smul, (F.realification.top_commutes _ hk ε).eq]
  simp only [realSquareObservable, cosetMap_smul, hs, one_smul]
  rw [hcomm, hu _ hk]
  exact mul_assoc _ _ _

variable (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)

theorem realSquare_descent_relative_character (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (v : F.squareFiltration.quotientTop.realification.Group ⧸
      ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom → ℂ)
    (hv : ∀ g, v (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl g)) =
      F.realSquareObservable Γ ε u (QuotientGroup.mk g))
    (k : F.squareFiltration.realification.Group)
    (hk : F.realSquareFstHom k ∈ F.realification.subgroup (s + 1))
    (hs : F.realSquareSndHom k = 1)
    (x : F.squareFiltration.quotientTop.realification.Group ⧸
      ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom) :
    v (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl k • x) =
      character (χ (F.realSquareFstHom k)) * v x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := F.squareFiltration.realQuotientStepHom_surjective
    (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl g
  change v (QuotientGroup.mk
    (F.squareFiltration.realQuotientStepHom _ (t := s) le_rfl k *
      F.squareFiltration.realQuotientStepHom _ (t := s) le_rfl y)) = _
  rw [← map_mul, hv, hv]
  exact F.realSquareObservable_relative_character Γ ε u χ hu k hk hs (QuotientGroup.mk y)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct

theorem vertical_frequency_on_real_direction
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (ξ : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.realification.subgroup s, ∀ x,
      f (z • x) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (y : L) (hy : y ∈ F.layer s) (a : ℝ)
    (hcharacter : ∀ t : ℝ, ∀ x,
      f ((⟨t ⊗ₜ[ℚ] y⟩ : F.realification.Group) • x) =
        character ((t * a : ℝ) : CircleFourier.Circle) * f x) :
    (ξ y : ℝ) = a := by
  obtain ⟨x, hx⟩ := hne
  apply real_frequency_eq_of_character_multiples
  intro t
  apply mul_right_cancel₀ hx
  have hz : (⟨t ⊗ₜ[ℚ] y⟩ : F.realification.Group) ∈ F.realification.subgroup s :=
    Submodule.tmul_mem_baseChange_of_mem t hy
  have heq := (hvert _ hz x).symm.trans (hcharacter t x)
  simpa only [realifyFunctional_tmul] using heq

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem square_mode_relative_frequency (hs : 1 ≤ s)
    (Γ : Subgroup F.squareFiltration.quotientTop.realification.Group)
    (η : L →ₗ[ℚ] ℚ)
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (f : F.squareFiltration.quotientTop.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.squareFiltration.quotientTop.realification.subgroup s, ∀ y,
      f (z • y) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * f y)
    (hne : ∃ y, f y ≠ 0)
    (hrelative : ∀ k : F.squareFiltration.realification.Group,
      F.realSquareFstHom k ∈ F.realification.subgroup (s + 1) →
      F.realSquareSndHom k = 1 → ∀ y,
      f (F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl k • y) =
        character ((realifyFunctional η (F.realSquareFstHom k).coord : ℝ) : CircleFourier.Circle) * f y)
    (x : F.layer (s + 1)) :
    ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
      (F.squareRelativeLayer s hs x).val) = η x := by
  let z : F.squareLieSubalgebra := (F.squareRelativeLayer s hs x).val
  let q := lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) z
  have hq : q ∈ F.squareFiltration.quotientTop.layer s :=
    F.squareFiltration.quotientLie_mem _ le_rfl (F.squareRelativeLayer s hs x).property
  have h := vertical_frequency_on_real_direction F.squareFiltration.quotientTop Γ ξ f
    hvert hne q hq (η x : ℝ) (by
      intro t y
      let k : F.squareFiltration.realification.Group := ⟨t ⊗ₜ[ℚ] z⟩
      have hf : F.realSquareFstHom k = (⟨t ⊗ₜ[ℚ] (x : L)⟩ : F.realification.Group) :=
        NilpotentLieBCHGroup.ext rfl
      have hk : F.realSquareFstHom k ∈ F.realification.subgroup (s + 1) := by
        rw [hf]
        exact Submodule.tmul_mem_baseChange_of_mem t x.property
      have hkzero : F.realSquareSndHom k = 1 := by
        apply NilpotentLieBCHGroup.ext
        change t ⊗ₜ[ℚ] (0 : L) = 0
        simp only [TensorProduct.tmul_zero]
      have hπ : F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl k =
          (⟨t ⊗ₜ[ℚ] q⟩ : F.squareFiltration.quotientTop.realification.Group) :=
        NilpotentLieBCHGroup.ext rfl
      have he := hrelative k hk hkzero y
      rw [hπ, hf] at he
      simpa only [realifyFunctional_tmul] using he)
  exact_mod_cast h

theorem descended_square_mode_frequency_restriction (hs : 1 ≤ s)
    (Γ : Subgroup F.Group) (ε : F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ y,
      u (z • y) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * u y)
    (v f : F.squareFiltration.quotientTop.realification.Group ⧸
      ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom → ℂ)
    (hv : ∀ g, v (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl g)) =
      F.realSquareObservable Γ ε u (QuotientGroup.mk g))
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (hvert : ∀ z ∈ F.squareFiltration.quotientTop.realification.subgroup s, ∀ y,
      f (z • y) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * f y)
    (hne : ∃ y, f y ≠ 0)
    (hpres : ∀ (z : F.squareFiltration.quotientTop.realification.Group) (c : ℂ),
      (∀ y, v (z • y) = c * v y) → ∀ y, f (z • y) = c * f y)
    (x : F.layer (s + 1)) :
    ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
      (F.squareRelativeLayer s hs x).val) = η x := by
  apply F.square_mode_relative_frequency hs _ η ξ f hvert hne
  intro k hk hkzero y
  exact hpres _ _
    (fun z => F.realSquare_descent_relative_character Γ ε u
      (fun a => ((realifyFunctional η a.coord : ℝ) : CircleFourier.Circle))
      hu v hv k hk hkzero z) y

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FilteredSubalgebraCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

omit [Fintype ι] in
theorem real_subalgebra_layer_eq_span (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) (j : ℕ) :
    (realificationLieSubalgebra U).toSubmodule ⊔ (F.realLayer j).toSubmodule =
      Submodule.span ℝ (Set.range (fun z => rationalLieInclusion (subalgebraLayerFamily e v ω j z))) := by
  have hlayer : Submodule.span ℚ (Set.range (fun i => if j ≤ ω i then e i else 0)) = F.layer j :=
    (span_conditional_basis e {i | j ≤ ω i}).trans (hlayers j).symm
  rw [subalgebraLayerFamily, real_span_sum_family,
    real_span_rational_family U.toSubmodule v hv,
    real_span_rational_family (F.layer j) _ hlayer]
  rfl

theorem real_subalgebra_layer_mem_iff_coordinates (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) (j : ℕ) (x : ℝ ⊗[ℚ] L) :
    x ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j ↔
      (e.baseChange ℝ).equivFun x ∈ Submodule.span ℝ
        (Set.range (fun z i => (e.repr (subalgebraLayerFamily e v ω j z) i : ℝ))) := by
  change x ∈ (realificationLieSubalgebra U).toSubmodule.restrictScalars ℚ ⊔
    (F.realLayer j).toSubmodule.restrictScalars ℚ ↔ _
  rw [← Submodule.restrictScalars_sup]
  change x ∈ (realificationLieSubalgebra U).toSubmodule ⊔ (F.realLayer j).toSubmodule ↔ _
  rw [F.real_subalgebra_layer_eq_span e ω hlayers U v hv j]
  exact real_span_family_mem_iff_coordinates e _ x

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedSquareMetric
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]

theorem realSquareObservable_lipschitz (e : Basis ι ℚ L) (b : Basis κ ℚ F.squareLieSubalgebra)
    (Γ : Subgroup F.Group) (l m H : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hSq : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid m)
    (hfst : ∀ k i, RationalHeightLE (e.repr (F.squareFst (b i)) k) H)
    (hsnd : ∀ k i, RationalHeightLE (e.repr (F.squareSnd (b i)) k) H)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (A K B : ℝ≥0)
    (hε : letI := realificationQuotientMetricSpace e Γ l hl hΓ
      LipschitzWith A (fun x : F.realification.Group ⧸ Γ.map realificationHom => ε • x))
    (hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith K u)
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let P := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) H
    letI := realificationQuotientMetricSpace b (F.squareLattice Γ) m hm hSq
    LipschitzWith (B * (K * P) + B * (K * (A * P))) (F.realSquareObservable Γ ε u) := by
  let := realificationQuotientMetricSpace e Γ l hl hΓ
  let := realificationQuotientMetricSpace b (F.squareLattice Γ) m hm hSq
  have hf := lipschitz_realificationMap_quotient b e F.squareFst (F.squareLattice Γ) Γ
    (F.squareLattice_le_fst Γ) m l hm hl hSq hΓ H hfst
  have hg := lipschitz_realificationMap_quotient b e F.squareSnd (F.squareLattice Γ) Γ
    (F.squareLattice_le_snd Γ) m l hm hl hSq hΓ H hsnd
  exact lipschitz_mul_star_of_bounds _ _ (hu.comp (hε.comp hf)) (hu.comp hg)
    (fun x => hb _) (fun x => hb _)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ChosenBasisGeometryBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem basis_geometry_of_forward_height {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (b : Basis ι ℚ L)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) :
    (Fintype.card ι : ℝ) ≤ p ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 4) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 4) ^ 11) := by
  have hdim : (Fintype.card ι : ℝ) ≤ p := by
    rw [← finrank_eq_card_basis b, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (b i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (hb i j)
  have hstructure : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hD.2.2.1 i j k).trans (by linarith))
  have hp2 : 0 ≤ p + 2 := by linarith
  have hdim2 : (Fintype.card ι : ℝ) ≤ p + 2 := hdim.trans (by linarith)
  have hd2 : (Fintype.card (Fin d) : ℝ) ≤ p + 2 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 2 by linarith)
  have hinverse : (rationalSolveHeight (Fintype.card ι) H : ℝ) ≤ Real.exp ((p + 4) ^ 5) := by
    simpa only [show p + 2 + 2 = p + 4 by ring] using
      rationalSolveHeight_le_budget (Fintype.card ι) H hp2 hdim2 hHp
  have hbracket : (rationalLieStructureHeight (Fintype.card (Fin d))
      (max H (rationalSolveHeight (Fintype.card ι) H)) : ℝ) ≤ Real.exp ((p + 4) ^ 11) := by
    simpa only [show p + 2 + 2 = p + 4 by ring] using
      rationalLieStructureHeight_inverse_budget (Fintype.card (Fin d)) (Fintype.card ι) H hp2 hd2 hdim2 hHp
  exact ⟨hdim,
    fun i j => rationalLogHeight_le_of_height (inverse_basis_entries_height D.basis b hH hentries i j) hinverse,
    fun i j k => rationalLogHeight_le_of_height
      (basis_change_structure_height D.basis b hH hentries hstructure i j k) hbracket⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrdinarySymbolBasisDimension
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem homogeneousSymbolLift_mem_pointwise (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule)
    (α : σ →₀ ℕ) (v : F.AssociatedGraded) (hv : v ∈ U) :
    F.homogeneousSymbolLift b ω hlayers w α v ∈ F.symbolPointwiseSubalgebra b ω hlayers w U := by
  classical
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  intro β
  rw [F.gradedSymbolPolynomial_homogeneousSymbolLift, coefficients_monomial]
  by_cases h : α = β
  · subst β
    rw [Finsupp.single_eq_same]
    exact hU (Finsupp.weight w α) v hv
  · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
    exact U.zero_mem

noncomputable def pointwiseSymbolSpanningFamily (v : κ → F.AssociatedGraded) :
    SymbolBasisIndex w ω × κ → F.PolynomialSymbol w :=
  fun z => F.homogeneousSymbolLift b ω hlayers w z.1.val.1 (v z.2)

theorem pointwiseSymbolSpanningFamily_span [Fintype (SymbolBasisIndex w ω)]
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v)) =
      (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply F.homogeneousSymbolLift_mem_pointwise b ω hlayers w U hU
    change v z.2 ∈ U.toSubmodule
    rw [← hspan]
    exact Submodule.subset_span ⟨z.2, rfl⟩
  · intro x hx
    rw [← sum_basisBlockProjection (F.polynomialSymbolBasis b ω hlayers w) (fun z => z.val.1) x]
    apply Submodule.sum_mem
    intro α hα
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hα
    rw [← F.homogeneousSymbolLift_coefficient]
    let W := Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v))
    have hmap : U.toSubmodule ≤ W.comap (F.homogeneousSymbolLift b ω hlayers w z.val.1) := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(z, j), rfl⟩
    exact hmap ((F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U x).mp hx z.val.1)

theorem pointwiseSymbolSpanningFamily_height (v : κ → F.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j) i) H) :
    ∀ z i, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
      (F.pointwiseSymbolSpanningFamily b ω hlayers w v z) i) H := by
  classical
  intro z i
  change RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
    (F.homogeneousSymbolLift b ω hlayers w z.1.val.1 (v z.2)) i) H
  rw [F.homogeneousSymbolLift_coordinate]
  split_ifs
  · exact hv z.2 i.val.2
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

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

theorem associatedGradedBasis_reindex :
    F.associatedGradedBasis (b.reindex e) (fun k => ω (e.symm k)) hF' =
      (F.associatedGradedBasis b ω hF).reindex e := by
  apply DFunLike.ext
  intro k
  rw [Basis.reindex_apply]
  rw [← F.associatedGradedPieceMap_basis (b.reindex e) (fun k => ω (e.symm k)) hF'
      (ω (e.symm k)) k le_rfl rfl,
    ← F.associatedGradedPieceMap_basis b ω hF (ω (e.symm k)) (e.symm k) le_rfl rfl]
  congr 1
  apply Subtype.ext
  exact Basis.reindex_apply b e k

end NilpotentLieFiltration
end Erdos3

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

theorem directionalDerivative_coordinate (f : L →ₗ[ℚ] ℝ) (h : σ → ℚ)
    (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    f (coefficients (directionalDerivative h p) α) =
      ∑ i, (h i : ℝ) * (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1)) := by
  rw [coefficients_directionalDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Rat.smul_def, mul_assoc]

end Erdos3.VectorPolynomial

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

def reindexWeightSurvivors (s : ℕ) (ω : ι → ℕ) (e : ι ≃ κ) :
    QuotientTopBasisIndex s ω ≃ QuotientTopBasisIndex s (fun k => ω (e.symm k)) where
  toFun i := ⟨e i.val, by simpa only [Equiv.symm_apply_apply] using i.property⟩
  invFun i := ⟨e.symm i.val, i.property⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i.val
  right_inv i := by apply Subtype.ext; exact e.apply_symm_apply i.val

end Erdos3.NilpotentLieFiltration

end

end OAI
end


