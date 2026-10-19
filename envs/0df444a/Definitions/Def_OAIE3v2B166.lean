-- Prove2me | Definitions.Def_OAIE3v2B166
-- name    : OAIE3v2B166
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:33:31.400967+00:00
-- url     : https://prove2.me/theorems/45f64c31-9995-4abc-8222-99ab53f69fac
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 168 of 311
-- statement:
--   Definitions bundle 168 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B153`, `OAIE3v2B154` of this split.
--
--   Modules: `Estimates/BiasedSynchronizedSquareFamily.lean`, `Estimates/ExtractedInitialState.lean`, `Estimates/FastCoefficientOperationBounds.lean`, `Estimates/FastHorizontalFactorization.lean`, `Estimates/FirstCoefficientDerivativeBounds.lean`, `Estimates/ReducedProjectedComparison.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Estimates/TerminalControlledFactorization.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Linear/ReducedProjectionBounds.lean`, `Polynomial/PolynomialDerivativeDifferences.lean`, `Sampling/RealAdaptedCoefficientGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B153
import Definitions.Def_OAIE3v2B154

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealAdaptedCoefficientGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedDirectionalDerivative_grid [Fintype σ] (l : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x) (h : σ → ℤ) :
    F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l
      (F.realAdaptedDirectionalDerivative (fun i => (h i : ℚ)) x) := by
  classical
  have hfull := (F.realAdaptedCoefficientGrid_polynomial_iff b ω hF (fun _ => 1) l
    (⟨x⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp hx
  obtain ⟨a, ha⟩ := hfull
  have hcoord (z : AdaptedBasisIndex (fun _ : σ => 1) ω) : ∃ n : ℤ, (n : ℝ) = (l : ℝ) *
      ((F.adaptedMonomialBasis b ω hF (fun _ => 1)).baseChange ℝ).repr
        (F.realAdaptedDirectionalDerivative (fun i => (h i : ℚ)) x) z := by
    rw [← F.realAdaptedPolynomialTensor_coordinates (fun _ => 1) b ω hF,
      F.realAdaptedDirectionalDerivative_polynomial]
    let f := ((b.baseChange ℝ).coord z.val.2).restrictScalars ℚ
    exact directionalDerivative_integral_coordinate f
      (F.realAdaptedPolynomialMap (fun _ => 1) x) l
      (fun β => ⟨a (β, z.val.2), congrFun ha (β, z.val.2)⟩) h z.val.1
  choose a ha using hcoord
  exact ⟨a, funext ha⟩

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

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedProjectedComparison
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem reducedSquareSndSymbolMap_spanning_height (w : σ → ℕ)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w) {H : ℕ}
    (hv : ∀ i z, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) z) H)
    (i : κ) (z : QuotientTopSymbolIndex s w ω) :
    RationalHeightLE ((F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (v i)) z) H := by
  rw [F.reducedSquareSndSymbolMap_repr e ω hF]
  exact hv i _

theorem exists_reduced_projected_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
        (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ i z, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) z) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A B D : F.quotientTop.RealPolynomialSymbolGroup w),
          P.coord ∈ realificationLieSubalgebra U →
          B.coord ∈ realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
          A * B * D = F.reducedSquareRealSymbolHom w (E * P * R) →
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + 2) ^ a)) E →
          F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
            (Real.exp ((p + 2) ^ a)) A →
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
          F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l D →
          (A⁻¹ * F.reducedSquareRealSymbolHom w E).coord ∈
            realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) ∧
          (F.reducedSquareRealSymbolHom w R * D⁻¹).coord ∈
            realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) ∧
          F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (A⁻¹ * F.reducedSquareRealSymbolHom w E) ∧
          F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w m
            (F.reducedSquareRealSymbolHom w R * D⁻¹) := by
  have hcomparisonExists := exists_bounded_symbol_comparison s a
  obtain ⟨C, hC, hcomparison⟩ := hcomparisonExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hc hv
  have hdim : (Fintype.card (QuotientTopBasisIndex s ω) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hι
  have hdata := hcomparison F.quotientTop (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w hw
    (U.map (F.reducedSquareSndSymbolMap w)) (fun i => F.reducedSquareSndSymbolMap w (v i))
    (F.reducedSquareSndSymbolMap_span w U v hspan) H l p hH hl hp hdim hσ hκ hHp hlp
    (F.quotientTopBasis_structure_height e ω hF hc)
    (F.reducedSquareSndSymbolMap_spanning_height e ω hF w v hv)
  obtain ⟨m, hm, hmp, hlm, hcompare⟩ := hdata
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro T hT E P R A B D hP hB heq hE hA hR hD
  exact hcompare T hT A B D (F.reducedSquareRealSymbolHom w E)
    (F.reducedSquareRealSymbolHom w P) (F.reducedSquareRealSymbolHom w R)
    hB (F.reducedSquareRealSymbolHom_fast w U P hP)
    (by simpa only [map_mul] using heq) hA (F.reducedSquareRealSymbolHom_slow e ω hF w T _ E hE)
    hD (F.reducedSquareRealSymbolHom_grid e ω hF w l R hR)

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

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem realNormalizedFirstCoefficientMap_adjoint (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w (F.realNormalizedRelativeAdjoint w g x) =
      F.realFirstCoefficientAdjoint w g (F.realNormalizedFirstCoefficientMap w x) := by
  rw [F.realNormalizedFirstCoefficientMap_eq, F.realNormalizedFirstCoefficientMap_eq,
    F.realFirstCoefficientAdjoint_map]
  apply congrArg (F.realFirstCoefficientMap w)
  apply Subtype.ext
  rw [F.realNormalizedRelativeInFirst_coe, F.realNormalizedRelativeAdjoint_inclusion]
  exact congrArg (dualAdjoint g) (F.realNormalizedRelativeInFirst_coe w x).symm

theorem realFirstCoefficientAdjoint_fast_mem (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (y : F.RealFirstCoefficientModule w)
    (hy : y ∈ F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)) :
    F.realFirstCoefficientAdjoint w g y ∈
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) := by
  have hr : y ∈ LinearMap.range (F.realNormalizedFirstCoefficientMap w) := by
    rw [F.realNormalizedFirstCoefficientMap_range]
    exact F.realFirstCoefficientFastSubmodule_le_horizontal_ker w hw _ hy
  obtain ⟨x, rfl⟩ := hr
  rw [← F.realNormalizedFirstCoefficientMap_adjoint, F.realNormalizedFirstCoefficientMap_mem_fast_iff]
  rw [F.realReducedRelativeSquareSymbolMap_adjoint]
  apply F.reducedSquareRealFastRelative_adjoint_mem w U hw _ hg
  exact (F.realNormalizedFirstCoefficientMap_mem_fast_iff w hw _ x).mp hy

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem realFirstCoefficientAdjoint_fast_map (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)) :
    (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).map
        (F.realFirstCoefficientAdjoint w g).toLinearMap =
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact F.realFirstCoefficientAdjoint_fast_mem w hw U g hg x hx
  · intro y hy
    have hgi : (F.adaptedReducedRealSymbolHom w g⁻¹).coord ∈
        realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U) := by
      rw [map_inv, coord_inv]
      exact (realificationLieSubalgebra _).neg_mem hg
    exact ⟨F.realFirstCoefficientAdjoint w g⁻¹ y,
      F.realFirstCoefficientAdjoint_fast_mem w hw U g⁻¹ hgi y hy,
      F.realFirstCoefficientAdjoint_cancel_inv w g y⟩

noncomputable def realFastCoefficientAdjoint (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)) :
    (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)) ≃ₗ[ℝ]
    (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)) :=
  Submodule.Quotient.equiv _ _ (F.realFirstCoefficientAdjoint w g)
    (F.realFirstCoefficientAdjoint_fast_map w hw U g hg)

theorem realFastCoefficientAdjoint_mk (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (x : F.RealFirstCoefficientModule w) :
    F.realFastCoefficientAdjoint w hw U g hg
        ((F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) =
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
        (F.realFirstCoefficientAdjoint w g x) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFastCoefficientAdjoint_one
    (h1 : (F.adaptedReducedRealSymbolHom w 1).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (x : F.RealFastCoefficientModule w hw U) :
    F.realFastCoefficientAdjoint w hw U 1 h1 x = x := by
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw
    (F.reducedSquareFastRelativeSubmodule w U)).mkQ_surjective x
  rw [F.realFastCoefficientAdjoint_mk]
  congr 1
  apply (F.realFirstCoefficientAdjoint w 1).injective
  have h := F.realFirstCoefficientAdjoint_mul w 1 1 x
  simpa only [one_mul] using h.symm

theorem realFastCoefficientAdjoint_mul
    (g h : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (hh : (F.adaptedReducedRealSymbolHom w h).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (hgh : (F.adaptedReducedRealSymbolHom w (g * h)).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (x : F.RealFastCoefficientModule w hw U) :
    F.realFastCoefficientAdjoint w hw U (g * h) hgh x =
      F.realFastCoefficientAdjoint w hw U g hg (F.realFastCoefficientAdjoint w hw U h hh x) := by
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw
    (F.reducedSquareFastRelativeSubmodule w U)).mkQ_surjective x
  change (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
    (F.realFirstCoefficientAdjoint w (g * h) x) =
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
        (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientAdjoint w h x))
  exact congrArg (F.realFirstCoefficientFastSubmodule w hw
    (F.reducedSquareFastRelativeSubmodule w U)).mkQ (F.realFirstCoefficientAdjoint_mul w g h x)

noncomputable def realFastCoefficientAction :
    F.realFastDiagonalSubgroup w U →*
      (F.RealFastCoefficientModule w hw U ≃ₗ[ℝ] F.RealFastCoefficientModule w hw U) where
  toFun g := F.realFastCoefficientAdjoint w hw U g.val g.property
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact F.realFastCoefficientAdjoint_one w hw U _ x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact F.realFastCoefficientAdjoint_mul w hw U g.val h.val g.property h.property _ x

theorem realFastCoefficientAction_mk (g : F.realFastDiagonalSubgroup w U)
    (x : F.RealFirstCoefficientModule w) :
    F.realFastCoefficientAction w hw U g
      ((F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) =
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
        (F.realFirstCoefficientAdjoint w g.val x) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
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

theorem symbolPointwiseSubalgebra_mono {U V : LieSubalgebra ℚ F.AssociatedGraded} (hUV : U ≤ V) :
    F.symbolPointwiseSubalgebra e ω hF w U ≤ F.symbolPointwiseSubalgebra e ω hF w V := by
  intro x hx
  exact fun α => hUV ((F.mem_symbolPointwiseSubalgebra_iff e ω hF w U x).mp hx α)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientOperationBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis κ ℝ (F.RealFastCoefficientModule w hw U))
  (R : (κ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)

local notation "π" => Submodule.mkQ
  (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U))

variable (hR : ∀ y,
  (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) =
    b.equivFun.symm y)

include hR

theorem fastCoefficientAdjoint_weighted_bound
    (rows : κ → FirstCoefficientIndex w ω) (T : σ → ℝ)
    (Cproj Clift D : ℝ) (hClift : 0 ≤ Clift) (hD : 0 ≤ D)
    (hproj : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      ∀ i, |b.equivFun (π x) i| ≤ Cproj * M / monomialScale T (rows i).val.1)
    (hlift : ∀ M, 0 ≤ M → ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
      F.FirstCoefficientSlowBound e ω hF w T (Clift * M) (R y))
    (g : F.realFastDiagonalSubgroup w U)
    (had : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      F.FirstCoefficientSlowBound e ω hF w T (D * M) (F.realFirstCoefficientAdjoint w g.val x))
    {M : ℝ} (hM : 0 ≤ M) (y : F.RealFastCoefficientModule w hw U)
    (hy : ∀ i, |b.equivFun y i| ≤ M / monomialScale T (rows i).val.1) :
    ∀ i, |b.equivFun (F.realFastCoefficientAction w hw U g y) i| ≤
      Cproj * D * Clift * M / monomialScale T (rows i).val.1 := by
  let x := R (b.equivFun y)
  have hx : π x = y := (hR (b.equivFun y)).trans (b.equivFun.symm_apply_apply y)
  have hbound := hproj (D * (Clift * M)) (mul_nonneg hD (mul_nonneg hClift hM))
    (F.realFirstCoefficientAdjoint w g.val x)
    (had (Clift * M) (mul_nonneg hClift hM) x (hlift M hM (b.equivFun y) hy))
  have he : F.realFastCoefficientAction w hw U g y = π (F.realFirstCoefficientAdjoint w g.val x) := by
    calc
      _ = F.realFastCoefficientAction w hw U g (π x) := congrArg _ hx.symm
      _ = _ := F.realFastCoefficientAction_mk w hw U g x
  intro i
  rw [he]
  convert hbound i using 1
  ring

theorem fastCoefficientAdjoint_grid (g : F.realFastDiagonalSubgroup w U) (l m n q : ℕ)
    (hlift : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (R y))
    (had : ∀ x, F.FirstCoefficientGrid e ω hF w m x →
      F.FirstCoefficientGrid e ω hF w n (F.realFirstCoefficientAdjoint w g.val x))
    (hproj : ∀ x, F.FirstCoefficientGrid e ω hF w n x → b.equivFun (π x) ∈ realDenominatorGrid q)
    (y : F.RealFastCoefficientModule w hw U) (hy : b.equivFun y ∈ realDenominatorGrid l) :
    b.equivFun (F.realFastCoefficientAction w hw U g y) ∈ realDenominatorGrid q := by
  let x := R (b.equivFun y)
  have hx : π x = y := (hR (b.equivFun y)).trans (b.equivFun.symm_apply_apply y)
  have hout := hproj _ (had x (hlift _ hy))
  have he : F.realFastCoefficientAction w hw U g y = π (F.realFirstCoefficientAdjoint w g.val x) := by
    calc
      _ = F.realFastCoefficientAction w hw U g (π x) := congrArg _ hx.symm
      _ = _ := F.realFastCoefficientAction_mk w hw U g x
  rw [he]
  exact hout

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastHorizontalFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

theorem realFastCoefficientAction_symm {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.realFastDiagonalSubgroup w U) (x : F.RealFastCoefficientModule w hw U) :
    (F.realFastCoefficientAction w hw U g).symm x = F.realFastCoefficientAction w hw U g⁻¹ x :=
  congrArg (fun A : F.RealFastCoefficientModule w hw U ≃ₗ[ℝ] F.RealFastCoefficientModule w hw U => A x)
    (map_inv (F.realFastCoefficientAction w hw U) g).symm

theorem fastCoefficientAdjoint_norm_bound {σ ι κ L : Type*}
    [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (b : Basis κ ℝ (F.RealFastCoefficientModule w hw U))
    (R : (κ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw
      (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y)
    (rows : κ → FirstCoefficientIndex w ω) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (Cproj Clift D : ℝ) (hCproj : 0 ≤ Cproj) (hClift : 0 ≤ Clift) (hD : 0 ≤ D)
    (hproj : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      ∀ i, |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
        (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
          Cproj * M / monomialScale T (rows i).val.1)
    (hlift : ∀ M, 0 ≤ M → ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
      F.FirstCoefficientSlowBound e ω hF w T (Clift * M) (R y))
    (g : F.realFastDiagonalSubgroup w U)
    (had : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      F.FirstCoefficientSlowBound e ω hF w T (D * M) (F.realFirstCoefficientAdjoint w g.val x))
    (x : F.RealFastCoefficientModule w hw U) :
    ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
        (F.realFastCoefficientAction w hw U g x)‖ ≤
      (Cproj * D * Clift) * ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) x‖ := by
  apply basisWeightedCoordinates_operator_bound b (fun i => monomialScale T (rows i).val.1)
    (fun i => monomialScale_pos T hT _) (F.realFastCoefficientAction w hw U g).toLinearMap
    (Cproj * D * Clift) (mul_nonneg (mul_nonneg hCproj hD) hClift)
  intro M hM y hy
  exact F.fastCoefficientAdjoint_weighted_bound e ω hF w hw U b R hR rows T
    Cproj Clift D hClift hD hproj hlift g had hM y hy

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def gradedLayerOneProjection : F.AssociatedGraded →ₗ[ℚ] (L ⧸ F.layer 2) :=
  (F.layer 2).mkQ.comp
    (e.repr.symm.toLinearMap.comp (F.associatedGradedBasis e ω hF).repr.toLinearMap)

theorem gradedLayerOneProjection_coordinate (x : F.AssociatedGraded) (i : LayerOneBasisIndex ω) :
    (F.layerOneBasis e ω hF).repr (F.gradedLayerOneProjection e ω hF x) i =
      (F.associatedGradedBasis e ω hF).repr x i.val := by
  change (F.layerOneBasis e ω hF).repr
    ((F.layer 2).mkQ (e.repr.symm ((F.associatedGradedBasis e ω hF).repr x))) i = _
  rw [F.layerOneBasis_repr_mk, LinearEquiv.apply_symm_apply]

theorem layerOneGradedMap_coordinate (x : L ⧸ F.layer 2) (i : LayerOneBasisIndex ω) :
    (F.associatedGradedBasis e ω hF).repr (F.layerOneGradedMap e ω hF x) i.val =
      (F.layerOneBasis e ω hF).repr x i := by
  obtain ⟨v, rfl⟩ := (F.layer 2).mkQ_surjective x
  rw [F.layerOneGradedMap_mk, F.gradedPieceProjection_coordinate, F.layerOneBasis_repr_mk]
  have hpos := F.adaptedBasis_weight_pos e ω hF i.val
  have hnot := i.property
  rw [if_pos (show ω i.val = 1 by omega)]

theorem gradedLayerOneProjection_rightInverse (x : L ⧸ F.layer 2) :
    F.gradedLayerOneProjection e ω hF (F.layerOneGradedMap e ω hF x) = x := by
  apply (F.layerOneBasis e ω hF).repr.injective
  ext i
  rw [F.gradedLayerOneProjection_coordinate, F.layerOneGradedMap_coordinate]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem layerOneGradedMap_injective : Function.Injective (F.layerOneGradedMap e ω hF) := by
  intro x y hxy
  have h := congrArg (F.gradedLayerOneProjection e ω hF) hxy
  simpa only [F.gradedLayerOneProjection_rightInverse] using h

noncomputable def gradedHorizontalKernel (K : Submodule ℚ (L ⧸ F.layer 2)) :
    Submodule ℚ F.AssociatedGraded := K.map (F.layerOneGradedMap e ω hF)

noncomputable def gradedHorizontalKernelEquiv (K : Submodule ℚ (L ⧸ F.layer 2)) :
    K ≃ₗ[ℚ] F.gradedHorizontalKernel e ω hF K :=
  Submodule.equivMapOfInjective (F.layerOneGradedMap e ω hF) (F.layerOneGradedMap_injective e ω hF) K

noncomputable def gradedHorizontalKernelBasis (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K) :
    Basis κ ℚ (F.gradedHorizontalKernel e ω hF K) := b.map (F.gradedHorizontalKernelEquiv e ω hF K)

theorem gradedHorizontalKernelBasis_coe (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K) (i : κ) :
    (F.gradedHorizontalKernelBasis e ω hF K b i : F.AssociatedGraded) =
      F.layerOneGradedMap e ω hF (b i : L ⧸ F.layer 2) := by
  rw [gradedHorizontalKernelBasis, Basis.map_apply]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExtractedInitialState
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_fastCoefficient_rational_removal_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
      (b : Basis κ ℝ (F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U))
      (R : (κ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1)),
      (∀ y, (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ (R y) = b.equivFun.symm y) →
      ∀ l L₀ dproj : ℕ, 0 < L₀ → (L₀ : ℝ) ≤ Real.exp p →
      0 < dproj → (dproj : ℝ) ≤ Real.exp p →
      (∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF (fun _ => 1) L₀ (R y)) →
      (∀ m x, F.FirstCoefficientGrid e ω hF (fun _ => 1) m x →
        b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈
            realDenominatorGrid (dproj * m)) →
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : F.realFastDiagonalSubgroup (fun _ : σ => 1) U,
          F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) L₀ g.val.coord →
          (∀ x, b.equivFun x ∈ realDenominatorGrid l →
            b.equivFun (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U g x) ∈
              realDenominatorGrid q) ∧
          (∀ h : σ → ℤ, b.equivFun (F.realFastCoefficientDirectionMap U g.val (fun i => (h i : ℝ))) ∈
            realDenominatorGrid q) ∧
          ∀ x, b.equivFun x ∈ realDenominatorGrid l → ∀ h : σ → ℤ,
            b.equivFun (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U g x -
              F.realFastCoefficientDirectionMap U g.val (fun i => (h i : ℝ))) ∈ realDenominatorGrid q := by
  have hex := exists_firstCoefficient_operation_grid (s + 1)
  obtain ⟨D, _, hfirst⟩ := hex
  let B : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF H p hH hp hι hσ hHp hc U b R hR
    l L₀ dproj hL hLp hd hdP hlift hproj
  have hdata := hfirst F e ω hF H p hH hp hι hσ hHp hc L₀ hL hLp
  obtain ⟨m, hm, hmp, _, had, hlog⟩ := hdata
  have hfinal : p + (p + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  have hq : ((dproj * m : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp ((p + D) ^ D) :=
        mul_le_mul hdP hmp (Nat.cast_nonneg m) (Real.exp_nonneg p)
      _ = Real.exp (p + (p + D) ^ D) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hfinal
  refine ⟨dproj * m, Nat.mul_pos hd hm, hq, ?_⟩
  intro g hg
  have haction : ∀ x, b.equivFun x ∈ realDenominatorGrid l →
      b.equivFun (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U g x) ∈
        realDenominatorGrid (dproj * m) := by
    intro x hx
    exact F.fastCoefficientAdjoint_grid e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
      U b R hR g l L₀ m (dproj * m) hlift (fun y hy => had g.val y hg hy) (hproj m) x hx
  have hderivative : ∀ h : σ → ℤ,
      b.equivFun (F.realFastCoefficientDirectionMap U g.val (fun i => (h i : ℝ))) ∈
        realDenominatorGrid (dproj * m) := by
    intro h
    exact hproj m _ (hlog g.val.coord hg h)
  refine ⟨haction, hderivative, ?_⟩
  intro x hx h
  rw [map_sub]
  exact realDenominatorGrid_sub (dproj * m) _ _ (haction x hx) (hderivative h)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_fastCoefficient_slow_removal_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
      (b : Basis κ ℝ (F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U))
      (R : (κ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1)),
      (∀ y, (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ (R y) = b.equivFun.symm y) →
      ∀ (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω) (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp p →
      (∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
        ∀ i, |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
            K * M / monomialScale T (rows i).val.1) →
      (∀ M, 0 ≤ M → ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (K * M) (R y)) →
      let N := basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
      let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
      let Y := fun (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) i =>
        F.realFastCoefficientDirectionMap U g.val (Pi.single i 1)
      ∀ g : F.realFastDiagonalSubgroup (fun _ : σ => 1) U,
        F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp ((p + 2) ^ a)) g.val.coord →
        (∀ x, ‖N ((ρ g).symm x)‖ ≤ Real.exp ((p + C) ^ C) * ‖N x‖) ∧
        (∀ i, ‖N (Y g i)‖ ≤ Real.exp ((p + C) ^ C) / T i) ∧
        ∀ (M : ℝ) (small : σ → F.RealFastCoefficientModule (fun _ => 1) (fun _ => Nat.zero_lt_one) U),
          (∀ i, ‖N (small i)‖ ≤ M / T i) →
          ∀ i, ‖N ((ρ g).symm (small i - Y g i))‖ ≤
            Real.exp ((p + C) ^ C) * (M + Real.exp ((p + C) ^ C)) / T i := by
  have hexA := exists_firstCoefficient_adjoint_bound (s + 1) a
  obtain ⟨cA, _, hA⟩ := hexA
  have hexD := exists_firstCoefficient_coordinate_derivative_bound (s + 1) a
  obtain ⟨cD, _, hD⟩ := hexD
  have hfactorBudget := exists_fast_removal_factor_budget s a cA cD
  obtain ⟨C, hC, hbudget⟩ := hfactorBudget
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ _ F e ω hF H p hH hp hι hσ hHp hc U b R hR rows T hT K hK hKp
    hproj hlift N ρ Y g hg
  obtain ⟨hAfactor, hDfactor⟩ := hbudget p hp K hK hKp
  have hginv := F.realAdaptedCoefficientBound_inv e ω hF (fun _ => 1) T
    (Real.exp ((p + 2) ^ a)) g.val hg
  have had := hA F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H p hH hp hι hσ hHp hc T hT (g⁻¹).val hginv
  have haction : ∀ x, ‖N ((ρ g).symm x)‖ ≤ Real.exp ((p + C) ^ C) * ‖N x‖ := by
    intro x
    have he := F.realFastCoefficientAction_symm (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U g x
    have hb := F.fastCoefficientAdjoint_norm_bound e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
      U b R hR rows T hT K K (Real.exp ((p + cA) ^ cA)) hK hK (Real.exp_nonneg _) hproj hlift
      g⁻¹ had x
    exact (congrArg (fun y => ‖N y‖) he).le.trans
      (hb.trans (mul_le_mul_of_nonneg_right hAfactor (norm_nonneg _)))
  have hfirst := hD F e ω hF H p hH hp hι hσ hHp hc T hT g.val.coord hg
  have hderivative : ∀ i, ‖N (Y g i)‖ ≤ Real.exp ((p + C) ^ C) / T i := by
    intro i
    have hb := F.fastCoefficientDirection_norm_bound e ω hF U b rows T hT K
      (Real.exp ((p + cD) ^ cD) * ((s + 1 : ℕ) * Real.exp ((p + 2) ^ a))) hK (by positivity)
      hproj g.val (fun j => by simpa only [mul_div_assoc] using hfirst j) i
    exact hb.trans (div_le_div_of_nonneg_right hDfactor (hT i).le)
  refine ⟨haction, hderivative, ?_⟩
  intro M small hsmall i
  exact norm_removed_derivative_bound N (ρ g).symm.toLinearMap (small i) (Y g i)
    (Real.exp ((p + C) ^ C)) M (Real.exp ((p + C) ^ C)) (T i)
    (Real.exp_nonneg _) (hT i) haction (hsmall i) (hderivative i)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TerminalControlledFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "bG" => F.associatedGradedBasis e ω hF
local notation "FG" => F.associatedGradedFiltration
local notation "U" => F.fullFastGradedDiagonal W
local notation "PG" => PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot

def FastTerminalFactorization (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (T : σ → ℝ) (original : PG) (p : ℝ) : Prop :=
  ∃ Z : LieSubalgebra ℚ F.AssociatedGraded, BasisGradedSubmodule bG ω Z.toSubmodule ∧
    (∀ x ∈ Z, η (basisGradeProjection bG ω (s + 1) x) = 0) ∧
    ∃ bZ : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
      (∀ i j, (((bG).repr (bZ i : F.AssociatedGraded) j).num.natAbs : ℝ) ≤ Real.exp p ∧
        (((bG).repr (bZ i : F.AssociatedGraded) j).den : ℝ) ≤ Real.exp p) ∧
      ∃ A P B : PG, A * P * B = original ∧
        (FG).FormalCorrectionProperty bG ω (realificationLieSubalgebra U) A ∧
        (FG).FormalCorrectionProperty bG ω (realificationLieSubalgebra U) B ∧
        coefficients P.coord 0 = 0 ∧
        P.coord ∈ gradedPolynomialSubmodule ((bG).baseChange ℝ) ω (fun _ : σ => 1) ∧
        (∀ α, coefficients P.coord α ∈ realificationLieSubalgebra Z) ∧
        CoefficientBound ((bG).baseChange ℝ) T (Real.exp p) A.coord ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ CoefficientGrid ((bG).baseChange ℝ) m B.coord

omit [Fintype σ] [Fintype ι] in
theorem FastTerminalFactorization.mono
    {η : F.AssociatedGraded →ₗ[ℚ] ℚ} {T : σ → ℝ} {original : PG} {p q : ℝ}
    (h : F.FastTerminalFactorization e ω hF W η T original p)
    (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.FastTerminalFactorization e ω hF W η T original q := by
  obtain ⟨Z, hZ, hη, bZ, hbZ, A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff,
    hbound, m, hm, hmp, hgrid⟩ := h
  have hepq := Real.exp_le_exp.mpr hpq
  exact ⟨Z, hZ, hη, bZ, fun i j => ⟨(hbZ i j).1.trans hepq, (hbZ i j).2.trans hepq⟩,
    A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff, hbound.mono _ T hT hepq,
    m, hm, hmp.trans hepq, hgrid⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedSynchronizedSquareFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem symbolFastIn_reducedSquareRealSymbolHom {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolFastIn w U g) :
    F.quotientTop.SymbolFastIn w (U.map (F.reducedSquareSndSymbolMap w))
      (F.reducedSquareRealSymbolHom w g) := F.reducedSquareRealSymbolHom_fast w U g hg

end Erdos3.NilpotentLieFiltration

end

end OAI
end


