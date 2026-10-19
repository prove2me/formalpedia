-- Prove2me | Definitions.Def_OAIE3v2B185
-- name    : OAIE3v2B185
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:54:22.346273+00:00
-- url     : https://prove2.me/theorems/943e8c3f-af38-4129-85ef-d6c35ad79d04
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 188 of 311
-- statement:
--   Definitions bundle 188 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B163`, `OAIE3v2B164`, `OAIE3v2B165`, `OAIE3v2B166`, `OAIE3v2B167`, `OAIE3v2B168`, `OAIE3v2B169`, `OAIE3v2B170` of this split.
--
--   Modules: `Estimates/BiasedSynchronizedSquareFamily.lean`, `Estimates/CommonNativeSquareFactors.lean`, `Estimates/FirstCoefficientDerivativeBounds.lean`, `Estimates/MixedFixedReduction.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/NativeDilationDescent.lean`, `Estimates/NativeMultilinearityCorrelation.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/NormalizedCommonFamily.lean`, `Estimates/RealReducedCoefficientMap.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/TerminalControlledFactorization.lean`, `Estimates/UnnormalizedCommonSymbolFactorization.lean`, `Lattices/NativeIntegerHalving.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Nilpotent/StepOneGradedNiltestSplitting.lean`, `Polynomial/FirstCoefficientPolynomialDerivative.lean`, `Polynomial/FormalPolynomialOperationBounds.lean`, `Polynomial/GradedPolynomialSymbolInverse.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B163
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B165
import Definitions.Def_OAIE3v2B166
import Definitions.Def_OAIE3v2B167
import Definitions.Def_OAIE3v2B168
import Definitions.Def_OAIE3v2B169
import Definitions.Def_OAIE3v2B170

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

variable [Fintype σ]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem realReducedRelativeCoefficient_triple
    (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (a b : F.RealAdaptedPolynomialGroup w)
    (ha : F.adaptedReducedRealSymbolHom w a = F.reducedSquareRealSymbolHom w E)
    (hb : F.adaptedReducedRealSymbolHom w b = F.reducedSquareRealSymbolHom w P) :
    F.realReducedRelativeCoefficient w hw (E * P * R) =
      F.realReducedRelativeCoefficient w hw E +
        F.realFirstCoefficientAdjoint w a (F.realReducedRelativeCoefficient w hw P) +
        F.realFirstCoefficientAdjoint w (a * b) (F.realReducedRelativeCoefficient w hw R) := by
  have hE := F.reducedSquareRealRelativePart_exists_preimage w hw E
  have hP := F.reducedSquareRealRelativePart_exists_preimage w hw P
  have hR := F.reducedSquareRealRelativePart_exists_preimage w hw R
  obtain ⟨x, hx⟩ := hE
  obtain ⟨y, hy⟩ := hP
  obtain ⟨z, hz⟩ := hR
  have hp := F.realReducedRelativeSquareSymbolMap_triple_preimage w hw E P R a b ha hb x y z hx hy hz
  have hc := F.realReducedRelativeCoefficient_of_preimage w hw (E * P * R) _ hp
  rw [map_add, map_add, F.realNormalizedFirstCoefficientMap_adjoint,
    F.realNormalizedFirstCoefficientMap_adjoint,
    F.realReducedRelativeCoefficient_of_preimage w hw E x hx,
    F.realReducedRelativeCoefficient_of_preimage w hw P y hy,
    F.realReducedRelativeCoefficient_of_preimage w hw R z hz] at hc
  exact hc.symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

variable [Fintype σ] {ι : Type*} (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFirstCoefficient_common_derivative (h : σ → ℚ)
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (ε μ u Z v : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hsquare : F.realFirstCoefficientDirectionMap (A * B * D).coord (fun i => (h i : ℝ)) - ε -
      F.realFirstCoefficientAdjoint (fun _ => 1) (A * B * D) μ =
        u + F.realFirstCoefficientAdjoint (fun _ => 1) A Z +
          F.realFirstCoefficientAdjoint (fun _ => 1) (A * B) v) :
    F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) =
      F.realFirstCoefficientAdjoint (fun _ => 1) A⁻¹
        (ε + u - F.realFirstCoefficientDirectionMap A.coord (fun i => (h i : ℝ))) +
      F.realFirstCoefficientAdjoint (fun _ => 1) B
        (v + F.realFirstCoefficientAdjoint (fun _ => 1) D μ -
          F.realFirstCoefficientDirectionMap D.coord (fun i => (h i : ℝ))) + Z :=
  F.coefficient_common_derivative_identity (fun _ => 1) A B D _ _ _ _ ε μ u Z v
    (F.realFirstCoefficientDirectionMap_triple_rat e ω hF h A B D) hsquare

theorem realFirstCoefficient_common_mod_fast (h : σ → ℚ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (ε μ u Z v ZB : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hsquare : F.realFirstCoefficientDirectionMap (A * B * D).coord (fun i => (h i : ℝ)) - ε -
      F.realFirstCoefficientAdjoint (fun _ => 1) (A * B * D) μ =
        u + F.realFirstCoefficientAdjoint (fun _ => 1) A Z +
          F.realFirstCoefficientAdjoint (fun _ => 1) (A * B) v)
    (hZ : Z - ZB ∈ F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)) :
    F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (F.realFirstCoefficientAdjoint (fun _ => 1) A⁻¹
        (ε + u - F.realFirstCoefficientDirectionMap A.coord (fun i => (h i : ℝ))) +
      F.realFirstCoefficientAdjoint (fun _ => 1) B
        (v + F.realFirstCoefficientAdjoint (fun _ => 1) D μ -
          F.realFirstCoefficientDirectionMap D.coord (fun i => (h i : ℝ))) + ZB) ∈
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) := by
  rw [F.realFirstCoefficient_common_derivative e ω hF h A B D ε μ u Z v hsquare]
  convert hZ using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem synchronized_coefficient_common_derivative {ι : Type*}
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (h : σ → ℚ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (E P R P₀ : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (ε μ : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hA : F.adaptedReducedRealSymbolHom (fun _ => 1) A = F.reducedSquareRealSymbolHom (fun _ => 1) E)
    (hB : F.adaptedReducedRealSymbolHom (fun _ => 1) B = F.reducedSquareRealSymbolHom (fun _ => 1) P)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP₀ : P₀.coord ∈ realificationLieSubalgebra U)
    (hdiag : F.reducedSquareRealSymbolHom (fun _ => 1) P = F.reducedSquareRealSymbolHom (fun _ => 1) P₀)
    (hrelative : F.realFirstCoefficientDirectionMap (A * B * D).coord (fun i => (h i : ℝ)) - ε -
      F.realFirstCoefficientAdjoint (fun _ => 1) (A * B * D) μ =
        F.realReducedRelativeCoefficient (fun _ => 1) (by simp) (E * P * R)) :
    F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) ε
          (F.realReducedRelativeCoefficient (fun _ => 1) (by simp) E) +
        F.realFirstCoefficientAdjoint (fun _ => 1) B
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) μ
            (F.realReducedRelativeCoefficient (fun _ => 1) (by simp) R)) +
        F.realReducedRelativeCoefficient (fun _ => 1) (by simp) P₀) ∈
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) := by
  exact F.realFirstCoefficient_common_mod_fast e ω hF h U A B D ε μ _ _ _ _
    (hrelative.trans (F.realReducedRelativeCoefficient_triple (fun _ => 1) (by simp) E P R A B hA hB))
    (F.realReducedRelativeCoefficient_same_diagonal (fun _ => 1) (by simp) U hP hP₀ hdiag)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

theorem exists_firstCoefficient_direction_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
      F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp ((p + 2) ^ a)) g.coord →
      ∀ h : σ → ℤ, (∀ i, |(h i : ℝ)| ≤ T i) →
      F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
        (F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_real_adapted_log_derivative_bound s a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure T hT g hg h hh
  have hd := hbound F e ω hF H p hH hp hι hσ hHp hstructure T hT g.coord hg
    (fun i => (h i : ℚ)) (by simpa only [Rat.cast_intCast] using hh)
  have he := F.realFirstCoefficientDirectionMap_rat g.coord (fun i => (h i : ℚ))
  simp only [Rat.cast_intCast] at he
  rw [he]
  exact F.firstCoefficientSlowBound_map e ω hF (fun _ => 1) T _ _ hd

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

universe uσ uι uL

theorem exists_reducedRelativeCoefficient_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ReducedRelativeCoefficientSpec.{uσ, uι, uL} s C := by
  obtain ⟨a, _, hslow⟩ := exists_symbol_slow_mul_inv_bound.{uσ, uι, uL} s
  obtain ⟨b, _, hgrid⟩ := exists_symbol_rational_product_bound.{uσ, uι, uL} s 2
  obtain ⟨C, hC, hbudget⟩ := exists_reducedRelative_budget s a b
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  classical
  let w : σ → ℕ := fun _ => 1
  have hw : ∀ i, 0 < w i := fun _ => Nat.zero_lt_one
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let : Fintype (FirstCoefficientIndex w ω) :=
    firstCoefficientIndexFintype w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF)
  let G := F.squareFiltration.quotientTop
  let f := F.reducedSquareBasis e ω hF
  let ν : ReducedSquareBasisIndex s ω → ℕ := fun i => squareBasisWeight ω i.val
  have hG := F.reducedSquareBasis_layers e ω hF
  have hc := F.reducedSquareBasis_structure_height e ω hF hH hstructure
  let d : ℝ := (p + (s + 2)) ^ (s + 2)
  let q := reducedRelativeParameter s p
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq := (reducedRelativeParameter_controls s hp).1
  have hpq := (reducedRelativeParameter_controls s hp).2.1
  have hdim : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ q := by
    have hcard : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
      (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
    have hh := Nat.cast_le (α := ℝ).mpr hcard
    rw [Nat.cast_mul, Nat.cast_ofNat] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hι (by norm_num)).trans
      (reducedRelativeParameter_controls s hp).2.2.1)
  have hquot : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ d :=
    (Nat.cast_le.mpr (F.quotientTopSymbolIndex_card_le e ω hF w hw)).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hsquare : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ 2 * d := by
    have hh := Nat.cast_le (α := ℝ).mpr (F.reducedSquareSymbolIndex_card_le e ω hF w hw)
    rw [Nat.cast_mul, Nat.cast_ofNat] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ) (by norm_num))
  have hHpq := hHp.trans (Real.exp_le_exp.mpr hpq)
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hgrid G f ν hG w hw H q hH hq hdim
    (hσ.trans hpq) hHpq hc l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr (hbudget p hp).2), hlm, ?_⟩
  intro T hT E R hE hR
  constructor
  · have hdiag := F.reducedSquareRealDiagonalHom_slow e ω hF w T hT (Real.exp p)
      (Real.exp_nonneg _) _ (F.reducedSquareRealSymbolHom_slow e ω hF w T (Real.exp p) E hE)
    have hdiagSize : ((Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) + 1) * 2 * Real.exp p ≤
        Real.exp (q + 2) := by
      have hexp : 2 * d + 2 ≤ Real.exp (2 * d + 2) := by linarith [Real.add_one_le_exp (2 * d + 2)]
      calc
        _ ≤ Real.exp (2 * d + 2) * Real.exp p :=
          mul_le_mul_of_nonneg_right ((by linarith :
            ((Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) + 1) * 2 ≤ 2 * d + 2).trans hexp)
            (Real.exp_nonneg _)
        _ = Real.exp (p + 2 * d + 2) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (reducedRelativeParameter_controls s hp).2.2.2
    have hE' := G.symbolSlowBound_mono f ν hG w T hT
      (Real.exp_le_exp.mpr (show p ≤ q + 2 by linarith)) E hE
    have hdiag' := G.symbolSlowBound_mono f ν hG w T hT hdiagSize _ hdiag
    have hrelative := hslow G f ν hG w hw H q hH hq hdim (hσ.trans hpq) hHpq hc T hT E _ hE' hdiag'
    have hextract := F.realReducedSquareCoefficientMap_slow e ω hF w T hT
      (Real.exp ((q + a) ^ a)) (Real.exp_nonneg _) (F.reducedSquareRealRelativePart w E) hrelative
    have hsize : ((Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) + 1) * 2 *
        Real.exp ((q + a) ^ a) ≤ Real.exp ((p + C) ^ C) := by
      have hexp : 4 * d + 2 ≤ Real.exp (4 * d + 2) := by linarith [Real.add_one_le_exp (4 * d + 2)]
      calc
        _ ≤ Real.exp (4 * d + 2) * Real.exp ((q + a) ^ a) :=
          mul_le_mul_of_nonneg_right ((by linarith :
            ((Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) + 1) * 2 ≤ 4 * d + 2).trans hexp)
            (Real.exp_nonneg _)
        _ = Real.exp (4 * d + 2 + (q + a) ^ a) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (hbudget p hp).1
    rw [F.realReducedRelativeCoefficient_eq_map]
    exact F.firstCoefficientSlowBound_mono e ω hF w T hT hsize _ hextract
  · let D := F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w R)
    have hD := F.reducedSquareRealDiagonalHom_grid e ω hF w l _
      (F.reducedSquareRealSymbolHom_grid e ω hF w l R hR)
    have hinputs : ∀ x ∈ [R, D⁻¹], G.SymbolRationalGrid f ν hG w l x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hR
      · exact G.symbolRationalGrid_inv f ν hG w l hD
    have hrelative : G.SymbolRationalGrid f ν hG w m (F.reducedSquareRealRelativePart w R) := by
      change G.SymbolRationalGrid f ν hG w m (R * D⁻¹)
      simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [R, D⁻¹] (by simp) hinputs
    rw [F.realReducedRelativeCoefficient_eq_map]
    exact F.realReducedSquareCoefficientMap_grid e ω hF w m _ hrelative

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCommonFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

universe uσ uι uL

theorem exists_coefficient_correction_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CoefficientCorrectionSpec.{uσ, uι, uL} s C := by
  obtain ⟨a, _, hadjoint⟩ := exists_firstCoefficient_adjoint_bound.{uσ, uι, uL} (s + 1) 1
  obtain ⟨d, _, hderivative⟩ := exists_firstCoefficient_direction_bound.{uσ, uι, uL} (s + 1) 1
  obtain ⟨r, _, hgrid⟩ := exists_firstCoefficient_operation_grid.{uσ, uι, uL} (s + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_synchronizedCorrection_budget a d r
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  have hgrids := hgrid F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hAdjointGrid, hDerivativeGrid⟩ := hgrids
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr (hbudget p hp).2), hlm, ?_⟩
  intro T hT A D hA hD h hh ε u μ v hε hu hμ hv
  have hinput : Real.exp p ≤ Real.exp ((p + 2) ^ 1) :=
    Real.exp_le_exp.mpr (by rw [pow_one]; linarith)
  have hA' := F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT hinput A.coord hA
  have hAi : F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ 1)) A⁻¹.coord := by
    intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hA' i
  have hdir := hderivative F e ω hF H p hH hp hι hσ hHp hstructure T hT A hA' h hh
  have hsum := F.firstCoefficientSlowBound_add e ω hF (fun _ => 1) T (Real.exp p) (Real.exp p) ε u hε hu
  have hdiff := F.firstCoefficientSlowBound_sub e ω hF (fun _ => 1) T
    (Real.exp p + Real.exp p) (Real.exp ((p + d) ^ d)) _ _ hsum hdir
  have hslow := hadjoint F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H p hH hp hι hσ hHp hstructure T hT A⁻¹ hAi
    (Real.exp p + Real.exp p + Real.exp ((p + d) ^ d)) (by positivity) _ hdiff
  have hsize : Real.exp ((p + a) ^ a) * (Real.exp p + Real.exp p + Real.exp ((p + d) ^ d)) ≤
      Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp ((p + a) ^ a) * Real.exp (p + (p + d) ^ d + 2) :=
        mul_le_mul_of_nonneg_left (exp_repeated_add_le hp (by positivity)) (Real.exp_nonneg _)
      _ = Real.exp ((p + a) ^ a + p + (p + d) ^ d + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (hbudget p hp).1
  constructor
  · exact F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT hsize _ hslow
  · have hv' := F.firstCoefficientGrid_mono e ω hF (fun _ => 1) hl hlm v hv
    have hsumGrid := F.firstCoefficientGrid_add e ω hF (fun _ => 1) m _ _ hv'
      (hAdjointGrid D μ hD hμ)
    exact F.firstCoefficientGrid_sub e ω hF (fun _ => 1) m _ _ hsumGrid (hDerivativeGrid D.coord hD h)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module

universe uσ uι uL

theorem exists_synchronizedSquare_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedSquareBoundSpec.{uσ, uι, uL} s C := by
  obtain ⟨r, _, hrelative⟩ := exists_reducedRelativeCoefficient_bound.{uσ, uι, uL} s
  obtain ⟨a, _, hcorrection⟩ := exists_coefficient_correction_bound.{uσ, uι, uL} s
  obtain ⟨C, hC, hbudget⟩ := exists_synchronizedSquare_budget r a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨n, hn, hnp, hln, hrelative⟩ := hrelative F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  let q : ℝ := p + (p + r) ^ r
  have hpow : 0 ≤ (p + r) ^ r := by positivity
  have hq : 0 ≤ q := add_nonneg hp hpow
  have hpq : p ≤ q := le_add_of_nonneg_right hpow
  have hrq : (p + r) ^ r ≤ q := le_add_of_nonneg_left hp
  have hpqExp := Real.exp_le_exp.mpr hpq
  have hrqExp := Real.exp_le_exp.mpr hrq
  obtain ⟨m, hm, hmp, hnm, hcorrection⟩ := hcorrection F e ω hF H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans hpqExp) hstructure n hn (hnp.trans hrqExp)
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr (hbudget p hp)), hln.trans hnm, ?_⟩
  intro T hT A D hA hD h hh E R hE hR ε μ hε hμ
  obtain ⟨hu, hv⟩ := hrelative T hT E R hE hR
  have hA' := F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT hpqExp A.coord hA
  have hD' := F.realAdaptedCoefficientGrid_mono e ω hF (fun _ => 1) hl hln D.coord hD
  have hε' := F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT hpqExp ε hε
  have hu' := F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT hrqExp _ hu
  have hμ' := F.firstCoefficientGrid_mono e ω hF (fun _ => 1) hl hln μ hμ
  obtain ⟨hleft, hright⟩ := hcorrection T hT A D hA' hD' h hh ε _ μ _ hε' hu' hμ' hv
  exact ⟨F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr (hbudget p hp)) _ hleft, hright⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem synchronized_normalized_coefficient_common_derivative
    (h : σ → ℚ) (ε μ : ℝ ⊗[ℚ] L)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (r : F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (E P R P₀ : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hf : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-ε) (-μ) (F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord))
    (hs : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord)
    (hr : F.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r = E * P * R)
    (hA : F.adaptedReducedRealSymbolHom (fun _ => 1) A = F.reducedSquareRealSymbolHom (fun _ => 1) E)
    (hB : F.adaptedReducedRealSymbolHom (fun _ => 1) B = F.reducedSquareRealSymbolHom (fun _ => 1) P)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP₀ : P₀.coord ∈ realificationLieSubalgebra U)
    (hdiag : F.reducedSquareRealSymbolHom (fun _ => 1) P = F.reducedSquareRealSymbolHom (fun _ => 1) P₀) :
    F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) ε)
          (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) E) +
        F.realFirstCoefficientAdjoint (fun _ => 1) B
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) μ)
            (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) R)) +
        F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) P₀) ∈
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) := by
  apply F.synchronized_coefficient_common_derivative b ω hF h U A B D E P R P₀
    (F.realFirstCoefficientConstant (fun _ => 1) ε) (F.realFirstCoefficientConstant (fun _ => 1) μ)
    hA hB hP hP₀ hdiag
  have hderivative := F.normalized_real_square_derivative_identity b ω hF h ε μ (A * B * D) r hf hs
  rwa [hr] at hderivative

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uL

variable {σ : Type uσ} {ι : Type uι} {L : Type uL}
  [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

theorem exists_normalized_common_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
        [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1))),
        F.NormalizedCommonFamilySpec b ω hF U C := by
  obtain ⟨C, hC, hbound⟩ := exists_synchronizedSquare_bound.{uσ, uι, uL} s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF U H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hcorrect⟩ := hbound F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro T hT A B D hA hD Hshifts r E P R P₀ ε μ hbox hf hs hr hleft hmiddle hP hP₀ hdiag hE hR hε hμ
  let S : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1) := fun h =>
    F.coefficientSlowCorrection A (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) (ε h))
      (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) (E h))
  let K : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1) := fun h =>
    F.coefficientGridCorrection D (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) (μ h))
      (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) (R h))
  refine ⟨S, K, ?_⟩
  intro h hh
  have hε' := F.realFirstCoefficientConstant_slow (fun _ => 1) b ω hF T hT
    (Real.exp p) (Real.exp_nonneg _) (ε h) (hε h hh)
  have hμ' := F.realFirstCoefficientConstant_grid (fun _ : σ => 1) b ω hF l (μ h) (hμ h hh)
  have hbounds := hcorrect T hT A D hA hD h (hbox h hh) (E h) (R h) (hE h hh) (hR h hh)
    (F.realFirstCoefficientConstant (fun _ : σ => 1) (ε h))
    (F.realFirstCoefficientConstant (fun _ : σ => 1) (μ h)) hε' hμ'
  refine ⟨?_, hbounds.1, hbounds.2⟩
  have hcommon := F.synchronized_normalized_coefficient_common_derivative b ω hF
    (fun i => (h i : ℚ)) (ε h) (μ h) U A B D (r h) (E h) (P h) (R h) P₀
    (hf h hh) (hs h hh) (hr h hh) (hleft h hh) (hmiddle h hh) (hP h hh) hP₀ (hdiag h hh)
  simpa only [Rat.cast_intCast] using hcommon

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.StepOneGradedNiltestSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

omit [DecidableEq σ] in
theorem stepOne_niltest_eval_affine (P : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    (hP : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (x : σ → ℤ) :
    P.eval x = P.observable (QuotientGroup.mk (1 : D.RealGroup)) *
      character (((realifyFunctional η (coefficients P.orbit.log 0) +
        ∑ i, (x i : ℝ) * realifyFunctional η (coefficients P.orbit.log (Finsupp.single i 1))) : ℝ) :
          CircleFourier.Circle) := by
  rw [Niltest.eval, ← D.filtration.realification.polynomialOrbitRealEval_integer]
  rw [stepOne_vertical_character D.filtration D.realLattice η P.observable hP,
    D.filtration.realification.polynomialOrbitRealEval_coord,
    eval₂_affine_of_degreeLE_one P.orbit.log P.orbit.degreeLE]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  rw [mul_comm]

theorem stepOne_niltest_linear_phase_bias (P : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    (hP : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (T : σ → ℕ) {M δ : ℝ} (hM : 0 < M)
    (hbound : (P.normBound : ℝ) ≤ M) (hbias : δ ≤ ‖𝔼 x ∈ integerBox T, P.eval x‖) :
    δ / M ≤ ‖linearPhaseMean T (fun i =>
      (realifyFunctional η (coefficients P.orbit.log (Finsupp.single i 1)) : CircleFourier.Circle))‖ := by
  apply linearPhaseMean_norm_ge_of_affine_bias T
    (P.observable (QuotientGroup.mk (1 : D.RealGroup)))
    (realifyFunctional η (coefficients P.orbit.log 0) : CircleFourier.Circle) _ hM
    ((P.norm_le _).trans hbound)
  rw [integerBox_expect_eq_fin] at hbias
  convert hbias using 2
  apply Finset.expect_congr rfl
  intro t _
  rw [D.stepOne_niltest_eval_affine P η hP]
  congr 2
  have hcoe (f : σ → ℝ) : ((∑ i, f i : ℝ) : CircleFourier.Circle) = ∑ i, (f i : CircleFourier.Circle) :=
    map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
  simp only [Int.cast_natCast, AddCircle.coe_add, hcoe, ← nsmul_eq_mul, AddCircle.coe_nsmul]

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

theorem exists_stepOne_niltest_splitting (P : D.Niltest (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p) (hP : P.ComplexityLE p)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hvertical : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ integerBox T, P.eval x‖) :
    ∃ (m : ℕ) (E Q R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (v : Fin d → L),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧
      D.filtration.realification.polynomialSymbolHom (fun _ => 1) (E * Q * R) =
        D.filtration.realification.polynomialSymbolHom (fun _ => 1) ⟨⟨P.orbit.log, P.orbit.property⟩⟩ ∧
      D.filtration.PolynomialSlowBound D.basis (fun _ => 1) (fun i => (T i : ℝ))
        (Real.exp ((p + 2) ^ 4)) E ∧
      D.filtration.PolynomialRationalGrid D.basis (fun _ => 1) m R ∧
      Submodule.span ℚ (Set.range v) = (D.filtration.stepOneFrequencyKernel η).toSubmodule ∧
      (∀ i j, rationalLogHeight (D.basis.repr (v i) j) ≤ (p + 2) ^ 4) ∧
      (∀ t : σ → ℝ, eval₂ t (Q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
        realificationLieSubalgebra (D.filtration.stepOneFrequencyKernel η)) ∧
      coefficients (Q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hheight : ∀ i, RationalHeightLE (η (D.basis i)) H :=
    fun i => rationalHeightLE_ceil_exp (hηheight i)
  have hnorm : (P.normBound : ℝ) ≤ Real.exp p := by
    have h := P.observable_budget hP
    have hl := P.lipBound.coe_nonneg
    linarith
  have hphase := D.stepOne_niltest_linear_phase_bias P η hvertical T (Real.exp_pos p) hnorm hbias
  obtain ⟨m, E, Q, R, hm, hmH, hsum, he, hr, hq, hq0⟩ :=
    D.filtration.exists_stepOne_linear_splitting D.basis η hH hheight T hT
      (fun i => coefficients P.orbit.log (Finsupp.single i 1))
      (div_pos (Real.exp_pos (-p)) (Real.exp_pos p)) hphase
  obtain ⟨v, hvspan, hvheight⟩ := exists_bounded_frequency_kernel_spanning D.basis η hH hheight
  refine ⟨m, E, Q, R, v, hm, (Nat.cast_le.mpr hmH).trans (stepOne_denominator_budget hp), ?_, ?_, hr,
    hvspan, ?_, hq, hq0⟩
  · rw [hsum]
    apply NilpotentLieBCHGroup.ext
    exact D.filtration.realification.stepOne_symbol_linearPart ⟨P.orbit.log, P.orbit.property⟩
  · exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) (fun i => (T i : ℝ))
      (fun i => Nat.cast_pos.mpr (hT i)) (stepOne_slow_budget hp) E he
  · intro i j
    exact rationalLogHeight_le_of_height
      (hvheight i j) (stepOne_kernel_height_budget hp)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

theorem exists_stepOne_graded_niltest_splitting
    (ω : Fin d → ℕ)
    (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (P : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hP : P.ComplexityLE p)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hvertical : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ integerBox T, P.eval x‖) :
    ∃ (m : ℕ) (E Q R : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : Fin d → D.filtration.AssociatedGraded),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧
      E * Q * R = D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1)
        ⟨⟨P.orbit.log, P.orbit.property⟩⟩ ∧
      D.filtration.SymbolSlowBound D.basis ω hlayers (fun _ => 1) (fun i => (T i : ℝ))
        (Real.exp ((p + 2) ^ 4)) E ∧
      D.filtration.SymbolRationalGrid D.basis ω hlayers (fun _ => 1) m R ∧
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hlayers) ω W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        ((D.filtration.associatedGradedBasis D.basis ω hlayers).repr (v i) j) ≤ (p + 2) ^ 4) ∧
      (∀ x ∈ W, D.filtration.stepOneGradedFrequency D.basis ω hlayers η x = 0) ∧
      (∀ t : σ → ℝ, eval₂ t
        (D.filtration.realGradedSymbolPolynomial D.basis ω hlayers (fun _ => 1) Q.coord) ∈
          realificationLieSubalgebra W) := by
  obtain ⟨m, E, Q, R, v, hm, hmbound, hsymbol, he, hr, hvspan, hvheight, hq, _⟩ :=
    D.exists_stepOne_niltest_splitting P η hp hP hηheight hvertical T hT hbias
  refine ⟨m,
    D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1) E,
    D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1) Q,
    D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1) R,
    D.filtration.stepOneGradedKernel D.basis ω hlayers η,
    (fun i => D.filtration.stepOneGradedEquiv D.basis ω hlayers (v i)),
    hm, hmbound, ?_,
    D.filtration.polynomialSlowBound_symbol D.basis ω hlayers (fun _ => 1) _ _ E he,
    D.filtration.polynomialRationalGrid_symbol D.basis ω hlayers (fun _ => 1) m R hr,
    D.filtration.stepOneGradedKernel_span D.basis ω hlayers η v hvspan,
    D.filtration.stepOne_graded_submodule D.basis ω hlayers _, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    exact D.filtration.realPolynomialSymbolHom_eq_of_quotient_eq D.basis ω hlayers
      (fun _ => 1) _ _ hsymbol
  · intro i j
    rw [D.filtration.stepOneGradedEquiv_coordinate]
    exact hvheight i j
  · intro x hx
    exact (D.filtration.mem_stepOneGradedKernel D.basis ω hlayers η x).mp hx
  · exact D.filtration.stepOne_symbol_values_in_gradedKernel D.basis ω hlayers η
      (fun _ => 1) (Q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) hq

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

theorem stepOne_controlled_symbol_factorization (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hvertical : ∀ z ∈ D.filtration.realification.subgroup 1, ∀ x,
      T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
        T.observable x)
    (origin : σ → ℤ) (lengths : σ → ℕ) (hlengths : ∀ i, 0 < lengths i)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖) :
    D.filtration.ControlledSymbolFactorization D.basis ω hF η (fun i => (lengths i : ℝ))
      (T.symbol D.basis ω hF) ((p + 2) ^ 4) := by
  let U := T.translate (fun _ => Nat.zero_lt_one) origin
  have hUbias : Real.exp (-p) ≤ ‖𝔼 x ∈ integerBox lengths, U.eval x‖ := by
    rw [T.mean_translate_box (fun _ => Nat.zero_lt_one) origin lengths]
    exact hbias
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hheight, hη, hfast⟩ :=
    D.exists_stepOne_graded_niltest_splitting ω hF U η hp hT hηheight hvertical
      lengths hlengths hUbias
  refine ⟨m, E, P, R, W, v, hm, hmp, ?_, hE, hR, hv, hW, hheight, ?_, ?_⟩
  · exact hprod.trans (T.symbol_translate D.basis ω hF (fun _ => Nat.zero_lt_one) origin)
  · intro x hx _
    change D.filtration.stepOneGradedFrequency D.basis ω hF η x = 0
    exact hη x hx
  · exact (D.filtration.mem_real_symbolPointwiseSubalgebra_iff_values D.basis ω hF
      (fun _ => 1) W P.coord).mpr hfast

end RationalFilteredNilmanifold

theorem translatedStepDropSpec_one : TranslatedStepDropSpec.{uσ, uL} 1 4 := by
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p hp _ T hT η hη hvertical origin lengths hlengths _ hbias
  have h := D.stepOne_controlled_symbol_factorization ω hF T η hp hT hη hvertical
    origin lengths hlengths hbias
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono D.filtration D.basis ω hF h
    (pow_le_pow_left₀ (by linarith) (by norm_num) 4)
    (fun i => by exact_mod_cast hlengths i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FirstCoefficientPolynomialDerivative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realFirstCoefficientGradedPolynomial_injective :
    Function.Injective (F.realFirstCoefficientGradedPolynomial b ω hF w) := by
  intro x y hxy
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [← F.realFirstCoefficientGradedPolynomial_coordinate,
    ← F.realFirstCoefficientGradedPolynomial_coordinate, hxy]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GradedPolynomialSymbolInverse
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem exists_symbol_of_gradedPolynomial
    (P : PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    (hP : P.coord ∈ gradedPolynomialSubmodule ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω w) :
    ∃ x : F.RealPolynomialSymbolGroup w, F.realGradedSymbolPolynomialHom e ω hF w x = P := by
  refine ⟨⟨F.realSymbolOfGradedPolynomial e ω hF w P.coord⟩, ?_⟩
  apply NilpotentLieBCHGroup.ext
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial e ω hF w P.coord hP

theorem realGradedSymbolPolynomialHom_native (g : F.RealAdaptedPolynomialGroup w) :
    F.realGradedSymbolPolynomialHom e ω hF w
      (F.realPolynomialSymbolHom e ω hF w (F.realAdaptedPolynomialGroupHom w g)) =
      F.realAdaptedGradedPolynomialHom e ω hF w g := by
  apply NilpotentLieBCHGroup.ext
  change F.realGradedSymbolPolynomial e ω hF w
    (F.realSymbolOfPolynomial e ω hF w (F.realAdaptedPolynomialMap w g.coord)) = _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  exact (F.realAdaptedGradedPolynomialLie_symbol e ω hF w g.coord).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialOperationBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_polynomial_operation_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
        A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) A.coord →
        ∀ M : ℝ, 0 ≤ M → ∀ Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L),
        Q ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
        CoefficientBound (b.baseChange ℝ) T M Q →
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) * M) (dualAdjoint A Q)) ∧
      (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
        A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) A.coord →
        ∀ i : σ, CoefficientBound (b.baseChange ℝ) T
          (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
          (formalLogDerivative i A)) := by
  obtain ⟨C, hC, hoperations⟩ := exists_scaled_polynomial_dual_bound s a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT
  classical
  have hN : (1 : ℝ) ≤ Real.exp ((p + 2) ^ a) := Real.one_le_exp (by positivity)
  have hops := hoperations F b ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H p hH hp hι hσ hHp hc T hT
  constructor
  · intro A hA hAbound M hM Q hQ hQbound
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    obtain ⟨y, hy⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) Q hQ
    let G : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) := ⟨x⟩
    have hG : F.realFullPolynomialHom (fun _ : σ => 1) G = A := NilpotentLieBCHGroup.ext hx
    have hxbound : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ a)) x := by
      apply (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT (Real.exp_nonneg _) x).mpr
      rwa [hx]
    have hybound : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T M y := by
      apply (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT hM y).mpr
      rwa [hy]
    have hunit : ∀ z, F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T 1 z →
        F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + C) ^ C)) (dualAdjoint G z) := by
      intro z hz
      exact hops.2 G z hxbound (F.realAdaptedCoefficientBound_mono b ω hF _ T hT hN z hz)
    have hout : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
        (Real.exp ((p + C) ^ C) * M) (dualAdjoint G y) :=
      weighted_linear_bound_of_unit
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        (fun z => monomialScale T z.val.1) (fun z => monomialScale T z.val.1)
        (dualAdjointRealLinearEquiv G).toLinearMap _ hunit hM y hybound
    have hf := (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT
      (mul_nonneg (Real.exp_nonneg _) hM) _).mp hout
    rw [F.realAdaptedAdjoint_eq_formal, hG, hy] at hf
    exact hf
  · intro A hA hAbound i
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    have hxbound : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ a)) x := by
      apply (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT (Real.exp_nonneg _) x).mpr
      rwa [hx]
    let Φ := dualRealLogarithmicDifferential
      (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot) x
    have hunit : ∀ y, F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T 1 y →
        F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + C) ^ C)) (Φ y) := by
      intro y hy
      have hy' := F.realAdaptedCoefficientBound_mono b ω hF _ T hT hN y hy
      change F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + C) ^ C))
        (dualLogDerivative ⟨dualConstantLie x + dualInfinitesimal y⟩)
      apply hops.1
      · simpa only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero] using hxbound
      · simpa only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add] using hy'
    have hderivative := F.realAdaptedDirectionalDerivative_single_bound b ω hF T hT
      (Real.exp_nonneg _) x hxbound i
    have hfactor : 0 ≤ (s : ℝ) * Real.exp ((p + 2) ^ a) / T i :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)) (hT i).le
    have hout : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
        (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
        (F.realAdaptedLogDerivative (Pi.single i 1) x) :=
      weighted_linear_bound_of_unit
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        (fun z => monomialScale T z.val.1) (fun z => monomialScale T z.val.1)
        Φ _ hunit hfactor _ hderivative
    have hf := (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT
      (mul_nonneg (Real.exp_nonneg _) hfactor) _).mp hout
    rw [F.realAdaptedLogDerivative_eq_formal, hx] at hf
    exact hf

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

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "SG" => F.RealPolynomialSymbolGroup (fun _ : σ => 1)
local notation "φ" => F.realGradedSymbolPolynomialHom e ω hF (fun _ : σ => 1)

theorem symbolTerminalFactorization_of_graded
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (original : SG) (p : ℝ)
    (h : F.FastTerminalFactorization e ω hF W η T (φ original) p) :
    F.SymbolTerminalFactorization e ω hF W η T original p := by
  obtain ⟨Z, hZ, hZη, bZ, hbZ, A, P, B, hfactor, hA, hB, _, hdegree, hcoeff,
    hbound, m, hm, hmp, hgrid⟩ := h
  obtain ⟨a, ha⟩ := F.exists_symbol_of_gradedPolynomial e ω hF (fun _ : σ => 1) A hA.2.1
  obtain ⟨c, hc⟩ := F.exists_symbol_of_gradedPolynomial e ω hF (fun _ : σ => 1) P hdegree
  obtain ⟨b, hb⟩ := F.exists_symbol_of_gradedPolynomial e ω hF (fun _ : σ => 1) B hB.2.1
  refine ⟨Z, hZ, hZη, bZ, hbZ, a, c, b, ?_, ?_, ?_, ?_, ?_, m, hm, hmp, ?_⟩
  · apply F.realGradedSymbolPolynomialHom_injective e ω hF (fun _ : σ => 1)
    rw [map_mul, map_mul, ha, hc, hb]
    exact hfactor
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ : σ => 1)
      (F.fullFastGradedDiagonal W) a.coord).mpr
    intro α
    change coefficients (φ a).coord α ∈ _
    rw [ha]
    exact hA.1 α
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ : σ => 1)
      (F.fullFastGradedDiagonal W) b.coord).mpr
    intro α
    change coefficients (φ b).coord α ∈ _
    rw [hb]
    exact hB.1 α
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ : σ => 1) Z c.coord).mpr
    intro α
    change coefficients (φ c).coord α ∈ _
    rw [hc]
    exact hcoeff α
  · apply F.symbolSlowBound_of_gradedPolynomial e ω hF (fun _ : σ => 1) T (Real.exp p) a
    rw [ha]
    exact hbound
  · apply F.symbolRationalGrid_of_gradedPolynomial e ω hF (fun _ : σ => 1) m b
    rw [hb]
    exact hgrid

theorem symbolTerminalFactorization_of_native
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (p : ℝ)
    (h : F.FastTerminalFactorization e ω hF W η T
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g) p) :
    F.SymbolTerminalFactorization e ω hF W η T
      (F.realPolynomialSymbolHom e ω hF (fun _ : σ => 1) (F.realAdaptedPolynomialGroupHom (fun _ => 1) g)) p := by
  apply F.symbolTerminalFactorization_of_graded e ω hF W η T _ p
  rw [F.realGradedSymbolPolynomialHom_native]
  exact h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnnormalizedCommonSymbolFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem nativeSymbolNormalize_symbol (g : F.RealAdaptedPolynomialGroup w) :
    F.realExtendedSymbolMap w (F.nativeSymbolNormalize b ω hF w g).coord =
      F.realExtendedSymbolMap w g.coord := by
  have he : F.realPolynomialSymbolHom b ω hF w
      (F.realAdaptedPolynomialGroupHom w (F.nativeSymbolNormalize b ω hF w g)) =
      F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g) := by
    unfold nativeSymbolNormalize
    rw [F.realAdaptedPolynomialGroupHom_lift, F.realPolynomialSymbolHom_lift]
  have hc := congrArg NilpotentLieBCHGroup.coord he
  simpa only [F.realPolynomialSymbolHom_groupHom_coord] using hc

theorem realAdaptedGradedPolynomialHom_eq_of_symbol_eq
    (g h : F.RealAdaptedPolynomialGroup w)
    (he : F.realExtendedSymbolMap w g.coord = F.realExtendedSymbolMap w h.coord) :
    F.realAdaptedGradedPolynomialHom b ω hF w g = F.realAdaptedGradedPolynomialHom b ω hF w h := by
  apply NilpotentLieBCHGroup.ext
  change F.realAdaptedGradedPolynomialLie b ω hF w g.coord =
    F.realAdaptedGradedPolynomialLie b ω hF w h.coord
  rw [F.realAdaptedGradedPolynomialLie_symbol, F.realAdaptedGradedPolynomialLie_symbol]
  change F.realGradedSymbolPolynomial b ω hF w (F.realExtendedSymbolMap w g.coord) =
    F.realGradedSymbolPolynomial b ω hF w (F.realExtendedSymbolMap w h.coord)
  rw [he]

include b ω hF in
theorem realFirstCoefficientDirectionMap_eq_of_symbol_eq [Fintype σ]
    (g h : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (he : F.realExtendedSymbolMap (fun _ => 1) g.coord = F.realExtendedSymbolMap (fun _ => 1) h.coord) :
    F.realFirstCoefficientDirectionMap g.coord = F.realFirstCoefficientDirectionMap h.coord := by
  classical
  apply (Pi.basisFun ℝ σ).ext
  intro i
  apply F.realFirstCoefficientGradedPolynomial_injective b ω hF (fun _ => 1)
  change F.realFirstCoefficientGradedPolynomial b ω hF (fun _ => 1)
      (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1)) =
    F.realFirstCoefficientGradedPolynomial b ω hF (fun _ => 1)
      (F.realFirstCoefficientDirectionMap h.coord (Pi.single i 1))
  rw [F.realFirstCoefficientGradedPolynomial_direction, F.realFirstCoefficientGradedPolynomial_direction,
    F.realAdaptedGradedPolynomialHom_eq_of_symbol_eq b ω hF (fun _ => 1) g h he]

include b ω hF in
theorem realFirstCoefficientAdjoint_eq_of_symbol_eq
    (g h : F.RealAdaptedPolynomialGroup w)
    (he : F.realExtendedSymbolMap w g.coord = F.realExtendedSymbolMap w h.coord)
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientAdjoint w g x = F.realFirstCoefficientAdjoint w h x := by
  apply F.realFirstCoefficientGradedPolynomial_injective b ω hF w
  rw [F.realFirstCoefficientGradedPolynomial_adjoint, F.realFirstCoefficientGradedPolynomial_adjoint,
    F.realAdaptedGradedPolynomialHom_eq_of_symbol_eq b ω hF w g h he]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedSynchronizedSquareFamily
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

def SynchronizedNativeCommonCoefficientSpec (s C : ℕ) : Prop :=
  ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H l m : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hm : 0 < m) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p) (_hd : (d : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hgrid : (D.grid : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hb : ∀ i j, RationalHeightLE (b.repr (D.basis j) i) H)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ S)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (_hbox : ∀ h ∈ S, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hdata : D.SynchronizedNativeSquareData b ω hF T g S h₀ W p p l m),
    let q := (p + 2) ^ 3 + 3 * p + 1
    let U := D.filtration.fastPointwiseSquare b ω hF (fun _ : σ => 1) W
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((q + C) ^ C) ∧ l ∣ n ∧ m ∣ n ∧
      ∃ (A B R : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (small rational : (σ → ℤ) → D.filtration.RealFirstCoefficientModule (fun _ : σ => 1))
        (Z : D.filtration.RealFirstCoefficientModule (fun _ : σ => 1)),
        A * B * R = g ∧ B ∈ D.filtration.realFastDiagonalSubgroup (fun _ => 1) U ∧
        D.filtration.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp p) A.coord ∧
        D.filtration.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l R.coord ∧
        coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) A.coord) 0 = 0 ∧
        coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) R.coord) 0 = 0 ∧
        coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) B.coord) 0 =
          coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) 0 ∧
        ∀ h ∈ S,
          (D.filtration.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
            (small h + D.filtration.realFirstCoefficientAdjoint (fun _ => 1) B (rational h) + Z) ∈
              D.filtration.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
                (D.filtration.reducedSquareFastRelativeSubmodule (fun _ => 1) U)) ∧
          D.filtration.FirstCoefficientSlowBound b ω hF (fun _ => 1) T
            (Real.exp ((q + C) ^ C)) (small h) ∧
          D.filtration.FirstCoefficientGrid b ω hF (fun _ => 1) n (rational h)

theorem exists_synchronized_native_common_coefficients (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedNativeCommonCoefficientSpec s C := by
  obtain ⟨C, hC, hfamily⟩ := exists_normalized_common_family s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ d D b ω hF H l m p hH hl hm hp hι hσ hd hHp hlp hmp hgrid hc hb
    T hT g S h₀ hh₀ W hbox hdata
  let U := D.filtration.fastPointwiseSquare b ω hF (fun _ : σ => 1) W
  let δ := matrixDenominator (fun i j => b.repr (D.basis j) i)
  let k := δ * D.grid * l * m
  let q := (p + 2) ^ 3 + 3 * p + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have h3 : 0 ≤ (p + 2) ^ 3 := by positivity
    dsimp [q]
    linarith
  have h2q : (p + 2) ^ 2 ≤ q := by
    have h23 : (p + 2) ^ 2 ≤ (p + 2) ^ 3 := pow_le_pow_right₀ (by linarith) (by decide)
    dsimp [q]
    linarith
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hδ : 0 < δ := matrixDenominator_pos _
  have hk : 0 < k := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hδ D.grid_pos) hl) hm
  have hδp : (δ : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    real_basis_transfer_denominator D.basis b hp hd' hι hHp hb
  have hkq : (k : ℝ) ≤ Real.exp q := by
    dsimp only [k]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul (mul_le_mul hδp hgrid (Nat.cast_nonneg _) (Real.exp_nonneg _))
          hlp (Nat.cast_nonneg _) (by positivity)) hmp (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp ((p + 2) ^ 3 + 3 * p) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp q := Real.exp_le_exp.mpr (by dsimp [q]; linarith)
  have hlk : l ∣ k := dvd_mul_of_dvd_left (dvd_mul_left l (δ * D.grid)) m
  have hmk : m ∣ k := dvd_mul_left m (δ * D.grid * l)
  have hδk : δ * D.grid ∣ k :=
    (dvd_mul_right (δ * D.grid) l).trans (dvd_mul_right (δ * D.grid * l) m)
  obtain ⟨ε, γ, r, E, P, R, A₀, B₀, R₀, hproduct, hA₀, hR₀, hB₀, hgood, _⟩ := hdata
  obtain ⟨A, B, D₀, hABD, hA, hB, hD, hAslow, hDgrid, hAzero, hDzero, hBzero⟩ :=
    D.filtration.exists_reduced_native_factorization b ω hF (fun _ : σ => 1)
      T hT (Real.exp_nonneg p) l g A₀ B₀ R₀ hproduct hA₀ hR₀
  have hBfast : B ∈ D.filtration.realFastDiagonalSubgroup (fun _ => 1) U := by
    change (D.filtration.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (U.map (D.filtration.reducedSquareSndSymbolMap (fun _ => 1)))
    rw [hB]
    exact hB₀
  obtain ⟨n, hn, hnq, hkn, hcoeff⟩ := hfamily D.filtration b ω hF U H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq)) hc k hk hkq
  have hE : ∀ h ∈ S, D.filtration.squareFiltration.quotientTop.SymbolSlowBound
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T (Real.exp q) (E h) := by
    intro h hh
    exact D.filtration.squareFiltration.quotientTop.symbolSlowBound_mono
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hpq) (E h) (hgood h hh).2.2.2.2.2.2.2.2.2.2.1
  have hR : ∀ h ∈ S, D.filtration.squareFiltration.quotientTop.SymbolRationalGrid
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) k (R h) := by
    intro h hh
    exact D.filtration.squareFiltration.quotientTop.symbolRationalGrid_mono
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) hm hmk (R h)
      (hgood h hh).2.2.2.2.2.2.2.2.2.2.2
  have hε : ∀ h ∈ S, ∀ i, |(b.baseChange ℝ).repr (ε h).coord i| ≤ Real.exp q := by
    intro h hh i
    exact (real_basis_coordinates_exp_bound D.basis b hp hd' hHp hb (ε h).coord
      (hgood h hh).2.1 i).trans (Real.exp_le_exp.mpr h2q)
  have hγ : ∀ h ∈ S, (fun i => (b.baseChange ℝ).repr (γ h).coord i) ∈ realDenominatorGrid k := by
    intro h hh
    have hdeclared := realification_subgroup_grid D.basis D.lattice D.grid D.outer_grid
      (γ h) (hgood h hh).1
    exact realDenominatorGrid_subset_of_dvd (Nat.mul_pos hδ D.grid_pos) hδk
      (real_basis_coordinates_grid D.basis b D.grid (γ h).coord hdeclared)
  obtain ⟨small, rational, hcommon⟩ := hcoeff T hT A B D₀
    (D.filtration.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hpq) A.coord hAslow)
    (D.filtration.realAdaptedCoefficientGrid_mono b ω hF (fun _ => 1) hl hlk D₀.coord hDgrid)
    S r E P R (P h₀) (fun h => (ε h).coord) (fun h => (γ h).coord) hbox
    (by intro h hh; rw [hABD]; exact (hgood h hh).2.2.1)
    (by intro h hh; rw [hABD, (hgood h hh).2.2.2.1])
    (fun h hh => (hgood h hh).2.2.2.2.2.1.symm)
    (fun h hh => hA.trans (hgood h hh).2.2.2.2.2.2.2.1.symm)
    (fun h hh => hB.trans (hgood h hh).2.2.2.2.2.2.2.2.2.1.symm)
    (fun h hh => (hgood h hh).2.2.2.2.2.2.1)
    (hgood h₀ hh₀).2.2.2.2.2.2.1
    (fun h hh => (hgood h hh).2.2.2.2.2.2.2.2.2.1.trans
      (hgood h₀ hh₀).2.2.2.2.2.2.2.2.2.1.symm) hE hR hε hγ
  exact ⟨n, hn, hnq, hlk.trans hkn, hmk.trans hkn, A, B, D₀, small, rational,
    D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) (P h₀),
    hABD, hBfast, hAslow, hDgrid, hAzero, hDzero, hBzero, hcommon⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerHalving
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem exists_trans_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
      {s : ℕ} {p : ℝ}
      {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ} {psi : M → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p chi eta → NativeIntegerVectorEquivalence s p eta psi →
      (∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) → NativeIntegerVectorEquivalence s ((p + C) ^ C) chi psi := by
  let Y : Polynomial ℕ := Polynomial.X + 2
  let P := (Y + 2) ^ 2 + Y + (Y + (Y ^ 2 + Y + 3) ^ 2) + Y ^ 2 + 4 + 2 * Y + Y
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J K M _ _ _ s p chi eta psi hp E F hunit
  have hpq : p ≤ p + 2 := by linarith
  have hbudget : productNiltestBudget (p + 2) + 2 * (p + 2) + (p + 2) ≤ (p + C) ^ C := by
    simpa [P, Y, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget]
      using hbound p hp
  exact ((E.mono hpq).trans (F.mono hpq) hunit (by linarith)).mono hbudget

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerExpansion

theorem exists_mul_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
      {f g : (σ → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion w s p f → NativeIntegerExpansion w s p g →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) (fun x => f x * g x)) := by
  obtain ⟨a, _, ha⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 2 + Polynomial.C a) ^ a + 2 * (X + 2))
  refine ⟨C, hC, ?_⟩
  intro σ w s p f g hp E F
  have hpq : p ≤ p + 2 := by linarith
  have hcost : (p + 2 + a) ^ a + 2 * (p + 2) ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : productNiltestBudget (p + 2) + 2 * (p + 2) ≤ (p + C) ^ C :=
    (add_le_add (ha _ (by linarith)) (le_refl _)).trans hcost
  exact ⟨(((E.mono hpq).mul (F.mono hpq) (by linarith)).mono hbound)⟩

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

noncomputable def NativeIntegerExpansion.tensorCrossProduct {σ : Type*} {s : ℕ} {p : ℝ}
    {f g h k : (σ → ℤ) → ℂ}
    (A : NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => f x * star (h x)))
    (B : NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => g x * star (k x)))
    (hp : 2 ≤ p) :
    NativeIntegerExpansion (fun _ : σ => 1) s (productNiltestBudget p + 2 * p)
      (fun x => (f x * g x) * star (h x * k x)) := by
  have heq : (fun x => (f x * star (h x)) * (g x * star (k x))) =
      (fun x => (f x * g x) * star (h x * k x)) :=
    funext (fun x => complex_tensor_cross_product (f x) (h x) (g x) (k x))
  exact heq ▸ A.mul B hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationDescent
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_native_addition_orbit (i : σ) (hi : bound i ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) s r)
    (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ) :
    ∃ q : E.filtration.realification.PolynomialOrbit (fun _ : Option σ => 1),
      E.filtration.realification.polynomialOrbitEval _ 0 q = 1 ∧
      ∀ (x : Option σ → ℤ) (j : Fin 3),
        (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi
          (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i) j
          (E.filtration.realification.polynomialOrbitEval _ x q)) : D.Space) =
          QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x j) g) := by
  let F := M.filtration.additiveTripleFiltration i hi
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)
  obtain ⟨q, hq0, hq⟩ := M.filtration.exists_real_normalized_addition_orbit i hi g ε γ hfactor
  have hF : F.realification = E.filtration.realification := by rw [hEF]
  let qE := F.realification.orbitEquivOfEq hF (fun _ : Option σ => 1) q
  have hqE (x : Option σ → ℤ) : E.filtration.realification.polynomialOrbitEval _ x qE =
      F.realification.polynomialOrbitEval _ x q := F.realification.orbitEquivOfEq_eval hF _ q x
  have hvalues (x : Option σ → ℤ) (j : Fin 3) :
      M.filtration.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) j
        (F.realification.polynomialOrbitEval _ x q) =
          ε⁻¹ * M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x j) g * γ⁻¹ := by
    fin_cases j
    · exact (hq x).1
    · exact (hq x).2.1
    · exact (hq x).2.2
  refine ⟨qE, (hqE 0).trans hq0, ?_⟩
  intro x j
  rw [hqE, hvalues]
  simp only [← mul_assoc, mul_inv_cancel, one_mul]
  exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem unitVertical_triple_top_invariant (i : σ) (hi : bound i = 1)
    (hs : ∑ j, bound j = s)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi.le
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a : Fin 3 → I) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi.le
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)).realification.subgroup s)
    (x : E.Space) :
    M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i) E hEL ε
        (fun j => V.observable (a j)) (k • x) =
      M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i) E hEL ε
        (fun j => V.observable (a j)) x := by
  apply M.tripleObservable_top_invariant i hi.le _ (omittedCoordinateWeight_le_one i) E hEL
    ε (fun j => V.observable (a j))
    (fun z => (realifyFunctional V.frequency z.coord : CircleFourier.Circle)) ?_ k hk ?_ x
  · intro j z hz y
    exact M.unitVertical_top_action hs V (a j) z hz y
  · exact M.filtration.realAdditiveTriple_omitted_frequency_phase i hi hs V.frequency ⟨k.coord⟩ hk

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1)
  (hs : ∑ j, bound j = s + 1)

variable (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))] [T2Space (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))]

variable (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))) s n)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))] [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))]

include hs hEF hQL

theorem exists_lipschitz_unitVertical_triple_descent
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a : Fin 3 → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j)))) :
    letI := Q.metricSpace
    ∃ v : Q.Space → ℂ,
      (∀ g : E.RealGroup, v (QuotientGroup.mk (realificationMap
        (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap (E.filtration.layerIdeal (s + 1))) g)) =
          M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
            E hEL ε (fun j => V.observable (a j)) (QuotientGroup.mk g)) ∧
      LipschitzWith (rationalReconstructionLipschitzBound s r n H A 1) v ∧
      ∀ x, ‖v x‖ ≤ 1 := by
  let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
    realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
  have hcover : Q.lattice ≤ E.lattice.map (mapOfSteps
      (hL := E.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap (E.filtration.layerIdeal (s + 1)))) := by
    rw [hQL]
    exact le_rfl
  have hker : ∀ k ∈ (realificationMap
      (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap (E.filtration.layerIdeal (s + 1)))).ker,
      ∀ x : E.RealGroup,
        M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
          E hEL ε (fun j => V.observable (a j)) (QuotientGroup.mk (k * x)) =
        M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
          E hEL ε (fun j => V.observable (a j)) (QuotientGroup.mk x) := by
    intro k hk x
    have hkE : k ∈ E.filtration.realification.subgroup (s + 1) :=
      (E.filtration.mem_realQuotientStepHom_ker (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl k).mp hk
    have hkF : k ∈ (M.filtration.additiveTripleFiltration i hi.le
        (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)).realification.subgroup (s + 1) := by
      rw [← hEF]
      exact hkE
    exact M.unitVertical_triple_top_invariant i hi hs E hEL V ε a k hkF (QuotientGroup.mk x)
  obtain ⟨v, hv, hvlip, hvnorm⟩ := exists_lipschitz_realification_reconstruction
    (hL := E.filtration.lowerCentralSeries_eq_bot) (hM := Q.filtration.lowerCentralSeries_eq_bot)
    E.basis Q.basis (lieQuotientMap (E.filtration.layerIdeal (s + 1))) (lieQuotientMap_surjective (E.filtration.layerIdeal (s + 1))) E.lattice Q.lattice hcover
    E.grid Q.grid H E.grid_pos Q.grid_pos hH E.outer_grid Q.outer_grid hentries hstructure
    (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
      E hEL ε (fun j => V.observable (a j))) hker A 1 hLip
    (M.tripleObservable_norm_le i hi.le _ (omittedCoordinateWeight_le_one i)
      E hEL ε (fun j => V.observable (a j)) (fun j x => V.norm (a j) x))
  let vQ : Q.Space → ℂ := v
  refine ⟨vQ, hv, ?_, ?_⟩
  · exact hvlip.weaken (by simp only [Fintype.card_fin, le_refl])
  · intro x
    exact hvnorm x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearityCorrelation
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem of_addition_family {σ I : Type*} [DecidableEq σ] [Fintype I]
    {s : ℕ} {p q r : ℝ} (f : I → (σ → ℤ) → ℂ) (i : σ)
    (R : NativeIntegerModelFamily (fun _ : Option σ => 1) s q
      (fun a => coordinateAdditionProduct f a i))
    (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hpr : p ≤ r) (h2pr : 2 * p ≤ r) (hqr : q ≤ r) :
    NativeIntegerVectorEquivalence s r (coordinateSumVector f i) (coordinateTensorVector f i) := by
  refine {
    left_dimension := hcard.trans (Real.exp_le_exp.mpr hpr)
    right_dimension := ?_
    expansion := ?_ }
  · simp only [Fintype.card_prod, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul hcard hcard (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]
      _ ≤ Real.exp r := Real.exp_le_exp.mpr h2pr
  · intro a b
    have heq : (fun x => coordinateAdditionProduct f ![a, b.1, b.2] i x) =
        (fun x => coordinateSumVector f i a x * star (coordinateTensorVector f i b x)) :=
      funext (coordinateAdditionProduct_eq f i a b)
    exact ⟨heq ▸ (NativeIntegerExpansion.ofModelFamily R ![a, b.1, b.2]).mono hqr⟩

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

theorem mixedTranslationExpansion_factor {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length) (x : Fin 3 → ℤ) :
    coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a (mixedTranslationSample s x) =
      V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a)
        (fun j => correlationInput (x 0) (x 1) j.1) *
      translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a (mixedTranslationSample s x) :=
  coordinateTranslationExpansion_factor V.eval (mixedTranslationCoordinates s) a (mixedTranslationSample s x)

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

theorem untranslatedMixedProduct_eq {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (h₁ h₂ h₃ h₄ n : ℤ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) :
    untranslatedMixedProduct V k h₁ h₂ h₃ h₄ n = mixedParallelogramProduct V k ![h₁, h₂, h₃, n] := by
  have hh₄ : h₄ = h₂ + h₃ - h₁ := by omega
  subst h₄
  rfl

end Erdos3

end

section

namespace Erdos3

theorem exists_mixed_error_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      mixedErrorPairBudget p ≤ (p + C) ^ C ∧ mixedErrorBudget p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4 + 2 * X
  let T := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4 + 2 * R
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + T)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hpair : 0 ≤ mixedErrorPairBudget p := hp.trans (le_mixedErrorPairBudget hp)
  have hglobal : 0 ≤ mixedErrorBudget p := by
    change 0 ≤ mixedErrorPairBudget (mixedErrorPairBudget p)
    exact hpair.trans (le_mixedErrorPairBudget hpair)
  have hb : mixedErrorPairBudget p + mixedErrorBudget p ≤ (p + C) ^ C := by
    simpa [X, R, T, mixedErrorPairBudget, mixedErrorBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget p hp
  constructor <;> linarith only [hpair, hglobal, hb]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFixedReduction
namespace OAI

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

def translationCodeEquiv (k : Fin 4 → Fin V.outputDim) :
    D.TranslationCode k ≃
      (Σ a₂ : MixedExpansionIndex V, Σ a₄ : MixedExpansionIndex V,
        Fin (D.translation.selectedExpansion (k 1) a₂).count ×
          Fin (D.translation.selectedExpansion (k 3) a₄).count) where
  toFun t := ⟨t.second, t.fourth, t.secondTerm, t.fourthTerm⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance translationCodeFintype (k : Fin 4 → Fin V.outputDim) :
    Fintype (D.TranslationCode k) :=
  Fintype.ofEquiv _ (D.translationCodeEquiv k).symm

theorem translationCode_card (k : Fin 4 → Fin V.outputDim) :
    (Fintype.card (D.TranslationCode k) : ℝ) ≤ Real.exp (4 * P) := by
  classical
  have he := D.translation.right_dimension
  calc
    (Fintype.card (D.TranslationCode k) : ℝ) =
        ∑ a₂ : MixedExpansionIndex V, ∑ a₄ : MixedExpansionIndex V,
          ((D.translation.selectedExpansion (k 1) a₂).count : ℝ) *
            ((D.translation.selectedExpansion (k 3) a₄).count : ℝ) := by
      rw [Fintype.card_congr (D.translationCodeEquiv k)]
      simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
        Nat.cast_sum, Nat.cast_mul]
    _ ≤ ∑ _ : MixedExpansionIndex V, ∑ _ : MixedExpansionIndex V,
        Real.exp P * Real.exp P := by
      apply Finset.sum_le_sum
      intro a₂ _
      apply Finset.sum_le_sum
      intro a₄ _
      exact mul_le_mul (D.translation.selectedExpansion (k 1) a₂).count_bound
        (D.translation.selectedExpansion (k 3) a₄).count_bound
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (Fintype.card (MixedExpansionIndex V) : ℝ) *
        ((Fintype.card (MixedExpansionIndex V) : ℝ) * (Real.exp P * Real.exp P)) := by
      simp
    _ ≤ Real.exp P * (Real.exp P * (Real.exp P * Real.exp P)) := by
      gcongr
    _ = Real.exp (4 * P) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3.NativeMixedReductionData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

theorem integerProduct_fourPoint_factorization (A B : ZMod N → ℤ → ℂ)
    (h₁ h₂ h₃ h₄ : H) (a n : ℤ) :
    fourPointProduct (U.integerProduct (fun h x => A h x * B h x) h₁)
      (U.integerProduct (fun h x => A h x * B h x) h₂)
      (U.integerProduct (fun h x => A h x * B h x) h₃)
      (U.integerProduct (fun h x => A h x * B h x) h₄) a n =
      fourPointProduct (A h₁) (A h₂) (A h₃) (A h₄) a n *
      fourPointProduct (B h₁) (B h₂) (B h₃) (B h₄) a n *
      fourPointProduct (U.integerLower h₁) (U.integerLower h₂)
        (U.integerLower h₃) (U.integerLower h₄) a n := by
  simp only [fourPointProduct, integerProduct, star_mul]
  ring

end Erdos3.NativeCrossWitnesses

end

end OAI
end


