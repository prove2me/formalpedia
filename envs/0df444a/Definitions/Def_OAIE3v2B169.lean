-- Prove2me | Definitions.Def_OAIE3v2B169
-- name    : OAIE3v2B169
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:41:02.482029+00:00
-- url     : https://prove2.me/theorems/f0d61d63-d4eb-4ce2-8a9d-7a1d1aef707d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 171 of 311
-- statement:
--   Definitions bundle 171 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B153`, `OAIE3v2B154`, `OAIE3v2B155`, `OAIE3v2B156`, `OAIE3v2B157` of this split.
--
--   Modules: `Estimates/FirstCoefficientDerivativeBounds.lean`, `Estimates/FormalCurrentInputBounds.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/NormalizedCommonFamily.lean`, `Estimates/RealReducedCoefficientMap.lean`, `Estimates/ReducedDiagonalBounds.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/StepOneSymbolLinearPart.lean`, `Estimates/UnnormalizedCommonSymbolFactorization.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Linear/StepOneGradedKernel.lean`, `Nilpotent/StepOneGradedNiltestSplitting.lean`, `Nilpotent/UniformControlledBracketStage.lean`, `Polynomial/GradedPolynomialSymbolInverse.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B153
import Definitions.Def_OAIE3v2B154
import Definitions.Def_OAIE3v2B155
import Definitions.Def_OAIE3v2B156
import Definitions.Def_OAIE3v2B157

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalCurrentInputBounds
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {σ κ ι μ L : Type*} [Fintype κ] [Fintype ι] [Fintype μ]
  [LieRing L] [LieAlgebra ℚ L] {V : Submodule ℚ L}

omit [Fintype μ] in
theorem projected_lift_array_homogeneous (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) {j : ℕ} (hj : 2 ≤ j)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ t, S t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) :
    ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 →
      coefficients (liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α = 0 := by
  intro α hα
  apply liftQuotientArray_coefficient_eq_zero
  intro t
  rw [projected_lift_residual_eq (b.baseChange ℝ) w (by omega) (S t) _ (hk t)]
  exact shifted_one_projection_homogeneous (b.baseChange ℝ) w (S t) (hS t) (by omega) α hα

theorem projected_lift_array_grid (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) {j : ℕ} (hj : 2 ≤ j)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    (l : ℕ) (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hR : ∀ t α, (b.baseChange ℝ).equivFun (coefficients (R t) α) ∈ realDenominatorGrid l) :
    ∀ α, coefficients (liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  intro α
  apply liftQuotientArray_grid
  intro t
  rw [projected_lift_residual_eq (b.baseChange ℝ) w (by omega) (R t) _ (hk t), coefficients_map]
  apply realQuotientCoordinateMap_grid b f l
  exact basisCoordinateProjection_real_grid (b.baseChange ℝ) {n | w n = j} l _ (hR t α)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareRealRelativePart_mul_coord (hw : ∀ i, 0 < w i)
    (g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareRealRelativePart w (g * h)).coord =
      (F.reducedSquareRealRelativePart w g).coord +
      (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) *
        F.reducedSquareRealRelativePart w h *
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g))⁻¹).coord := by
  have hk : F.reducedSquareRealSymbolHom w
      (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) *
        F.reducedSquareRealRelativePart w h *
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g))⁻¹) = 1 := by
    simp only [map_mul, map_inv, F.reducedSquareRealSymbolHom_diagonal,
      F.reducedSquareRealRelativePart_projection, mul_one, mul_inv_cancel]
  rw [F.reducedSquareRealRelativePart_mul, coord_mul]
  exact F.reducedSquareRealSymbolKernel_bch w hw
    (F.reducedSquareRealRelativePart_coord_kernel w g) (congrArg NilpotentLieBCHGroup.coord hk)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw in
theorem reducedSquareRealRelativePart_triple_coord
    (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareRealRelativePart w (E * P * R)).coord =
      (F.reducedSquareRealRelativePart w E).coord +
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w E) *
          F.reducedSquareRealRelativePart w P *
            (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w E))⁻¹).coord +
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w (E * P)) *
          F.reducedSquareRealRelativePart w R *
            (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w (E * P)))⁻¹).coord := by
  rw [F.reducedSquareRealRelativePart_mul_coord w hw (E * P) R,
    F.reducedSquareRealRelativePart_mul_coord w hw E P]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realNormalizedFirstCoefficientMap_sub_mem_fast_iff
    (x y : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w x - F.realNormalizedFirstCoefficientMap w y ∈
        F.realFirstCoefficientFastSubmodule w hw U ↔
      F.realReducedRelativeSquareSymbolMap w hw x - F.realReducedRelativeSquareSymbolMap w hw y ∈
        U.baseChange ℝ := by
  rw [← map_sub, ← map_sub]
  exact F.realNormalizedFirstCoefficientMap_mem_fast_iff w hw U (x - y)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw in
theorem reducedSquareRealRelative_conjugation
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ x = 0) :
    dualAdjoint g x =
      (g * (⟨x⟩ : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) * g⁻¹).coord := by
  let I := (realLieHomToRat (realificationLieHom (F.reducedSquareSndSymbolMap w))).ker
  apply dualAdjoint_eq_conjugation_of_abelian_ideal I _ g x hx
  intro a ha b hb
  exact F.reducedSquareRealSymbolKernel_lie_eq_zero w hw ha hb

theorem realReducedRelativeSquareSymbolMap_conjugation
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realReducedRelativeSquareSymbolMap w hw (F.realNormalizedRelativeAdjoint w g x) =
      (F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g) *
        (⟨F.realReducedRelativeSquareSymbolMap w hw x⟩ :
          F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) *
        (F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g))⁻¹).coord := by
  rw [F.realReducedRelativeSquareSymbolMap_adjoint]
  exact F.reducedSquareRealRelative_conjugation w hw _ _
    (F.realReducedRelativeSquareSymbolMap_projection w hw x)

theorem realReducedRelativeSquareSymbolMap_conjugation_of_eq
    (g : F.RealAdaptedPolynomialGroup w) (h : F.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (r : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.adaptedReducedRealSymbolHom w g = h)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = r.coord) :
    F.realReducedRelativeSquareSymbolMap w hw (F.realNormalizedRelativeAdjoint w g x) =
      (F.reducedSquareRealDiagonalHom w h * r * (F.reducedSquareRealDiagonalHom w h)⁻¹).coord := by
  rw [F.realReducedRelativeSquareSymbolMap_conjugation, hg, hx]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem realReducedRelativeCoefficient_same_diagonal
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    {g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w}
    (hg : g.coord ∈ realificationLieSubalgebra U) (hh : h.coord ∈ realificationLieSubalgebra U)
    (hproj : F.reducedSquareRealSymbolHom w g = F.reducedSquareRealSymbolHom w h) :
    F.realReducedRelativeCoefficient w hw g - F.realReducedRelativeCoefficient w hw h ∈
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) := by
  obtain ⟨x, hx⟩ := F.reducedSquareRealRelativePart_exists_preimage w hw g
  obtain ⟨y, hy⟩ := F.reducedSquareRealRelativePart_exists_preimage w hw h
  rw [← F.realReducedRelativeCoefficient_of_preimage w hw g x hx,
    ← F.realReducedRelativeCoefficient_of_preimage w hw h y hy,
    F.realNormalizedFirstCoefficientMap_sub_mem_fast_iff w hw]
  rw [hx, hy]
  exact F.reducedSquareRealRelative_same_diagonal_mod_kernel w hw U hg hh hproj

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF
local notation "Ba" => F.adaptedMonomialBasis b ω hF w

theorem realReducedNativeLift_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolSlowBound bq ωq hq w T M g) :
    F.RealAdaptedCoefficientBound b ω hF w T M (F.realReducedNativeLift b ω hF w g).coord := by
  intro z
  by_cases hz : ∃ j, reducedNativeIndex s w ω j = z
  · obtain ⟨j, rfl⟩ := hz
    change |((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord)
      (reducedNativeIndex s w ω j)| ≤ _
    rw [F.reducedNativeSection_real_coordinate]
    exact hg j
  · change |((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) z| ≤ _
    rw [F.reducedNativeSection_real_coordinate_zero b ω hF w g.coord z (fun j hj => hz ⟨j, hj⟩), abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT z.val.1).le

theorem realReducedNativeLift_grid (l : ℕ) (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolRationalGrid bq ωq hq w l g) :
    F.RealAdaptedCoefficientGrid b ω hF w l (F.realReducedNativeLift b ω hF w g).coord := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => if hz : ∃ j, reducedNativeIndex s w ω j = z then a hz.choose else 0, ?_⟩
  funext z
  change ((if hz : ∃ j, reducedNativeIndex s w ω j = z then a hz.choose else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) z
  by_cases hz : ∃ j, reducedNativeIndex s w ω j = z
  · rw [dif_pos hz]
    have hc := F.reducedNativeSection_real_coordinate b ω hF w g.coord hz.choose
    have he := congrArg (fun t => ((Ba).baseChange ℝ).repr
      ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) t) hz.choose_spec
    rw [he.symm.trans hc]
    exact congrFun ha hz.choose
  · rw [dif_neg hz, Int.cast_zero,
      F.reducedNativeSection_real_coordinate_zero b ω hF w g.coord z (fun j hj => hz ⟨j, hj⟩), mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF

theorem exists_reduced_native_factorization (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (l : ℕ) (g : F.RealAdaptedPolynomialGroup w)
    (A P R : F.quotientTop.RealPolynomialSymbolGroup w)
    (hprod : A * P * R = F.adaptedReducedRealSymbolHom w g)
    (hA : F.quotientTop.SymbolSlowBound bq ωq hq w T M A)
    (hR : F.quotientTop.SymbolRationalGrid bq ωq hq w l R) :
    ∃ a p r : F.RealAdaptedPolynomialGroup w,
      a * p * r = g ∧ F.adaptedReducedRealSymbolHom w a = A ∧
      F.adaptedReducedRealSymbolHom w p = P ∧ F.adaptedReducedRealSymbolHom w r = R ∧
      F.RealAdaptedCoefficientBound b ω hF w T M a.coord ∧
      F.RealAdaptedCoefficientGrid b ω hF w l r.coord ∧
      coefficients (F.realAdaptedPolynomialMap w a.coord) 0 = 0 ∧
      coefficients (F.realAdaptedPolynomialMap w r.coord) 0 = 0 ∧
      coefficients (F.realAdaptedPolynomialMap w p.coord) 0 =
        coefficients (F.realAdaptedPolynomialMap w g.coord) 0 := by
  let a := F.realReducedNativeLift b ω hF w A
  let r := F.realReducedNativeLift b ω hF w R
  let p := a⁻¹ * g * r⁻¹
  have hapr : a * p * r = g := by simp [p, mul_assoc]
  have ha : F.adaptedReducedRealSymbolHom w a = A := F.adaptedReducedRealSymbolHom_lift b ω hF w A
  have hr : F.adaptedReducedRealSymbolHom w r = R := F.adaptedReducedRealSymbolHom_lift b ω hF w R
  have hp : F.adaptedReducedRealSymbolHom w p = P := by
    change F.adaptedReducedRealSymbolHom w (a⁻¹ * g * r⁻¹) = P
    rw [map_mul, map_mul, map_inv, map_inv, ha, hr, ← hprod]
    simp [mul_assoc]
  have ha0 := F.realReducedNativeLift_constant b ω hF w A
  have hr0 := F.realReducedNativeLift_constant b ω hF w R
  refine ⟨a, p, r, hapr, ha, hp, hr, F.realReducedNativeLift_slow b ω hF w T hT hM A hA,
    F.realReducedNativeLift_grid b ω hF w l R hR, ha0, hr0, ?_⟩
  have hpoly : F.realAdaptedPolynomialGroupHom w a * F.realAdaptedPolynomialGroupHom w p *
      F.realAdaptedPolynomialGroupHom w r = F.realAdaptedPolynomialGroupHom w g := by
    rw [← map_mul, ← map_mul, hapr]
  exact F.realification.polynomial_factor_middle_constant w
    (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialGroupHom w a)
    (F.realAdaptedPolynomialGroupHom w p) (F.realAdaptedPolynomialGroupHom w r) hpoly ha0 hr0

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

theorem realReducedRelativeCoefficient_eq_map (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.realReducedRelativeCoefficient w hw g =
      F.realReducedSquareCoefficientMap w (F.reducedSquareRealRelativePart w g).coord := by
  obtain ⟨x, hx⟩ := F.reducedSquareRealRelativePart_exists_preimage w hw g
  rw [← hx, F.realReducedSquareCoefficientMap_relative]
  exact (F.realReducedRelativeCoefficient_of_preimage w hw g x hx).symm

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem realReducedRelativeSquareSymbolMap_triple_preimage
    (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (a b : F.RealAdaptedPolynomialGroup w)
    (ha : F.adaptedReducedRealSymbolHom w a = F.reducedSquareRealSymbolHom w E)
    (hb : F.adaptedReducedRealSymbolHom w b = F.reducedSquareRealSymbolHom w P)
    (x y z : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = (F.reducedSquareRealRelativePart w E).coord)
    (hy : F.realReducedRelativeSquareSymbolMap w hw y = (F.reducedSquareRealRelativePart w P).coord)
    (hz : F.realReducedRelativeSquareSymbolMap w hw z = (F.reducedSquareRealRelativePart w R).coord) :
    F.realReducedRelativeSquareSymbolMap w hw
      (x + F.realNormalizedRelativeAdjoint w a y + F.realNormalizedRelativeAdjoint w (a * b) z) =
      (F.reducedSquareRealRelativePart w (E * P * R)).coord := by
  have hab : F.adaptedReducedRealSymbolHom w (a * b) = F.reducedSquareRealSymbolHom w (E * P) := by
    rw [map_mul, map_mul, ha, hb]
  have hy' := F.realReducedRelativeSquareSymbolMap_conjugation_of_eq w hw a
    (F.reducedSquareRealSymbolHom w E) y (F.reducedSquareRealRelativePart w P) ha hy
  have hz' := F.realReducedRelativeSquareSymbolMap_conjugation_of_eq w hw (a * b)
    (F.reducedSquareRealSymbolHom w (E * P)) z (F.reducedSquareRealRelativePart w R) hab hz
  rw [map_add, map_add]
  exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hx hy') hz').trans
    (F.reducedSquareRealRelativePart_triple_coord w hw E P R).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem coefficient_common_derivative_identity (w : σ → ℕ)
    (A B D : F.RealAdaptedPolynomialGroup w)
    (YA YB YD YX ε μ u Z v : F.RealFirstCoefficientModule w)
    (hprod : YX = YA + F.realFirstCoefficientAdjoint w A YB +
      F.realFirstCoefficientAdjoint w (A * B) YD)
    (hsquare : YX - ε - F.realFirstCoefficientAdjoint w (A * B * D) μ =
      u + F.realFirstCoefficientAdjoint w A Z + F.realFirstCoefficientAdjoint w (A * B) v) :
    YB = F.realFirstCoefficientAdjoint w A⁻¹ (ε + u - YA) +
      F.realFirstCoefficientAdjoint w B (v + F.realFirstCoefficientAdjoint w D μ - YD) + Z := by
  apply (F.realFirstCoefficientAdjoint w A).injective
  simp only [map_add, map_sub, F.realFirstCoefficientAdjoint_cancel_inv,
    ← F.realFirstCoefficientAdjoint_mul, ← mul_assoc]
  calc
    F.realFirstCoefficientAdjoint w A YB =
        (YX - ε - F.realFirstCoefficientAdjoint w (A * B * D) μ) - YA -
          F.realFirstCoefficientAdjoint w (A * B) YD + ε +
          F.realFirstCoefficientAdjoint w (A * B * D) μ := by rw [hprod]; abel
    _ = (u + F.realFirstCoefficientAdjoint w A Z + F.realFirstCoefficientAdjoint w (A * B) v) -
        YA - F.realFirstCoefficientAdjoint w (A * B) YD + ε +
        F.realFirstCoefficientAdjoint w (A * B * D) μ := by rw [hsquare]
    _ = _ := by abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

section Elementary

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem firstCoefficientSlowBound_add (w : σ → ℕ) (T : σ → ℝ) (M N : ℝ)
    (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x)
    (hy : F.FirstCoefficientSlowBound e ω hF w T N y) :
    F.FirstCoefficientSlowBound e ω hF w T (M + N) (x + y) := by
  intro i
  simp only [map_add, Finsupp.add_apply]
  exact (abs_add_le _ _).trans ((add_le_add (hx i) (hy i)).trans_eq (add_div M N _).symm)

theorem firstCoefficientSlowBound_mono (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x) :
    F.FirstCoefficientSlowBound e ω hF w T N x := by
  intro i
  exact (hx i).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT _).le)

theorem firstCoefficientGrid_add (w : σ → ℕ) (l : ℕ) (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid e ω hF w l x) (hy : F.FirstCoefficientGrid e ω hF w l y) :
    F.FirstCoefficientGrid e ω hF w l (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  funext i
  change ((a i + b i : ℤ) : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis e ω hF w).repr (x + y) i
  simp only [Int.cast_add, map_add, Finsupp.add_apply, mul_add]
  exact congrArg₂ (· + ·) (congrFun ha i) (congrFun hb i)

theorem firstCoefficientGrid_mono (w : σ → ℕ) {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (x : F.RealFirstCoefficientModule w) (hx : F.FirstCoefficientGrid e ω hF w l x) :
    F.FirstCoefficientGrid e ω hF w m x := realDenominatorGrid_subset_of_dvd hl hlm hx

end Elementary

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

universe uσ uι uL

def ReducedRelativeCoefficientSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (E R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
        (_hE : F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) T (Real.exp p) E)
        (_hR : F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) l R),
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
          (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) E) ∧
        F.FirstCoefficientGrid e ω hF (fun _ => 1) m
          (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) R)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section General

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedSymbolPolynomial_unit_eval (x : F.AssociatedGraded) :
    eval (fun _ : Unit => (1 : ℚ)) (F.gradedSymbolPolynomial e ω hF (fun _ : Unit => 1) x) = x := by
  have he : (eval (fun _ : Unit => (1 : ℚ))).comp
      (F.gradedSymbolPolynomial e ω hF (fun _ : Unit => 1)) = LinearMap.id := by
    apply (F.associatedGradedBasis e ω hF).ext
    intro i
    rw [LinearMap.comp_apply, F.associatedGradedBasis_apply, F.gradedSymbolPolynomial_basis,
      eval_monomial]
    simp
  exact LinearMap.congr_fun he x

theorem adaptedGradedPolynomialLie_unit_eval (p : F.adaptedLieSubalgebra (fun _ : Unit => 1)) :
    eval (fun _ : Unit => (1 : ℚ)) (F.adaptedGradedPolynomialLie e ω hF (fun _ : Unit => 1) p) =
      F.polynomialSymbolMap (fun _ : Unit => 1) p := by
  rw [F.adaptedGradedPolynomialLie_apply, F.adaptedShiftedGradedPolynomial_apply,
    F.shiftedGradedPolynomial_zero, F.gradedSymbolPolynomial_unit_eval]

end General

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

def CoefficientCorrectionSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (A D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (_hA : F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp p) A.coord)
        (_hD : F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l D.coord)
        (h : σ → ℤ) (_hh : ∀ i, |(h i : ℝ)| ≤ T i)
        (ε u μ v : F.RealFirstCoefficientModule (fun _ : σ => 1))
        (_hε : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp p) ε)
        (_hu : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp p) u)
        (_hμ : F.FirstCoefficientGrid e ω hF (fun _ => 1) l μ)
        (_hv : F.FirstCoefficientGrid e ω hF (fun _ => 1) l v),
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
          (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) ε u) ∧
        F.FirstCoefficientGrid e ω hF (fun _ => 1) m
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) μ v)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module

universe uσ uι uL

def SynchronizedSquareBoundSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (A D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (_hA : F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp p) A.coord)
        (_hD : F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l D.coord)
        (h : σ → ℤ) (_hh : ∀ i, |(h i : ℝ)| ≤ T i)
        (E R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
        (_hE : F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) T (Real.exp p) E)
        (_hR : F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) l R)
        (ε μ : F.RealFirstCoefficientModule (fun _ : σ => 1))
        (_hε : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp p) ε)
        (_hμ : F.FirstCoefficientGrid e ω hF (fun _ => 1) l μ),
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
          (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) ε
            (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) E)) ∧
        F.FirstCoefficientGrid e ω hF (fun _ => 1) m
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) μ
            (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) R))

end NilpotentLieFiltration
end Erdos3

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

local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
local notation "E₁" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "SGroup" => F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1)

def NormalizedCommonFamilySpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (_hA : F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp p) A.coord)
        (_hD : F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l D.coord)
        (Hshifts : Finset (σ → ℤ))
        (r : (σ → ℤ) → F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (E P R : (σ → ℤ) → SGroup) (P₀ : SGroup)
        (ε μ : (σ → ℤ) → ℝ ⊗[ℚ] L)
        (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
        (_hf : ∀ h ∈ Hshifts,
          F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) (r h)).coord =
            normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε h) (-μ h)
              (F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord))
        (_hs : ∀ h ∈ Hshifts,
          F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) (r h)).coord =
            F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord)
        (_hr : ∀ h ∈ Hshifts, F.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h) =
          E h * P h * R h)
        (_hleft : ∀ h ∈ Hshifts, F.adaptedReducedRealSymbolHom (fun _ => 1) A =
          F.reducedSquareRealSymbolHom (fun _ => 1) (E h))
        (_hmiddle : ∀ h ∈ Hshifts, F.adaptedReducedRealSymbolHom (fun _ => 1) B =
          F.reducedSquareRealSymbolHom (fun _ => 1) (P h))
        (_hP : ∀ h ∈ Hshifts, (P h).coord ∈ realificationLieSubalgebra U)
        (_hP₀ : P₀.coord ∈ realificationLieSubalgebra U)
        (_hdiag : ∀ h ∈ Hshifts, F.reducedSquareRealSymbolHom (fun _ => 1) (P h) =
          F.reducedSquareRealSymbolHom (fun _ => 1) P₀)
        (_hE : ∀ h ∈ Hshifts, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
          (fun _ => 1) T (Real.exp p) (E h))
        (_hR : ∀ h ∈ Hshifts, F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
          (fun _ => 1) l (R h))
        (_hε : ∀ h ∈ Hshifts, ∀ i, |(b.baseChange ℝ).repr (ε h) i| ≤ Real.exp p)
        (_hμ : ∀ h ∈ Hshifts, (fun i => (b.baseChange ℝ).repr (μ h) i) ∈ realDenominatorGrid l),
        ∃ S K : (σ → ℤ) → E₁, ∀ h ∈ Hshifts,
          (F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
            (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (K h) +
              F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) P₀) ∈ J) ∧
          F.FirstCoefficientSlowBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C)) (S h) ∧
          F.FirstCoefficientGrid b ω hF (fun _ => 1) m (K h)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepOneSymbolLinearPart
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def stepOneFrequencyKernel (F : NilpotentLieFiltration L 1) (η : L →ₗ[ℚ] ℚ) :
    LieSubalgebra ℚ L :=
  { LinearMap.ker η with
    lie_mem' := fun {a b} _ _ => by
      change η ⁅a, b⁆ = 0
      rw [F.stepOne_lie_eq_zero, map_zero] }

theorem mem_real_stepOneFrequencyKernel (F : NilpotentLieFiltration L 1) (η : L →ₗ[ℚ] ℚ)
    (x : ℝ ⊗[ℚ] L) :
    x ∈ realificationLieSubalgebra (F.stepOneFrequencyKernel η) ↔ realifyFunctional η x = 0 :=
  mem_realified_frequency_kernel_iff η x

theorem exists_stepOne_linear_splitting {σ ι : Type*} [Fintype σ] [DecidableEq σ]
    (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L)
    (η : L →ₗ[ℚ] ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] L)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (E P R : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      0 < m ∧ m ≤ H ∧ E * P * R = F.realification.linearPolynomialGroup a ∧
      F.PolynomialSlowBound b (fun _ => 1) (fun i => (T i : ℝ)) ((H : ℝ) / (2 * δ)) E ∧
      F.PolynomialRationalGrid b (fun _ => 1) m R ∧
      (∀ t : σ → ℝ, eval₂ t (P.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
        realificationLieSubalgebra (F.stepOneFrequencyKernel η)) ∧
      coefficients (P.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  obtain ⟨m, e, p, r, hm, hmH, hsum, hp, he, hr⟩ :=
    exists_linear_frequency_splitting b η hH hheight T hT a hδ hbias
  let E := F.realification.linearPolynomialGroup e
  let P := F.realification.linearPolynomialGroup p
  let R := F.realification.linearPolynomialGroup r
  refine ⟨m, E, P, R, hm, hmH, ?_, ?_, F.polynomialRationalGrid_linear b m r hr, ?_, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    rw [(F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).stepOne_coord_mul,
      (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).stepOne_coord_mul]
    apply Subtype.ext
    change linearPolynomial e + linearPolynomial p + linearPolynomial r = linearPolynomial a
    rw [← map_add, ← map_add]
    congr 1
    funext i
    exact hsum i
  · apply F.polynomialSlowBound_linear b (fun i => (T i : ℝ)) (fun i => Nat.cast_pos.mpr (hT i))
      (div_nonneg (Nat.cast_nonneg H) (by positivity))
    intro i j
    apply (he i j).trans_eq
    field_simp
  · intro t
    rw [F.mem_real_stepOneFrequencyKernel]
    change realifyFunctional η (eval₂ t (linearPolynomial p)) = 0
    simp only [eval₂_linearPolynomial, map_sum, map_smul, hp, smul_zero, Finset.sum_const_zero]
  · exact coefficients_linearPolynomial_zero p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L)

variable (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include F b hlayers in
theorem stepOne_basis_weight (i : ι) : ω i = 1 := by
  have hpos := F.adaptedBasis_weight_pos b ω hlayers i
  have hle := F.adaptedBasis_weight_le_step b ω hlayers i
  omega

theorem stepOne_gradedPieceProjection (j : ℕ) (x : L) :
    F.gradedPieceProjection b ω hlayers j x =
      if j = 1 then F.stepOneGradedEquiv b ω hlayers x else 0 := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [F.gradedPieceProjection_coordinate, F.stepOne_basis_weight b ω hlayers i]
  by_cases hj : j = 1
  · simp only [hj, ite_true, F.stepOneGradedEquiv_coordinate]
  · simp only [hj, Ne.symm hj, ite_false, map_zero, Finsupp.zero_apply]

theorem stepOne_graded_submodule (U : Submodule ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U := by
  intro j x hx
  have he : basisGradeProjection (F.associatedGradedBasis b ω hlayers) ω j x =
      if j = 1 then x else 0 := by
    classical
    apply (F.associatedGradedBasis b ω hlayers).repr.injective
    ext i
    rw [basisGradeProjection_repr, F.stepOne_basis_weight b ω hlayers i]
    by_cases hj : j = 1
    · simp only [hj, ite_true]
    · simp only [hj, Ne.symm hj, ite_false, map_zero, Finsupp.zero_apply]
  rw [he]
  split_ifs
  · exact hx
  · exact U.zero_mem

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1)

theorem stepOne_symbol_linearPart (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.polynomialSymbolMap (fun _ => 1)
      (F.linearPolynomialGroup (fun i => coefficients p.val (Finsupp.single i 1))).coord =
      F.polynomialSymbolMap (fun _ => 1) p := by
  have hp : DegreeLE (fun _ : σ => 1) 1 p.val :=
    F.adapted_degreeLE _ ((F.mem_adaptedSubmodule _ _).mp p.property)
  have he : F.adaptedConstant (fun _ : σ => 1) (coefficients p.val 0) +
      (F.linearPolynomialGroup (fun i => coefficients p.val (Finsupp.single i 1))).coord = p := by
    apply Subtype.ext
    exact (eq_affine_of_degreeLE_one p.val hp).symm
  calc
    _ = F.polynomialSymbolMap (fun _ : σ => 1)
        (F.adaptedConstant (fun _ : σ => 1) (coefficients p.val 0) +
          (F.linearPolynomialGroup (fun i => coefficients p.val (Finsupp.single i 1))).coord) := by
      rw [map_add, F.polynomialSymbolMap_constant, zero_add]
    _ = _ := congrArg (F.polynomialSymbolMap (fun _ : σ => 1)) he

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

theorem realGradedSymbolPolynomialHom_injective :
    Function.Injective (F.realGradedSymbolPolynomialHom e ω hF w) := by
  intro x y h
  apply NilpotentLieBCHGroup.ext
  apply F.realGradedSymbolPolynomial_injective e ω hF w
  exact congrArg NilpotentLieBCHGroup.coord h

theorem symbolSlowBound_of_gradedPolynomial (T : σ → ℝ) (M : ℝ) (x : F.RealPolynomialSymbolGroup w)
    (hx : CoefficientBound ((F.associatedGradedBasis e ω hF).baseChange ℝ) T M
      (F.realGradedSymbolPolynomialHom e ω hF w x).coord) : F.SymbolSlowBound e ω hF w T M x := by
  intro z
  rw [← F.realGradedSymbolPolynomial_coordinate e ω hF w x.coord z]
  exact hx z.val.1 z.val.2

theorem symbolRationalGrid_of_gradedPolynomial (l : ℕ) (x : F.RealPolynomialSymbolGroup w)
    (hx : CoefficientGrid ((F.associatedGradedBasis e ω hF).baseChange ℝ) l
      (F.realGradedSymbolPolynomialHom e ω hF w x).coord) : F.SymbolRationalGrid e ω hF w l x := by
  choose a ha using hx
  refine ⟨fun z => a z.val.1 z.val.2, ?_⟩
  funext z
  have hz := congrFun (ha z.val.1) z.val.2
  change (a z.val.1 z.val.2 : ℝ) = (l : ℝ) *
    ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial e ω hF w x.coord) z.val.1) z.val.2 at hz
  rw [F.realGradedSymbolPolynomial_coordinate e ω hF w x.coord z] at hz
  exact hz

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UniformControlledBracketStage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_formal_bracket_step
    (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    {j H J Q l : ℕ} (hj : 2 ≤ j)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p M : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p) (hcols : (Fintype.card ν : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : ((matrixDenominator (quotientCoordinateMatrix b f) * l : ℕ) : ℝ) ≤ Real.exp p)
    (hMp : (((Fintype.card μ : ℝ) + 1) * (Q + 1)) * M ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) ∈ E.baseChange ℝ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (hSgraded : ∀ t, S t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hRgraded : ∀ t, R t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hS : ∀ t α, coefficients (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hR : ∀ t α, coefficients (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ)
    (hsmall : ∀ t α, ‖(b.baseChange ℝ).equivFun (coefficients (S t) α)‖ ≤ M / monomialScale T α)
    (hrational : ∀ t α, (b.baseChange ℝ).equivFun (coefficients (R t) α) ∈ realDenominatorGrid l) :
    ∃ (m : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      let P' := A⁻¹ * P * B⁻¹
      let S' := fun t => dualAdjoint A⁻¹ (S t)
      let R' := fun t => dualAdjoint B (R t)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ d < j - 1,
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        (∀ d < j, ∀ t α,
          ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' S' R' ∧
        ∀ t α,
          coefficients (S' t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (R' t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          ⁅coefficients P'.coord α, (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  let π := (basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ
  let Pd := VectorPolynomial.map
    ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P.coord
  let small := liftQuotientArray f (fun t => VectorPolynomial.map π (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))
  let rational := liftQuotientArray f (fun t => VectorPolynomial.map π (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hcurrent := F.formal_current_bracket_equation_mod b w hlayers hgraded hs U (V.baseChange ℝ)
    hUV hV (fun t => (1 : ℝ) ⊗ₜ[ℚ] k t) hk hj P hPU S R hSR hR hlower
  have harr := bracket_array_equation_of_current_relation f k
    (basisGradeProjection (b.baseChange ℝ) w j) Pd S R (fun t α => by
      rw [coefficients_map]
      exact hcurrent t α)
  have hsmallhom := projected_lift_array_homogeneous b w f k hj hk S hSgraded
  have hrhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients rational α = 0 := by
    intro α hα
    change coefficients (liftQuotientArray f (fun t => VectorPolynomial.map π (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) α = 0
    rw [liftQuotientArray_map_neg, map_neg, Finsupp.neg_apply]
    rw [projected_lift_array_homogeneous b w f k hj hk R hRgraded α hα, neg_zero]
  have hsbound (α : σ →₀ ℕ) : ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α :=
    (projected_lift_array_bound b w f k hj hk hf T hTpos hM S hsmall α).trans
      (div_le_div_of_nonneg_right hMp (monomialScale_pos T hTpos α).le)
  have hrgrid (α : σ →₀ ℕ) : coefficients rational α ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
    change coefficients (liftQuotientArray f (fun t => VectorPolynomial.map π (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) α ∈ _
    rw [liftQuotientArray_map_neg, map_neg, Finsupp.neg_apply]
    exact realDenominatorGrid_neg _ (projected_lift_array_grid b w f k hj hk l R hrational α)
  have h := F.exists_controlled_bracket_polynomial_step b w hlayers U e f k (hgraded.baseChange b w)
    (by omega : 0 < j - 1) hE hEU hH (Nat.mul_pos (matrixDenominator_pos _) hl)
    hA he hp hrows hcols hHp hlp T hT P.coord Pd hPU hPgraded rfl
    (fun α => by rw [coefficients_map]; exact hPE α) small rational hsmallhom hrhom hsbound hrgrid harr
  obtain ⟨m, a, c, Pnew, hm, hmp, haQ, hcQ, hac, hahom, hchom, hanorm, hcgrid,
    hremove, _, hconstant, hnewgraded, _, _, _⟩ := h
  have hmatching := F.bracket_arrays_match_lifts b w hlayers hV f k j S R a c hS hR haQ hcQ
  have hstep := F.formal_bracket_induction_step_mod b w hlayers hgraded hs U (V.baseChange ℝ) hUV hV
    (fun t => (1 : ℝ) ⊗ₜ[ℚ] k t) hk hj P ⟨a⟩ ⟨c⟩ hPU
    (fun α => hEU _ (hac α).1) (fun α => hEU _ (hac α).2)
    (fun α => hE _ (hac α).1) (fun α => hE _ (hac α).2) S R hSR hR hlower hmatching.1 hmatching.2
  obtain ⟨hprod, hnewU, hbelow, hbrackets, hlifts, hrems⟩ := hstep
  refine ⟨m, ⟨a⟩, ⟨c⟩, hm, hmp, hac, hahom, hchom, hanorm, hcgrid,
    hprod, ?_, ?_, hnewU, hbelow, hbrackets, hlifts, hrems⟩
  · change coefficients (bchRemove s a P.coord c) 0 = coefficients P.coord 0
    rw [← hremove]
    exact hconstant
  · change bchRemove s a P.coord c ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    rw [← hremove]
    exact hnewgraded

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_bracket_step :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (_hk : ∀ z, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k z) = (1 : ℝ) ⊗ₜ[ℚ] k z)
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p M : ℝ} (_hp : 0 ≤ p) (_hM : 0 ≤ M)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hquotient : (Fintype.card ι : ℝ) ≤ p)
    (_hkernel : (Fintype.card κ : ℝ) ≤ p) (_hsource : (Fintype.card ν : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p) (_hMp : M ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) ∈ E.baseChange ℝ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (_hSgraded : ∀ z, S z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ z, R z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hS : ∀ z α, coefficients (S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hR : ∀ z α, coefficients (R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hlower : ∀ d < j - 1, ∀ z α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ)
    (_hsmall : ∀ z α, ‖(b.baseChange ℝ).equivFun (coefficients (S z) α)‖ ≤ M / monomialScale T α)
    (_hrational : ∀ z α, (b.baseChange ℝ).equivFun (coefficients (R z) α) ∈ realDenominatorGrid l),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈ realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let S' := fun z => dualAdjoint A⁻¹ (S z)
      let R' := fun z => dualAdjoint B (R z)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ d < j - 1,
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        (∀ d < j, ∀ z α,
          ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' S' R' ∧
        ∀ z α,
          coefficients (S' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (R' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          ⁅coefficients P'.coord α, (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  obtain ⟨C, hC, hCbound⟩ := exists_bracket_uniform_budget
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ ν σ _ _ _ _ _ _ s F b w hF E V hgraded hs U hUV hV e f k hk j H J Q l
    hj hE hEU hH hl hA he hf p M hp hM hambient hquotient hkernel hsource
    hHp hJp hQp hlp hMp T hT P hPU hPgraded hPE S R hSR hSgraded hRgraded hS hR hlower hsmall hrational
  let q := bracketConstructionBudget p
  let r := bracketCorrectionBudget p
  have hq : 0 ≤ q := bracketConstructionBudget_nonneg hp
  have hr : 0 ≤ r := bracketCorrectionBudget_nonneg hp
  obtain ⟨hpq, hrowsq, hdenq, hnormq⟩ := bracket_construction_budget_bounds hp
  have hrows : (Fintype.card (κ × ι) : ℝ) ≤ q := by
    apply le_trans _ hrowsq
    rw [Fintype.card_prod, Nat.cast_mul, pow_two]
    exact mul_le_mul (hkernel.trans (by linarith)) (hquotient.trans (by linarith))
      (Nat.cast_nonneg _) (by linarith)
  have hpplus : Real.exp p ≤ Real.exp ((p + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  have hD := matrixDenominator_le_exp_power (quotientCoordinateMatrix b f) hp 1 hquotient hambient (fun i z =>
    (show (((quotientCoordinateMatrix b f i z).den) : ℝ) ≤ Q from Nat.cast_le.mpr (hf i z).2).trans
      (hQp.trans hpplus))
  have hEden := matrixDenominator_le_exp_power (bracketLiftMatrix b e) hp 1 hambient hsource (fun i z =>
    (show (((bracketLiftMatrix b e i z).den) : ℝ) ≤ J from Nat.cast_le.mpr (he i z).2).trans
      (hJp.trans hpplus))
  have hden : ((matrixDenominator (quotientCoordinateMatrix b f) * l : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp p :=
        mul_le_mul hD hlp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdenq
  have hnorm : (((Fintype.card μ : ℝ) + 1) * (Q + 1)) * M ≤ Real.exp q := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp p :=
        mul_le_mul (current_layer_coordinate_factor_bound hp (Fintype.card μ) Q hambient hQp)
          hMp hM (Real.exp_nonneg _)
      _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hnormq
  have htotal : separationBudget q + r ≤ (p + C) ^ C := hCbound p hp
  have hcut : separationBudget q ≤ (p + C) ^ C := by linarith
  have hout : r ≤ (p + C) ^ C := by linarith [separationBudget_nonneg hq]
  have hTq : ∀ i, Real.exp (separationBudget q) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hcut).trans (hT i)
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  obtain ⟨m, A, B, hm, hmbound, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hbelow, hbrackets, hlifts, hremainders⟩ :=
    F.exists_controlled_formal_bracket_step b w hF hgraded hs Uq hUV hV e f k hk hj hE hEU
      hH hl hA he hf hq hM hrows (hsource.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
      hden hnorm T hTq P hPU hPgraded hPE S R hSR hSgraded hRgraded hS hR hlower hsmall hrational
  have houtputs := bracket_correction_budget_bounds hp (Fintype.card ν) J
    (matrixDenominator (bracketLiftMatrix b e)) hsource hJp hEden
  let n := matrixDenominator (bracketLiftMatrix b e) * m
  have hnbound : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (matrixDenominator (bracketLiftMatrix b e) : ℝ) * (m : ℝ) := Nat.cast_mul _ _
      _ ≤ (matrixDenominator (bracketLiftMatrix b e) : ℝ) * Real.exp ((q + 2) ^ 36) :=
        mul_le_mul_of_nonneg_left hmbound (Nat.cast_nonneg _)
      _ ≤ Real.exp r := houtputs.2
      _ ≤ _ := Real.exp_le_exp.mpr hout
  refine ⟨n, A, B, Nat.mul_pos (matrixDenominator_pos _) hm, hnbound,
    hAB, hAhom, hBhom, ?_, hBgrid, hprod, hconstant, hnewgraded, hnewU,
    hbelow, hbrackets, hlifts, hremainders⟩
  intro α
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  exact (hAnorm α).trans (div_le_div_of_nonneg_right
    (houtputs.1.trans (Real.exp_le_exp.mpr hout)) (monomialScale_pos T hTpos α).le)

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

noncomputable def nativeSymbolNormalize (g : F.RealAdaptedPolynomialGroup w) :
    F.RealAdaptedPolynomialGroup w :=
  F.realAdaptedPolynomialGroupLift w b ω hF
    (F.realPolynomialSymbolLift b ω hF w
      (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)))

theorem nativeSymbolNormalize_constant (g : F.RealAdaptedPolynomialGroup w) :
    coefficients (F.realAdaptedPolynomialMap w (F.nativeSymbolNormalize b ω hF w g).coord) 0 = 0 := by
  let X : F.RealPolynomialSymbolGroup w :=
    F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)
  have hX : coefficients (F.realSymbolRepresentative b ω hF w X.coord) 0 = 0 :=
    F.realSymbolRepresentative_constant b ω hF w X.coord
  change coefficients (F.realAdaptedPolynomialGroupHom w
    (F.realAdaptedPolynomialGroupLift w b ω hF (F.realPolynomialSymbolLift b ω hF w X))).coord.val 0 = 0
  rw [F.realAdaptedPolynomialGroupHom_lift, F.realPolynomialSymbolLift_log, hX]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3

namespace NativeIntegerVectorEquivalence

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p q : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}

theorem mono (E : NativeIntegerVectorEquivalence s p chi eta) (hpq : p ≤ q) :
    NativeIntegerVectorEquivalence s q chi eta where
  left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
  right_dimension := E.right_dimension.trans (Real.exp_le_exp.mpr hpq)
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.mono hpq⟩

end NativeIntegerVectorEquivalence

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.StepOneGradedKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def stepOneGradedKernel (η : L →ₗ[ℚ] ℚ) : LieSubalgebra ℚ F.AssociatedGraded :=
  F.associatedGradedFiltration.stepOneFrequencyKernel (F.stepOneGradedFrequency b ω hlayers η)

theorem mem_stepOneGradedKernel (η : L →ₗ[ℚ] ℚ) (x : F.AssociatedGraded) :
    x ∈ F.stepOneGradedKernel b ω hlayers η ↔ F.stepOneGradedFrequency b ω hlayers η x = 0 := Iff.rfl

theorem stepOneGradedKernel_span {κ : Type*} (η : L →ₗ[ℚ] ℚ) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = (F.stepOneFrequencyKernel η).toSubmodule) :
    Submodule.span ℚ (Set.range (fun i => F.stepOneGradedEquiv b ω hlayers (v i))) =
      (F.stepOneGradedKernel b ω hlayers η).toSubmodule := by
  have hmap : (F.stepOneFrequencyKernel η).toSubmodule.map
      (F.stepOneGradedEquiv b ω hlayers).toLinearEquiv.toLinearMap =
      (F.stepOneGradedKernel b ω hlayers η).toSubmodule := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change F.stepOneGradedFrequency b ω hlayers η (F.stepOneGradedEquiv b ω hlayers x) = 0
      rw [F.stepOneGradedFrequency_equiv]
      exact hx
    · intro hy
      refine ⟨(F.stepOneGradedEquiv b ω hlayers).symm y, hy, ?_⟩
      exact (F.stepOneGradedEquiv b ω hlayers).apply_symm_apply y
  calc
    _ = (Submodule.span ℚ (Set.range v)).map
        (F.stepOneGradedEquiv b ω hlayers).toLinearEquiv.toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = _ := by rw [hv, hmap]

theorem stepOne_gradedPieceProjection_mem_kernel (η : L →ₗ[ℚ] ℚ) (j : ℕ)
    {x : L} (hx : x ∈ F.stepOneFrequencyKernel η) :
    F.gradedPieceProjection b ω hlayers j x ∈ F.stepOneGradedKernel b ω hlayers η := by
  rw [F.stepOne_gradedPieceProjection]
  split_ifs
  · change F.stepOneGradedFrequency b ω hlayers η (F.stepOneGradedEquiv b ω hlayers x) = 0
    rw [F.stepOneGradedFrequency_equiv]
    exact hx
  · exact (F.stepOneGradedKernel b ω hlayers η).zero_mem

theorem stepOne_symbol_values_in_gradedKernel (η : L →ₗ[ℚ] ℚ)
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ t : σ → ℝ, eval₂ t p ∈ realificationLieSubalgebra (F.stepOneFrequencyKernel η)) :
    ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realSymbolOfPolynomial b ω hlayers w p)) ∈
        realificationLieSubalgebra (F.stepOneGradedKernel b ω hlayers η) := by
  have hc := (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (F.stepOneFrequencyKernel η)).toSubmodule p).mp hp
  apply (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (F.stepOneGradedKernel b ω hlayers η)).toSubmodule _).mpr
  intro α
  rw [F.realGradedSymbolPolynomial_coefficient_of_polynomial]
  exact baseChange_mem_of_mapsTo (F.stepOneFrequencyKernel η).toSubmodule
    (F.stepOneGradedKernel b ω hlayers η).toSubmodule
    (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α))
    (fun _ hx => F.stepOne_gradedPieceProjection_mem_kernel b ω hlayers η _ hx) (hc α)

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

theorem stepOne_vertical_character {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L 1) (Γ : Subgroup F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hf : ∀ z : F.realification.Group, z ∈ F.realification.subgroup 1 → ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (g : F.realification.Group) :
    f (QuotientGroup.mk g) = character ((realifyFunctional η g.coord : ℝ) : CircleFourier.Circle) *
      f (QuotientGroup.mk (1 : F.realification.Group)) := by
  have hg : g ∈ F.realification.subgroup 1 := by rw [F.realification.subgroup_one]; trivial
  simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using
    hf g hg (QuotientGroup.mk (1 : F.realification.Group))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

theorem le_factorizationInputBudget (s : ℕ) {p : ℝ} (_hp : 0 ≤ p) :
    p ≤ p + factorizationInputOffset s :=
  le_add_of_nonneg_right (Nat.cast_nonneg _)

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end


