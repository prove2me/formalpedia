-- Prove2me | Definitions.Def_OAIErdos3B105
-- name    : OAIErdos3B105
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T21:34:09.768502+00:00
-- url     : https://prove2.me/theorems/81b8a004-ef6e-44d3-88b1-d8e06f5feeda
-- title:
--   OpenAI Erdős-3 split, definitions bundle 106 of 117
-- statement:
--   Definitions bundle 106 of 117 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B104`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 106 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialLiftSystemMod.extend_basis`, `OAI.Erdos3.NilpotentLieBCHGroup.basisPolynomialLift_adjoint`, `OAI.Erdos3.NilpotentLieBCHGroup.basisPolynomialLift_adjoint_residual`, `OAI.Erdos3.NilpotentLieFiltration.FormalCorrectionProperty`, `OAI.Erdos3.NilpotentLieFiltration.FormalCorrectionProperty.list_prod`, `OAI.Erdos3.NilpotentLieFiltration.FormalCorrectionProperty.mul`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionRun`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionRun.extend`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionRun.start`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionRun.terminal_lower_bracket`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionRun.terminal_lower_log`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionState.bracket_source`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionState.enlarge`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionState.enlarge_P`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionState.recOn`, `OAI.Erdos3.NilpotentLieFiltration.FormalStageGeometry.rec`, `OAI.Erdos3.NilpotentLieFiltration.RealFastCoefficientModule`, `OAI.Erdos3.NilpotentLieFiltration.ReducedRelativeCoefficientSpec`, `OAI.Erdos3.NilpotentLieFiltration.coefficientGridCorrection`, `OAI.Erdos3.NilpotentLieFiltration.coefficientSlowCorrection`, `OAI.Erdos3.NilpotentLieFiltration.coefficient_common_derivative_difference`, `OAI.Erdos3.NilpotentLieFiltration.coefficient_common_derivative_identity`, `OAI.Erdos3.NilpotentLieFiltration.exists_firstCoefficient_direction_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_induction_run_product_controls`, `OAI.Erdos3.NilpotentLieFiltration.exists_reducedRelativeCoefficient_bound`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficientAdjoint_grid`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficientAdjoint_weighted_bound`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGrid_add`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGrid_mono`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGrid_sub`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientSlowBound_add`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientSlowBound_mono`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientSlowBound_sub`, `OAI.Erdos3.NilpotentLieFiltration.mem_realFastDiagonalSubgroup`, `OAI.Erdos3.NilpotentLieFiltration.normalizedRelativeInFirst`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAction`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAction_horizontal`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAction_mk`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAdjoint`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAdjoint_mk`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAdjoint_mul`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAdjoint_one`, `OAI.Erdos3.NilpotentLieFiltration.realFastDiagonalSubgroup`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientAdjoint_basis_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientAdjoint_cancel_inv`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientAdjoint_fast_map`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientAdjoint_fast_mem`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientAdjoint_matrix_entry`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientAdjoint_mul`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientHorizontal_adjoint`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficient_common_derivative`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficient_common_mod_fast`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedFirstCoefficientMap_adjoint`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedFirstCoefficientMap_eq`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedRelativeInFirst`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedRelativeInFirst_coe`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeCoefficient_triple`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeSquareSymbolMap_triple_preimage`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealFastRelative_adjoint_mem`, `OAI.Erdos3.NilpotentLieFiltration.synchronized_coefficient_common_derivative`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_basis`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_coefficientBound`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_coefficientGrid`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_coefficients`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_mem`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_residual`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_shiftedGraded`, `OAI.Erdos3.VectorPolynomial.realLinearPolynomial_mem_of_basis`, `OAI.Erdos3.liftQuotientArray_map_neg`, `OAI.Erdos3.projected_lift_array_bound`, `OAI.Erdos3.projected_lift_array_grid`, `OAI.Erdos3.projected_lift_array_homogeneous`, `OAI.Erdos3.projected_lift_residual_eq`, `OAI.Erdos3.projected_polynomial_coefficient_bound`, `OAI.Erdos3.projected_polynomial_coefficient_grid`, `OAI.Erdos3.real_bracket_mem_of_basis`, `OAI.Erdos3.uniform_current_layer_inputs_from_ambient`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B031

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientAdjoint_basis_coordinate (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (i k : FirstCoefficientIndex w ω)
    (hki : ω k.val.2 ≤ ω i.val.2) :
    (F.realFirstCoefficientBasis b ω hF w).repr
      (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientBasis b ω hF w i)) k =
      (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientBasis b ω hF w i) k := by
  simp only [F.realFirstCoefficientBasis_apply, F.realFirstCoefficientAdjoint_map,
    F.realFirstCoefficientBasis_repr_map, F.realShiftedMonomialBasis_coe]
  exact (F.adaptedPolynomialFiltration w).dualAdjoint_realBasis_coordinate
    (F.adaptedMonomialBasis b ω hF w) (fun z => ω z.val.2)
    (F.adaptedPolynomialFiltration_layer b ω hF w) g
    ((firstCoefficientSurvivorEquiv w ω).symm i).val.val
    ((firstCoefficientSurvivorEquiv w ω).symm k).val.val hki

theorem realFirstCoefficientAdjoint_matrix_entry (w : σ → ℕ)
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (g : F.RealAdaptedPolynomialGroup w) (i k : FirstCoefficientIndex w ω)
    (hki : ω k.val.2 ≤ ω i.val.2) :
    LinearMap.toMatrix (F.realFirstCoefficientBasis b ω hF w) (F.realFirstCoefficientBasis b ω hF w)
      (F.realFirstCoefficientAdjoint w g).toLinearMap k i = if i = k then 1 else 0 := by
  rw [LinearMap.toMatrix_apply]
  change (F.realFirstCoefficientBasis b ω hF w).repr
    (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientBasis b ω hF w i)) k = _
  rw [F.realFirstCoefficientAdjoint_basis_coordinate b ω hF w g i k hki]
  exact (F.realFirstCoefficientBasis b ω hF w).equivFun_self i k

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem reducedSquareRealFastRelative_adjoint_mem (hw : ∀ i, 0 < w i)
    (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : g.coord ∈ realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (x : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : x ∈ (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ) :
    dualAdjoint (F.reducedSquareRealDiagonalHom w g) x ∈
      (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ := by
  let A := (realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)).map
    (realificationLieHom (F.reducedSquareDiagonalSymbolMap w))
  have ha : (F.reducedSquareRealDiagonalHom w g).coord ∈ realLieSubalgebraOverRat A :=
    ⟨g.coord, hg, rfl⟩
  apply dualAdjoint_real_mem_of_invariant (realLieSubalgebraOverRat A)
    ((F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ) _ _ ha _ hx
  rintro z ⟨u, hu, rfl⟩ y hy
  exact F.reducedSquareRealFastRelative_action_mem w U hw hu hy

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def normalizedRelativeInFirst :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.shiftedPolynomialIdeal w 1 :=
  (F.normalizedRelativeSubmodule w).subtype.codRestrict
    (F.shiftedPolynomialIdeal w 1).toSubmodule (fun p => p.property.1)

noncomputable def realNormalizedRelativeInFirst :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) →ₗ[ℝ] F.realShiftedCoefficientSubmodule w 1 :=
  (realificationSubmoduleEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule).toLinearMap.comp
    ((F.normalizedRelativeInFirst w).baseChange ℝ)

theorem realNormalizedRelativeInFirst_coe (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.realNormalizedRelativeInFirst w x).val = (F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x := by
  change (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype.baseChange ℝ
    ((F.normalizedRelativeInFirst w).baseChange ℝ x) = _
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

theorem realNormalizedFirstCoefficientMap_eq (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w x =
      F.realFirstCoefficientMap w (F.realNormalizedRelativeInFirst w x) := by
  change F.firstCoefficientRealEquiv w
    (((F.firstCoefficientMap w).comp (F.normalizedRelativeInFirst w)).baseChange ℝ x) = _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply, F.firstCoefficientRealEquiv_map]
  rfl

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

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem realFirstCoefficientAdjoint_mul (g h : F.RealAdaptedPolynomialGroup w)
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientAdjoint w (g * h) x =
      F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientAdjoint w h x) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype) x
  change F.realFirstCoefficientAdjoint w (g * h) (F.realFirstCoefficientMap w y) =
    F.realFirstCoefficientAdjoint w g
      (F.realFirstCoefficientAdjoint w h (F.realFirstCoefficientMap w y))
  rw [F.realFirstCoefficientAdjoint_map, F.realFirstCoefficientAdjoint_map,
    F.realFirstCoefficientAdjoint_map]
  apply congrArg (F.realFirstCoefficientMap w)
  exact Subtype.ext (dualAdjoint_mul g h y.val)

theorem realFirstCoefficientAdjoint_cancel_inv (g : F.RealAdaptedPolynomialGroup w)
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientAdjoint w g⁻¹ x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype) x
  change F.realFirstCoefficientAdjoint w g
    (F.realFirstCoefficientAdjoint w g⁻¹ (F.realFirstCoefficientMap w y)) = F.realFirstCoefficientMap w y
  rw [F.realFirstCoefficientAdjoint_map, F.realFirstCoefficientAdjoint_map]
  apply congrArg (F.realFirstCoefficientMap w)
  exact Subtype.ext (dualAdjoint_cancel_inv g y.val)

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

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem firstCoefficientSlowBound_sub (w : σ → ℕ) (T : σ → ℝ) (M N : ℝ)
    (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x)
    (hy : F.FirstCoefficientSlowBound e ω hF w T N y) :
    F.FirstCoefficientSlowBound e ω hF w T (M + N) (x - y) := by
  intro i
  simp only [map_sub, Finsupp.sub_apply]
  exact (abs_sub _ _).trans ((add_le_add (hx i) (hy i)).trans_eq (add_div M N _).symm)

theorem firstCoefficientGrid_sub (w : σ → ℕ) (l : ℕ) (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid e ω hF w l x)
    (hy : F.FirstCoefficientGrid e ω hF w l y) :
    F.FirstCoefficientGrid e ω hF w l (x - y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a - b, ?_⟩
  funext i
  have hai := congrFun ha i
  have hbi := congrFun hb i
  change ((a i - b i : ℤ) : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis e ω hF w).repr (x - y) i
  simp only [Int.cast_sub, map_sub, Finsupp.sub_apply, mul_sub]
  exact congrArg₂ (· - ·) hai hbi

theorem coefficient_common_derivative_difference [Fintype σ]
    (V : Submodule ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1)))
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h h₀ : σ → ℝ)
    (S S₀ R R₀ Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hh : F.realFirstCoefficientDirectionMap B.coord h -
      (S + F.realFirstCoefficientAdjoint (fun _ => 1) B R + Z) ∈ V)
    (hh₀ : F.realFirstCoefficientDirectionMap B.coord h₀ -
      (S₀ + F.realFirstCoefficientAdjoint (fun _ => 1) B R₀ + Z) ∈ V) :
    F.realFirstCoefficientDirectionMap B.coord (h - h₀) -
      ((S - S₀) + F.realFirstCoefficientAdjoint (fun _ => 1) B (R - R₀)) ∈ V := by
  have hd := V.sub_mem hh hh₀
  rw [map_sub, map_sub]
  convert hd using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

include e ω hF

theorem realFirstCoefficientHorizontal_adjoint
    (g : F.RealAdaptedPolynomialGroup w) (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientHorizontal w (F.realFirstCoefficientAdjoint w g x) =
      F.realFirstCoefficientHorizontal w x := by
  have he : (F.realFirstCoefficientHorizontal w).comp
      (F.realFirstCoefficientAdjoint w g).toLinearMap = F.realFirstCoefficientHorizontal w := by
    apply (F.realFirstCoefficientBasis e ω hF w).ext
    intro i
    apply ((F.layerOneBasis e ω hF).baseChange ℝ).repr.injective
    ext j
    change ((F.layerOneBasis e ω hF).baseChange ℝ).repr
      (F.realFirstCoefficientHorizontal w
        (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientBasis e ω hF w i))) j = _
    rw [F.realFirstCoefficientHorizontal_coordinates, F.realFirstCoefficientHorizontal_coordinates]
    apply F.realFirstCoefficientAdjoint_basis_coordinate e ω hF w g i
    have hi := i.property
    have hj := (F.horizontalCoefficientIndex e ω hF w j).property
    change Finsupp.weight w 0 + 1 = ω j.val at hj
    simp only [map_zero, Nat.zero_add] at hj
    change ω j.val ≤ ω i.val.2
    omega
  exact DFunLike.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def coefficientSlowCorrection
    (A : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ)
    (ε u : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    F.RealFirstCoefficientModule (fun _ : σ => 1) :=
  F.realFirstCoefficientAdjoint (fun _ => 1) A⁻¹
    (ε + u - F.realFirstCoefficientDirectionMap A.coord h)

noncomputable def coefficientGridCorrection
    (D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ)
    (μ v : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    F.RealFirstCoefficientModule (fun _ : σ => 1) :=
  v + F.realFirstCoefficientAdjoint (fun _ => 1) D μ - F.realFirstCoefficientDirectionMap D.coord h

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

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

abbrev RealFastCoefficientModule := F.RealFirstCoefficientModule w ⧸
  F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)

noncomputable def realFastDiagonalSubgroup : Subgroup (F.RealAdaptedPolynomialGroup w) :=
  (show Subgroup (F.quotientTop.RealPolynomialSymbolGroup w) from
    realLieSubgroup (realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))).comap
      (F.adaptedReducedRealSymbolHom w)

@[simp] theorem mem_realFastDiagonalSubgroup (g : F.RealAdaptedPolynomialGroup w) :
    g ∈ F.realFastDiagonalSubgroup w U ↔ (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U) := Iff.rfl

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

theorem realFastCoefficientAction_horizontal {ι : Type*}
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (g : F.realFastDiagonalSubgroup w U) (x : F.RealFastCoefficientModule w hw U) :
    F.realFastCoefficientHorizontal w hw (F.reducedSquareFastRelativeSubmodule w U)
      (F.realFastCoefficientAction w hw U g x) =
      F.realFastCoefficientHorizontal w hw (F.reducedSquareFastRelativeSubmodule w U) x := by
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw
    (F.reducedSquareFastRelativeSubmodule w U)).mkQ_surjective x
  rw [F.realFastCoefficientAction_mk]
  exact F.realFirstCoefficientHorizontal_adjoint e ω hF w g.val x

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalCurrentInputBounds
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem projected_lift_residual_eq {σ μ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (b : Basis μ ℝ L) (w : μ → ℕ) {j : ℕ} (hj : j ≠ 1)
    (S : VectorPolynomial σ ℚ L) (k : L) (hk : basisGradeProjection b w 1 k = k) :
    map ((basisGradeProjection b w j).restrictScalars ℚ) (S - monomial 0 k) =
      map ((basisGradeProjection b w j).restrictScalars ℚ) S := by
  have hz := basisGradeProjection_other b w hj k
  rw [hk] at hz
  rw [map_sub, map_monomial]
  change map ((basisGradeProjection b w j).restrictScalars ℚ) S -
    monomial 0 (basisGradeProjection b w j k) = _
  rw [hz]
  simp only [monomial, TensorProduct.tmul_zero, sub_zero]

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

theorem projected_lift_array_bound (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) {j H : ℕ} (hj : 2 ≤ j)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    (hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ t α, ‖(b.baseChange ℝ).equivFun (coefficients (S t) α)‖ ≤ M / monomialScale T α) :
    ∀ α, ‖coefficients (liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α‖ ≤
      (((Fintype.card μ : ℝ) + 1) * (H + 1)) * M / monomialScale T α := by
  intro α
  let C : ℝ := ((Fintype.card μ : ℝ) + 1) * (H + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply liftQuotientArray_norm_bound f _ α (div_nonneg (mul_nonneg hC hM) (monomialScale_pos T hT α).le)
  intro t
  rw [projected_lift_residual_eq (b.baseChange ℝ) w (by omega) (S t) _ (hk t), coefficients_map]
  change ‖realQuotientCoordinateMap f
    (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α))‖ ≤ C * M / monomialScale T α
  calc
    _ ≤ C * ‖(b.baseChange ℝ).equivFun
        (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α))‖ :=
      realQuotientCoordinateMap_norm_bound b f hf _
    _ ≤ C * ‖(b.baseChange ℝ).equivFun (coefficients (S t) α)‖ :=
      mul_le_mul_of_nonneg_left (basisCoordinateProjection_norm_le (b.baseChange ℝ) {n | w n = j} _) hC
    _ ≤ C * (M / monomialScale T α) := mul_le_mul_of_nonneg_left (hS t α) hC
    _ = C * M / monomialScale T α := (mul_div_assoc C M (monomialScale T α)).symm

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

theorem liftQuotientArray_map_neg (f : Basis ι ℚ (L ⧸ V))
    (π : (ℝ ⊗[ℚ] L) →ₗ[ℚ] (ℝ ⊗[ℚ] L))
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    liftQuotientArray f (fun t => map π (-(R t))) = -liftQuotientArray f (fun t => map π (R t)) := by
  simp only [map_neg]
  exact liftQuotientArray_neg f _

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {L μ ι σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] {V : Submodule ℚ L}

theorem projected_polynomial_coefficient_bound (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (j : ℕ) {H : ℕ}
    (hf : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : CoefficientBound (b.baseChange ℝ) T M P)
    (α : σ →₀ ℕ) :
    ‖realQuotientCoordinateMap f (coefficients
      (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P) α)‖ ≤
      (((Fintype.card μ : ℝ) + 1) * (H + 1)) * M / monomialScale T α := by
  rw [coefficients_map]
  let C : ℝ := ((Fintype.card μ : ℝ) + 1) * (H + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb := (coefficientBound_iff_norm (b.baseChange ℝ) T hT hM P).mp hP α
  calc
    _ ≤ C * ‖(b.baseChange ℝ).equivFun
        (basisGradeProjection (b.baseChange ℝ) w j (coefficients P α))‖ :=
      realQuotientCoordinateMap_norm_bound b f hf _
    _ ≤ C * ‖(b.baseChange ℝ).equivFun (coefficients P α)‖ :=
      mul_le_mul_of_nonneg_left (basisCoordinateProjection_norm_le (b.baseChange ℝ) {z | w z = j} _) hC
    _ ≤ C * (M / monomialScale T α) := mul_le_mul_of_nonneg_left hb hC
    _ = _ := by ring

theorem projected_polynomial_coefficient_grid (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (j l : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : CoefficientGrid (b.baseChange ℝ) l P)
    (α : σ →₀ ℕ) :
    realQuotientCoordinateMap f (coefficients
      (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P) α) ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  rw [coefficients_map]
  apply realQuotientCoordinateMap_grid b f l
  exact basisCoordinateProjection_real_grid (b.baseChange ℝ) {z | w z = j} l _ (hP α)

theorem uniform_current_layer_inputs_from_ambient (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (j : ℕ) {H l : ℕ}
    (hl : 0 < l) (hf : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hambient : (Fintype.card μ : ℝ) ≤ p)
    (hquotient : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i))
    (hrational : ∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp (bracketConstructionBudget p) ∧
      (∀ i α, ‖realQuotientCoordinateMap f (coefficients
        (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
          Real.exp (bracketConstructionBudget p) / (T i * monomialScale T α)) ∧
      ∀ i α, realQuotientCoordinateMap f (coefficients
        (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
          realDenominatorGrid n := by
  let n := matrixDenominator (quotientCoordinateMatrix b f) * l
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos _) hl
  obtain ⟨_, _, hdenCap, hnormCap⟩ := bracket_construction_budget_bounds hp
  have hD := matrixDenominator_le_exp_power (quotientCoordinateMatrix b f) hp 1 hquotient hambient
    (fun i z => (show (((quotientCoordinateMatrix b f i z).den) : ℝ) ≤ H from Nat.cast_le.mpr (hf i z).2).trans
      (hHp.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))))
  have hnbound : (n : ℝ) ≤ Real.exp (bracketConstructionBudget p) := by
    calc
      _ = (matrixDenominator (quotientCoordinateMatrix b f) : ℝ) * (l : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp p :=
        mul_le_mul hD hlp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdenCap
  have hfactor : (((Fintype.card μ : ℝ) + 1) * (H + 1)) * Real.exp p ≤
      Real.exp (bracketConstructionBudget p) := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp p :=
        mul_le_mul_of_nonneg_right (current_layer_coordinate_factor_bound hp _ H hambient hHp) (Real.exp_nonneg _)
      _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hnormCap
  refine ⟨n, hn, hnbound, ?_, fun i α => projected_polynomial_coefficient_grid b w f j l _ (hrational i) α⟩
  intro i α
  have h := projected_polynomial_coefficient_bound b w f j hf T hT
    (div_nonneg (Real.exp_nonneg p) (hT i).le) (small i) (hsmall i) α
  calc
    _ ≤ (((Fintype.card μ : ℝ) + 1) * (H + 1)) * (Real.exp p / T i) / monomialScale T α := h
    _ = ((((Fintype.card μ : ℝ) + 1) * (H + 1)) * Real.exp p) / (T i * monomialScale T α) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hfactor (mul_nonneg (hT i).le (monomialScale_pos T hT α).le)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalInductionTerminal
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ κ K L : Type*} [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L]

noncomputable def basisPolynomialLift (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    K →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) := b.constr ℝ S

@[simp] theorem basisPolynomialLift_basis (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : κ) :
    basisPolynomialLift b S (b k) = S k := b.constr_basis ℝ S k

variable [Fintype κ]

theorem basisPolynomialLift_coefficients (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (x : K) (α : σ →₀ ℕ) :
    coefficients (basisPolynomialLift b S x) α =
      ∑ k, b.equivFun x k • coefficients (S k) α := by
  classical
  change realCoefficient α (b.constr ℝ S x) = _
  rw [Basis.constr_apply_fintype (S := ℝ)]
  simp only [map_sum, map_smul, realCoefficient_apply]

theorem realLinearPolynomial_mem_of_basis (b : Basis κ ℝ K)
    (S : K →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (W : (σ →₀ ℕ) → Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (S (b k)) α ∈ W α) (x : K) (α : σ →₀ ℕ) :
    coefficients (S x) α ∈ W α := by
  classical
  change ((realCoefficient α).comp S) x ∈ W α
  rw [← b.sum_repr x, map_sum]
  apply (W α).sum_mem
  intro k _
  rw [map_smul]
  exact (W α).smul_mem _ (h k α)

theorem basisPolynomialLift_mem (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (W : (σ →₀ ℕ) → Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (S k) α ∈ W α) (x : K) (α : σ →₀ ℕ) :
    coefficients (basisPolynomialLift b S x) α ∈ W α :=
  realLinearPolynomial_mem_of_basis b (basisPolynomialLift b S) W
    (fun k α => by rw [basisPolynomialLift_basis]; exact h k α) x α

theorem basisPolynomialLift_residual (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (I : K →ₗ[ℝ] ℝ ⊗[ℚ] L)
    (W : Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (S k - monomial 0 (I (b k))) α ∈ W)
    (x : K) (α : σ →₀ ℕ) :
    coefficients (basisPolynomialLift b S x - monomial 0 (I x)) α ∈ W := by
  let D : K →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
    basisPolynomialLift b S - (realMonomial 0).comp I
  have hD : ∀ k β, coefficients (D (b k)) β ∈ W := by
    intro k β
    simp only [D, LinearMap.sub_apply, LinearMap.comp_apply, realMonomial_apply,
      basisPolynomialLift_basis]
    exact h k β
  have hx := realLinearPolynomial_mem_of_basis b D (fun _ => W) hD x α
  simp only [D, LinearMap.sub_apply, LinearMap.comp_apply, realMonomial_apply] at hx
  exact hx

theorem basisPolynomialLift_shiftedGraded {ι : Type*} (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (w : ι → ℕ) (v : σ → ℕ) (r : ℕ)
    (h : ∀ k, S k ∈ shiftedGradedPolynomialSubmodule e w v r) (x : K) :
    basisPolynomialLift b S x ∈ shiftedGradedPolynomialSubmodule e w v r := by
  intro α
  let W := fun β : σ →₀ ℕ => LinearMap.ker
    (basisGradeProjection e w (Finsupp.weight v β + r) - LinearMap.id)
  have hm := basisPolynomialLift_mem b S W (fun k β => by
    change basisGradeProjection e w (Finsupp.weight v β + r) (coefficients (S k) β) -
      coefficients (S k) β = 0
    exact sub_eq_zero.mpr (h k β)) x α
  exact sub_eq_zero.mp hm

theorem basisPolynomialLift_coefficientBound {ι : Type*} (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (M : ℝ)
    (h : ∀ k, CoefficientBound e T M (S k)) (x : K) :
    CoefficientBound e T ((Fintype.card κ : ℝ) * M * ‖b.equivFun x‖)
      (basisPolynomialLift b S x) := by
  classical
  intro α i
  rw [basisPolynomialLift_coefficients]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    |∑ k, b.equivFun x k * e.repr (coefficients (S k) α) i| ≤
        ∑ k, |b.equivFun x k * e.repr (coefficients (S k) α) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : κ, ‖b.equivFun x‖ * (M / monomialScale T α) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm (b.equivFun x) k) (h k α i)
        (abs_nonneg _) (norm_nonneg _)
    _ = ((Fintype.card κ : ℝ) * M * ‖b.equivFun x‖) / monomialScale T α := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem basisPolynomialLift_coefficientGrid {ι : Type*} (b : Basis κ ℝ K)
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (l m : ℕ) (hR : ∀ k, CoefficientGrid e m (R k))
    (x : K) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    CoefficientGrid e (m * l) (basisPolynomialLift b R x) := by
  intro α
  have h := realDenominatorGrid_linear_combination l m (b.equivFun x)
    (fun k i => e.repr (coefficients (R k) α) i) hx (fun k => hR k α)
  convert h using 1
  ext i
  rw [basisPolynomialLift_coefficients]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
    Finset.sum_apply, Pi.smul_apply]

end VectorPolynomial

namespace NilpotentLieBCHGroup

variable {σ κ K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥}

theorem PolynomialLiftSystemMod.extend_basis (b : Basis κ ℝ K)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (h : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R) :
    PolynomialLiftSystemMod (V.restrictScalars ℚ) P
      (basisPolynomialLift b S) (basisPolynomialLift b R) := by
  let D := basisPolynomialLift b S -
    (dualAdjointRealLinearEquiv P).toLinearMap.comp (basisPolynomialLift b R)
  intro x α
  apply realLinearPolynomial_mem_of_basis b D (fun _ => V) _ x α
  intro k β
  change coefficients (basisPolynomialLift b S (b k) -
    dualAdjoint P (basisPolynomialLift b R (b k))) β ∈ V
  rw [basisPolynomialLift_basis, basisPolynomialLift_basis]
  exact h k β

omit [Fintype κ] in
theorem basisPolynomialLift_adjoint (b : Basis κ ℝ K) (A : PolynomialGroup σ hnil)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    basisPolynomialLift b (fun k => dualAdjoint A (S k)) =
      (dualAdjointRealLinearEquiv A).toLinearMap.comp (basisPolynomialLift b S) := by
  apply b.ext
  intro k
  simp only [basisPolynomialLift_basis, LinearMap.comp_apply,
    LinearEquiv.coe_coe, dualAdjointRealLinearEquiv_apply]

theorem basisPolynomialLift_adjoint_residual (b : Basis κ ℝ K)
    (A : PolynomialGroup σ hnil) (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (I : K →ₗ[ℝ] ℝ ⊗[ℚ] L) (W : Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (dualAdjoint A (S k) - monomial 0 (I (b k))) α ∈ W)
    (x : K) (α : σ →₀ ℕ) :
    coefficients (dualAdjoint A (basisPolynomialLift b S x) - monomial 0 (I x)) α ∈ W := by
  have hx := basisPolynomialLift_residual b (fun k => dualAdjoint A (S k)) I W h x α
  rw [basisPolynomialLift_adjoint] at hx
  exact hx

end NilpotentLieBCHGroup

theorem real_bracket_mem_of_basis {κ K L : Type*} [Fintype κ]
    [AddCommGroup K] [Module ℝ K] [LieRing L] [LieAlgebra ℝ L]
    (b : Basis κ ℝ K) (I : K →ₗ[ℝ] L) (W : Submodule ℝ L) (p : L)
    (h : ∀ k, ⁅p, I (b k)⁆ ∈ W) (x : K) : ⁅p, I x⁆ ∈ W := by
  classical
  rw [← b.sum_repr x, map_sum, lie_sum]
  apply W.sum_mem
  intro k _
  rw [map_smul, lie_smul]
  exact W.smul_mem _ (h k)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype κ] {s : ℕ}

structure FormalInductionState (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L)
    (w : μ → ℕ) (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (e : Basis κ ℚ K) (T : σ → ℝ) (j : ℕ) (p : ℝ) where
  P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot
  S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  small : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  k : σ → κ → ℝ
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p
  constant_zero : coefficients P.coord 0 = 0
  mem_U : ∀ α, coefficients P.coord α ∈ U
  graded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
  horizontal : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K.baseChange ℝ
  lower_log : ∀ α d, 2 ≤ d → d < j →
    basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ
  lower_bracket : ∀ d < j - 1, ∀ z α,
    ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] (e z : L)⁆ ∈ V.baseChange ℝ
  lift_system : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R
  derivative_system : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational
    (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S (k i))
  S_shift : ∀ z, S z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  R_shift : ∀ z, R z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  small_shift : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  rational_shift : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  S_remainder : ∀ z α, coefficients (S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
    V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  R_remainder : ∀ z α, coefficients (R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
    V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  small_remainder : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  rational_remainder : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  S_bound : ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (S z)
  R_grid : ∀ z, CoefficientGrid (b.baseChange ℝ) denominator (R z)
  small_bound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i)
  rational_grid : ∀ i, CoefficientGrid (b.baseChange ℝ) denominator (rational i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}

def FormalCorrectionProperty (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L)
    (w : μ → ℕ) (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (g : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) : Prop :=
  (∀ α, coefficients g.coord α ∈ U) ∧
    g.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
    coefficients g.coord 0 = 0

structure FormalInductionRun (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L)
    (w : μ → ℕ) (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (eK : Basis κ ℚ K) (T : σ → ℝ)
    (original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) (r : ℕ) (q : ℝ) where
  state : F.FormalInductionState b w U V K eK T (2 + r) q
  left : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
  right : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp ((r + 1 : ℝ) * q)
  state_denominator_dvd : state.denominator ∣ denominator
  left_length : left.length = 2 * r
  right_length : right.length = 2 * r
  left_good : ∀ g ∈ left, F.FormalCorrectionProperty b w U g
  right_good : ∀ g ∈ right, F.FormalCorrectionProperty b w U g
  left_bound : ∀ g ∈ left, CoefficientBound (b.baseChange ℝ) T (Real.exp q) g.coord
  right_grid : ∀ g ∈ right, CoefficientGrid (b.baseChange ℝ) denominator g.coord
  factorization : left.prod * state.P * right.prod = original

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s j : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ} {p q : ℝ}

noncomputable def FormalInductionState.enlarge
    (X : F.FormalInductionState b w U V K eK T j p) (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.FormalInductionState b w U V K eK T j q :=
  { X with
    denominator_bound := X.denominator_bound.trans (Real.exp_le_exp.mpr hpq)
    S_bound := fun z => (X.S_bound z).mono _ T hT (Real.exp_le_exp.mpr hpq)
    small_bound := fun i => (X.small_bound i).mono _ T hT
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpq) (hT i).le) }

@[simp] theorem FormalInductionState.enlarge_P
    (X : F.FormalInductionState b w U V K eK T j p) (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    (X.enlarge hpq hT).P = X.P := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]

structure FormalStageGeometry (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V)) (j H : ℕ) where
  bracketSpace : Submodule ℚ L
  currentSpace : Submodule ℚ L
  bracketRank : ℕ
  currentRank : ℕ
  bracketBasis : Basis (Fin bracketRank) ℚ bracketSpace
  currentBasis : Basis (Fin currentRank) ℚ currentSpace
  bracket_grade : ∀ x ∈ bracketSpace.baseChange ℝ,
    basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x
  bracket_U : bracketSpace.baseChange ℝ ≤ U.toSubmodule
  bracket_K : j = 2 → bracketSpace.baseChange ℝ ≤ K.baseChange ℝ
  bracket_V : 2 < j → bracketSpace.baseChange ℝ ≤ V.baseChange ℝ
  bracket_complete : ∀ x ∈ U,
    basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x →
    (j = 2 → x ∈ K.baseChange ℝ) → (2 < j → x ∈ V.baseChange ℝ) →
    x ∈ bracketSpace.baseChange ℝ
  current_grade : ∀ x ∈ currentSpace.baseChange ℝ,
    basisGradeProjection (b.baseChange ℝ) w j x = x
  current_U : currentSpace.baseChange ℝ ≤ U.toSubmodule
  current_projection : ∀ x ∈ U, basisGradeProjection (b.baseChange ℝ) w j x ∈ currentSpace.baseChange ℝ
  bracket_matrix_height : ∀ i z,
    RationalHeightLE (bracketSystemMatrix bracketBasis f (fun z => (eK z : L)) i z) H
  current_matrix_height : ∀ i z, RationalHeightLE (subspaceQuotientMatrix currentBasis f i z) H
  bracket_basis_height : ∀ i z, RationalHeightLE (b.repr (bracketBasis z : L) i) H
  current_basis_height : ∀ i z, RationalHeightLE (b.repr (currentBasis z : L) i) H

theorem FormalInductionState.bracket_source {s j H : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
    {eK : Basis κ ℚ K} {f : Basis ι ℚ (L ⧸ V)} {T : σ → ℝ} {p : ℝ}
    (X : F.FormalInductionState b w U V K eK T j p)
    (G : FormalStageGeometry b w U V K eK f j H)
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule) (hj : 2 ≤ j) :
    ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients X.P.coord α) ∈
      G.bracketSpace.baseChange ℝ := by
  intro α
  apply G.bracket_complete _ (hU _ _ (X.mem_U α))
  · exact basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1} _
  · intro hj2
    subst j
    exact X.horizontal α
  · intro hj2
    exact X.lower_log α (j - 1) (by omega) (by omega)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ}

noncomputable def FormalInductionRun.start {p : ℝ}
    (X : F.FormalInductionState b w U V K eK T 2 p) :
    F.FormalInductionRun b w U V K eK T X.P 0 p where
  state := X
  left := []
  right := []
  denominator := X.denominator
  denominator_pos := X.denominator_pos
  denominator_bound := by simpa using X.denominator_bound
  state_denominator_dvd := dvd_refl _
  left_length := by simp
  right_length := by simp
  left_good := by simp
  right_good := by simp
  left_bound := by simp
  right_grid := by simp
  factorization := by simp

noncomputable def FormalInductionRun.extend
    {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot} {r : ℕ} {q q' : ℝ}
    (W : F.FormalInductionRun b w U V K eK T original r q)
    (hq : q ≤ q') (hT : ∀ i, 0 < T i)
    (Y : F.FormalInductionState b w U V K eK T (2 + (r + 1)) q')
    (A₁ A₂ B₁ B₂ : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hfactor : (A₁ * A₂) * Y.P * (B₂ * B₁) = W.state.P)
    (hA₁ : F.FormalCorrectionProperty b w U A₁)
    (hA₂ : F.FormalCorrectionProperty b w U A₂)
    (hB₁ : F.FormalCorrectionProperty b w U B₁)
    (hB₂ : F.FormalCorrectionProperty b w U B₂)
    (hA₁bound : CoefficientBound (b.baseChange ℝ) T (Real.exp q') A₁.coord)
    (hA₂bound : CoefficientBound (b.baseChange ℝ) T (Real.exp q') A₂.coord)
    (hB₁grid : CoefficientGrid (b.baseChange ℝ) Y.denominator B₁.coord)
    (hB₂grid : CoefficientGrid (b.baseChange ℝ) Y.denominator B₂.coord) :
    F.FormalInductionRun b w U V K eK T original (r + 1) q' := by
  refine {
    state := Y
    left := W.left ++ [A₁, A₂]
    right := [B₂, B₁] ++ W.right
    denominator := W.denominator * Y.denominator
    denominator_pos := Nat.mul_pos W.denominator_pos Y.denominator_pos
    denominator_bound := ?_
    state_denominator_dvd := dvd_mul_left _ _
    left_length := ?_
    right_length := ?_
    left_good := ?_
    right_good := ?_
    left_bound := ?_
    right_grid := ?_
    factorization := ?_ }
  · have hmul : (r + 1 : ℝ) * q ≤ (r + 1 : ℝ) * q' :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    calc
      ((W.denominator * Y.denominator : ℕ) : ℝ) =
          (W.denominator : ℝ) * (Y.denominator : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp ((r + 1 : ℝ) * q') * Real.exp q' :=
        mul_le_mul (W.denominator_bound.trans (Real.exp_le_exp.mpr hmul))
          Y.denominator_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((r + 1 + 1 : ℝ) * q') := by rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp (((r + 1 : ℕ) + 1 : ℝ) * q') := by push_cast; rfl
  · simp only [List.length_append, List.length_cons, List.length_nil, W.left_length]
    omega
  · simp only [List.length_append, List.length_cons, List.length_nil, W.right_length]
    omega
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact W.left_good g hg
    · exact hA₁
    · exact hA₂
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl) | hg
    · exact hB₂
    · exact hB₁
    · exact W.right_good g hg
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact (W.left_bound g hg).mono _ T hT (Real.exp_le_exp.mpr hq)
    · exact hA₁bound
    · exact hA₂bound
  · intro g hg α
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl) | hg
    · exact realDenominatorGrid_subset_of_dvd Y.denominator_pos
        (dvd_mul_left _ _) (hB₂grid α)
    · exact realDenominatorGrid_subset_of_dvd Y.denominator_pos
        (dvd_mul_left _ _) (hB₁grid α)
    · exact realDenominatorGrid_subset_of_dvd W.denominator_pos
        (dvd_mul_right _ _) (W.right_grid g hg α)
  · have h : W.left.prod * ((A₁ * A₂) * Y.P * (B₂ * B₁)) * W.right.prod = original := by
      rw [hfactor]
      exact W.factorization
    simpa only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem FormalCorrectionProperty.mul
    {L μ σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} (hgraded : BasisHomogeneousBrackets b w)
    {A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}
    (hA : F.FormalCorrectionProperty b w U A) (hB : F.FormalCorrectionProperty b w U B) :
    F.FormalCorrectionProperty b w U (A * B) := by
  refine ⟨?_, ?_, ?_⟩
  · let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
      { U.toSubmodule.restrictScalars ℚ with lie_mem' := U.lie_mem }
    exact lieBCH_mem (coefficientLieSubalgebra Uq) s hA.1 hB.1
  · exact lieBCH_mem
      (gradedPolynomialSubalgebra (b.baseChange ℝ) w (hgraded.baseChange b w) (fun _ : σ => 1))
      s hA.2.1 hB.2.1
  · have h := eval_lieBCH (fun _ : σ => (0 : ℚ)) s A.coord B.coord
    simp only [eval_zero_eq_coefficient, hA.2.2, hB.2.2] at h
    change coefficients (lieBCH s A.coord B.coord) 0 = 0
    rw [h]
    change ((1 : F.realification.Group) * 1).coord = 0
    rw [one_mul]
    rfl

theorem FormalCorrectionProperty.list_prod
    {L μ σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} (hgraded : BasisHomogeneousBrackets b w)
    (rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot))
    (hrs : ∀ r ∈ rs, F.FormalCorrectionProperty b w U r) :
    F.FormalCorrectionProperty b w U rs.prod := by
  induction rs with
  | nil =>
    refine ⟨?_, (gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)).zero_mem, ?_⟩
    · intro α
      change coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈ U
      simp only [map_zero, Finsupp.zero_apply, zero_mem]
    · change coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
      simp only [map_zero, Finsupp.zero_apply]
  | cons r rs ih =>
    exact (hrs r List.mem_cons_self).mul hgraded (ih (fun x hx => hrs x (List.mem_cons_of_mem r hx)))

theorem exists_formal_induction_run_product_controls (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w)
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L} {eK : Basis κ ℚ K}
    {T : σ → ℝ} (_hT : ∀ i, 0 < T i)
    {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}
    {r : ℕ} (_hr : r ≤ s) {q : ℝ}
    (W : F.FormalInductionRun b w U V K eK T original r q)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hStructure : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    {p : ℝ} (_hp : 0 ≤ p) (_hqp : q ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hDenom : (W.denominator : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ W.denominator ∣ m ∧
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) W.left.prod.coord ∧
      CoefficientGrid (b.baseChange ℝ) m W.right.prod.coord ∧
      F.FormalCorrectionProperty b w U W.left.prod ∧
      F.FormalCorrectionProperty b w U W.right.prod := by
  obtain ⟨A, hA, hslow⟩ := exists_formal_polynomial_product_bound s 1 (2 * s)
  obtain ⟨B, hB, hgrid⟩ := exists_formal_polynomial_product_grid s (2 * s)
  let C := max A B
  refine ⟨C, hA.trans (Nat.le_max_left A B), ?_⟩
  intro L μ κ σ _ _ _ _ _ F b w hF hgraded U V K eK T hT original r hr q W H hH hStructure
    p hp hqp hμ hσ hHp hDenom
  have hAC : (p + A) ^ A ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_left A B)
  have hBC : (p + B) ^ B ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_right A B)
  have hleft : CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + A) ^ A)) W.left.prod.coord := by
    apply hslow F b w hF H p hH hp hμ hσ hHp hStructure T hT W.left
    · rw [W.left_length]
      exact Nat.mul_le_mul_left 2 hr
    · intro x hx
      exact F.gradedPolynomial_mem_adapted b w hF (fun _ => 1) x.coord (W.left_good x hx).2.1
    · intro x hx
      apply (W.left_bound x hx).mono _ T hT (Real.exp_le_exp.mpr ?_)
      simpa only [pow_one] using hqp.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  obtain ⟨m, hm, hmp, hdm, hproducts⟩ :=
    hgrid F b w hF H p hH hp hμ hσ hHp hStructure W.denominator W.denominator_pos hDenom
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hBC), hdm,
    hleft.mono _ T hT (Real.exp_le_exp.mpr hAC), ?_,
    FormalCorrectionProperty.list_prod hgraded W.left W.left_good,
    FormalCorrectionProperty.list_prod hgraded W.right W.right_good⟩
  apply hproducts W.right
  · rw [W.right_length]
    exact Nat.mul_le_mul_left 2 hr
  · intro x hx
    exact F.gradedPolynomial_mem_adapted b w hF (fun _ => 1) x.coord (W.right_good x hx).2.1
  · exact W.right_grid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ} {q : ℝ}
  {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}

theorem FormalInductionRun.terminal_lower_log
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (α : σ →₀ ℕ) (d : ℕ) (hd : 2 ≤ d) (hds : d ≤ s) :
    basisGradeProjection (b.baseChange ℝ) w d (coefficients W.state.P.coord α) ∈ V.baseChange ℝ :=
  W.state.lower_log α d hd (by omega)

theorem FormalInductionRun.terminal_lower_bracket
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (d : ℕ) (hd : d < s) (z : κ) (α : σ →₀ ℕ) :
    ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients W.state.P.coord α),
      (1 : ℝ) ⊗ₜ[ℚ] (eK z : L)⁆ ∈ V.baseChange ℝ :=
  W.state.lower_bracket d (by omega) z α

end Erdos3.NilpotentLieFiltration

end

end OAI

end


