-- Prove2me | Definitions.Def_OAIErdos3B131
-- name    : OAIErdos3B131
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T08:00:34.290796+00:00
-- url     : https://prove2.me/theorems/fa98115f-609f-430e-abf0-377f481dce8b
-- title:
--   OpenAI Erdős-3 split, definitions bundle 132 of 132
-- statement:
--   Definitions bundle 132 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B130`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 132 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.adaptedGradedPolynomialLie`, `OAI.Erdos3.NilpotentLieFiltration.adaptedGradedPolynomialLie_apply`, `OAI.Erdos3.NilpotentLieFiltration.adaptedGradedPolynomialLie_unit_eval`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftedGradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftedGradedPolynomial_apply`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftedGradedPolynomial_directionalDerivative`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftedGradedPolynomial_lie`, `OAI.Erdos3.NilpotentLieFiltration.fastGradedDiagonal`, `OAI.Erdos3.NilpotentLieFiltration.fastGradedDiagonal_graded`, `OAI.Erdos3.NilpotentLieFiltration.fastPointwiseDiagonal_eq`, `OAI.Erdos3.NilpotentLieFiltration.fastPointwiseSquare`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_horizontal`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_injective`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_map`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_normalized`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_normalized_lie`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_reducedSquare`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_reducedSquare_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_reducedSquare_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedPolynomial_reducedSquare_symbol`, `OAI.Erdos3.NilpotentLieFiltration.fullFastGradedDiagonal`, `OAI.Erdos3.NilpotentLieFiltration.fullFastGradedDiagonal_graded`, `OAI.Erdos3.NilpotentLieFiltration.fullFastPointwise_eq_comap`, `OAI.Erdos3.NilpotentLieFiltration.fullFastPointwise_image_le`, `OAI.Erdos3.NilpotentLieFiltration.fullFastPointwise_subgroup_eq`, `OAI.Erdos3.NilpotentLieFiltration.fullFast_horizontal_derivative_mem`, `OAI.Erdos3.NilpotentLieFiltration.gradedPieceProjection_basis`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_unit_eval`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialHom`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie_apply`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie_symbol`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie_tensor`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomial_firstJet`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomial_logDerivative`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedShiftedGradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedShiftedGradedPolynomial_adjoint`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedShiftedGradedPolynomial_directionalDerivative`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedShiftedGradedPolynomial_lie`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedShiftedGradedPolynomial_tensor`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_adjoint`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_bound`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_coordinate_of_ne`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_direction`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_grid`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_horizontal`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_injective`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_map`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_realEquiv`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_tmul`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifference_basis`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDifference`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDifference_basis`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDifference_gradeProjection`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDifference_projection`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDifference_relative_lie`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDifference_unit`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedSndMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedSnd_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSnd_homogeneousSymbolLift`, `OAI.Erdos3.anisotropicSpatialDensityLip_le_exp`, `OAI.Erdos3.anisotropicSpatialMeshLog`, `OAI.Erdos3.anisotropicSpatialMeshLog_le_envelope`, `OAI.Erdos3.map_coefficientErrorSpatialLog`, `OAI.Erdos3.map_spatialParameterBudget`, `OAI.Erdos3.map_spatialPrimitiveEnvelope`, `OAI.Erdos3.map_spatialTupleToleranceLog`, `OAI.Erdos3.normalizedTupleLateBudget`, `OAI.Erdos3.normalizedTupleNarrowWidth`, `OAI.Erdos3.normalizedTupleRadius`, `OAI.Erdos3.normalizedTupleResolution`, `OAI.Erdos3.normalizedTupleSideLog`, `OAI.Erdos3.normalizedTupleTolerance`, `OAI.Erdos3.normalizedTupleWidthLog`, `OAI.Erdos3.probabilityProfileLipschitz_le_comparisonProfileBound`, `OAI.Erdos3.sharedWidthNormalizedTupleSideLog`, `OAI.Erdos3.spatialAuxiliaryDimensions`, `OAI.Erdos3.spatialBoundaryEnvelope`, `OAI.Erdos3.spatialCostEnvelopes_nonneg`, `OAI.Erdos3.spatialDiscretizationEnvelope`, `OAI.Erdos3.spatialDiscretizationLog_le_envelope`, `OAI.Erdos3.spatialDisplacementEnvelope`, `OAI.Erdos3.spatialDisplacementLog_le_envelope`, `OAI.Erdos3.spatialFixedProfileEnvelope`, `OAI.Erdos3.spatialLipschitzCostEnvelope`, `OAI.Erdos3.spatialLipschitzEnvelope`, `OAI.Erdos3.spatialMeshEnvelope`, `OAI.Erdos3.spatialMovementEnvelope`, `OAI.Erdos3.spatialParameterBudget`, `OAI.Erdos3.spatialPrimitiveEnvelope`, `OAI.Erdos3.spatialProfileLog_le_fixedEnvelope`, `OAI.Erdos3.spatialThresholdEnvelope`, `OAI.Erdos3.spatialTupleCoarseMesh`, `OAI.Erdos3.spatialTupleCoarseMesh_spec`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B048

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FirstCoefficientPolynomialDerivative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def adaptedShiftedGradedPolynomial (k : ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded :=
  (F.shiftedGradedPolynomial b ω hF w k).comp (F.adaptedLieSubalgebra w).incl.toLinearMap

@[simp] theorem adaptedShiftedGradedPolynomial_apply (k : ℕ) (p : F.adaptedLieSubalgebra w) :
    F.adaptedShiftedGradedPolynomial b ω hF w k p =
      F.shiftedGradedPolynomial b ω hF w k p.val := rfl

noncomputable def adaptedGradedPolynomialLie :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ F.AssociatedGraded :=
  (F.gradedSymbolPolynomialLie b ω hF w).comp (F.polynomialSymbolMap w)

theorem adaptedGradedPolynomialLie_apply (p : F.adaptedLieSubalgebra w) :
    F.adaptedGradedPolynomialLie b ω hF w p = F.adaptedShiftedGradedPolynomial b ω hF w 0 p := by
  exact (F.shiftedGradedPolynomial_zero b ω hF w p).symm

theorem adaptedShiftedGradedPolynomial_lie (p q : F.adaptedLieSubalgebra w)
    (hq : q ∈ F.shiftedPolynomialIdeal w 1) :
    F.adaptedShiftedGradedPolynomial b ω hF w 1 ⁅p, q⁆ =
      ⁅F.adaptedGradedPolynomialLie b ω hF w p, F.adaptedShiftedGradedPolynomial b ω hF w 1 q⁆ := by
  have hp : p.val ∈ F.shiftedAdaptedSubmodule w 0 := by
    intro α
    simpa only [Nat.add_zero] using p.property α
  rw [F.adaptedGradedPolynomialLie_apply]
  have hq' : q.val ∈ F.shiftedAdaptedSubmodule w 1 := hq
  rw [F.adaptedShiftedGradedPolynomial_apply, F.adaptedShiftedGradedPolynomial_apply,
    F.adaptedShiftedGradedPolynomial_apply, LieSubalgebra.coe_bracket]
  have he := F.shiftedGradedPolynomial_lie b ω hF w (i := 0) (j := 1)
    (p := p.val) (q := q.val) hp hq'
  rw [Nat.zero_add] at he
  rw [he]

noncomputable def firstCoefficientGradedPolynomial :
    F.FirstCoefficientModule w →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded :=
  ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
    (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).liftQ
      ((F.adaptedShiftedGradedPolynomial b ω hF w 1).comp
        (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype) (by
          intro p hp
          rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
            F.adaptedShiftedGradedPolynomial_apply]
          have hp' : p.val.val ∈ F.shiftedAdaptedSubmodule w 1 := p.property
          have hp'' : p.val.val ∈ F.shiftedAdaptedSubmodule w 2 := hp
          exact (F.shiftedGradedPolynomial_eq_zero_iff b ω hF w 1 hp').mpr hp'')

@[simp] theorem firstCoefficientGradedPolynomial_map (p : F.shiftedPolynomialIdeal w 1) :
    F.firstCoefficientGradedPolynomial b ω hF w (F.firstCoefficientMap w p) =
      F.adaptedShiftedGradedPolynomial b ω hF w 1 p.val := by
  unfold firstCoefficientGradedPolynomial firstCoefficientMap
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  rfl

theorem firstCoefficientGradedPolynomial_coordinate (x : F.FirstCoefficientModule w)
    (α : σ →₀ ℕ) (i : ι) :
    (F.associatedGradedBasis b ω hF).repr
      (coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α) i =
      if h : Finsupp.weight w α + 1 = ω i then
        (F.firstCoefficientBasis b ω hF w).repr x ⟨(α, i), h⟩ else 0 := by
  classical
  obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientGradedPolynomial_map, F.adaptedShiftedGradedPolynomial_apply,
    F.shiftedGradedPolynomial_coefficient, F.gradedPieceProjection_coordinate]
  by_cases h : Finsupp.weight w α + 1 = ω i
  · rw [dif_pos h, if_pos h.symm, F.firstCoefficientBasis_repr_map]
  · rw [dif_neg h, if_neg (Ne.symm h)]

theorem firstCoefficientGradedPolynomial_injective :
    Function.Injective (F.firstCoefficientGradedPolynomial b ω hF w) := by
  intro x y hxy
  apply (F.firstCoefficientBasis b ω hF w).repr.injective
  ext z
  have h := congrArg (fun P => (F.associatedGradedBasis b ω hF).repr (coefficients P z.val.1) z.val.2) hxy
  simpa only [F.firstCoefficientGradedPolynomial_coordinate, dif_pos z.property] using h

theorem firstCoefficientGradedPolynomial_homogeneous (x : F.FirstCoefficientModule w) (α : σ →₀ ℕ) :
    basisGradeProjection (F.associatedGradedBasis b ω hF) ω (Finsupp.weight w α + 1)
      (coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α) =
        coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α := by
  apply (F.associatedGradedBasis b ω hF).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases hi : ω i = Finsupp.weight w α + 1
  · rw [if_pos hi]
  · rw [if_neg hi, F.firstCoefficientGradedPolynomial_coordinate, dif_neg (Ne.symm hi)]

theorem firstCoefficientGradedPolynomial_horizontal (x : F.FirstCoefficientModule w) :
    coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) 0 =
      F.layerOneGradedMap b ω hF (F.firstCoefficientHorizontal w x) := by
  obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientGradedPolynomial_map, F.adaptedShiftedGradedPolynomial_apply,
    F.shiftedGradedPolynomial_coefficient, F.firstCoefficientHorizontal_map, F.layerOneGradedMap_mk]
  simp only [map_zero, zero_add]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realFirstCoefficientGradedPolynomial :
    F.RealFirstCoefficientModule w →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  realificationRealLinearEquiv.toLinearMap.comp
    (((F.firstCoefficientGradedPolynomial b ω hF w).baseChange ℝ).comp
      (F.firstCoefficientRealEquiv w).symm.toLinearMap)

theorem realFirstCoefficientGradedPolynomial_realEquiv (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w) :
    F.realFirstCoefficientGradedPolynomial b ω hF w (F.firstCoefficientRealEquiv w x) =
      realificationRealLinearEquiv ((F.firstCoefficientGradedPolynomial b ω hF w).baseChange ℝ x) := by
  simp only [realFirstCoefficientGradedPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

theorem realFirstCoefficientGradedPolynomial_tmul (a : ℝ) (x : F.FirstCoefficientModule w)
    (α : σ →₀ ℕ) :
    coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w
      (F.firstCoefficientRealEquiv w (a ⊗ₜ[ℚ] x))) α =
      a ⊗ₜ[ℚ] coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α := by
  rw [F.realFirstCoefficientGradedPolynomial_realEquiv, LinearMap.baseChange_tmul,
    realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul]

theorem realFirstCoefficientGradedPolynomial_coordinate (x : F.RealFirstCoefficientModule w)
    (z : FirstCoefficientIndex w ω) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) z.val.1) z.val.2 =
      (F.realFirstCoefficientBasis b ω hF w).repr x z := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  rw [F.firstCoefficientRealEquiv_coordinates]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [F.realFirstCoefficientGradedPolynomial_tmul, Basis.baseChange_repr_tmul,
      F.firstCoefficientGradedPolynomial_coordinate, dif_pos z.property,
      Basis.baseChange_repr_tmul]

theorem realFirstCoefficientGradedPolynomial_coordinate_of_ne (x : F.RealFirstCoefficientModule w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α + 1 ≠ ω i) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) α) i = 0 := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul a x =>
    rw [F.realFirstCoefficientGradedPolynomial_tmul, Basis.baseChange_repr_tmul,
      F.firstCoefficientGradedPolynomial_coordinate, dif_neg h, zero_smul]

theorem realFirstCoefficientGradedPolynomial_injective :
    Function.Injective (F.realFirstCoefficientGradedPolynomial b ω hF w) := by
  intro x y hxy
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [← F.realFirstCoefficientGradedPolynomial_coordinate,
    ← F.realFirstCoefficientGradedPolynomial_coordinate, hxy]

theorem realFirstCoefficientGradedPolynomial_homogeneous (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientGradedPolynomial b ω hF w x ∈
      shiftedGradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w 1 := by
  intro α
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [LinearMap.restrictScalars_apply, basisGradeProjection_repr]
  by_cases hi : ω i = Finsupp.weight w α + 1
  · rw [if_pos hi]
  · rw [if_neg hi, F.realFirstCoefficientGradedPolynomial_coordinate_of_ne b ω hF w x α i (Ne.symm hi)]

theorem realFirstCoefficientGradedPolynomial_bound (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound b ω hF w T M x) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
      (F.realFirstCoefficientGradedPolynomial b ω hF w x) := by
  intro α i
  by_cases hi : Finsupp.weight w α + 1 = ω i
  · rw [F.realFirstCoefficientGradedPolynomial_coordinate b ω hF w x ⟨(α, i), hi⟩]
    exact hx ⟨(α, i), hi⟩
  · rw [F.realFirstCoefficientGradedPolynomial_coordinate_of_ne b ω hF w x α i hi, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realFirstCoefficientGradedPolynomial_grid (l : ℕ) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid b ω hF w l x) :
    CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) l
      (F.realFirstCoefficientGradedPolynomial b ω hF w x) := by
  classical
  obtain ⟨v, hv⟩ := hx
  intro α
  refine ⟨fun i => if h : Finsupp.weight w α + 1 = ω i then v ⟨(α, i), h⟩ else 0, ?_⟩
  funext i
  change ((if h : Finsupp.weight w α + 1 = ω i then v ⟨(α, i), h⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) α) i
  by_cases hi : Finsupp.weight w α + 1 = ω i
  · rw [dif_pos hi, F.realFirstCoefficientGradedPolynomial_coordinate b ω hF w x ⟨(α, i), hi⟩]
    exact congrFun hv ⟨(α, i), hi⟩
  · rw [dif_neg hi, Int.cast_zero,
      F.realFirstCoefficientGradedPolynomial_coordinate_of_ne b ω hF w x α i hi, mul_zero]

theorem realFirstCoefficientGradedPolynomial_horizontal (x : F.RealFirstCoefficientModule w) :
    coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) 0 =
      (F.layerOneGradedMap b ω hF).baseChange ℝ (F.realFirstCoefficientHorizontal w x) := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  change _ = (F.layerOneGradedMap b ω hF).baseChange ℝ
    ((F.firstCoefficientHorizontal w).baseChange ℝ ((F.firstCoefficientRealEquiv w).symm
      (F.firstCoefficientRealEquiv w y)))
  rw [LinearEquiv.symm_apply_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [F.realFirstCoefficientGradedPolynomial_tmul, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, F.firstCoefficientGradedPolynomial_horizontal]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realAdaptedShiftedGradedPolynomial (k : ℕ) :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ[ℝ]
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  realificationRealLinearEquiv.toLinearMap.comp
    ((F.adaptedShiftedGradedPolynomial b ω hF w k).baseChange ℝ)

noncomputable def realAdaptedGradedPolynomialLie :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  realificationLieEquiv.toLieHom.comp
    (realLieHomToRat (realificationLieHom (F.adaptedGradedPolynomialLie b ω hF w)))

theorem realAdaptedShiftedGradedPolynomial_tensor (k : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedShiftedGradedPolynomial b ω hF w k x =
      realificationRealLinearEquiv ((F.adaptedShiftedGradedPolynomial b ω hF w k).baseChange ℝ x) := rfl

theorem realAdaptedGradedPolynomialLie_tensor (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie b ω hF w x =
      realificationLieEquiv (realificationLieHom (F.adaptedGradedPolynomialLie b ω hF w) x) := rfl

theorem realAdaptedGradedPolynomialLie_apply (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie b ω hF w x =
      F.realAdaptedShiftedGradedPolynomial b ω hF w 0 x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a p =>
    rw [F.realAdaptedGradedPolynomialLie_tensor, realificationLieHom_tmul,
      F.realAdaptedShiftedGradedPolynomial_tensor, LinearMap.baseChange_tmul,
      F.adaptedGradedPolynomialLie_apply]
    apply coefficients.injective
    ext α
    rw [coefficients_realificationLieEquiv_tmul, realificationRealLinearEquiv_apply,
      coefficients_realificationLinearEquiv_tmul]

theorem realAdaptedGradedPolynomialLie_symbol (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie b ω hF w x =
      F.realGradedSymbolPolynomial b ω hF w
        (realificationLieHom (F.polynomialSymbolMap w) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a p =>
    rw [F.realAdaptedGradedPolynomialLie_tensor, realificationLieHom_tmul,
      realificationLieHom_tmul]
    apply coefficients.injective
    ext α
    rw [coefficients_realificationLieEquiv_tmul, F.realGradedSymbolPolynomial_coefficient_tmul]
    rw [F.adaptedGradedPolynomialLie_apply, F.adaptedShiftedGradedPolynomial_apply,
      F.shiftedGradedPolynomial_zero]

theorem realAdaptedShiftedGradedPolynomial_lie
    (x y : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hy : y ∈ F.realShiftedCoefficientSubmodule w 1) :
    F.realAdaptedShiftedGradedPolynomial b ω hF w 1 ⁅x, y⁆ =
      ⁅F.realAdaptedGradedPolynomialLie b ω hF w x,
        F.realAdaptedShiftedGradedPolynomial b ω hF w 1 y⁆ := by
  change realificationLieEquiv
      ((F.adaptedShiftedGradedPolynomial b ω hF w 1).baseChange ℝ ⁅x, y⁆) =
    ⁅realificationLieEquiv (realificationLieHom (F.adaptedGradedPolynomialLie b ω hF w) x),
      realificationLieEquiv ((F.adaptedShiftedGradedPolynomial b ω hF w 1).baseChange ℝ y)⁆
  rw [realification_ideal_intertwining (F.shiftedPolynomialIdeal w 1)
    (F.adaptedGradedPolynomialLie b ω hF w) (F.adaptedShiftedGradedPolynomial b ω hF w 1)
    (F.adaptedShiftedGradedPolynomial_lie b ω hF w) x y hy, LieEquiv.map_lie]

theorem realFirstCoefficientGradedPolynomial_map (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientGradedPolynomial b ω hF w (F.realFirstCoefficientMap w x) =
      F.realAdaptedShiftedGradedPolynomial b ω hF w 1 x.val := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule).surjective x
  rw [← F.firstCoefficientRealEquiv_map, F.realFirstCoefficientGradedPolynomial_realEquiv]
  have he : (F.firstCoefficientGradedPolynomial b ω hF w).comp (F.firstCoefficientMap w) =
      (F.adaptedShiftedGradedPolynomial b ω hF w 1).comp
        (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype := by
    apply LinearMap.ext
    intro p
    exact F.firstCoefficientGradedPolynomial_map b ω hF w p
  change realificationRealLinearEquiv
      ((F.firstCoefficientGradedPolynomial b ω hF w).baseChange ℝ
        ((F.firstCoefficientMap w).baseChange ℝ y)) =
    realificationRealLinearEquiv
      ((F.adaptedShiftedGradedPolynomial b ω hF w 1).baseChange ℝ
        ((F.shiftedPolynomialIdeal w 1).toSubmodule.subtype.baseChange ℝ y))
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, he,
    LinearMap.baseChange_comp, LinearMap.comp_apply]

noncomputable def realAdaptedGradedPolynomialHom :
    F.RealAdaptedPolynomialGroup w →*
      PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.realAdaptedGradedPolynomialLie b ω hF w)

theorem realAdaptedShiftedGradedPolynomial_adjoint
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hx : x ∈ F.realShiftedCoefficientSubmodule w 1) :
    F.realAdaptedShiftedGradedPolynomial b ω hF w 1 (dualAdjoint g x) =
      dualAdjoint (F.realAdaptedGradedPolynomialHom b ω hF w g)
        (F.realAdaptedShiftedGradedPolynomial b ω hF w 1 x) := by
  let I : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
    { (F.realShiftedCoefficientSubmodule w 1).restrictScalars ℚ with
      lie_mem := fun {a y} hy => F.realShiftedCoefficient_lie_mem w 1 a y hy }
  exact dualLinearLift_adjoint
    (VectorPolynomial.lowerCentralSeries_eq_bot
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    I (F.realAdaptedGradedPolynomialLie b ω hF w)
    ((F.realAdaptedShiftedGradedPolynomial b ω hF w 1).restrictScalars ℚ)
    (F.realAdaptedShiftedGradedPolynomial_lie b ω hF w) g x hx

theorem realFirstCoefficientGradedPolynomial_adjoint
    (g : F.RealAdaptedPolynomialGroup w) (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientGradedPolynomial b ω hF w (F.realFirstCoefficientAdjoint w g x) =
      dualAdjoint (F.realAdaptedGradedPolynomialHom b ω hF w g)
        (F.realFirstCoefficientGradedPolynomial b ω hF w x) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype) x
  change F.realFirstCoefficientGradedPolynomial b ω hF w
      (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientMap w y)) =
    dualAdjoint (F.realAdaptedGradedPolynomialHom b ω hF w g)
      (F.realFirstCoefficientGradedPolynomial b ω hF w (F.realFirstCoefficientMap w y))
  rw [F.realFirstCoefficientAdjoint_map, F.realFirstCoefficientGradedPolynomial_map,
    F.realFirstCoefficientGradedPolynomial_map]
  exact F.realAdaptedShiftedGradedPolynomial_adjoint b ω hF w g y.val y.property

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem adaptedShiftedGradedPolynomial_directionalDerivative (h : σ → ℚ) (k : ℕ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) (k + 1)
        (F.adaptedDirectionalDerivative h p) =
      directionalDerivative h (F.adaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) k p) := by
  rw [F.adaptedShiftedGradedPolynomial_apply, F.adaptedDirectionalDerivative_coe,
    F.adaptedShiftedGradedPolynomial_apply]
  exact F.shiftedGradedPolynomial_directionalDerivative b ω hF h k p.val

theorem realAdaptedShiftedGradedPolynomial_directionalDerivative (h : σ → ℚ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1
        (F.realAdaptedDirectionalDerivative h x) =
      directionalDerivative h (F.realAdaptedGradedPolynomialLie b ω hF (fun _ : σ => 1) x) := by
  rw [F.realAdaptedGradedPolynomialLie_apply]
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a p =>
    have hd : F.realAdaptedDirectionalDerivative h (a ⊗ₜ[ℚ] p) =
        a ⊗ₜ[ℚ] F.adaptedDirectionalDerivative h p := rfl
    rw [hd, F.realAdaptedShiftedGradedPolynomial_tensor, F.realAdaptedShiftedGradedPolynomial_tensor,
      LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    rw [realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul,
      F.adaptedShiftedGradedPolynomial_directionalDerivative b ω hF h 0]
    rw [coefficients_directionalDerivative, coefficients_directionalDerivative]
    simp only [realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul]

variable [DecidableEq σ]

theorem realAdaptedGradedPolynomial_firstJet (i : σ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    dualLinearLift (F.realAdaptedGradedPolynomialLie b ω hF (fun _ : σ => 1))
        ((F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1).restrictScalars ℚ)
        (F.realAdaptedPolynomialJet (Pi.single i 1) g.coord).coord =
      (formalPolynomialJetHom i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g)).coord := by
  classical
  apply dual_ext
  · rw [dualLinearLift_base, F.realAdaptedPolynomialJet_base, formalPolynomialJet_base]
    rfl
  · rw [dualLinearLift_tangent, F.realAdaptedPolynomialJet_tangent, formalPolynomialJet_tangent,
      LinearMap.restrictScalars_apply, F.realAdaptedShiftedGradedPolynomial_directionalDerivative,
      directionalDerivative_single]
    rfl

theorem realAdaptedGradedPolynomial_logDerivative (i : σ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1
        (F.realAdaptedLogDerivative (Pi.single i 1) g.coord) =
      formalLogDerivative i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g) := by
  classical
  let I : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :=
    { (F.realShiftedCoefficientSubmodule (fun _ : σ => 1) 1).restrictScalars ℚ with
      lie_mem := fun {a y} hy => F.realShiftedCoefficient_lie_mem (fun _ : σ => 1) 1 a y hy }
  apply dualLinearLift_logDerivative_eq
    (VectorPolynomial.lowerCentralSeries_eq_bot
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    I (F.realAdaptedGradedPolynomialLie b ω hF (fun _ : σ => 1))
    ((F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1).restrictScalars ℚ)
    (F.realAdaptedShiftedGradedPolynomial_lie b ω hF (fun _ : σ => 1))
    (F.realAdaptedPolynomialJet (Pi.single i 1) g.coord) _
    (formalPolynomialJetHom i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g))
  · exact F.realAdaptedGradedPolynomial_firstJet b ω hF i g
  · rw [F.realAdaptedPolynomialJet_tangent]
    exact F.realAdaptedDirectionalDerivative_mem_first (Pi.single i 1) g.coord

theorem realFirstCoefficientGradedPolynomial_direction (i : σ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientGradedPolynomial b ω hF (fun _ : σ => 1)
        (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1)) =
      formalLogDerivative i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g) := by
  classical
  have he : (Pi.single i (1 : ℝ) : σ → ℝ) =
      (fun j => (((Pi.single i (1 : ℚ) : σ → ℚ) j) : ℝ)) := by
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [he, F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientGradedPolynomial_map]
  exact F.realAdaptedGradedPolynomial_logDerivative b ω hF i g

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareGradedSndMap :
    F.squareFiltration.quotientTop.AssociatedGraded →ₗ⁅ℚ⁆ F.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTop.associatedGradedMap F.quotientTop
    F.reducedSquareSnd F.reducedSquareSnd_mem

noncomputable def fastGradedDiagonal
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    LieSubalgebra ℚ F.quotientTop.AssociatedGraded :=
  W.map F.reducedSquareGradedSndMap

noncomputable def fullFastGradedDiagonal
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    LieSubalgebra ℚ F.AssociatedGraded :=
  (F.fastGradedDiagonal W).comap F.quotientTopGradedMap

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)

noncomputable def fastPointwiseSquare (w : σ → ℕ)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  F.squareFiltration.quotientTop.symbolPointwiseSubalgebra
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w W

theorem fastGradedDiagonal_graded
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule bQ ωQ (F.fastGradedDiagonal W).toSubmodule :=
  F.squareFiltration.quotientTop.associatedGradedMap_image_graded F.quotientTop
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem W hW

theorem fullFastGradedDiagonal_graded
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω (F.fullFastGradedDiagonal W).toSubmodule :=
  F.associatedGradedMap_comap_graded F.quotientTop e ω hF
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx)
    (F.fastGradedDiagonal W) (F.fastGradedDiagonal_graded e ω hF W hW)

theorem fastPointwiseDiagonal_eq [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W) =
      F.quotientTop.symbolPointwiseSubalgebra (F.quotientTopBasis e ω hF) ωQ
        (F.quotientTopBasis_layers e ω hF) w (F.fastGradedDiagonal W) := by
  let : Fintype (SymbolBasisIndex w ωQ) := symbolBasisIndexFintype w ωQ s hw
    (F.quotientTop.adaptedBasis_weight_le_step (F.quotientTopBasis e ω hF) ωQ
      (F.quotientTopBasis_layers e ω hF))
  exact F.squareFiltration.quotientTop.symbolPointwiseSubalgebra_map F.quotientTop
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w W hW

theorem fullFastPointwise_image_le [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    (F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W)).map (F.quotientTopSymbolMap w) ≤
      F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W) := by
  rw [F.fastPointwiseDiagonal_eq e ω hF w hw W hW]
  have hm := F.symbolPointwiseSubalgebra_map_le F.quotientTop e ω hF
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx)
    w (F.fullFastGradedDiagonal W)
  have hle : (F.fullFastGradedDiagonal W).map F.quotientTopGradedMap ≤ F.fastGradedDiagonal W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  exact hm.trans (F.quotientTop.symbolPointwiseSubalgebra_mono
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF) w hle)

theorem fullFastPointwise_eq_comap [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W) =
      (F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W)).comap
        (F.quotientTopSymbolMap w) := by
  rw [F.fastPointwiseDiagonal_eq e ω hF w hw W hW]
  exact (F.symbolPointwiseSubalgebra_comap F.quotientTop e ω hF
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx)
    w (F.fastGradedDiagonal W)).symm

theorem fullFastPointwise_subgroup_eq [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.realPointwisePolynomialSubgroup e ω hF w (F.fullFastGradedDiagonal W) =
      F.realFastDiagonalSubgroup w (F.fastPointwiseSquare e ω hF w W) := by
  ext g
  rw [F.mem_realPointwisePolynomialSubgroup, F.mem_realFastDiagonalSubgroup,
    F.adaptedReducedRealSymbolHom_coord]
  change F.realExtendedSymbolMap w g.coord ∈
      (F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W)).toSubmodule.baseChange ℝ ↔
    (F.quotientTopSymbolMap w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w g.coord) ∈
      (F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W)).toSubmodule.baseChange ℝ
  have he : (F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W)).toSubmodule =
      (F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W)).toSubmodule.comap
        (F.quotientTopSymbolMap w).toLinearMap :=
    congrArg LieSubalgebra.toSubmodule (F.fullFastPointwise_eq_comap e ω hF w hw W hW)
  rw [he, realification_comap]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
  (hW : BasisGradedSubmodule
    (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
    (fun i => squareBasisWeight ω i.val) W.toSubmodule)

include hW

theorem fullFast_horizontal_derivative_mem [DecidableEq σ]
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : B ∈ F.realFastDiagonalSubgroup (fun _ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W))
    (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.coord) 0 = 0) (i : σ) :
    F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W))
      (F.realFastCoefficientDirectionMap (F.fastPointwiseSquare e ω hF (fun _ => 1) W) B (Pi.single i 1)) ∈
      (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ := by
  have hb : B ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) (F.fullFastGradedDiagonal W) := by
    rw [F.fullFastPointwise_subgroup_eq e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW]
    exact hB
  have hs := (F.mem_realPointwisePolynomialSubgroup e ω hF (fun _ => 1) (F.fullFastGradedDiagonal W) B).mp hb
  exact F.pointwise_horizontal_derivative_mem e ω hF (F.fullFastGradedDiagonal W) B.coord hs hzero i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section Projection

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedPieceProjection_basis (j : ℕ) (i : ι) :
    F.gradedPieceProjection e ω hF j (e i) =
      if ω i = j then F.associatedGradedBasis e ω hF i else 0 := by
  classical
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext k
  rw [F.gradedPieceProjection_coordinate]
  by_cases hi : i = k <;> by_cases hj : ω i = j <;>
    simp_all only [Basis.repr_self, Finsupp.single_apply, ite_true, ite_false,
      map_zero, Finsupp.zero_apply, ite_self]

end Projection

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem reducedSquareDifference_basis (a : ReducedSquareBasisIndex s ω) :
    F.reducedSquareDifference (F.reducedSquareBasis e ω hF a) =
      Sum.elim (fun _ : ι => (0 : L)) (fun i : {i // 2 ≤ ω i} => e i.val) a.val := by
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareDifference_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl i => rw [F.adaptedSquareBasis_inl, sub_self]; rfl
  | inr i => rw [F.adaptedSquareBasis_inr, sub_zero]; rfl

noncomputable def reducedSquareGradedDifference :
    F.squareFiltration.quotientTop.AssociatedGraded →ₗ[ℚ] F.AssociatedGraded :=
  (bW).constr ℚ (fun a => Sum.elim (fun _ : ι => (0 : F.AssociatedGraded))
    (fun i : {i // 2 ≤ ω i} => F.associatedGradedBasis e ω hF i.val) a.val)

theorem reducedSquareGradedDifference_basis (a : ReducedSquareBasisIndex s ω) :
    F.reducedSquareGradedDifference e ω hF (bW a) =
      Sum.elim (fun _ : ι => (0 : F.AssociatedGraded))
        (fun i : {i // 2 ≤ ω i} => F.associatedGradedBasis e ω hF i.val) a.val := by
  exact Basis.constr_basis _ _ _ a

theorem reducedSquareGradedDifference_projection (j : ℕ)
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :
    F.reducedSquareGradedDifference e ω hF
        (F.squareFiltration.quotientTop.gradedPieceProjection
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) j x) =
      F.gradedPieceProjection e ω hF (j + 1) (F.reducedSquareDifference x) := by
  have he : (F.reducedSquareGradedDifference e ω hF).comp
      (F.squareFiltration.quotientTop.gradedPieceProjection
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) j) =
      (F.gradedPieceProjection e ω hF (j + 1)).comp F.reducedSquareDifference := by
    apply (F.reducedSquareBasis e ω hF).ext
    intro a
    simp only [LinearMap.comp_apply, F.squareFiltration.quotientTop.gradedPieceProjection_basis,
      F.reducedSquareDifference_basis]
    simp only [apply_ite, map_zero, F.reducedSquareGradedDifference_basis]
    rcases a with ⟨a, ha⟩
    cases a with
    | inl i => simp only [Sum.elim_inl, map_zero, ite_self]
    | inr i =>
      simp only [Sum.elim_inr, squareBasisWeight, F.gradedPieceProjection_basis]
      have hi : (ω i.val - 1 = j) ↔ ω i.val = j + 1 := by have h := i.property; omega
      simp only [hi]
  exact LinearMap.congr_fun he x

theorem reducedSquareGradedDifference_gradeProjection (j : ℕ)
    (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.reducedSquareGradedDifference e ω hF (basisGradeProjection bW ωW j x) =
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (j + 1)
        (F.reducedSquareGradedDifference e ω hF x) := by
  have he : (F.reducedSquareGradedDifference e ω hF).comp (basisGradeProjection bW ωW j) =
      (basisGradeProjection (F.associatedGradedBasis e ω hF) ω (j + 1)).comp
        (F.reducedSquareGradedDifference e ω hF) := by
    apply (bW).ext
    intro a
    simp only [LinearMap.comp_apply, basisGradeProjection, basisCoordinateProjection_basis,
      Set.mem_ofPred_eq]
    simp only [apply_ite, map_zero, F.reducedSquareGradedDifference_basis]
    rcases a with ⟨a, ha⟩
    cases a with
    | inl i => simp only [Sum.elim_inl, map_zero, ite_self]
    | inr i =>
      simp only [Sum.elim_inr, squareBasisWeight, basisCoordinateProjection_basis, Set.mem_ofPred_eq]
      have hi : (ω i.val - 1 = j) ↔ ω i.val = j + 1 := by have h := i.property; omega
      simp only [hi]
  exact LinearMap.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))

theorem firstCoefficientGradedPolynomial_normalized (p : F.normalizedRelativeSubmodule w) :
    F.firstCoefficientGradedPolynomial e ω hF w (F.normalizedFirstCoefficientMap w p) =
      F.shiftedGradedPolynomial e ω hF w 1 p.val.val := by
  change F.firstCoefficientGradedPolynomial e ω hF w
    (F.firstCoefficientMap w ⟨p.val, p.property.1⟩) = _
  rw [F.firstCoefficientGradedPolynomial_map, F.adaptedShiftedGradedPolynomial_apply]

theorem firstCoefficientGradedPolynomial_reducedSquare_symbol
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w
      (F.squareFiltration.quotientTop.polynomialSymbolMap w p))) α =
      F.reducedSquareGradedDifference e ω hF
        (coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w
            (F.squareFiltration.quotientTop.polynomialSymbolMap w p)) α) := by
  have hl : coefficients (F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w
      (F.squareFiltration.quotientTop.polynomialSymbolMap w p))) α =
      F.gradedPieceProjection e ω hF (Finsupp.weight w α + 1)
        (F.reducedSquareDifference (coefficients p.val α)) := by
    rw [F.reducedSquareCoefficientMap_symbol, F.firstCoefficientGradedPolynomial_normalized,
      F.shiftedGradedPolynomial_coefficient, F.reducedSquareDifferenceRelative_coefficient]
  have hr : coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w
        (F.squareFiltration.quotientTop.polynomialSymbolMap w p)) α =
      F.squareFiltration.quotientTop.gradedPieceProjection
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
        (Finsupp.weight w α) (coefficients p.val α) := by
    rw [← F.squareFiltration.quotientTop.shiftedGradedPolynomial_zero
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w p,
      F.squareFiltration.quotientTop.shiftedGradedPolynomial_coefficient]
    simp only [Nat.add_zero]
  calc
    _ = F.gradedPieceProjection e ω hF (Finsupp.weight w α + 1)
        (F.reducedSquareDifference (coefficients p.val α)) := hl
    _ = F.reducedSquareGradedDifference e ω hF
        (F.squareFiltration.quotientTop.gradedPieceProjection
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
          (Finsupp.weight w α) (coefficients p.val α)) :=
      (F.reducedSquareGradedDifference_projection e ω hF (Finsupp.weight w α) (coefficients p.val α)).symm
    _ = _ := congrArg (F.reducedSquareGradedDifference e ω hF) hr.symm

theorem firstCoefficientGradedPolynomial_reducedSquare_coefficient
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w x)) α =
      F.reducedSquareGradedDifference e ω hF
        (coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w x) α) := by
  obtain ⟨p, rfl⟩ := F.squareFiltration.quotientTop.polynomialSymbolMap_surjective w x
  exact F.firstCoefficientGradedPolynomial_reducedSquare_symbol e ω hF w p α

theorem firstCoefficientGradedPolynomial_reducedSquare
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) :
    F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w x) =
      VectorPolynomial.map (F.reducedSquareGradedDifference e ω hF)
        (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map, F.firstCoefficientGradedPolynomial_reducedSquare_coefficient]

theorem firstCoefficientGradedPolynomial_reducedSquare_homogeneous (α : σ →₀ ℕ)
    (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.firstCoefficientGradedPolynomial e ω hF w
        (F.reducedSquareCoefficientMap w
          (F.squareFiltration.quotientTop.homogeneousSymbolLift
            (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α x)) =
      monomial α (basisGradeProjection (F.associatedGradedBasis e ω hF) ω (Finsupp.weight w α + 1)
        (F.reducedSquareGradedDifference e ω hF x)) := by
  rw [F.firstCoefficientGradedPolynomial_reducedSquare,
    F.squareFiltration.quotientTop.gradedSymbolPolynomial_homogeneousSymbolLift,
    VectorPolynomial.map_monomial, F.reducedSquareGradedDifference_gradeProjection]

theorem reducedSquareGradedSnd_coefficient
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) (α : σ →₀ ℕ) :
    F.reducedSquareGradedSndMap
        (coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w x) α) =
      coefficients (F.quotientTop.gradedSymbolPolynomial (F.quotientTopBasis e ω hF)
        (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w (F.reducedSquareSndSymbolMap w x)) α := by
  unfold reducedSquareGradedSndMap reducedSquareSndSymbolMap
  rw [F.squareFiltration.quotientTop.gradedSymbolPolynomial_filteredMap_coefficient
    F.quotientTop (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w x α]

theorem reducedSquareSnd_homogeneousSymbolLift (α : σ →₀ ℕ)
    (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.reducedSquareSndSymbolMap w
        (F.squareFiltration.quotientTop.homogeneousSymbolLift
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α x) =
      F.quotientTop.homogeneousSymbolLift (F.quotientTopBasis e ω hF)
        (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w α (F.reducedSquareGradedSndMap x) := by
  exact F.squareFiltration.quotientTop.homogeneousSymbolLift_filteredMap
    F.quotientTop (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w α x

end Erdos3.NilpotentLieFiltration

end

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

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem firstCoefficientGradedPolynomial_normalized_lie (w : σ → ℕ)
    (a : F.adaptedLieSubalgebra w) (p : F.normalizedRelativeSubmodule w) :
    F.firstCoefficientGradedPolynomial e ω hF w
      (F.normalizedFirstCoefficientMap w
        ⟨⁅a, p.val⁆, F.normalizedRelativeSubmodule_lie_mem w a p.val p.property⟩) =
      ⁅F.adaptedGradedPolynomialLie e ω hF w a,
        F.firstCoefficientGradedPolynomial e ω hF w (F.normalizedFirstCoefficientMap w p)⁆ := by
  rw [F.firstCoefficientGradedPolynomial_normalized, F.firstCoefficientGradedPolynomial_normalized]
  have he := F.adaptedShiftedGradedPolynomial_lie e ω hF w a p.val p.property.1
  simp only [F.adaptedShiftedGradedPolynomial_apply] at he
  rw [he]

theorem reducedSquareGradedDifference_unit (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    eval (fun _ : Unit => (1 : ℚ))
      (F.firstCoefficientGradedPolynomial e ω hF (fun _ : Unit => 1)
        (F.reducedSquareCoefficientMap (fun _ : Unit => 1) x)) =
      F.reducedSquareGradedDifference e ω hF x := by
  rw [F.firstCoefficientGradedPolynomial_reducedSquare, eval_map,
    F.squareFiltration.quotientTop.gradedSymbolPolynomial_unit_eval]

theorem reducedSquareGradedDifference_relative_lie
    (a : F.adaptedLieSubalgebra (fun _ : Unit => 1))
    (p : F.normalizedRelativeSubmodule (fun _ : Unit => 1)) :
    F.reducedSquareGradedDifference e ω hF
      ⁅F.reducedSquareDiagonalSymbolMap (fun _ : Unit => 1)
          (F.adaptedReducedSymbolMap (fun _ : Unit => 1) a),
        F.reducedRelativeSquareSymbolMap (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p⁆ =
      ⁅F.polynomialSymbolMap (fun _ : Unit => 1) a,
        F.reducedSquareGradedDifference e ω hF
          (F.reducedRelativeSquareSymbolMap (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p)⁆ := by
  rw [← F.reducedRelativeSquareSymbolMap_lie,
    ← F.reducedSquareGradedDifference_unit, F.reducedSquareCoefficientMap_relative,
    F.firstCoefficientGradedPolynomial_normalized_lie]
  change (evalLie (fun _ : Unit => (1 : ℚ))) ⁅_, _⁆ = _
  rw [LieHom.map_lie]
  simp only [evalLie_apply]
  rw [F.adaptedGradedPolynomialLie_unit_eval,
    ← F.reducedSquareCoefficientMap_relative (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p,
    F.reducedSquareGradedDifference_unit]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicSpatialMeshLog (j d : ℕ) (p l : ℝ) : ℝ :=
  (j : ℝ) ^ 2 + j * l + 4 * (j + d) + spatialProfileLog j d p + 3

theorem anisotropicSpatialDensityLip_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {M : ℕ} {p : ℝ} (hp : 0 ≤ p) (hM : 0 < M)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hI : (Fintype.card (Unit ⊕ I) : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p) :
    anisotropicSpatialDensityLip s (1 / (M : ℝ)) ≤
      Real.exp (anisotropicSpatialCapLog p +
        2 * spatialProfileLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s)) p) := by
  let P := spatialProfileLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s)) p
  have hdata := spatialProfileLog_bounds Empty s hp hMp
  have hinv : physicalSpatialInverseBound I (1 / (M : ℝ)) ≤ Real.exp P := by
    rw [physicalSpatialInverseBound_eq_scalar]
    simpa only [P, Fintype.card_sum, Fintype.card_empty, add_zero] using hdata.2.1
  have hK : ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) *
      probabilityProfileLipschitz) ≤ Real.exp P := by
    simpa only [P, Fintype.card_sum, Fintype.card_empty, add_zero] using hdata.2.2.2
  have hcap := anisotropicSpatialDensityCap_exp_bound s hp hM hMp hI hJ
  have hcap0 := anisotropicSpatialDensityCap_nonneg s
    (show 0 ≤ 1 / (M : ℝ) by positivity)
  have hinv0 : 0 ≤ physicalSpatialInverseBound I (1 / (M : ℝ)) := by
    unfold physicalSpatialInverseBound
    positivity
  unfold anisotropicSpatialDensityLip
  calc
    _ ≤ Real.exp (anisotropicSpatialCapLog p) * Real.exp P * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem probabilityProfileLipschitz_le_comparisonProfileBound :
    (probabilityProfileLipschitz : ℝ) ≤ VectorPolynomial.comparisonProfileBound :=
  (Nat.le_ceil _).trans (by unfold VectorPolynomial.comparisonProfileBound; push_cast; linarith)

noncomputable def spatialFixedProfileEnvelope {A : Type*} [Semiring A] (p : A) : A :=
  (p + 1) * p + p ^ 2 + 4 * p + (VectorPolynomial.comparisonProfileBound : ℕ) + 1

noncomputable def spatialDisplacementEnvelope {A : Type*} [Semiring A] (p : A) : A :=
  p ^ 2 + (p + 3) * spatialFixedProfileEnvelope p + 2 * p + p

noncomputable def spatialDiscretizationEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  2 * p ^ 2 + (2 * p + 4) * spatialFixedProfileEnvelope p +
    (p + 2 * (2 * p)) * (spatialFixedProfileEnvelope p + 4) + 4 + p * l

noncomputable def spatialMeshEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  p ^ 2 + p * l + 4 * (p + 2 * p) + spatialFixedProfileEnvelope p + 3

noncomputable def spatialLipschitzEnvelope {A : Type*} [Semiring A] (p : A) : A :=
  anisotropicSpatialCapLog p + 2 * spatialFixedProfileEnvelope p

theorem spatialCostEnvelopes_nonneg {p l : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l) :
    0 ≤ spatialFixedProfileEnvelope p ∧ 0 ≤ spatialDisplacementEnvelope p ∧
      0 ≤ spatialDiscretizationEnvelope p l ∧ 0 ≤ spatialMeshEnvelope p l ∧
      0 ≤ spatialLipschitzEnvelope p := by
  dsimp only [spatialDisplacementEnvelope, spatialDiscretizationEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope, anisotropicSpatialCapLog]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> positivity

theorem spatialProfileLog_le_fixedEnvelope (j d : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p) :
    spatialProfileLog j d p ≤ spatialFixedProfileEnvelope p := by
  have hprofile := probabilityProfileLipschitz_le_comparisonProfileBound
  calc
    _ ≤ (p + 1) * p + p ^ 2 + 2 * p + 2 * p +
        (VectorPolynomial.comparisonProfileBound : ℝ) + 1 := by
      unfold spatialProfileLog
      gcongr
    _ = _ := by unfold spatialFixedProfileEnvelope; ring

theorem spatialDisplacementLog_le_envelope (j d e n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p)
    (he : (e : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) :
    spatialDisplacementLog j d e n p ≤ spatialDisplacementEnvelope p := by
  have hprofile := spatialProfileLog_le_fixedEnvelope j d hp hj hd
  have hprofile0 := spatialProfileLog_nonneg j d hp
  unfold spatialDisplacementLog spatialDisplacementEnvelope
  gcongr

theorem spatialDiscretizationLog_le_envelope (j d : ℕ) {p l : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ l) (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p) :
    spatialDiscretizationLog j d p l ≤ spatialDiscretizationEnvelope p l := by
  have hprofile := spatialProfileLog_le_fixedEnvelope j d hp hj hd
  have hprofile0 := spatialProfileLog_nonneg j d hp
  dsimp only [spatialDiscretizationLog, spatialDiscretizationEnvelope]
  gcongr

theorem anisotropicSpatialMeshLog_le_envelope (j d : ℕ) {p l : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ l) (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p) :
    anisotropicSpatialMeshLog j d p l ≤ spatialMeshEnvelope p l := by
  have hprofile := spatialProfileLog_le_fixedEnvelope j d hp hj hd
  unfold anisotropicSpatialMeshLog spatialMeshEnvelope
  gcongr

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def spatialLipschitzCostEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  p ^ 3 + spatialLipschitzEnvelope p + l + 1

noncomputable def spatialThresholdEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  spatialMeshEnvelope p l + (VectorPolynomial.comparisonProfileBound : ℕ) + 2 * p + l + 16

noncomputable def spatialBoundaryEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  l + (VectorPolynomial.comparisonProfileBound : ℕ) + 3 * p + 25

def spatialMovementEnvelope {A : Type*} [Semiring A] (p l : A) : A := p + l + 2

theorem spatialAuxiliaryDimensions {I G N : Type*} [Fintype I] [Fintype G] [Fintype N]
    (s : I ↪ G) {p : ℝ} (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p) :
    (Fintype.card (UnselectedColumn s) : ℝ) ≤ p ∧
      (Fintype.card (UnselectedColumn s ⊕ N) : ℝ) ≤ 2 * p ∧
      (Fintype.card (Option (G ⊕ N)) : ℝ) ≤ 1 + 2 * p := by
  have he : (Fintype.card (UnselectedColumn s) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hG
  refine ⟨he, ?_, ?_⟩
  · simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  · simp only [Fintype.card_option, Fintype.card_sum, Nat.cast_add, Nat.cast_one]
    linarith

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

noncomputable def normalizedTupleTolerance (X : Type*) [Fintype X] (p E : ℝ) : ℝ :=
  spatialTupleTolerance (Fintype.card X) (Real.exp (p ^ 3 + anisotropicSpatialCapLog p))
    (Real.exp (coefficientErrorVolumeLog p + 4)) (normalizedSpatialShare E / 2)

noncomputable def normalizedTupleNarrowWidth (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E : ℝ) : ℝ :=
  twoTermErrorWidth (smoothSpatialDisplacementCost N s M) (normalizedTupleTolerance X p E)

noncomputable def normalizedTupleRadius (X : Type*) [Fintype X]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E W : ℝ) : ℝ :=
  twoTermErrorWidth (Real.exp (p ^ 3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W)))
    (normalizedTupleTolerance X p E)

noncomputable def normalizedTupleResolution (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ)
    (p E C₀ W Cg Centry : ℝ) : ℝ :=
  twoTermErrorResolution
    (anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
      2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry))
    (anisotropicSpatialDiscretizationCost N s M C₀) (normalizedTupleTolerance X p E) +
    (Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X))) /
      (normalizedSpatialShare E / 2) +
    (Fintype.card N * (2 * Centry)) / normalizedTupleRadius X s M p E W

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial

noncomputable def spatialTupleCoarseMesh (n : ℕ) (G V K ε : ℝ) : ℝ :=
  twoTermErrorWidth K (spatialTupleTolerance n G V ε) / 4

theorem spatialTupleCoarseMesh_spec (n : ℕ) {G V K ε : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hK : 0 ≤ K) (hε : 0 < ε) :
    0 < spatialTupleCoarseMesh n G V K ε ∧ spatialTupleCoarseMesh n G V K ε ≤ 1 / 4 ∧
      ∀ {g k v : ℝ}, 0 ≤ g → g ≤ G → 0 ≤ k → k ≤ K → 0 ≤ v → v ≤ V →
        n * (8 * k * spatialTupleCoarseMesh n G V K ε) * (1 + g)^n * v ≤ ε := by
  let t := spatialTupleTolerance n G V ε
  let δ := twoTermErrorWidth K t
  have ht := spatialTupleTolerance_spec n hG hV hε
  have hδ := twoTermErrorWidth_spec hK ht.1
  have ht0 : 0 < t := ht.1
  have hδ0 : 0 < δ := hδ.1
  have hr : 0 < spatialTupleCoarseMesh n G V K ε := div_pos hδ.1 (by norm_num)
  refine ⟨hr, div_le_div_of_nonneg_right hδ.2.1 (by norm_num), ?_⟩
  intro g k v hg hgG hk hkK hv hvV
  have hinner : 8 * k * spatialTupleCoarseMesh n G V K ε ≤ t := by
    have hkδ : k * δ ≤ K * δ := mul_le_mul_of_nonneg_right hkK hδ0.le
    change 8 * k * (δ / 4) ≤ t
    linarith [hδ.2.2]
  have hp : (1 + g)^n ≤ (2 + G)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ n * t * (2 + G)^n * V := by gcongr
    _ = t * (2 + G)^n * (n * V) := by ring
    _ ≤ t * (2 + G)^n * (2 * (n + 1) * (1 + V)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    _ = t * (2 * (n + 1) * (2 + G)^n * (1 + V)) := by ring
    _ ≤ ε := ht.2.2

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

end Erdos3.VectorPolynomial

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

noncomputable def spatialPrimitiveEnvelope {A : Type*} [Semiring A] (p E l : A) : A :=
  p + E + l + 3 + (p ^ 3 + anisotropicSpatialCapLog p) +
    (coefficientErrorVolumeLog p + 4) + spatialDisplacementEnvelope p +
    spatialDiscretizationEnvelope p l + spatialLipschitzCostEnvelope p l +
    spatialThresholdEnvelope p l + spatialBoundaryEnvelope p l + spatialMovementEnvelope p l

noncomputable def spatialParameterBudget {A : Type*} [Semiring A] (p E l : A) : A :=
  let R := spatialPrimitiveEnvelope p E l
  3 * (2 * (R + spatialTupleToleranceLog R) + 4) + 8

end Erdos3

end

section

namespace Erdos3

section Maps

variable {α β : Type*} [Semiring α] [Semiring β] (f : α →+* β)

@[simp] theorem map_coefficientErrorSpatialLog (p : α) :
    f (coefficientErrorSpatialLog p) = coefficientErrorSpatialLog (f p) := by
  simp [coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
    map_ofNat]

@[simp] theorem map_spatialPrimitiveEnvelope (p E l : α) :
    f (spatialPrimitiveEnvelope p E l) = spatialPrimitiveEnvelope (f p) (f E) (f l) := by
  simp [spatialPrimitiveEnvelope, spatialDisplacementEnvelope,
    spatialDiscretizationEnvelope, spatialLipschitzCostEnvelope,
    spatialThresholdEnvelope, spatialBoundaryEnvelope, spatialMovementEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog, map_ofNat]

@[simp] theorem map_spatialTupleToleranceLog (p : α) :
    f (spatialTupleToleranceLog p) = spatialTupleToleranceLog (f p) := by
  simp [spatialTupleToleranceLog, map_ofNat]

@[simp] theorem map_spatialParameterBudget (p E l : α) :
    f (spatialParameterBudget p E l) = spatialParameterBudget (f p) (f E) (f l) := by
  simp only [spatialParameterBudget, map_add, map_mul, map_ofNat,
    map_spatialPrimitiveEnvelope, map_spatialTupleToleranceLog]

end Maps

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedWidthNormalizedTupleSideBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def normalizedTupleLateBudget (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E l : ℝ) : ℝ :=
  let j := Fintype.card (Unit ⊕ Fin q)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  spatialDiscretizationLog j d p l + anisotropicSpatialMeshLog j d p l +
    (p ^ 3 + anisotropicSpatialCapLog p +
      2 * spatialProfileLog j (Fintype.card (UnselectedColumn s)) p + l + 1) +
    spatialTupleToleranceLog (anisotropicTupleEarlyBudget N s p (E + 3)) + E + 3 + 2 * l +
    Fintype.card (Option (G ⊕ N)) + Fintype.card (Option (G ⊕ N) × X) + Fintype.card N + 40

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def normalizedTupleWidthLog (N : Type*) [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E : ℝ) : ℝ :=
  let Q := anisotropicTupleEarlyBudget N s p (E + 3)
  2 * (Q + spatialTupleToleranceLog Q) + 4

noncomputable def normalizedTupleSideLog (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E l : ℝ) : ℝ :=
  3 * normalizedTupleLateBudget X N s p E l + normalizedTupleWidthLog N s p E + 3 * l + 17

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def sharedWidthNormalizedTupleSideLog (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E l Bξ : ℝ) : ℝ :=
  3 * normalizedTupleLateBudget X N s p E l + Bξ + 3 * l + 17

end Erdos3

end

end OAI

end


