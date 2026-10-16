-- Prove2me | Definitions.Def_OAIErdos3B074
-- name    : OAIErdos3B074
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T18:26:18.427786+00:00
-- url     : https://prove2.me/theorems/38ec9694-72ea-424a-83da-59e17a83e3c1
-- title:
--   OpenAI Erdős-3 split, definitions bundle 75 of 1336
-- statement:
--   Definitions bundle 75 of 1336 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B073`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 75 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.coeff_realSymbolCoordinate`, `OAI.Erdos3.NilpotentLieFiltration.exists_full_restricted_grade_vector_major_detection`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolCoordinate`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolCoordinate_coeff_of_ne`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolCoordinate_coeff_symbol`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolCoordinate_coeff_zero`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolCoordinate_constantCoeff`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolCoordinate_isWeightedHomogeneous`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_joint_grid`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseCoordinatePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseCoordinatePolynomial_eval`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseCoordinatePolynomial_mass_of_slow`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseCoordinatePolynomial_scaled_totalDegree`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseCoordinatePolynomial_totalDegree`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationGroupCoordinates_uniform_bounds`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationGroupEval_normalized_left`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationGroupPolynomial`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationGroupPolynomial_specialize`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinatePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinate_common_coefficient_grid`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinate_constant`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinate_eq_canonical`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinate_eq_scalar`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinate_homogeneous`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinate_joint_grid`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinate_normalized_mass`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinate_slow_coefficients`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogCoordinate_totalDegree`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogFunctional`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogFunctional_basis`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogProjectionMatrix`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogProjectionMatrix_height_of_basis`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationLogProjectionMatrix_logHeight`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationNormalizedBase`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationNormalizedBase_eval`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationNormalizedPhase`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationNormalizedPhase_eval`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_coefficientGrid`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_eq_logMixed`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_eval`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_isWeightedHomogeneous`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_mass_of_slow`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_normalized_mass`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_scaled_totalDegree`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_scaled_weightedSupportLE`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_totalDegree`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationPhasePolynomial_weightedSupportLE`, `OAI.Erdos3.PolynomialTranslationLie.exists_detectedTranslationLogCoordinate_common_grid`, `OAI.Erdos3.PolynomialTranslationLie.exists_detectedTranslationLogCoordinate_grid_of_basis_height`, `OAI.Erdos3.PolynomialTranslationLie.exists_detectedTranslation_normalized_weighted_decomposition`, `OAI.Erdos3.PolynomialTranslationLie.exists_detectedTranslation_rational_right`, `OAI.Erdos3.PolynomialTranslationLie.exists_reduced_majorPolynomial_degree_twisted_correlation_decomposition`, `OAI.Erdos3.PolynomialTranslationLie.nativeTranslationGroupPolynomial`, `OAI.Erdos3.PolynomialTranslationLie.nativeTranslationGroupPolynomial_orbit`, `OAI.Erdos3.PolynomialTranslationLie.nativeTranslationGroupPolynomial_specialize`, `OAI.Erdos3.PolynomialTranslationLie.nativeTranslationLogCoordinate`, `OAI.Erdos3.PolynomialTranslationLie.nativeTranslationLogCoordinate_coeff`, `OAI.Erdos3.PolynomialTranslationLie.nativeTranslationLogCoordinate_eval`, `OAI.Erdos3.PolynomialTranslationLie.nativeTranslationLogCoordinate_symbol`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_base_abs_le_one`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_base_integer`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_polynomial_mass_le_one`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_polynomial_real_grid`, `OAI.Erdos3.VectorPolynomial.exists_homogeneous_vector_major_detection`, `OAI.Erdos3.VectorPolynomial.exists_majorPhase_detected_decomposition`, `OAI.Erdos3.VectorPolynomial.exists_majorPhase_residue_detection`, `OAI.Erdos3.VectorPolynomial.majorPhase_affine_integrand`, `OAI.Erdos3.VectorPolynomial.majorPhase_residue_lowTagged_rank`, `OAI.Erdos3.detectedTranslationCoordinateConstant`, `OAI.Erdos3.realPolynomialMass_specializeMajorParameters_zero_le`, `OAI.Erdos3.realPolynomialMass_weightedHomogeneousComponent_le`, `OAI.Erdos3.realifyFunctional_basis_coord`, `OAI.Erdos3.reducedMajorZeroSlice_mass_le`, `OAI.Erdos3.scaleMvPolynomialAxes_mass_le_of_totalDegree`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B210

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationLogCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realSymbolCoordinate (x : F.RealPolynomialSymbol w) (i : ι) :
    MvPolynomial σ ℝ :=
  coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom
    (F.realSymbolRepresentative b ω hlayers w x)

@[simp] theorem coeff_realSymbolCoordinate (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) :
    (F.realSymbolCoordinate b ω hlayers w x i).coeff α =
      (b.baseChange ℝ).repr
        (coefficients (F.realSymbolRepresentative b ω hlayers w x) α) i := by
  simp only [realSymbolCoordinate, coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    Basis.coord_apply]

theorem realSymbolCoordinate_coeff_of_ne (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α ≠ ω i) :
    (F.realSymbolCoordinate b ω hlayers w x i).coeff α = 0 := by
  rw [F.coeff_realSymbolCoordinate]
  exact F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w x α i h

@[simp] theorem realSymbolCoordinate_coeff_symbol (x : F.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w ω) :
    (F.realSymbolCoordinate b ω hlayers w x z.val.2).coeff z.val.1 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z := by
  rw [F.coeff_realSymbolCoordinate]
  exact F.realSymbolRepresentative_coefficient b ω hlayers w x z

theorem realSymbolCoordinate_isWeightedHomogeneous (x : F.RealPolynomialSymbol w)
    (i : ι) :
    (F.realSymbolCoordinate b ω hlayers w x i).IsWeightedHomogeneous w (ω i) := by
  intro α hα
  by_contra h
  exact hα (F.realSymbolCoordinate_coeff_of_ne b ω hlayers w x α i h)

@[simp] theorem realSymbolCoordinate_coeff_zero (x : F.RealPolynomialSymbol w) (i : ι) :
    (F.realSymbolCoordinate b ω hlayers w x i).coeff 0 = 0 := by
  rw [F.coeff_realSymbolCoordinate, F.realSymbolRepresentative_constant b ω hlayers w x,
    map_zero, Finsupp.zero_apply]

@[simp] theorem realSymbolCoordinate_constantCoeff (x : F.RealPolynomialSymbol w) (i : ι) :
    MvPolynomial.constantCoeff (F.realSymbolCoordinate b ω hlayers w x i) = 0 := by
  exact F.realSymbolCoordinate_coeff_zero b ω hlayers w x i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

noncomputable def nativeTranslationLogCoordinate (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) (k : κ) :
    MvPolynomial U ℝ :=
  VectorPolynomial.coordinate ((b.baseChange ℝ).coord k).toAddMonoidHom p

omit [Fintype κ] in
@[simp] theorem nativeTranslationLogCoordinate_coeff (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d))
    (k : κ) (α : U →₀ ℕ) :
    (nativeTranslationLogCoordinate w d b p k).coeff α =
      (b.baseChange ℝ).repr (VectorPolynomial.coefficients p α) k :=
  VectorPolynomial.coeff_coordinate _ _ _

theorem nativeTranslationLogCoordinate_eval (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) (u : U → ℝ) :
    VectorPolynomial.eval₂ u p =
      ∑ k, (eval u (nativeTranslationLogCoordinate w d b p k)) ⊗ₜ[ℚ] b k := by
  calc
    VectorPolynomial.eval₂ u p =
        ∑ k, (b.baseChange ℝ).repr (VectorPolynomial.eval₂ u p) k •
          (b.baseChange ℝ) k := ((b.baseChange ℝ).sum_repr _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      change ((b.baseChange ℝ).coord k) (VectorPolynomial.eval₂ u p) •
        (b.baseChange ℝ) k = _
      rw [VectorPolynomial.coordinate_eval₂, Basis.baseChange_apply]
      simp only [nativeTranslationLogCoordinate, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

noncomputable def nativeTranslationGroupPolynomial (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) :
    PolynomialTranslationGroupOver (MvPolynomial U ℝ) B :=
  translationLogGroupPolynomial w d b (nativeTranslationLogCoordinate w d b p)

theorem nativeTranslationGroupPolynomial_specialize (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u) (nativeTranslationGroupPolynomial w d b p) =
      bchRealTranslationHom w d hwd ⟨VectorPolynomial.eval₂ u p⟩ := by
  rw [nativeTranslationGroupPolynomial, translationLogGroupPolynomial_specialize,
    ← nativeTranslationLogCoordinate_eval]

theorem nativeTranslationGroupPolynomial_orbit (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (v : U → ℕ) (g : (weightedFiltration w d hwd).realification.PolynomialOrbit v)
    (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u) (nativeTranslationGroupPolynomial w d b g.log) =
      bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval v u g) :=
  nativeTranslationGroupPolynomial_specialize w d hwd b g.log u

omit [Fintype κ] in
@[simp] theorem nativeTranslationLogCoordinate_symbol (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (ω : κ → ℕ)
    (hb : ∀ j, (weightedFiltration w d hwd).layer j =
      Submodule.span ℚ (b '' {k | j ≤ ω k}))
    (v : U → ℕ) (g : (weightedFiltration w d hwd).RealPolynomialSymbolGroup v)
    (k : κ) :
    nativeTranslationLogCoordinate w d b
        ((weightedFiltration w d hwd).realPolynomialSymbolLift b ω hb v g).coord.val k =
      (weightedFiltration w d hwd).realSymbolCoordinate b ω hb v g.coord k := rfl

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem realifyFunctional_basis_coord {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (i : ι) :
    realifyFunctional (b.coord i) = (b.baseChange ℝ).coord i := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [realifyFunctional_tmul]
    change a * (b.repr x i : ℝ) = (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] x) i
    rw [Basis.baseChange_repr_tmul]
    simp only [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace NilpotentLieFiltration

theorem scalarSymbolPolynomial_joint_grid
    {σ ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (θ : κ → F.AssociatedGraded →ₗ[ℚ] ℚ) (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g) :
    (fun z : (σ →₀ ℕ) × κ =>
      (F.scalarSymbolPolynomial b ω hF w (θ z.2) g).coeff z.1) ∈
        realDenominatorGrid (matrixDenominator (fun k i => θ k (F.associatedGradedBasis b ω hF i)) * m) := by
  classical
  let ℓ : F.AssociatedGraded →ₗ[ℚ] (κ → ℚ) := LinearMap.pi θ
  have hval (α : σ →₀ ℕ) :
      realifyCoordinateMap ℓ
        (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) =
        fun k => (F.scalarSymbolPolynomial b ω hF w (θ k) g).coeff α := by
    funext k
    rw [F.coeff_scalarSymbolPolynomial]
    rfl
  have hgrid (α : σ →₀ ℕ) :
      (fun k => (F.scalarSymbolPolynomial b ω hF w (θ k) g).coeff α) ∈
        realDenominatorGrid (matrixDenominator (fun k i => θ k (F.associatedGradedBasis b ω hF i)) * m) := by
    have h := realifyCoordinateMap_grid (F.associatedGradedBasis b ω hF) ℓ m _
      (F.realGradedSymbolPolynomial_rational_coordinates b ω hF w m g hg α)
    rw [hval] at h
    exact h
  choose a ha using hgrid
  refine ⟨fun z => a z.1 z.2, ?_⟩
  funext z
  exact congrFun (ha z.1) z.2

end NilpotentLieFiltration

namespace PolynomialTranslationLie

open RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationLogCoordinatePolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) : MvPolynomial U ℝ :=
  coordinate (((weightedBasis w d hw).baseChange ℝ).coord k).toAddMonoidHom
    (detectedTranslationSymbolLift w d hw hwd M hM D E).log

theorem detectedTranslationLogCoordinate_eq_canonical
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k =
      (weightedFiltration w d hwd).realSymbolCoordinate (weightedBasis w d hw)
        (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
        (fun _ : U => 1) (detectedTranslationSymbolProjection w d hw hwd M hM D E).coord k := by
  simp only [detectedTranslationLogCoordinatePolynomial, detectedTranslationSymbolLift_log,
    NilpotentLieFiltration.realSymbolCoordinate, detectedTranslationSymbolProjection_coord]

theorem detectedTranslationLogCoordinate_homogeneous
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).IsWeightedHomogeneous
      (fun _ : U => 1) (weightedBasisGrade w d k) := by
  rw [detectedTranslationLogCoordinate_eq_canonical]
  exact (weightedFiltration w d hwd).realSymbolCoordinate_isWeightedHomogeneous
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) _ _ k

@[simp] theorem detectedTranslationLogCoordinate_constant
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).coeff 0 = 0 := by
  rw [detectedTranslationLogCoordinate_eq_canonical]
  exact (weightedFiltration w d hwd).realSymbolCoordinate_coeff_zero
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) _ _ k

noncomputable def detectedTranslationLogFunctional (k : WeightedBasisIndex w d) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded →ₗ[ℚ] ℚ :=
  ((weightedBasis w d hw).coord k).comp
    (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
      w d hw hwd (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).toLinearMap

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationLogCoordinate_eq_scalar
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k =
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
        b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D k) E := by
  rw [detectedTranslationLogCoordinatePolynomial, detectedTranslationSymbolLift_log]
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.homogeneousProjected_scalar_coordinate
    (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    (fun _ : U => 1) ((weightedBasis w d hw).coord k) E.coord
  rw [realifyFunctional_basis_coord] at h
  change (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
    b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D k) E = _ at h
  convert h.symm using 1

noncomputable def detectedTranslationLogProjectionMatrix : Matrix (WeightedBasisIndex w d) ι ℚ :=
  fun k i => if ω i = weightedBasisGrade w d k then (weightedBasis w d hw).repr (b i true) k else 0

theorem detectedTranslationLogFunctional_basis (k : WeightedBasisIndex w d) (i : ι) :
    detectedTranslationLogFunctional w d hw hwd M hM D k
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN i) =
      detectedTranslationLogProjectionMatrix w d hw b ω k i := by
  exact (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.homogeneousGradedProjection_basis_repr
    (weightedFiltration w d hwd) (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    b ω hN i k

theorem detectedTranslationLogCoordinate_slow_coefficients [Fintype ι]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (k : WeightedBasisIndex w d)
    (hproj : ∀ i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) (α : U →₀ ℕ) :
    |(detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).coeff α| ≤
      (Fintype.card ι : ℝ) * H * A / monomialScale T α := by
  rw [detectedTranslationLogCoordinate_eq_scalar w d hw hwd M hM D b ω hN]
  apply NilpotentLieFiltration.scalarSymbolPolynomial_slow_coefficients
    _ b ω hN _ _ T hT hA hH _ E hE α
  intro i
  simpa only [detectedTranslationLogFunctional_basis w d hw hwd M hM D b ω hN] using hproj i

theorem detectedTranslationLogCoordinate_joint_grid [Fintype ι]
    (m : ℕ)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m E) :
    (fun z : (U →₀ ℕ) × WeightedBasisIndex w d =>
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E z.2).coeff z.1)
        ∈ realDenominatorGrid (matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m) := by
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_joint_grid
    b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D) m E hE
  simpa only [detectedTranslationLogFunctional_basis w d hw hwd M hM D b ω hN,
    ← detectedTranslationLogCoordinate_eq_scalar w d hw hwd M hM D b ω hN] using h

theorem detectedTranslationLogCoordinate_common_coefficient_grid [Fintype ι]
    (m : ℕ)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m E) (k : WeightedBasisIndex w d) :
    realPolynomialCoefficientGrid
      (matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m)
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) := by
  obtain ⟨a, ha⟩ := detectedTranslationLogCoordinate_joint_grid w d hw hwd M hM D b ω hN m E hE
  refine ⟨fun α => a (α, k), ?_⟩
  funext α
  exact congrFun ha (α, k)

theorem exists_detectedTranslationLogCoordinate_common_grid [Fintype ι]
    {H : ℕ}
    (hproj : ∀ k i, RationalHeightLE (detectedTranslationLogProjectionMatrix w d hw b ω k i) H)
    (m : ℕ) (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧
      q ≤ H ^ (Fintype.card (WeightedBasisIndex w d) * Fintype.card ι) * m ∧
      ∀ E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1),
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
          b ω hN (fun _ : U => 1) m E →
        ∀ k, realPolynomialCoefficientGrid q
          (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) := by
  refine ⟨matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m,
    Nat.mul_pos (matrixDenominator_pos _) hm,
    Nat.mul_le_mul_right m (matrixDenominator_le _ hproj), ?_⟩
  intro E hE k
  exact detectedTranslationLogCoordinate_common_coefficient_grid w d hw hwd M hM D b ω hN m E hE k

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DetectedTranslationNormalizedLogBounds
namespace OAI

section

namespace Erdos3

theorem scaleMvPolynomialAxes_mass_le_of_totalDegree {U : Type*} [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) (P : MvPolynomial U ℝ)
    {d : ℕ} (hd : P.totalDegree ≤ d) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ α, |P.coeff α| ≤ A / monomialScale T α) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤
      ((Fintype.card U : ℝ) + 1) ^ d * A := by
  apply (scaleMvPolynomialAxes_mass_le T hT P hcoeff).trans
  apply mul_le_mul_of_nonneg_right _ hA
  exact_mod_cast mvPolynomial_support_card_le_totalDegree P hd

namespace PolynomialTranslationLie

open Module VectorPolynomial RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationLogCoordinate_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).totalDegree ≤ d :=
  (degreeLE_one_iff_basis_totalDegree ((weightedBasis w d hw).baseChange ℝ) d
    (detectedTranslationSymbolLift w d hw hwd M hM D E).log).mp
      (detectedTranslationSymbolLift w d hw hwd M hM D E).degreeLE k

theorem detectedTranslationLogCoordinate_normalized_mass [Fintype U] [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (k : WeightedBasisIndex w d)
    (hproj : ∀ i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) ≤
        ((Fintype.card U : ℝ) + 1) ^ d * ((Fintype.card ι : ℝ) * H * A) := by
  apply scaleMvPolynomialAxes_mass_le_of_totalDegree T hT _
    (detectedTranslationLogCoordinate_totalDegree w d hw hwd M hM D E k)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hH) hA)
  exact detectedTranslationLogCoordinate_slow_coefficients w d hw hwd M hM D b ω hN
    T hT hA hH k hproj E hE

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DetectedTranslationLogProjectionHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)

theorem detectedTranslationLogProjectionMatrix_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (k : WeightedBasisIndex w d) (i : ι) :
    rationalLogHeight (detectedTranslationLogProjectionMatrix w d hw b ω k i) ≤ p := by
  unfold detectedTranslationLogProjectionMatrix
  split_ifs
  · exact pairResidueTranslationProjection_coordinate_logHeight w d hw hwd M hM D
      (b i) (hb i) k
  · simpa [rationalLogHeight] using hp

theorem detectedTranslationLogProjectionMatrix_height_of_basis {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (k : WeightedBasisIndex w d) (i : ι) :
    RationalHeightLE (detectedTranslationLogProjectionMatrix w d hw b ω k i) ⌈Real.exp p⌉₊ :=
  rationalHeightLE_ceil_exp
    (detectedTranslationLogProjectionMatrix_logHeight w d hw hwd M hM D b ω hp hb k i)

variable (hN : ∀ j,
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_detectedTranslationLogCoordinate_grid_of_basis_height [Fintype ι]
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (m : ℕ) (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧
      q ≤ ⌈Real.exp p⌉₊ ^ (Fintype.card (WeightedBasisIndex w d) * Fintype.card ι) * m ∧
      ∀ E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1),
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
          b ω hN (fun _ : U => 1) m E →
        ∀ k, realPolynomialCoefficientGrid q
          (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) :=
  exists_detectedTranslationLogCoordinate_common_grid w d hw hwd M hM D b ω hN
    (detectedTranslationLogProjectionMatrix_height_of_basis w d hw hwd M hM D b ω hp hb) m hm

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DetectedTranslationPhaseDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {σ R : Type*} [CommRing R]

variable {U B : Type*} [Fintype B]

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)

theorem weightedBasis_base_abs_le_one (a : WeightedBasisIndex w d) (i : σ) :
    |((weightedBasis w d hw a).val.base i : ℝ)| ≤ 1 := by
  classical
  cases a with
  | inl j =>
    rw [weightedBasis_inl_base]
    by_cases h : i = j <;> simp [h]
  | inr a => simp

theorem weightedBasis_polynomial_mass_le_one (a : WeightedBasisIndex w d) :
    realPolynomialMass
      (MvPolynomial.map (Rat.castHom ℝ) (weightedBasis w d hw a).val.polynomial) ≤ 1 := by
  cases a with
  | inl i => simp [realPolynomialMass_zero]
  | inr a => simp [realPolynomialMass_monomial]

theorem weightedBasis_base_integer (a : WeightedBasisIndex w d) (i : σ) :
    ∃ z : ℤ, (z : ℚ) = (weightedBasis w d hw a).val.base i := by
  classical
  cases a with
  | inl j =>
    rw [weightedBasis_inl_base]
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | inr a => exact ⟨0, by simp⟩

theorem weightedBasis_polynomial_real_grid (a : WeightedBasisIndex w d) :
    realPolynomialCoefficientGrid 1
      (MvPolynomial.map (Rat.castHom ℝ) (weightedBasis w d hw a).val.polynomial) := by
  apply (realPolynomialCoefficientGrid_iff 1 _).mpr
  simp only [Nat.cast_one, map_one, one_mul]
  cases a with
  | inl i =>
    simp only [weightedBasis_inl_polynomial, map_zero]
    exact (integralRealPolynomialSubring σ).zero_mem
  | inr a =>
    simp only [weightedBasis_inr_polynomial, map_monomial, map_one]
    exact ⟨monomial a.val (1 : ℤ), by simp⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationGroupPolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    PolynomialTranslationGroupOver (MvPolynomial U ℝ) B :=
  nativeTranslationGroupPolynomial w d (weightedBasis w d hw)
    (detectedTranslationSymbolLift w d hw hwd M hM D E).log

noncomputable def detectedTranslationBaseCoordinatePolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (i : B) : MvPolynomial U ℝ :=
  (detectedTranslationGroupPolynomial w d hw hwd M hM D E).base i

noncomputable def detectedTranslationPhasePolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    MvPolynomial (U ⊕ B) ℝ :=
  packTranslationPolynomial
    (detectedTranslationGroupPolynomial w d hw hwd M hM D E).polynomial

theorem detectedTranslationPhasePolynomial_eq_logMixed
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationPhasePolynomial w d hw hwd M hM D E =
      translationLogMixedGroupPolynomial w d (weightedBasis w d hw)
        (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E) := rfl

theorem detectedTranslationGroupPolynomial_specialize
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u)
        (detectedTranslationGroupPolynomial w d hw hwd M hM D E) =
      detectedTranslationGroupEval w d hw hwd M hM D u E :=
  nativeTranslationGroupPolynomial_orbit w d hwd (weightedBasis w d hw)
    (fun _ : U => 1) (detectedTranslationSymbolLift w d hw hwd M hM D E) u

theorem detectedTranslationBaseCoordinatePolynomial_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) (i : B) :
    eval u (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i) =
      (detectedTranslationGroupEval w d hw hwd M hM D u E).base i :=
  congrArg (fun g => g.base i)
    (detectedTranslationGroupPolynomial_specialize w d hw hwd M hM D E u)

theorem detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (i : B) :
    detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i =
      nativeTranslationLogCoordinate w d (weightedBasis w d hw)
        (detectedTranslationSymbolLift w d hw hwd M hM D E).log (Sum.inl i) := by
  apply MvPolynomial.funext
  intro u
  rw [detectedTranslationBaseCoordinatePolynomial_eval]
  change (bchRealTranslationHom w d hwd
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval (fun _ : U => 1) u
      (detectedTranslationSymbolLift w d hw hwd M hM D E))).base i = _
  rw [bchRealTranslationHom_base_coordinate w d hw hwd]
  exact VectorPolynomial.coordinate_eval₂
    (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)) u _

theorem detectedTranslationPhasePolynomial_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) (a : B → ℝ) :
    eval (Sum.elim u a) (detectedTranslationPhasePolynomial w d hw hwd M hM D E) =
      eval a (detectedTranslationGroupEval w d hw hwd M hM D u E).polynomial := by
  rw [detectedTranslationPhasePolynomial, packTranslationPolynomial_eval]
  exact congrArg (fun g => eval a g.polynomial)
    (detectedTranslationGroupPolynomial_specialize w d hw hwd M hM D E u)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationPhasePolynomial_normalized_mass
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ k, realPolynomialMass (scaleMvPolynomialAxes H
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) ≤ A) :
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E)) ≤
      ((d : ℝ) + 1) * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * A) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * A)) ^ d := by
  have h := realPolynomialMass_translationLogMixedGroupPolynomial_scale w d hw hwd
    (weightedBasis w d hw) (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E) H hA (by norm_num : (0 : ℝ) ≤ 1)
    hf (weightedBasis_base_abs_le_one w d hw) (weightedBasis_polynomial_mass_le_one w d hw)
  rw [detectedTranslationPhasePolynomial_eq_logMixed]
  simpa only [mul_one] using h

theorem detectedTranslationPhasePolynomial_coefficientGrid
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    {q : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) :
    realPolynomialCoefficientGrid (d.factorial * q ^ (d + 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E) := by
  have hbase (k : WeightedBasisIndex w d) (i : B) :
      ∃ z : ℤ, (z : ℝ) = ((1 : ℕ) : ℝ) * ((weightedBasis w d hw k).val.base i : ℝ) := by
    obtain ⟨z, hz⟩ := weightedBasis_base_integer w d hw k i
    refine ⟨z, ?_⟩
    simp only [Nat.cast_one, one_mul]
    exact_mod_cast hz
  have h := translationLogMixedGroupPolynomial_coefficientGrid_of_inputs w d hwd
    (weightedBasis w d hw) (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E)
    hf hbase (weightedBasis_polynomial_real_grid w d hw)
  rw [detectedTranslationPhasePolynomial_eq_logMixed]
  simpa only [mul_one] using h

variable {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationPhasePolynomial_mass_of_slow [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hproj : ∀ k i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) :
    let Z := ((Fintype.card U : ℝ) + 1) ^ d * ((Fintype.card ι : ℝ) * H * A)
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim T (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E)) ≤
      ((d : ℝ) + 1) * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * Z) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * Z)) ^ d := by
  dsimp only
  apply detectedTranslationPhasePolynomial_normalized_mass w d hw hwd M hM D E T (by positivity)
  intro k
  exact detectedTranslationLogCoordinate_normalized_mass w d hw hwd M hM D b ω hN
    T hT hA hH k (hproj k) E hE

theorem detectedTranslationBaseCoordinatePolynomial_mass_of_slow [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hproj : ∀ k i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) (i : B) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)) ≤
      ((Fintype.card U : ℝ) + 1) ^ d * ((Fintype.card ι : ℝ) * H * A) := by
  rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
  exact detectedTranslationLogCoordinate_normalized_mass w d hw hwd M hM D b ω hN
    T hT hA hH (Sum.inl i) (hproj (Sum.inl i)) E hE

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationPhasePolynomial_isWeightedHomogeneous
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E).IsWeightedHomogeneous
      (Sum.elim (fun _ : U => 1) w) d := by
  rw [detectedTranslationPhasePolynomial_eq_logMixed,
    translationLogMixedGroupPolynomial_eq_series w d hwd]
  have hf := detectedTranslationLogCoordinate_homogeneous w d hw hwd M hM D E
  exact translationDirectionalSeries_isWeightedHomogeneous (fun _ : U => 1) w d _
    (translationLogBasePolynomial_weightedBasis_isWeightedHomogeneous (fun _ : U => 1) w d hw _ hf)
    (pack_translationLogPhasePolynomial_weightedBasis_isWeightedHomogeneous (fun _ : U => 1) w d hw _ hf)

theorem detectedTranslationPhasePolynomial_weightedSupportLE
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationPhasePolynomial w d hw hwd M hM D E ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
  intro α hα
  exact (detectedTranslationPhasePolynomial_isWeightedHomogeneous w d hw hwd M hM D E
    (mem_support_iff.mp hα)).le

theorem detectedTranslationPhasePolynomial_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E).totalDegree ≤ d := by
  have hP := detectedTranslationPhasePolynomial_weightedSupportLE w d hw hwd M hM D E
  rw [totalDegree_eq]
  apply Finset.sup_le
  intro α hα
  have hweight : α.sum (fun _ n => n) ≤ Finsupp.weight (Sum.elim (fun _ : U => 1) w) α := by
    change (∑ i ∈ α.support, α i) ≤ ∑ i ∈ α.support, α i • Sum.elim (fun _ : U => 1) w i
    apply Finset.sum_le_sum
    intro i _
    cases i with
    | inl i => simp
    | inr i => simpa only [Sum.elim_inr, smul_eq_mul] using Nat.le_mul_of_pos_right (α (Sum.inr i)) (hw i)
  rw [Finsupp.card_toMultiset]
  change (α.sum fun _ n => n) ≤ d
  exact hweight.trans (hP hα)

theorem detectedTranslationPhasePolynomial_scaled_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) :
    (scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E)).totalDegree ≤ d :=
  (scaleMvPolynomialAxes_totalDegree_le _ _).trans
    (detectedTranslationPhasePolynomial_totalDegree w d hw hwd M hM D E)

theorem detectedTranslationBaseCoordinatePolynomial_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) (i : B) :
    (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i).totalDegree ≤ w i := by
  rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
  have h := detectedTranslationLogCoordinate_homogeneous w d hw hwd M hM D E (Sum.inl i)
  rw [totalDegree_eq]
  apply Finset.sup_le
  intro α hα
  have hh := h (mem_support_iff.mp hα)
  rw [Finsupp.card_toMultiset]
  change (α.sum fun _ n => n) ≤ w i
  simpa only [Finsupp.weight_apply, smul_eq_mul, mul_one, weightedBasisGrade, Sum.elim_inl] using hh.le

theorem detectedTranslationBaseCoordinatePolynomial_scaled_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (i : B) :
    (scaleMvPolynomialAxes H
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)).totalDegree ≤ w i :=
  (scaleMvPolynomialAxes_totalDegree_le _ _).trans
    (detectedTranslationBaseCoordinatePolynomial_totalDegree w d hw hwd M hM D E i)

theorem detectedTranslationPhasePolynomial_scaled_weightedSupportLE
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) :
    scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E) ∈
        weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
  scaleMvPolynomialAxes_mem_weightedSupportLE _ _ _
    (detectedTranslationPhasePolynomial_weightedSupportLE w d hw hwd M hM D E)

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationUniformCoordinateBounds
namespace OAI

section

namespace Erdos3

noncomputable def detectedTranslationCoordinateConstant (d : ℕ) : ℕ :=
  (exists_detectedTranslationPhase_budget d).choose

namespace PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
variable {B L : Type} {U ι : Type*} [Fintype B] [Fintype U] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationGroupCoordinates_uniform_bounds
    {p : ℝ} (hp : 0 ≤ p)
    (hU : (Fintype.card U : ℝ) ≤ p) (hB : (Fintype.card B : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (T : U → ℝ) (hT : ∀ i, 0 < T i)
    (E Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T (Real.exp p) E)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m Q) :
    let C := detectedTranslationCoordinateConstant d
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      realPolynomialMass (scaleMvPolynomialAxes (Sum.elim T (fun _ : B => 1))
        (detectedTranslationPhasePolynomial w d hw hwd M hM D E)) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ i, realPolynomialMass (scaleMvPolynomialAxes T
        (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)) ≤ Real.exp ((p + C) ^ C)) ∧
      realPolynomialCoefficientGrid q (detectedTranslationPhasePolynomial w d hw hwd M hM D Q) ∧
      (∀ i, realPolynomialCoefficientGrid q
        (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i)) := by
  have hκ : (Fintype.card (WeightedBasisIndex w d) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (weightedBasisIndex_card_le_pair_basis w d hw b)).trans hι
  have hproj : ∀ k i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ Real.exp p := by
    intro k i
    exact (rational_abs_real_le_numerator _).trans
      ((rationalLogHeight_le_iff _ p).mp
        (detectedTranslationLogProjectionMatrix_logHeight w d hw hwd M hM D b ω hp hb k i)).1
  obtain ⟨q₀, hq₀, hq₀bound, hq₀grid⟩ :=
    exists_detectedTranslationLogCoordinate_grid_of_basis_height w d hw hwd M hM D b ω hN hp hb m hm
  have hbudget := (exists_detectedTranslationPhase_budget d).choose_spec.2
    (Fintype.card U) (Fintype.card (WeightedBasisIndex w d)) (Fintype.card ι)
    (Fintype.card B) m q₀ p (Real.exp p) (Real.exp p) hp hU hκ hι hB
    (Real.exp_pos p).le le_rfl (Real.exp_pos p).le le_rfl hmp hq₀bound
  obtain ⟨hbase, hphase, hden⟩ := hbudget
  refine ⟨d.factorial * q₀ ^ (d + 1), by positivity, hden, ?_, ?_, ?_, ?_⟩
  · have h := detectedTranslationPhasePolynomial_mass_of_slow w d hw hwd M hM D b ω hN T hT
      (Real.exp_pos p).le (Real.exp_pos p).le hproj E hE
    exact h.trans (by simpa only [mul_assoc, detectedTranslationCoordinateConstant] using hphase)
  · intro i
    have h := detectedTranslationBaseCoordinatePolynomial_mass_of_slow w d hw hwd M hM D b ω hN T hT
      (Real.exp_pos p).le (Real.exp_pos p).le hproj E hE i
    exact h.trans (by simpa only [mul_assoc, detectedTranslationCoordinateConstant] using hbase)
  · exact detectedTranslationPhasePolynomial_coefficientGrid w d hw hwd M hM D Q (hq₀grid Q hQ)
  · intro i
    apply realPolynomialCoefficientGrid_mono (show q₀ ∣ d.factorial * q₀ ^ (d + 1) from
      dvd_mul_of_dvd_right (dvd_pow_self q₀ (by omega : d + 1 ≠ 0)) _)
    rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
    exact hq₀grid Q hQ (Sum.inl i)

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationDecomposition
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem realPolynomialMass_weightedHomogeneousComponent_le
    {σ : Type*} (P : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ) :
    realPolynomialMass (weightedHomogeneousComponent w d P) ≤ realPolynomialMass P := by
  classical
  have hs : (weightedHomogeneousComponent w d P).support ⊆ P.support := by
    rw [support_weightedHomogeneousComponent]
    exact Finset.filter_subset _ _
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support hs]
  apply Finset.sum_le_sum
  intro α _
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg (P.coeff α)

theorem realPolynomialMass_specializeMajorParameters_zero_le
    {U B : Type*} (P : MvPolynomial (U ⊕ B) ℝ) :
    realPolynomialMass (specializeMajorParameters (RingHom.id ℝ) P 0) ≤ realPolynomialMass P := by
  have h := realPolynomialMass_substitution_le P
    (Sum.elim (fun _ : U => (0 : MvPolynomial B ℝ)) X)
    (M := 1) le_rfl (fun i => by
      cases i with
      | inl i => simpa only [Sum.elim_inl, realPolynomialMass_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      | inr i => exact (realPolynomialMass_X i).le) (d := P.totalDegree) le_rfl
  simpa only [specializeMajorParameters, RingHomCompTriple.comp_eq, RingHom.coe_comp,
    Function.comp_apply, RingHom.id_apply, Pi.zero_apply, map_zero, one_pow, mul_one] using h

theorem reducedMajorZeroSlice_mass_le
    {U B : Type*} [Fintype U] [Fintype B]
    (w : B → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    realPolynomialMass (specializeMajorParameters (RingHom.id ℝ)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (fractionalCoefficientPolynomial F)) 0) ≤
      ((Fintype.card U : ℝ) + (Fintype.card B : ℝ) + 1)^d := by
  apply (realPolynomialMass_specializeMajorParameters_zero_le _).trans
  apply (realPolynomialMass_weightedHomogeneousComponent_le _ _ _).trans
  have h := fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE F
    (Sum.elim (fun _ : U => 1) w) (fun i => by cases i <;> simp_all) d hF
  simpa only [Fintype.card_sum, Nat.cast_add] using h

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationNormalizedBase
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (i : B) : MvPolynomial U ℝ :=
  scaleMvPolynomialAxes H (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)

noncomputable def detectedTranslationNormalizedPhase
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E)

theorem detectedTranslationNormalizedBase_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (hH : ∀ i, H i ≠ 0) (u : U → ℝ) (i : B) :
    eval (fun j => u j / H j) (detectedTranslationNormalizedBase w d hw hwd M hM D E H i) =
      (detectedTranslationGroupEval w d hw hwd M hM D u E).base i := by
  rw [detectedTranslationNormalizedBase, scaleMvPolynomialAxes_eval]
  have hc : (fun j => H j * (u j / H j)) = u := by
    funext j
    exact mul_div_cancel₀ (u j) (hH j)
  rw [hc, detectedTranslationBaseCoordinatePolynomial_eval]

theorem detectedTranslationNormalizedPhase_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (hH : ∀ i, H i ≠ 0) (u : U → ℝ) (z : B → ℝ) :
    eval (Sum.elim (fun j => u j / H j) z)
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) =
      eval z (detectedTranslationGroupEval w d hw hwd M hM D u E).polynomial := by
  rw [detectedTranslationNormalizedPhase, scaleMvPolynomialAxes_eval]
  have hc : (fun j => Sum.elim H (fun _ : B => 1) j *
      Sum.elim (fun i => u i / H i) z j) = Sum.elim u z := by
    funext j
    cases j with
    | inl i => exact mul_div_cancel₀ (u i) (hH i)
    | inr i => exact one_mul _
  rw [hc, detectedTranslationPhasePolynomial_eval]

theorem detectedTranslationGroupEval_normalized_left
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (hH : ∀ i, H i ≠ 0) (u : U → ℝ) :
    normalizedMajorLeft
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H) H u =
      detectedTranslationGroupEval w d hw hwd M hM D u E := by
  apply PolynomialTranslationGroupOver.ext
  · funext i
    exact detectedTranslationNormalizedBase_eval w d hw hwd M hM D E H hH u i
  · apply MvPolynomial.funext
    intro z
    change eval z (specializeMajorParameters (RingHom.id ℝ) _ _) = _
    rw [specializeMajorParameters_eval, eval₂_id]
    exact detectedTranslationNormalizedPhase_eval w d hw hwd M hM D E H hH u z

theorem exists_detectedTranslation_rational_right
    (Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (q : ℕ) (hq : 0 < q)
    (hphase : realPolynomialCoefficientGrid q
      (detectedTranslationPhasePolynomial w d hw hwd M hM D Q))
    (hbase : ∀ i, realPolynomialCoefficientGrid q
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i)) :
    ∃ (Qrat : MvPolynomial (U ⊕ B) ℚ) (a : B → MvPolynomial U ℚ),
      map (algebraMap ℚ ℝ) Qrat = detectedTranslationPhasePolynomial w d hw hwd M hM D Q ∧
      (∀ i, map (algebraMap ℚ ℝ) (a i) =
        detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i) ∧
      (fun α => Qrat.coeff α) ∈ denominatorGrid q ∧
      (∀ i, (fun α => (a i).coeff α) ∈ denominatorGrid q) ∧
      Qrat.totalDegree = (detectedTranslationPhasePolynomial w d hw hwd M hM D Q).totalDegree ∧
      ∀ u, rationalMajorRight Qrat a u = detectedTranslationGroupEval w d hw hwd M hM D u Q := by
  obtain ⟨Qrat, hQrat, hQgrid, hQdegree⟩ :=
    exists_rationalPolynomial_of_realCoefficientGrid _ hq hphase
  choose a ha hagrid _hadegree using fun i =>
    exists_rationalPolynomial_of_realCoefficientGrid _ hq (hbase i)
  refine ⟨Qrat, a, hQrat, ha, hQgrid, hagrid, hQdegree, ?_⟩
  intro u
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change eval₂ (algebraMap ℚ ℝ) u (a i) = _
    rw [← eval_map, ha i]
    exact detectedTranslationBaseCoordinatePolynomial_eval w d hw hwd M hM D Q u i
  · apply MvPolynomial.funext
    intro z
    change eval z (specializeMajorParameters (algebraMap ℚ ℝ) Qrat u) = _
    rw [specializeMajorParameters_eval, ← eval_map, hQrat]
    exact detectedTranslationPhasePolynomial_eval w d hw hwd M hM D Q u z

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_detectedTranslation_normalized_weighted_decomposition
    (hd : 0 < d)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : U => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W))
    (V : MvPolynomial B ℚ) (H : U → ℝ) (hH : ∀ i, H i ≠ 0)
    (q : ℕ) (hq : 0 < q) (Cbase : ℝ) (hCbase : 0 ≤ Cbase)
    (hphaseGrid : realPolynomialCoefficientGrid q
      (detectedTranslationPhasePolynomial w d hw hwd M hM D Q))
    (hbaseGrid : ∀ i, realPolynomialCoefficientGrid q
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i))
    (hVgrid : (fun α => V.coeff α) ∈ denominatorGrid q)
    (hVweight : V ∈ weightedSupportLE w d)
    (heMass : ∀ i, realPolynomialMass
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H i) ≤ Cbase) :
    let fast := W.map (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))
    let K := (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
    let Ftop := weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F
    let F₀ := specializeMajorParameters (RingHom.id ℝ) Ftop 0
    (∀ x ∈ fast, ∀ z ∈ fast.toSubmodule.map
      (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) →
    (∀ u, (detectedTranslationGroupEval w d hw hwd M hM D u Q).base ∈ K) →
    ∃ (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ),
      (∀ u z, z ∈ K → eval (Sum.elim u z) Ftop =
        eval (Sum.elim (fun i => u i / H i)
          (fun j => z j - eval u (majorTranslationTopCoordinates w A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) R) ∧
      realPolynomialMass S ≤ realPolynomialMass F₀ +
        (realPolynomialMass (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) +
          realPolynomialMass (map (algebraMap ℚ ℝ) V)) * (1 + Cbase)^d ∧
      (fun α => R.coeff α) ∈ denominatorGrid (q^(d+1)) ∧
      S ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      R ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      S.totalDegree ≤ d ∧ R.totalDegree ≤ d := by
  intro fast K Ftop F₀ hderiv hright
  obtain ⟨Qrat, a, hQmap, hamap, hQgrid, hagrid, _hQratDegree, hQeval⟩ :=
    exists_detectedTranslation_rational_right w d hw hwd M hM D Q q hq hphaseGrid hbaseGrid
  have hfactor (u : U → ℝ) : algebraicMajorSymbol Ftop F₀
      (majorTranslationTopCoordinates w A) u =
        normalizedMajorLeft (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
          (detectedTranslationNormalizedBase w d hw hwd M hM D E H) H u *
        detectedTranslationGroupEval w d hw hwd M hM D u P * rationalMajorRight Qrat a u := by
    rw [detectedTranslationGroupEval_normalized_left w d hw hwd M hM D E H hH,
      hQeval]
    exact detectedTranslationGroupEval_major_factorization w d hw hwd M hM D b ω hN
      F hF A hA partner E P Q hprod u
  have hpotential := detectedTranslationGroupEval_fast_potential w d hw hwd M hM D b ω hN
    hd W P hP V hderiv
  have haright (u : U → ℝ) : (fun j => eval₂ (algebraMap ℚ ℝ) u (a j)) ∈ K := by
    have heq := congrArg PolynomialTranslationGroupOver.base (hQeval u)
    change (fun i => eval₂ (algebraMap ℚ ℝ) u (a i)) = _ at heq
    rw [heq]
    exact hright u
  have hFtopweight : Ftop ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
    intro α hα
    exact ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (mem_support_iff.mp hα)).le
  have hF₀weight : F₀ ∈ weightedSupportLE w d :=
    specializeMajorParameters_zero_weightedSupportLE w hFtopweight
  have hEweight : detectedTranslationNormalizedPhase w d hw hwd M hM D E H ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
    detectedTranslationPhasePolynomial_scaled_weightedSupportLE w d hw hwd M hM D E H
  have heweight (i : B) : detectedTranslationNormalizedBase w d hw hwd M hM D E H i ∈
      weightedSupportLE (fun _ : U => 1) (w i) :=
    (mem_weightedSupportLE_one_iff _ _).mpr
      (detectedTranslationBaseCoordinatePolynomial_scaled_totalDegree w d hw hwd M hM D E H i)
  have hQweight : Qrat ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
    apply weightedSupportLE_of_map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [hQmap]
    exact detectedTranslationPhasePolynomial_weightedSupportLE w d hw hwd M hM D Q
  have haweight (i : B) : a i ∈ weightedSupportLE (fun _ : U => 1) (w i) := by
    apply weightedSupportLE_of_map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [hamap i]
    exact (mem_weightedSupportLE_one_iff _ _).mpr
      (detectedTranslationBaseCoordinatePolynomial_totalDegree w d hw hwd M hM D Q i)
  have hVrealweight : map (algebraMap ℚ ℝ) V ∈ weightedSupportLE w d := by
    intro α hα
    exact hVweight (support_map_subset (algebraMap ℚ ℝ) V hα)
  have hVdegree : V.totalDegree ≤ d := weightedSupportLE_totalDegree_le_of_pos hw hVweight
  have hVrealDegree : (map (algebraMap ℚ ℝ) V).totalDegree ≤ d :=
    weightedSupportLE_totalDegree_le_of_pos hw hVrealweight
  have hEdegree : (detectedTranslationNormalizedPhase w d hw hwd M hM D E H).totalDegree ≤ d :=
    detectedTranslationPhasePolynomial_scaled_totalDegree w d hw hwd M hM D E H
  have hSweight := majorSlowPolynomial_weightedSupportLE (fun _ : U => 1) w F₀
    (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
    (map (algebraMap ℚ ℝ) V)
    (detectedTranslationNormalizedBase w d hw hwd M hM D E H)
    hF₀weight hEweight hVrealweight heweight
  have hRweight := majorRationalPolynomial_weightedSupportLE (fun _ : U => 1) w
    Qrat V a hQweight hVweight haweight
  have hpos (i : U ⊕ B) : 0 < Sum.elim (fun _ : U => 1) w i := by
    cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  refine ⟨majorSlowPolynomial F₀
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (map (algebraMap ℚ ℝ) V)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H),
    majorRationalPolynomial Qrat V a, ?_, ?_, ?_, hSweight, hRweight,
    weightedSupportLE_totalDegree_le_of_pos hpos hSweight,
    weightedSupportLE_totalDegree_le_of_pos hpos hRweight⟩
  · exact algebraic_major_normalized_identity_on_subspace K Ftop F₀
      (majorTranslationTopCoordinates w A)
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H) Qrat a V H
      (fun u => detectedTranslationGroupEval w d hw hwd M hM D u P)
      hfactor hpotential haright
  · exact algebraic_major_normalized_slow_mass F₀
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) V
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H)
      hCbase heMass hEdegree hVrealDegree
  · exact majorRationalPolynomial_denominatorGrid Qrat V a q d hVdegree hQgrid hVgrid hagrid

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_decomposition
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (_htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (_hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (_hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      ∀ (retained : Fin d → Submodule ℝ (Fin m → ℝ)),
      (∀ h, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p + C)^C)) (retained h)
        (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i)))) →
      (∀ α, coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i))) α ∈
        ⨆ h, retained h) →
      ∃ (fast : LieSubalgebra ℚ (weightedSubalgebra w d))
        (g : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → weightedSubalgebra w d)
        (Slow : MvPolynomial (U ⊕ Fin m) ℝ)
        (RatPart : MvPolynomial (U ⊕ Fin m) ℚ) (qOut : ℕ),
        (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L) : ℝ) ≤ (p+C)^C ∧
        Submodule.span ℚ (Set.range g) = fast.toSubmodule ∧
        BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) fast.toSubmodule ∧
        (∀ j i, rationalLogHeight ((weightedBasis w d hw).repr (g j) i) ≤ (p+C)^C) ∧
        BasisGradedSubmodule (Pi.basisFun ℝ (Fin m)) w
          ((fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        (∀ h, retained h ≤ (fast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        realPolynomialMass Slow ≤ Real.exp ((p+C)^C) ∧
        (∀ α, |Slow.coeff α| ≤ Real.exp ((p+C)^C)) ∧
        0 < qOut ∧ (qOut : ℝ) ≤ Real.exp ((p+C)^C) ∧
        (fun α => RatPart.coeff α) ∈ denominatorGrid qOut ∧
        (∀ α, (RatPart.coeff α).den ≤ qOut) ∧
        Slow ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
        RatPart ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
        ∀ (u : U → ℝ) (z : Fin m → ℝ),
          z ∈ (fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
          eval (Sum.elim u z) (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F) =
            eval (Sum.elim (fun i => u i / (lengths i : ℝ))
              (fun j => z j - eval u (majorTranslationTopCoordinates w A j))) Slow +
              eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) RatPart := by
  obtain ⟨a, ha, hdata⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_separated_data d hd
  let c := detectedTranslationCoordinateConstant d
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorDecomposition_budget d a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    retained hrank hAret
  let p₁ : ℝ := (p+a)^a
  let B : ℝ := p₁ + (p₁+c)^c + (2*p+2)^d + 1
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  obtain ⟨hb₁, hb₂, hbmass, hbden⟩ := hbudget p hp
  have hTpos (i : U) : 0 < (lengths i : ℝ) := by exact_mod_cast hlengths i
  have hlarge₁ (i : U) : Real.exp ((p+a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hb₁).trans (hlarge i)
  have hrank₁ h := (hrank h).mono (Real.exp_le_exp.mpr hb₁) hTpos
  obtain ⟨b, ω, hLayers, hb, l, E, P, Q, W, v, fast, V, qV,
      hl, hlp, hprod, hE, hQ, hfast, hfastdef, hv, hW, hh, hP, hV,
      hderiv, hqV, hqVp, hVgrid, hVmass, hVcoeff, hret, hgroup⟩ :=
    hdata w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr retained hrank₁ hAret
  let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
  let partner := D.raiseStepRealOrbit htd.le R.orbit
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase₀ : (Fintype.card (Fin m) : ℝ) ≤ p :=
    weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry
  have hbase := hbase₀.trans hpp₁
  obtain ⟨qNat, hqNat, hqNatp, hEmass, hebase, hphaseGrid, hbaseGrid⟩ :=
    detectedTranslationGroupCoordinates_uniform_bounds w d hw hwd M hM (D.raiseStep htd.le)
      b ω hLayers hp₁ (hU.trans hpp₁) hbase hdim hb (fun i => (lengths i : ℝ)) hTpos E Q hE l hl hlp hQ
  have hcpow : 0 ≤ (p₁+c)^c := by positivity
  have hdpow : 0 ≤ (2*p+2)^d := by positivity
  have hpB : p₁ ≤ B := by dsimp only [B]; linarith only [hcpow, hdpow]
  have hcB : (p₁+c)^c ≤ B := by dsimp only [B]; linarith only [hp₁, hdpow]
  have hB : 0 ≤ B := hp₁.trans hpB
  let F₀ := specializeMajorParameters (RingHom.id ℝ)
    (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d (fractionalCoefficientPolynomial F)) 0
  have hF₀mass : realPolynomialMass F₀ ≤ Real.exp B := by
    apply (reducedMajorZeroSlice_mass_le w hw d F hF).trans
    apply (pow_le_pow_left₀ (by positivity)
      (show (Fintype.card U : ℝ) + (Fintype.card (Fin m) : ℝ) + 1 ≤ 2*p+2 by linarith) d).trans
    have hb : (2*p+2)^d ≤ B := by dsimp only [B]; linarith only [hp₁, hcpow]
    exact hb.trans (by linarith only [Real.add_one_le_exp B])
  have hVm : realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp B :=
    hVmass.trans (Real.exp_le_exp.mpr hpB)
  have hEm : realPolynomialMass
      (detectedTranslationNormalizedPhase w d hw hwd M hM (D.raiseStep htd.le) E (fun i => (lengths i : ℝ))) ≤ Real.exp B :=
    hEmass.trans (Real.exp_le_exp.mpr hcB)
  have heb (i : Fin m) : realPolynomialMass
      (detectedTranslationNormalizedBase w d hw hwd M hM (D.raiseStep htd.le) E (fun i => (lengths i : ℝ)) i) ≤ Real.exp B :=
    (hebase i).trans (Real.exp_le_exp.mpr hcB)
  have hqVm : (qV : ℝ) ≤ Real.exp B := hqVp.trans (Real.exp_le_exp.mpr hpB)
  have hqNm : (qNat : ℝ) ≤ Real.exp B := hqNatp.trans (Real.exp_le_exp.mpr hcB)
  have hphaseGrid' := realPolynomialCoefficientGrid_mono (dvd_mul_left qNat qV) hphaseGrid
  have hbaseGrid' i := realPolynomialCoefficientGrid_mono (dvd_mul_left qNat qV) (hbaseGrid i)
  have hVgrid' := denominatorGrid_subset_of_dvd (dvd_mul_right qV qNat) hVgrid
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
  let hφ := pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le)
  let g := detectedTranslationProjectedGenerators N.filtration w d hw hwd φ hφ v
  have hgspan : Submodule.span ℚ (Set.range g) = fast.toSubmodule := by
    rw [hfastdef]
    exact detectedTranslationProjectedGenerators_span N.filtration w d hw hwd φ hφ W v hv
  have hgdata := residuePairProjectedGenerators_data w d hw hwd M hM (D.raiseStep htd.le)
    b ω hLayers W v hv hp₁ hdim hb hh
  have hgheight : ∀ j i, rationalLogHeight ((weightedBasis w d hw).repr (g j) i) ≤ (p+C)^C :=
    fun j i => (hgdata.2.2.1 j i).trans hb₂
  have hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) fast.toSubmodule := by
    rw [hfastdef]
    exact weightedTranslationGradedProjection_image_graded N.filtration w d hw hwd φ hφ b ω hLayers W hW
  have hVweight : V ∈ weightedSupportLE w d :=
    fun _ hα => (hV (mem_support_iff.mp hα)).le
  have hnormal := exists_detectedTranslation_normalized_weighted_decomposition w d hw hwd M hM
    (D.raiseStep htd.le) b ω hLayers hd (fractionalCoefficientPolynomial F)
    (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
    A hA partner E P Q hprod W hP V (fun i => (lengths i : ℝ)) (fun i => (hTpos i).ne')
    (qV*qNat) (Nat.mul_pos hqV hqNat) (Real.exp B) (Real.exp_pos B).le
    hphaseGrid' hbaseGrid' hVgrid' hVweight heb
  dsimp only at hnormal
  rw [← hfastdef] at hnormal
  obtain ⟨Slow, RatPart, hidentity, hSlowMass, hRatGrid, hSlowW, hRatW, _, _⟩ :=
    hnormal hderiv (fun u => (hgroup u).2)
  let qOut := (qV*qNat)^(d+1)
  have hqOut : 0 < qOut := pow_pos (Nat.mul_pos hqV hqNat) _
  have hdsq : (d : ℝ) ≤ ((d+1 : ℕ) : ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg (d : ℝ), Nat.cast_nonneg (α := ℝ) d]
  have hmassBudget : ((d : ℝ)+3)*(B+2) ≤ (p+C)^C :=
    (mul_le_mul_of_nonneg_right (by linarith : (d : ℝ)+3 ≤ ((d+1 : ℕ) : ℝ)^2+3)
      (by positivity : 0 ≤ B+2)).trans hbmass
  have hdenBudget : 2*((d : ℝ)+1)*B ≤ (p+C)^C :=
    (mul_le_mul_of_nonneg_right (by linarith : 2*((d : ℝ)+1) ≤ 2*(((d+1 : ℕ) : ℝ)^2+1)) hB).trans hbden
  have hSlowFinal : realPolynomialMass Slow ≤ Real.exp ((p+C)^C) := by
    apply hSlowMass.trans
    apply (algebraicMajor_mass_le_exp d hB (realPolynomialMass_nonneg _)
      (realPolynomialMass_nonneg _) (realPolynomialMass_nonneg _) (Real.exp_pos B).le
      hF₀mass hEm hVm le_rfl).trans
    exact Real.exp_le_exp.mpr hmassBudget
  have hqFinal : (qOut : ℝ) ≤ Real.exp ((p+C)^C) :=
    (algebraicMajor_denominator_le_exp d qV qNat hqVm hqNm).trans (Real.exp_le_exp.mpr hdenBudget)
  obtain ⟨hrestGrid, hrestW, hrestIdentity⟩ := algebraic_major_restore_integer_coefficients
    F (Sum.elim (fun _ : U => 1) w) d
    ((fast.toSubmodule.baseChange ℝ).map (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)))
    (majorTranslationTopCoordinates w A) (fun i => (lengths i : ℝ)) Slow RatPart qOut hRatGrid hRatW hidentity
  refine ⟨fast, g, Slow, restoredMajorRemainder F (Sum.elim (fun _ : U => 1) w) d RatPart,
    qOut, ?_, hgspan, hgraded, hgheight,
    weightedTranslationBase_real_image_graded w d hw fast.toSubmodule hgraded g hgspan,
    hret, hSlowFinal, ?_, hqOut, hqFinal,
    hrestGrid, (fun α => den_le_of_mem_denominatorGrid hqOut hrestGrid α), hSlowW, hrestW, hrestIdentity⟩
  · simpa only [Fintype.card_fin] using hdim.trans hb₁
  · intro α
    exact (realPolynomialMass_coeff_le Slow α).trans hSlowFinal

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseDetectedDecomposition
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem majorPhase_residue_lowTagged_rank {m : ℕ} {X : Type*}
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (N lengths : X → ℕ) (hN : ∀ i, 0 < (N i : ℝ))
    (hlengths : ∀ i, 0 < lengths i) (q : ℕ) (hq : 0 < q) (start : X → ℤ)
    (p E D B Rrank : ℝ) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hqbound : (q : ℝ) ≤ Real.exp p)
    (hcomparison : ∀ i, (N i : ℝ) ≤ Real.exp E * q * lengths i)
    (hrow : D ≤ B) (hden : (m : ℝ) * p + D ≤ B)
    (hslow : (m : ℝ) * E + D ≤ B) (hRrank : Real.exp B ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    ∀ h : Fin d, HasLayerSamplingRank (h.val + 1)
      (fun i => (lengths i : ℝ)) (Real.exp D) (lowTaggedRetained J d U h)
      (lowTaggedTopPolynomial J d (fun j => residueAffine q start (poly j))) := by
  have hsliced (j : Fin m) : HasLayerSamplingRank (j.val + 1)
      (fun i => (lengths i : ℝ)) (Real.exp D) (U j)
      (residueAffine q start (poly j)) := by
    apply (hrank j).residueAffine (hpoly j) hN
      (fun i => Nat.cast_pos.mpr (hlengths i)) q hq start (Real.exp E) hcomparison
    · exact (Real.exp_le_exp.mpr hrow).trans hRrank
    · exact (pow_mul_exp_le_exp_of_le_budget (Nat.cast_nonneg q) hqbound hp
        (Nat.succ_le_of_lt j.isLt) hden).trans hRrank
    · exact (pow_mul_exp_le_exp_of_le_budget (Real.exp_nonneg E) le_rfl hE
        (Nat.succ_le_of_lt j.isLt) hslow).trans hRrank
  exact lowTaggedTopPolynomial_hasLayerSamplingRank J d _ U _ _ hsliced

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

variable {m : ℕ} {X L : Type} [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
  (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
  (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
  (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
  {D : RationalFilteredNilmanifold L t e} (R : D.Niltest (fun _ : X => 1))
  (start : X → ℤ) (q M : ℕ) (hM : 0 < M) (a : (Σ j, J j) → ℤ)
  (hhigh : ∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0)

include hM hhigh in

theorem majorPhase_affine_integrand (v : X → ℤ) :
    let u := fun i => start i + (q : ℤ) * v i
    let A := fun i => residueAffinePolynomial q start
      (lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))
    let y := fun i => MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β u i : ℝ)
    (Real.fourierChar (MvPolynomial.eval
      (fun i => (start i : ℝ) + (q : ℝ) * v i)
      (normalizedTwistFrequencyPolynomial M a poly)) : ℂ) *
      majorPhaseSample J d poly Ψ c F β R.eval u =
    rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c y
        (fun i => (β u i : ZMod M)) * (Ψ.value y : ℂ) *
      (Real.fourierChar (MvPolynomial.eval
        (Sum.elim (fun i => (v i : ℝ)) (fun i => (β u i : ℝ)))
        (jointResidueAffinePolynomial q start F)) : ℂ) *
      (R.scalarAffinePullback (q : ℚ) (fun i => (start i : ℚ))).eval v := by
  have htrunc : truncateTaggedFrequency d a = a := by
    funext i
    rcases i with ⟨j, i⟩
    by_cases hj : j.val + 1 ≤ d
    · simp only [truncateTaggedFrequency, hj, ite_true]
    · simp only [truncateTaggedFrequency, hj, ite_false,
        hhigh j (Nat.lt_of_not_ge hj) i]
  let u : X → ℤ := fun i => start i + (q : ℤ) * v i
  have hfreq := normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist_affine
    J M d hM a poly start q v c (β u)
  rw [htrunc] at hfreq
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hfreq
  have hR : (R.scalarAffinePullback (q : ℚ) (fun i => (start i : ℚ))).eval v = R.eval u := by
    simpa only [Int.cast_natCast, add_comm] using
      R.scalarAffinePullback_eval_integer (q : ℤ) start v
  have hjoint : MvPolynomial.eval
      (Sum.elim (fun i => (v i : ℝ)) (fun i => (β u i : ℝ)))
      (jointResidueAffinePolynomial q start F) =
      MvPolynomial.eval (fun j => ((Sum.elim u (β u) j : ℤ) : ℝ)) F := by
    rw [jointResidueAffinePolynomial_eval]
    apply congrArg (fun x => MvPolynomial.eval x F)
    funext j
    cases j <;> simp only [Sum.elim_inl, Sum.elim_inr, u,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
  dsimp only
  simp only [residueAffinePolynomial_eval_real, map_sub, eval_C]
  rw [hfreq, hR, hjoint]
  simp only [majorPhaseSample, u, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

theorem exists_majorPhase_residue_detection (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      [Fintype (WeightedBasisIndex (lowTaggedWeight J d) d)]
      (D : RationalFilteredNilmanifold L t e) (_htd : t < d)
      (R : D.Niltest (fun _ : X => 1))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (W : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
      (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (_hF : F ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
      (start : X → ℤ) (q : ℕ) (_hq : 0 < q) (M : ℕ) (_hM : 0 < M)
      (a : (Σ j, J j) → ℤ)
      (_hhigh : ∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0)
      (lengths : X → ℕ) (_hlengths : ∀ i, 0 < lengths i)
      (p : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (M : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      (∀ i, Real.exp ((p+C)^C) ≤ (lengths i : ℝ)) →
      (∀ v ∈ integerBox lengths, ∀ i,
        |MvPolynomial.eval (fun x => (start x : ℝ) + (q : ℝ) * v x)
          (lowTaggedPolynomial J d poly i) - c i -
          (β (fun x => start x + (q : ℤ) * v x) i : ℝ)| ≤ 1/2) →
      Real.exp (-p) ≤ ‖𝔼 v ∈ integerBox lengths,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * v i)
          (normalizedTwistFrequencyPolynomial M a poly)) : ℂ) *
          majorPhaseSample J d poly Ψ c F β R.eval
            (fun i => start i + (q : ℤ) * v i)‖ →
      (∀ h : Fin d, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p+C)^C)) (lowTaggedRetained J d W h)
        (lowTaggedTopPolynomial J d (fun j => residueAffine q start (poly j)))) →
      ∃ (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d))
        (g : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra (lowTaggedWeight J d) d) L)) →
          weightedSubalgebra (lowTaggedWeight J d) d)
        (Slow : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
        (RatPart : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ)
        (qOut : ℕ),
        (finrank ℚ (PairAlgebra (weightedSubalgebra (lowTaggedWeight J d) d) L) : ℝ) ≤ (p+C)^C ∧
        Submodule.span ℚ (Set.range g) = fast.toSubmodule ∧
        BasisGradedSubmodule (weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d))
          (weightedBasisGrade (lowTaggedWeight J d) d) fast.toSubmodule ∧
        (∀ j i, rationalLogHeight
          ((weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d)).repr (g j) i) ≤ (p+C)^C) ∧
        BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d)
          ((fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))) ∧
        (∀ h, lowTaggedRetained J d W h ≤ (fast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))) ∧
        realPolynomialMass Slow ≤ Real.exp ((p+C)^C) ∧
        (∀ α, |Slow.coeff α| ≤ Real.exp ((p+C)^C)) ∧
        0 < qOut ∧ (qOut : ℝ) ≤ Real.exp ((p+C)^C) ∧
        (fun α => RatPart.coeff α) ∈ denominatorGrid qOut ∧
        (∀ α, (RatPart.coeff α).den ≤ qOut) ∧
        Slow ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d ∧
        RatPart ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d ∧
        ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
          z ∈ (fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype)) →
          MvPolynomial.eval (Sum.elim u z)
            (weightedHomogeneousComponent (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d
              (jointResidueAffinePolynomial q start F)) =
            MvPolynomial.eval (Sum.elim (fun i => u i / (lengths i : ℝ))
              (fun j => z j - MvPolynomial.eval u
                (majorTranslationTopCoordinates (lowTaggedWeight J d)
                  (fun i => residueAffinePolynomial q start
                    (lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))) j))) Slow +
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) RatPart := by
  obtain ⟨aC, _, hprimitive⟩ := exists_majorRationalLift_detection_budget d
  obtain ⟨bC, _, hdetect⟩ :=
    exists_reduced_majorPolynomial_degree_twisted_correlation_decomposition d hd
  obtain ⟨C, hC, hbudget⟩ := exists_majorPhaseLowFourierExtraction_budget aC bC
  refine ⟨C, hC, ?_⟩
  intro m X L _ _ _ _ t e _ _ _ _ J _ _ D htd R poly hpoly W hcoeff Ψ c F hF β
    start q hq M hM a hhigh lengths hlengths p hp hR hcap hdim hMexp hΨ ha hlarge hβ hcorr hrank
  let w := lowTaggedWeight J d
  let hw := lowTaggedWeight_pos J d
  let hwd := lowTaggedWeight_le J d
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    realification_moduleTopology_t2 (weightedBasis w d hw)
  let A := fun i => residueAffinePolynomial q start
    (lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))
  let F' := jointResidueAffinePolynomial q start F
  let R' := R.scalarAffinePullback (q : ℚ) (fun i => (start i : ℚ))
  let β' := fun (v : X → ℤ) i => β (fun x => start x + (q : ℤ) * v x) i
  let T := rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c
  let K := rationalLiftCharacterTwistLip M (lowTaggedFrequency J d a)
  let p' : ℝ := (p+aC)^aC+p+1
  have hpow : 0 ≤ (p+aC)^aC := by positivity
  have hpp' : p ≤ p' := by dsimp only [p']; linarith
  have hp' : 0 ≤ p' := hp.trans hpp'
  have hprimitive' : (p+aC)^aC ≤ p' := by dsimp only [p']; linarith
  have hfinal : (p'+bC)^bC ≤ (p+C)^C := (hbudget p hp).2.1
  have hdim' : ((Fintype.card X + Fintype.card (LowTaggedIndex J d) : ℕ) : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.add_le_add_left (lowTaggedIndex_card_le J d) _
  obtain ⟨hgeometry, hlog⟩ := hprimitive (U := X) w hw hwd M hM Ψ
    (lowTaggedFrequency J d a) p hp hdim' hMexp hΨ (lowTaggedFrequency_bound J d a _ ha)
  have hA : ∀ i, (A i).totalDegree ≤ w i := fun i =>
    residueAffinePolynomial_totalDegree_le q start _ _
      ((MvPolynomial.totalDegree_sub_C_le _ _).trans (lowTaggedPolynomial_degree J d poly hpoly i))
  have hF' : F' ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) w) d :=
    jointResidueAffinePolynomial_degree w q start hF
  have hzero : translatedIntegerBox (0 : X → ℤ) lengths = integerBox lengths := by
    ext v
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hβ' : ∀ v ∈ translatedIntegerBox (0 : X → ℤ) lengths, ∀ i,
      |MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β' v i : ℝ)| ≤ 1/2 := by
    rw [hzero]
    intro v hv i
    simpa only [A, β', residueAffinePolynomial_eval_real, map_sub, eval_C] using hβ v hv i
  have hcorr' : Real.exp (-p') ≤ ‖𝔼 v ∈ translatedIntegerBox (0 : X → ℤ) lengths,
      T (fun i => MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β' v i : ℝ))
          (fun i => (β' v i : ZMod M)) *
        (Ψ.value (fun i => MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β' v i : ℝ)) : ℂ) *
        (Real.fourierChar (MvPolynomial.eval (fun j => ((Sum.elim v (β' v) j : ℤ) : ℝ)) F') : ℂ) *
        R'.eval v‖ := by
    rw [hzero]
    apply (Real.exp_le_exp.mpr (neg_le_neg hpp')).trans
    refine le_of_le_of_eq hcorr (Eq.symm ?_)
    refine congrArg (fun z => ‖z‖) ?_
    apply Finset.expect_congr rfl
    intro v _
    have hcast : (fun j => ((Sum.elim v (β' v) j : ℤ) : ℝ)) =
        Sum.elim (fun i => (v i : ℝ)) (fun i => (β' v i : ℝ)) := by
      funext j
      cases j <;> rfl
    rw [hcast]
    simpa only [T, A, β', F', R', Function.comp_def] using
      (majorPhase_affine_integrand J d poly Ψ c F β R start q M hM a hhigh v).symm
  have htop : ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
      (fun i => weightedHomogeneousComponent (fun _ : X => 1) (w i) (A i)) =
      lowTaggedTopPolynomial J d (fun j => residueAffine q start (poly j)) := by
    exact lowTaggedTopPolynomial_centered_residueAffine J d poly q start c
  have hTpos (i : X) : 0 < (lengths i : ℝ) := by exact_mod_cast hlengths i
  have hrank' (h : Fin d) : HasLayerSamplingRank (h.val+1) (fun i => (lengths i : ℝ))
      (Real.exp ((p'+bC)^bC)) (lowTaggedRetained J d W h)
      (ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
        (fun i => weightedHomogeneousComponent (fun _ : X => 1) (w i) (A i))) := by
    rw [htop]
    exact (hrank h).mono (Real.exp_le_exp.mpr hfinal) hTpos
  have hcoeff' α : coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
      (fun i => weightedHomogeneousComponent (fun _ : X => 1) (w i) (A i))) α ∈
      ⨆ h, lowTaggedRetained J d W h := by
    rw [htop]
    exact lowTaggedTopPolynomial_residueAffine_coeff_mem_iSup J d poly W hcoeff q start α
  have hX : (Fintype.card X : ℝ) ≤ p' := by
    apply le_trans _ (hdim'.trans hpp')
    exact_mod_cast Nat.le_add_right (Fintype.card X) (Fintype.card (LowTaggedIndex J d))
  obtain ⟨fast, g, Slow, RatPart, qOut, hdimOut, hg, hgraded, hheight, hbasegraded,
      hret, hmass, hslow, hqOut, hqbound, hgrid, hden, hSlowW, hRatW, hidentity⟩ :=
    hdetect w hw hwd M hM D htd Ψ F' hF' A hA K T
      (fun x r => (rationalLiftCharacterTwist_norm M (lowTaggedFrequency J d a) c x r).le)
      (rationalLiftCharacterTwist_lipschitz M (lowTaggedFrequency J d a) c)
      R' p' hp' (GeometryComplexityLE.mono _ hgeometry hprimitive') (hlog.trans hprimitive')
      (hR.mono hpp') hcap 0 lengths hlengths hX
      (fun i => (Real.exp_le_exp.mpr hfinal).trans (hlarge i)) β' hβ' hcorr'
      (lowTaggedRetained J d W) hrank' hcoeff'
  exact ⟨fast, g, Slow, RatPart, qOut, hdimOut.trans hfinal, hg, hgraded,
    (fun j i => (hheight j i).trans hfinal), hbasegraded, hret,
    hmass.trans (Real.exp_le_exp.mpr hfinal),
    (fun α => (hslow α).trans (Real.exp_le_exp.mpr hfinal)), hqOut,
    hqbound.trans (Real.exp_le_exp.mpr hfinal), hgrid, hden, hSlowW, hRatW, hidentity⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

theorem exists_majorPhase_detected_decomposition (m d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold L t e) (_htd : t < d)
      (R : D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
      (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (_hF : F ∈ weightedSupportLE
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J d poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        W.eval N poly u * majorPhaseSample J d poly Ψ c F β R.eval u‖ →
      MajorPhaseDetectedConclusion (L := L) J d U poly c F N ((p + C) ^ C) := by
  obtain ⟨aC, _, hextract⟩ := exists_majorPhase_low_localized_correlating_frequency m d
  obtain ⟨bC, _, hdetect⟩ := exists_majorPhase_residue_detection d hd
  obtain ⟨C, hC, hbudget⟩ := exists_majorPhaseDetectedDecomposition_budget aC bC 1 m d
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W D htd R N poly hpoly U hcoeff
    Ψ c F hF β hβ p Rrank hp hR hcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  let E : ℝ := (p+aC)^aC
  let Q : ℝ := E+p+1
  let G : ℝ := (Q+bC)^bC
  let B : ℝ := (p+C)^C
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpQ : p ≤ Q := by dsimp [Q]; linarith
  have hEQ : E ≤ Q := by dsimp [Q]; linarith
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hb : E ≤ B ∧ E+(G+Q+1) ≤ B ∧ (m : ℝ)*p+(G+Q+1) ≤ B ∧
    (m : ℝ)*E+(G+Q+1) ≤ B ∧ (d : ℝ)*E+(G+Q+1) ≤ B ∧
    (d : ℝ)*p+(G+Q+1) ≤ B ∧ G+Q+1 ≤ B := by
      simpa only [E, Q, G, B, Nat.cast_one, pow_one] using hbudget p hp
  obtain ⟨hEB, hEGB, hmp, hmE, hdE, hdp, hGB⟩ := hb
  have hGle : G ≤ B := by linarith
  have hEGle : E+G ≤ B := by linarith
  have hNpos (i : X) : 0 < (N i : ℝ) := (Real.exp_pos B).trans_le (hN i)
  obtain ⟨start, lengths, a, hlengths, hlengthLower, hcomparison, hinside,
      ha, hselected, hhigh, _⟩ :=
    hextract J W D htd.le R hd N poly hpoly U hcoeff Ψ c F hF β hβ p Rrank hp hR hcap
      hdim hmod hcover hLip hΨ
      (fun i => (Real.exp_le_exp.mpr hEB).trans (hN i))
      ((Real.exp_le_exp.mpr hEB).trans hRrank) (fun j _ => hrank j) hcorr
  have hlong (i : X) : Real.exp G ≤ (lengths i : ℝ) := by
    calc
      Real.exp G = Real.exp (E+G) * Real.exp (-E) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp B * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hEGle) (Real.exp_nonneg _)
      _ ≤ (N i : ℝ) * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right (hN i) (Real.exp_nonneg _)
      _ ≤ _ := hlengthLower i
  let startInt := fun i => (start i : ℤ)
  have hsliceRank := majorPhase_residue_lowTagged_rank J d poly hpoly U N lengths
    hNpos hlengths W.modulus W.modulus_pos startInt p E G B Rrank hp hE hmod hcomparison
    hGle (by linarith) (by linarith) hRrank hrank
  have hβslice : ∀ v ∈ integerBox lengths, ∀ i,
      |MvPolynomial.eval (fun x => (startInt x : ℝ) + (W.modulus : ℝ) * v x)
        (lowTaggedPolynomial J d poly i) - c i -
        (β (fun x => startInt x + (W.modulus : ℤ) * v x) i : ℝ)| ≤ 1/2 := by
    intro v hv i
    simpa only [startInt, Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      hβ _ (hinside v hv) i
  have hselectedQ : Real.exp (-Q) ≤ ‖𝔼 v ∈ integerBox lengths,
      (Real.fourierChar (MvPolynomial.eval
        (fun i => (startInt i : ℝ) + (W.modulus : ℝ) * v i)
        (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
      majorPhaseSample J d poly Ψ c F β R.eval
        (fun i => startInt i + (W.modulus : ℤ) * v i)‖ := by
    simpa only [startInt, Int.cast_natCast] using
      (Real.exp_le_exp.mpr (neg_le_neg hEQ)).trans hselected
  let w := lowTaggedWeight J d
  let := weightedBasisIndex_finite w d (lowTaggedWeight_pos J d)
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  obtain ⟨fast, g, Slow, RatPart, qOut, hcount, hgspan, hgraded, hgheight, hKgraded,
      hretained, hmass, _, hqOut, hqBound, hgrid, _, hSlow, hRat, hidentity⟩ :=
    hdetect J D htd R poly hpoly U hcoeff Ψ c F hF β startInt W.modulus W.modulus_pos
      W.cover W.cover_pos a hhigh lengths hlengths Q hQ (hR.mono hpQ) hcap
      (hdim.trans hpQ) (hcover.trans (Real.exp_le_exp.mpr hpQ))
      (hΨ.trans (Real.exp_le_exp.mpr hpQ))
      (fun i => (ha i).trans (Real.exp_le_exp.mpr hEQ)) hlong hβslice hselectedQ hsliceRank
  let K := (fast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
  let A := fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)
  have hA : ∀ i, (A i).totalDegree ≤ w i := fun i =>
    (MvPolynomial.totalDegree_sub_C_le _ _).trans (lowTaggedPolynomial_degree J d poly hpoly i)
  obtain ⟨Slow', RatPart', _, _, hidentity', hmass', hSlow', hRat', _, _, hgrid'⟩ :=
    algebraic_major_weighted_affine_top_pullback_decomposition K w (lowTaggedWeight_pos J d)
      d F hF A hA Slow RatPart W.modulus W.modulus_pos startInt
      (fun i => (N i : ℝ)) (fun i => (lengths i : ℝ)) hNpos
      (fun i => Nat.cast_pos.mpr (hlengths i)) hidentity
      (Real.exp E) (Real.exp G) (Real.one_le_exp hE) hcomparison d qOut hSlow hRat hmass hgrid
  have hmassFinal : realPolynomialMass Slow' ≤ Real.exp B :=
    hmass'.trans (pow_mul_exp_le_exp_of_le_budget (Real.exp_nonneg E) le_rfl hE
      le_rfl (by linarith : (d : ℝ)*E+G ≤ B))
  have hdenFinal : ((W.modulus^d*qOut : ℕ) : ℝ) ≤ Real.exp B :=
    nat_pow_mul_le_exp_of_le_budget hmod hqBound (by linarith : (d : ℝ)*p+G ≤ B)
  have hdenPos : 0 < W.modulus^d*qOut := Nat.mul_pos (pow_pos W.modulus_pos _) hqOut
  refine ⟨fast, g, Slow', RatPart', W.modulus^d*qOut,
    hcount.trans hGle, hgspan, hgraded, (fun j i => (hgheight j i).trans hGle),
    hKgraded, hretained, hmassFinal, ?_, hdenPos, hdenFinal, hgrid', ?_,
    hSlow', hRat', hidentity'⟩
  · exact fun α => (realPolynomialMass_coeff_le Slow' α).trans hmassFinal
  · exact fun α => den_le_of_mem_denominatorGrid hdenPos hgrid' α

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullRestrictedGradeMajorMatching
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_homogeneous_vector_major_detection (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X M : Type} {η V : Type*} [Fintype X] [DecidableEq X] [Fintype η]
      [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
      [LieRing M] [LieAlgebra ℚ M] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (J : Fin m → Type) [∀ j, Fintype (J j)] (basis : Basis η ℝ V)
      (pvec : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ V)
      (_hhom : ∀ α, Finsupp.weight (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) α ≠ k →
        coefficients pvec α = 0)
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom pvec) β (R j).eval u‖) →
      MajorPhaseVectorDetectedConclusion (L := M) J k U poly c N ((p + C) ^ C) basis pvec := by
  obtain ⟨C, hC, hdetect⟩ := exists_majorPhase_detected_decomposition m k hk
  refine ⟨C, hC, ?_⟩
  intro X M η V _ _ _ _ _ _ _ _ _ t e _ _ _ _ J _ basis pvec hhom
    periodCap coverCap Lip W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR
    hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hsupport (j : η) : coordinate (basis.coord j).toAddMonoidHom pvec ∈
      weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) k := by
    have hh : (coordinate (basis.coord j).toAddMonoidHom pvec).IsWeightedHomogeneous
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) k := by
      intro α hα
      by_contra hweight
      apply hα
      rw [coeff_coordinate, hhom α hweight, map_zero]
    intro α hα
    exact (hh (MvPolynomial.mem_support_iff.mp hα)).le
  have hscalar (j : η) : MajorPhaseDetectedConclusion (L := M) J k U poly c
      (coordinate (basis.coord j).toAddMonoidHom pvec) N ((p + C) ^ C) :=
    hdetect J (W j) D htk (R j) N poly hpoly U hcoeff Ψ c
      (coordinate (basis.coord j).toAddMonoidHom pvec) (hsupport j)
      β hβ p Rrank hp (hR j) (hRcap j) hdim (hmod j) (hcover j) hLip hΨ hN hRrank hrank (hcorr j)
  exact majorPhaseVectorDetectedConclusion_of_coordinates J k U poly c N ((p + C) ^ C)
    basis pvec hhom hscalar

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_full_restricted_grade_vector_major_detection (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (residual : F.RealPolynomialSymbol (fullTaggedVariableWeight (X := X) J))
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom
            (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
              (fullTaggedVariableWeight J) fast k residual))) β (R j).eval u‖) →
      MajorPhaseVectorDetectedConclusion (L := M) J k U poly c N ((p + C) ^ C) basis
        (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
          (fullTaggedVariableWeight J) fast k residual)) ∧
      ∀ (u : X → ℝ) (z : ∀ j, J j → ℝ),
        eval₂ (Sum.elim u (fun a : Σ j, J j => z a.1 a.2))
          (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) fast k residual) =
        eval₂ (Sum.elim u (lowTaggedCoordinates J k z))
          (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight J) fast k residual)) := by
  obtain ⟨C, hC, hdetect⟩ := exists_homogeneous_vector_major_detection m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis residual
    periodCap coverCap Lip W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR
    hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  constructor
  · apply hdetect J basis
      (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight J) fast k residual))
      _ W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR hRcap hdim
      hmod hcover hLip hΨ hN hRrank hrank hcorr
    exact lowTaggedVectorRestrict_homogeneous J k _
      (F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF (fullTaggedVariableWeight J) fast k residual)
  · intro u z
    apply lowTaggedVectorRestrict_eval_real J k _ _ u z
    intro α hα
    exact F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF (fullTaggedVariableWeight J)
      fast k residual α (ne_of_gt hα)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

end Erdos3.NilpotentLieFiltration

end

end OAI

end


