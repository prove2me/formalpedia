-- Prove2me | Definitions.Def_OAIErdos3B124
-- name    : OAIErdos3B124
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T06:46:19.373805+00:00
-- url     : https://prove2.me/theorems/c0da5d85-c6e4-4914-ad2d-f308cff37dbd
-- title:
--   OpenAI Erdős-3 split, definitions bundle 125 of 132
-- statement:
--   Definitions bundle 125 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B123`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 125 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.quotientTopBasis_reindex`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareFinIndexEquiv`, `OAI.Erdos3.NilpotentLieFiltration.reindexWeightSurvivors`, `OAI.Erdos3.NilpotentLieFiltration.squareTopQuotientModel_basis_reindex`, `OAI.Erdos3.RationalFilteredNilmanifold.PreparedHigherShiftContradictionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.PrescribedAmbientInputPartitionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.PrescribedComplementInputPartitionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.PrescribedCoveredInputPartitionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.PrescribedPartitionExpansionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.SelectedRefilteredProductExpansionSpec`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.exists_bounded_chart_tag_basis`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.exists_bounded_rational_retractions`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.exists_certified_chart_basis_budget`, `OAI.Erdos3.VectorPolynomial.fullTaggedRealMatrixProjection`, `OAI.Erdos3.VectorPolynomial.rationalTagChartMatrix`, `OAI.Erdos3.VectorPolynomial.rationalTagChartMatrix_height`, `OAI.Erdos3.VectorPolynomial.rationalTagChartMatrix_of_ne`, `OAI.Erdos3.VectorPolynomial.rationalTagChartMatrix_same`, `OAI.Erdos3.basis_projection_range_eq_span`, `OAI.Erdos3.euclideanDerivative_covolume_factorization`, `OAI.Erdos3.euclideanDerivative_covolume_product_bound`, `OAI.Erdos3.euclideanDerivative_horizontal_basis_data`, `OAI.Erdos3.euclideanDerivative_horizontal_injective`, `OAI.Erdos3.euclideanDerivative_index_graph_bounds`, `OAI.Erdos3.euclideanDerivative_rational_lift_matrix_data`, `OAI.Erdos3.euclideanDerivative_vertical_covolume_lower`, `OAI.Erdos3.euclideanDerivative_vertical_minor_data`, `OAI.Erdos3.euclideanVerticalMap_horizontal`, `OAI.Erdos3.exists_bounded_rational_projection_lift`, `OAI.Erdos3.exists_bounded_rational_tag_retraction`, `OAI.Erdos3.exists_bounded_real_rational_tag_retraction`, `OAI.Erdos3.exists_bounded_real_rational_tag_retraction_grid`, `OAI.Erdos3.exists_derivative_vertical_basis_matrix`, `OAI.Erdos3.exists_vertical_derivative_grid_matrix`, `OAI.Erdos3.exists_weighted_minor_lower_bound`, `OAI.Erdos3.lower_triangular_horizontal_mulVec`, `OAI.Erdos3.lower_triangular_horizontal_row`, `OAI.Erdos3.rationalCoordinateRealBasis`, `OAI.Erdos3.rationalCoordinateRealBasis_apply`, `OAI.Erdos3.rationalMatrix_real_fixes_coordinateSpan`, `OAI.Erdos3.rationalMatrix_real_range_eq_coordinateSpan`, `OAI.Erdos3.rationalMatrix_real_retraction`, `OAI.Erdos3.realRationalCoordinateSpan_basis`, `OAI.Erdos3.realSubmoduleBasis`, `OAI.Erdos3.realSubmoduleBasis_coe`, `OAI.Erdos3.realSubmoduleBasis_matrix_coordinates`, `OAI.Erdos3.realSubmoduleBasis_matrix_span`, `OAI.Erdos3.realSubmoduleParameterization`, `OAI.Erdos3.realSubmoduleParameterization_basis`, `OAI.Erdos3.scaled_covolume_product_le`, `OAI.Erdos3.submoduleBasisMatrix`, `OAI.Erdos3.weighted_isometric_lattice_covolume_lower`, `OAI.Erdos3.weighted_isometric_lattice_minor_data`, `OAI.Erdos3.weighted_row_minor_det`, `_private.Linear.CertifiedChartBasisBudget.0.OAI.Erdos3.VectorPolynomial.certifiedChartMatrix_budget`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B042
import Definitions.Def_OAIErdos3B109

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DerivativeVerticalBasis
namespace OAI

section

namespace Erdos3

theorem exists_vertical_derivative_grid_matrix
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ] {k : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (v : Fin k → EuclideanSpace ℝ (σ ⊕ κ))
    (hli : LinearIndependent ℝ v)
    (hv : ∀ j, v j ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl)
    (hzero : ∀ j, euclideanDerivativeShiftMap T hT (v j) = 0) :
    ∃ B : Matrix κ (Fin k) ℝ, LinearIndependent ℝ B.col ∧
      (∀ j, B.col j ∈ realDenominatorGrid l) ∧
      ∀ j, v j = euclideanVerticalMap scale hscale A (B.col j) := by
  choose r hr he using fun j =>
    euclideanDerivative_vertical_grid_coordinates T hT scale hscale Y A l hl (v j) (hv j) (hzero j)
  let B : Matrix κ (Fin k) ℝ := fun i j => r j i
  refine ⟨B, ?_, hr, he⟩
  apply LinearIndependent.of_comp (euclideanVerticalMap scale hscale A)
  have hf : euclideanVerticalMap scale hscale A ∘ B.col = v :=
    funext (fun j => (he j).symm)
  rw [hf]
  exact hli

end Erdos3

end

section

namespace Erdos3

theorem exists_derivative_vertical_basis_matrix
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℤ L,
      ∃ B : Matrix κ (Fin (Module.finrank ℝ V)) ℝ,
        LinearIndependent ℝ B.col ∧ (∀ j, B.col j ∈ realDenominatorGrid l) ∧
        ∀ j, (b j).val.val.val = euclideanVerticalMap scale hscale A (B.col j) := by
  let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hscale Y A l hl R
  let b := finiteLatticeBasis L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ κ) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let v := fun j => f (b j).val
  have hli : LinearIndependent ℝ v := by
    have h := (b.ofZLatticeBasis ℝ L).linearIndependent.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr f.injective)
    simpa only [v, Function.comp_def, Module.Basis.ofZLatticeBasis_apply,
      LinearIsometry.coe_toLinearMap] using h
  have hv (j) : v j ∈ Λ := (b j).property
  have hz (j) : euclideanDerivativeShiftMap T hT (v j) = 0 := (b j).val.property
  obtain ⟨B, hB, hgrid, he⟩ := exists_vertical_derivative_grid_matrix
    T hT scale hscale Y A l hl v hli hv hz
  exact ⟨b, B, hB, hgrid, he⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
namespace OAI

section

namespace Erdos3

theorem weighted_row_minor_det {m k : ℕ} (N : Matrix (Fin m) (Fin k) ℝ)
    (w : Fin m → ℝ) (p : Fin k → Fin m) :
    (Matrix.of (fun i j => w (p i) * N (p i) j)).det =
      (∏ i, w (p i)) * (N.submatrix p id).det := by
  have he : Matrix.of (fun i j => w (p i) * N (p i) j) =
      Matrix.diagonal (fun i => w (p i)) * N.submatrix p id := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [he, Matrix.det_mul, Matrix.det_diagonal]

theorem exists_weighted_minor_lower_bound {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤
        |(Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).det| := by
  obtain ⟨p, hp, hdet, hpreserve⟩ := exists_preserved_nonzero_row_minor A hA
  have hsubgrid : ∀ j, (fun i => (A.submatrix p id) i j) ∈ realDenominatorGrid l := by
    intro j
    obtain ⟨z, hz⟩ := hgrid j
    exact ⟨fun i => z (p i), funext (fun i => congrFun hz (p i))⟩
  have hminor := one_div_pow_le_abs_grid_det (A.submatrix p id) l hl hsubgrid hdet
  simp only [Fintype.card_fin] at hminor
  refine ⟨p, hp, ?_⟩
  rw [weighted_row_minor_det, hpreserve M hM hdiag, abs_mul,
    abs_of_pos (Finset.prod_pos (fun i _ => hw (p i)))]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right hminor (Finset.prod_nonneg (fun i _ => (hw (p i)).le))

theorem weighted_isometric_lattice_covolume_lower {ι E : Type*} [Fintype ι] {m k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : Fin m → ι) (he : Function.Injective e)
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (hcoord : ∀ j i, f (b j).val (e i) = w i * (M * A) i j) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ ZLattice.covolume Λ := by
  obtain ⟨p, hp, hlower⟩ := exists_weighted_minor_lower_bound A hA l hl hgrid M hM hdiag w hw
  refine ⟨p, hp, hlower.trans ?_⟩
  have hupper := abs_isometric_lattice_basis_det_le_covolume Λ b f (e ∘ p) (he.comp hp)
  have hmatrix : Matrix.of (fun i j => f (b i).val ((e ∘ p) j)) =
      (Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).transpose := by
    ext i j
    exact hcoord i (p j)
  simpa only [hmatrix, Matrix.det_transpose] using hupper

end Erdos3

end

section

namespace Erdos3

theorem weighted_isometric_lattice_minor_data {ι E : Type*} [Fintype ι] {m k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : Fin m → ι) (he : Function.Injective e)
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (hcoord : ∀ j i, f (b j).val (e i) = w i * (M * A) i j) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧ (A.submatrix p id).det ≠ 0 ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ ZLattice.covolume Λ := by
  obtain ⟨p, hp, hdet, hpreserve⟩ := exists_preserved_nonzero_row_minor A hA
  have hsubgrid : ∀ j, (fun i => (A.submatrix p id) i j) ∈ realDenominatorGrid l := by
    intro j
    obtain ⟨z, hz⟩ := hgrid j
    exact ⟨fun i => z (p i), funext (fun i => congrFun hz (p i))⟩
  have hminor := one_div_pow_le_abs_grid_det (A.submatrix p id) l hl hsubgrid hdet
  simp only [Fintype.card_fin] at hminor
  have hlower : 1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤
      |(Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).det| := by
    rw [weighted_row_minor_det, hpreserve M hM hdiag, abs_mul,
      abs_of_pos (Finset.prod_pos (fun i _ => hw (p i)))]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hminor (Finset.prod_nonneg (fun i _ => (hw (p i)).le))
  refine ⟨p, hp, hdet, hlower.trans ?_⟩
  have hupper := abs_isometric_lattice_basis_det_le_covolume Λ b f (e ∘ p) (he.comp hp)
  have hmatrix : Matrix.of (fun i j => f (b i).val ((e ∘ p) j)) =
      (Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).transpose := by
    ext i j
    exact hcoord i (p j)
  simpa only [hmatrix, Matrix.det_transpose] using hupper

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem lower_triangular_horizontal_row {m a : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0)
    (hblock : ∀ i j, i.val < a → j.val < a → M i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (i : Fin m) (hi : i.val < a) (j : Fin m) :
    M i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j := by
  by_cases hj : j.val < a
  · exact hblock i j hi hj
  · have hij : i < j := by omega
    rw [hM i j hij, Matrix.one_apply, if_neg (ne_of_lt hij)]

theorem lower_triangular_horizontal_mulVec {m a : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0)
    (hblock : ∀ i j, i.val < a → j.val < a → M i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (x : Fin m → ℝ) (i : Fin m) (hi : i.val < a) : (M *ᵥ x) i = x i := by
  calc
    _ = ((1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ x) i := by
      simp only [Matrix.mulVec, dotProduct, lower_triangular_horizontal_row M hM hblock i hi]
    _ = x i := congrFun (Matrix.one_mulVec x) i

theorem euclideanVerticalMap_horizontal {σ : Type*} {m a : ℕ}
    (scale : Fin m → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (x : Fin m → ℝ) (i : Fin m) (hi : i.val < a) :
    euclideanVerticalMap (σ := σ) scale hscale A x (Sum.inr i) = x i := by
  rw [euclideanVerticalMap_apply_inr, hscalehor i hi, one_mul]
  calc
    A x i = ((LinearMap.toMatrix' A.toLinearMap) *ᵥ x) i :=
      (congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap x) i).symm
    _ = x i := lower_triangular_horizontal_mulVec _ hA hblock x i hi

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_vertical_covolume_lower
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 0 < scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let k := Module.finrank ℝ V
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, scale (p i)) ≤
        ZLattice.covolume (latticeKernel (shortVectorLattice Λ R) π)
          (MeasureTheory.volume (α := V)) := by
  let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let : IsZLattice ℝ L :=
    euclideanDerivative_vertical_lattice_full T hT scale (fun j => (hscale j).ne') Y A l hl R
  let b := finiteLatticeBasis L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let v := fun j => f (b j).val
  have hli : LinearIndependent ℝ v := by
    have h := (b.ofZLatticeBasis ℝ L).linearIndependent.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr f.injective)
    simpa only [v, Function.comp_def, Module.Basis.ofZLatticeBasis_apply,
      LinearIsometry.coe_toLinearMap] using h
  have hv (j) : v j ∈ Λ := (b j).property
  have hz (j) : euclideanDerivativeShiftMap T hT (v j) = 0 := (b j).val.property
  obtain ⟨B, hB, hgrid, he⟩ := exists_vertical_derivative_grid_matrix
    T hT scale (fun j => (hscale j).ne') Y A l hl v hli hv hz
  apply weighted_isometric_lattice_covolume_lower L b f Sum.inr Sum.inr_injective
    B hB l hl hgrid (LinearMap.toMatrix' A.toLinearMap) hA hdiag scale hscale
  intro j i
  have hc := congrArg (fun x : EuclideanSpace ℝ (σ ⊕ Fin m) => x (Sum.inr i)) (he j)
  change f (b j).val (Sum.inr i) = scale i * _
  rw [hc, euclideanVerticalMap_apply_inr]
  apply congrArg (fun t : ℝ => scale i * t)
  have hm := congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap (B.col j)) i
  exact hm.symm

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_vertical_minor_data
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 0 < scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let k := Module.finrank ℝ V
    ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
      LinearIndependent ℝ B.col ∧ (∀ j, B.col j ∈ realDenominatorGrid l) ∧
      (∀ j, (b j).val.val.val = euclideanVerticalMap scale (fun j => (hscale j).ne') A (B.col j)) ∧
      ∃ p : Fin k → Fin m, Function.Injective p ∧ (B.submatrix p id).det ≠ 0 ∧
        1 / (l : ℝ) ^ k * (∏ i, scale (p i)) ≤
          ZLattice.covolume L (MeasureTheory.volume (α := V)) := by
  let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let : IsZLattice ℝ L :=
    euclideanDerivative_vertical_lattice_full T hT scale (fun j => (hscale j).ne') Y A l hl R
  obtain ⟨b, B, hB, hgrid, he⟩ := exists_derivative_vertical_basis_matrix
    T hT scale (fun j => (hscale j).ne') Y A l hl R
  refine ⟨b, B, hB, hgrid, he, ?_⟩
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  apply weighted_isometric_lattice_minor_data L b f Sum.inr Sum.inr_injective
    B hB l hl hgrid (LinearMap.toMatrix' A.toLinearMap) hA hdiag scale hscale
  intro j i
  have hc := congrArg (fun x : EuclideanSpace ℝ (σ ⊕ Fin m) => x (Sum.inr i)) (he j)
  change (b j).val.val.val (Sum.inr i) = scale i * _
  rw [hc, euclideanVerticalMap_apply_inr]
  apply congrArg (fun t : ℝ => scale i * t)
  exact (congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap (B.col j)) i).symm

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_basis_data
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
    ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
      LinearIndependent ℝ B.col ∧ (∀ j, B.col j ∈ realDenominatorGrid l) ∧
      (∀ j, (b j).val.val.val = euclideanVerticalMap scale hs0 A (B.col j)) ∧
      ∃ p : Fin k → Fin a, Function.Injective p ∧
        (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0 := by
  let hspos : ∀ j, 0 < scale j := fun j => lt_of_lt_of_le zero_lt_one (hscale j)
  let Λ := euclideanDerivativeLattice T hT scale (fun j => (hspos j).ne') Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  dsimp only
  intro hupper
  obtain ⟨b, B, hB, hgrid, hrep, p, hp, hdet, hlower⟩ :=
    euclideanDerivative_vertical_minor_data T hT scale hspos Y A hA hdiag l hl R
  have hhor := pivots_lt_of_weighted_bound p hp scale hscale l hl a Tmin C _ hfar hlower hupper hlarge
  let q : Fin (Module.finrank ℝ V) → Fin a := fun i => ⟨(p i).val, hhor i⟩
  have hq (i) : Fin.castLE ha (q i) = p i := Fin.ext rfl
  refine ⟨b, B, hB, hgrid, hrep, q, ?_, ?_⟩
  · intro i j hij
    apply hp
    rw [← hq i, ← hq j, hij]
  · have he : Fin.castLE ha ∘ q = p := funext hq
    simpa only [he] using hdet

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_injective
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      Function.Injective ((euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)) := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, _, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  let bR := b.ofZLatticeBasis ℝ L
  have hcoord (j) (i : Fin a) : P (bR j) i = B (Fin.castLE ha i) j := by
    simp only [bR, Module.Basis.ofZLatticeBasis_apply]
    change (b j).val.val.val (Sum.inr (Fin.castLE ha i)) = B (Fin.castLE ha i) j
    rw [hrep]
    exact euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt
  apply basis_projection_injective_of_minor bR P p
  have he : Matrix.of (fun i j => P (bR j) (p i)) = B.submatrix (Fin.castLE ha ∘ p) id := by
    ext i j
    exact hcoord j (p i)
  rw [he]
  exact hdet

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_covolume_factorization
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hscale Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup
    0 < I ∧ ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume (shortVectorLattice Λ ρ) =
        ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
          (MeasureTheory.volume (α := LinearMap.ker π)) *
          ((I : ℝ) / ∏ i, T i) *
          Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det := by
  let hTpos : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T (fun i => (hTpos i).ne') scale hscale Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T (fun i => (hTpos i).ne')).comp Z.subtype
  have hproj := euclideanDerivativeLattice_shortSpan_projection
    T hT scale hscale Y A l hl R δ hR H r hr hnorm hdense hlarge
  have hsurj : Function.Surjective π :=
    euclidean_shift_subspace_surjective Z T (fun i => (hTpos i).ne') hproj
  have hinteger : ∀ x ∈ shortVectorLattice Λ ρ, π x ∈ realIntegerGrid := by
    intro x hx
    exact euclideanDerivativeShiftMap_integer T (fun i => (hTpos i).ne')
      scale hscale Y A l hl x.val hx
  exact ⟨latticeImage_index_pos _ π hinteger hsurj,
    exists_euclidean_lattice_graph_identity Z (shortVectorLattice Λ ρ) T hTpos hinteger hsurj⟩

end Erdos3

end

section

namespace Erdos3

theorem scaled_covolume_product_le {z k I E t C δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hfactor : z = k * (I / t) * E) (hbound : z ≤ C / (δ * t)) :
    k * I * E ≤ C / δ := by
  calc
    k * I * E = z * t := by rw [hfactor]; field_simp [ht.ne']
    _ ≤ C / (δ * t) * t := mul_le_mul_of_nonneg_right hbound ht.le
    _ = C / δ := by field_simp

open Module

theorem euclideanDerivative_covolume_product_bound
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hscale Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup
    0 < I ∧ ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
        (MeasureTheory.volume (α := LinearMap.ker π)) * (I : ℝ) *
        Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det ≤
        (((finrank ℝ Z : ℝ) + 2) * ρ) ^ finrank ℝ Z / δ := by
  obtain ⟨hI, G, hG, hsection, hfactor⟩ := euclideanDerivative_covolume_factorization
    T hT scale hscale Y A l hl R δ hR H r hr hnorm hdense hlarge
  refine ⟨hI, G, hG, hsection, ?_⟩
  have hTpos (i) : 0 < T i := lt_of_lt_of_le zero_lt_one (hT i)
  have hbound := euclideanDerivative_covolume_density_bound T hTpos scale hscale
    Y A l hl R δ (zero_le_one.trans hR) hδ H r hr hnorm hdense
  exact scaled_covolume_product_le (Finset.prod_pos (fun i _ => hTpos i)) hδ hfactor hbound

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_index_graph_bounds
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let k := Module.finrank ℝ (LinearMap.ker π)
    let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup
    let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
    0 < I ∧ ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
        (MeasureTheory.volume (α := LinearMap.ker π)) ≤ C ∧
      (I : ℝ) ≤ C * (l : ℝ) ^ k ∧
      Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det ≤ C * (l : ℝ) ^ k := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let hspos : ∀ j, 0 < scale j := fun j => lt_of_lt_of_le zero_lt_one (hscale j)
  let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale (fun j => (hspos j).ne') Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let k := Module.finrank ℝ (LinearMap.ker π)
  have hresult := euclideanDerivative_covolume_product_bound
    T hT scale (fun j => (hspos j).ne') Y A l hl R δ hR hδ H r hr hnorm hdense hlarge
  obtain ⟨hI, G, hG, hsection, hprod⟩ := hresult
  refine ⟨hI, G, hG, hsection, ?_⟩
  obtain ⟨p, _, hp⟩ := euclideanDerivative_vertical_covolume_lower
    T hT0 scale hspos Y A hA hdiag l hl ρ
  have hden : 0 < (l : ℝ) ^ k := pow_pos (by exact_mod_cast hl) _
  have hweights : 1 ≤ ∏ i, scale (p i) := Finset.one_le_prod (fun i _ => hscale (p i))
  have hlower : 1 / (l : ℝ) ^ k ≤
      ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
        (MeasureTheory.volume (α := LinearMap.ker π)) := by
    calc
      1 / (l : ℝ) ^ k = 1 / (l : ℝ) ^ k * 1 := (mul_one _).symm
      _ ≤ 1 / (l : ℝ) ^ k * (∏ i, scale (p i)) :=
        mul_le_mul_of_nonneg_left hweights (one_div_pos.mpr hden).le
      _ ≤ _ := hp
  apply covolume_index_graph_bounds hden hlower
    (by exact_mod_cast Nat.succ_le_iff.mpr hI)
    (one_le_euclidean_section_gram_sqrt Z G hG)
  exact hprod

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {κ V : Type*} [AddCommGroup V] [Module ℚ V]
  (K : Submodule ℚ V) (b : Basis κ ℚ K)

noncomputable def realSubmoduleBasis : Basis κ ℝ (K.baseChange ℝ) :=
  (b.baseChange ℝ).map (realificationSubmoduleEquiv K)

theorem realSubmoduleBasis_coe (i : κ) :
    (realSubmoduleBasis K b i : ℝ ⊗[ℚ] V) = (1 : ℝ) ⊗ₜ[ℚ] (b i : V) := by
  rw [realSubmoduleBasis, Basis.map_apply, Basis.baseChange_apply, realificationSubmoduleEquiv_tmul]

variable [Fintype κ]

noncomputable def realSubmoduleParameterization : (κ → ℝ) ≃ₗ[ℝ] K.baseChange ℝ :=
  (realSubmoduleBasis K b).equivFun.symm

theorem realSubmoduleParameterization_basis (i : κ) :
    realSubmoduleParameterization K b (Pi.basisFun ℝ κ i) = realSubmoduleBasis K b i := by
  classical
  apply (realSubmoduleBasis K b).equivFun.injective
  rw [realSubmoduleParameterization, LinearEquiv.apply_symm_apply]
  ext j
  simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]

end Erdos3

end

section

namespace Erdos3

theorem basis_projection_range_eq_span {E ι κ : Type*}
    [AddCommGroup E] [Module ℝ E] (b : Module.Basis κ ℝ E)
    (P : E →ₗ[ℝ] (ι → ℝ)) :
    LinearMap.range P = Submodule.span ℝ (Set.range (fun j => P (b j))) := by
  rw [← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  rfl

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem exists_bounded_rational_projection_lift
    {E F α β : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype α] {k : ℕ}
    (b : Module.Basis (Fin k) ℝ E) (P : E →ₗ[ℝ] (α → ℝ))
    (hP : Function.Injective P) (g : E →ₗ[ℝ] (β → ℝ))
    (e : α → β) (hhor : ∀ v i, g v (e i) = P v i)
    (W : (β → ℝ) →ₗ[ℝ] F) (C : ℝ)
    (hbound : ∀ v, ‖W (g v)‖ ≤ C * ‖P v‖)
    (B : Matrix β (Fin k) ℝ) (hB : ∀ i j, B i j = g (b j) i)
    (p : Fin k → α) (hp : (B.submatrix (e ∘ p) id).det ≠ 0)
    (Q : Matrix β (Fin k) ℚ)
    (hQ : Q.map (Rat.castHom ℝ) = B * (B.submatrix (e ∘ p) id)⁻¹)
    (hQid : Q.submatrix (e ∘ p) id = 1) :
    let QH := Q.submatrix e id
    ∃ R : LinearMap.range P →ₗ[ℝ] (β → ℝ),
      (∀ x i, R x (e i) = x.val i) ∧
      (∀ x, ‖W (R x)‖ ≤ C * ‖x‖) ∧
      (∀ v, R ⟨P v, v, rfl⟩ = g v) ∧
      LinearMap.range P = Submodule.span ℝ (Set.range (QH.map (Rat.castHom ℝ)).col) ∧
      LinearIndependent ℝ (QH.map (Rat.castHom ℝ)).col ∧
      LinearIndependent ℚ QH.col ∧
      (∀ j, ∃ x : LinearMap.range P,
        x.val = (QH.map (Rat.castHom ℝ)).col j ∧ R x = (Q.map (Rat.castHom ℝ)).col j) := by
  let J := (LinearEquiv.ofInjective P hP).symm.toLinearMap
  have hJ (x : LinearMap.range P) : P (J x) = x.val :=
    congrArg Subtype.val ((LinearEquiv.ofInjective P hP).apply_symm_apply x)
  let R := g.comp J
  let H := B.submatrix e id
  let QH := Q.submatrix e id
  have hHcol : H.col = fun j => P (b j) := by
    funext j i
    exact (hB (e i) j).trans (hhor (b j) i)
  have hQH : QH.map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ := by
    ext i j
    exact congrArg (fun M : Matrix β (Fin k) ℝ => M (e i) j) hQ
  have hQHid : QH.submatrix p id = 1 := hQid
  have hrealid : (QH.map (Rat.castHom ℝ)).submatrix p id = 1 := by
    rw [hQH]
    exact row_normalization_submatrix H p hp
  refine ⟨R, ?_, ?_, ?_, ?_, independent_columns_of_identity_minor _ p hrealid,
    independent_columns_of_identity_minor QH p hQHid, ?_⟩
  · intro x i
    exact (hhor (J x) i).trans (congrFun (hJ x) i)
  · intro x
    have h := hbound (J x)
    rw [hJ x] at h
    exact h
  · intro v
    have h : J ⟨P v, v, rfl⟩ = v := hP (hJ ⟨P v, v, rfl⟩)
    change g (J ⟨P v, v, rfl⟩) = g v
    rw [h]
  · change LinearMap.range P = Submodule.span ℝ (Set.range (QH.map (Rat.castHom ℝ)).col)
    rw [hQH, row_normalization_col_span H p hp, hHcol]
    exact basis_projection_range_eq_span b P
  · intro j
    obtain ⟨v, hv⟩ := exists_normalized_basis_vector b g B hB
      (B.submatrix (e ∘ p) id)⁻¹ j
    have hv' : g v = (Q.map (Rat.castHom ℝ)).col j := by
      rw [hQ]
      exact hv
    let x : LinearMap.range P := ⟨P v, v, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · funext i
      exact (hhor v i).symm.trans (congrFun hv' (e i))
    · have hx : J x = v := hP (hJ x)
      change g (J x) = _
      rw [hx]
      exact hv'

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
  (e : Basis ι ℚ V) (K : Submodule ℚ V) (b : Basis κ ℚ K)

noncomputable def submoduleBasisMatrix : Matrix ι κ ℚ :=
  fun i j => e.repr (b j).val i

theorem realSubmoduleBasis_matrix_coordinates (j : κ) :
    (e.baseChange ℝ).equivFun (realSubmoduleBasis K b j).val =
      ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col j := by
  funext i
  rw [Basis.equivFun_apply, realSubmoduleBasis_coe, Basis.baseChange_repr_tmul]
  simp [submoduleBasisMatrix, Matrix.col, Algebra.smul_def]

theorem realSubmoduleBasis_matrix_span :
    Submodule.span ℝ (Set.range ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col) =
      (K.baseChange ℝ).map (e.baseChange ℝ).equivFun.toLinearMap := by
  let f := (e.baseChange ℝ).equivFun.toLinearMap.comp (K.baseChange ℝ).subtype
  have he : (f ∘ realSubmoduleBasis K b) =
      ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col := by
    funext j
    exact realSubmoduleBasis_matrix_coordinates e K b j
  have hs := congrArg (fun U : Submodule ℝ (K.baseChange ℝ) => U.map f)
    (realSubmoduleBasis K b).span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, he] at hs
  exact hs.trans (by simp only [f, LinearMap.range_comp, Submodule.range_subtype])

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {B I : Type*} [Fintype B]
  (U : Submodule ℚ (B → ℚ)) (b : Basis I ℚ U)

noncomputable def rationalCoordinateRealBasis : Basis I ℝ (realRationalCoordinateSpan U) :=
  (realSubmoduleBasis U b).map (realRationalCoordinateEquiv.submoduleMap (U.baseChange ℝ))

@[simp] theorem rationalCoordinateRealBasis_apply (i : I) (j : B) :
    (rationalCoordinateRealBasis U b i : B → ℝ) j = ((b i : B → ℚ) j : ℝ) := by
  change realRationalCoordinateEquiv (realSubmoduleBasis U b i : ℝ ⊗[ℚ] (B → ℚ)) j = _
  rw [realSubmoduleBasis_coe, realRationalCoordinateEquiv_tmul, one_mul]

theorem realRationalCoordinateSpan_basis :
    Submodule.span ℝ (Set.range (fun i j => ((b i : B → ℚ) j : ℝ))) =
      realRationalCoordinateSpan U := by
  have hb : Submodule.span ℚ (Set.range (fun i => (b i : B → ℚ))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ b)) = U
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  exact (realRationalCoordinateSpan_span (fun i => (b i : B → ℚ))).symm.trans
    (congrArg realRationalCoordinateSpan hb)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_rational_lift_matrix_data
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
        ∃ p : Fin k → Fin a,
          (∀ j, B.col j ∈ realDenominatorGrid l) ∧
          (∀ j, (b j).val.val.val = euclideanVerticalMap scale hs0 A (B.col j)) ∧
          (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0 ∧
          ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
            ∃ Q : Matrix (Fin m) (Fin k) ℚ,
              (∀ j, Q.col j ∈ denominatorGrid D) ∧
              Q.map (Rat.castHom ℝ) = B * (B.submatrix (Fin.castLE ha ∘ p) id)⁻¹ ∧
              Q.submatrix (Fin.castLE ha ∘ p) id = 1 ∧
              (∀ i j, RationalHeightLE (Q (Fin.castLE ha i) j)
                (Nat.ceil (C * (l : ℝ) ^ k))) := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  dsimp only
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, hgrid, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  refine ⟨b, B, p, hgrid, hrep, hdet, ?_⟩
  apply exists_partially_bounded_grid_normalization B l hl hgrid (Fin.castLE ha) p hdet C
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let e : Fin a → σ ⊕ Fin m := fun i => Sum.inr (Fin.castLE ha i)
  have he : Function.Injective e := by
    intro i j hij
    have h : Fin.castLE ha i = Fin.castLE ha j := Sum.inr.inj hij
    exact Fin.ext (congrArg (fun u : Fin m => u.val) h)
  let H := B.submatrix (Fin.castLE ha) id
  have hH (i j) : H i j = f (b j).val (e i) := by
    change B (Fin.castLE ha i) j = (b j).val.val.val (Sum.inr (Fin.castLE ha i))
    rw [hrep]
    exact (euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt).symm
  intro q
  exact (lattice_projection_all_minors_bound L b f e he H hH q).trans hupper

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*}

noncomputable def rationalTagChartMatrix
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) :
    (Σ j, Fin (n j)) → (Σ j, J j) → ℚ :=
  fun a x => (Pi.single (M := fun j => J j → ℚ) a.1
    (b a.1 a.2 : J a.1 → ℚ)) x.1 x.2

theorem rationalTagChartMatrix_same
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) (j : Fin m) (a : Fin (n j)) (i : J j) :
    rationalTagChartMatrix W n b ⟨j, a⟩ ⟨j, i⟩ = (b j a : J j → ℚ) i := by
  simp [rationalTagChartMatrix]

theorem rationalTagChartMatrix_of_ne
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) (a : Σ j, Fin (n j)) (x : Σ j, J j)
    (h : x.1 ≠ a.1) : rationalTagChartMatrix W n b a x = 0 := by
  simp [rationalTagChartMatrix, Pi.single_eq_of_ne h]

theorem rationalTagChartMatrix_height
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) {P : ℝ} (hP : 0 ≤ P)
    (hb : ∀ j a i, rationalLogHeight ((b j a : J j → ℚ) i) ≤ P) :
    ∀ a x, rationalLogHeight (rationalTagChartMatrix W n b a x) ≤ P := by
  rintro ⟨j, a⟩ ⟨k, i⟩
  by_cases h : k = j
  · subst k
    rw [rationalTagChartMatrix_same]
    exact hb j a i
  · rw [rationalTagChartMatrix_of_ne W n b ⟨j, a⟩ ⟨k, i⟩ h]
    simpa [rationalLogHeight] using hP

theorem RationalTaggedConstraintCertificate.exists_bounded_chart_tag_basis {X : Type*}
    [∀ j, Fintype (J j)]
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (n : Fin m → ℕ) (Ktag : Submodule ℝ ((Σ j, J j) → ℝ))
      (b : Basis (Σ j, Fin (n j)) ℝ Ktag)
      (matrix : (Σ j, Fin (n j)) → (Σ j, J j) → ℚ),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ a x, (b a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ)) ∧
      (∀ a x, x.1 ≠ a.1 → matrix a x = 0) ∧
      (∀ a x, rationalLogHeight (matrix a x) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} ∧
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
        (∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K) →
        ∀ v : (Σ j, J j) → ℝ, (∀ j, (fun i => v ⟨j, i⟩) ∈ U j) → v ∈ Ktag := by
  classical
  obtain ⟨W, n, b, hn, hb, hK⟩ := hcert.exists_bounded_tag_bases_univ hp hdim hblocks
  let R := fun j => realRationalCoordinateSpan (W j)
  let br := fun j => rationalCoordinateRealBasis (W j) (b j)
  let Ktag := taggedSubmodule R
  let basis : Basis (Σ j, Fin (n j)) ℝ Ktag := taggedSubmoduleBasis R br
  let matrix := rationalTagChartMatrix W n b
  have hentry (a : Σ j, Fin (n j)) (x : Σ j, J j) :
      (basis a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ) := by
    rcases a with ⟨j, a⟩
    rcases x with ⟨k, i⟩
    by_cases h : k = j
    · subst k
      change ((taggedSubmoduleBasis R br ⟨j, a⟩ : (Σ j, J j) → ℝ) ⟨j, i⟩) = _
      rw [taggedSubmoduleBasis_same]
      dsimp only [matrix]
      rw [rationalTagChartMatrix_same]
      exact rationalCoordinateRealBasis_apply (W j) (b j) a i
    · rw [show (basis ⟨j, a⟩ : (Σ j, J j) → ℝ) ⟨k, i⟩ = 0 from
        taggedSubmoduleBasis_of_ne R br j a k i h]
      rw [show matrix ⟨j, a⟩ ⟨k, i⟩ = 0 from
        rationalTagChartMatrix_of_ne W n b ⟨j, a⟩ ⟨k, i⟩ h, Rat.cast_zero]
  have htag : K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} := by
    rw [hK]
    ext point
    change (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
      Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))) ↔
      ∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ realRationalCoordinateSpan (W j)
    simp_rw [realRationalCoordinateSpan_basis]
  refine ⟨n, Ktag, basis, matrix, hn, hentry,
    rationalTagChartMatrix_of_ne W n b,
    rationalTagChartMatrix_height W n b (by positivity) hb, htag, ?_⟩
  intro U hret v hv
  have hpoint := hret (Sum.elim (fun _ : X => (0 : ℝ)) v) (by simpa using hv)
  simpa only [htag, Set.mem_ofPred_eq, Sum.elim_inr] using hpoint

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

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem quotientTopBasis_reindex (e : ι ≃ κ)
    (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)})) :
    F.quotientTopBasis (b.reindex e) (fun k => ω (e.symm k)) hF' =
      (F.quotientTopBasis b ω hF).reindex (reindexWeightSurvivors s ω e) := by
  apply DFunLike.ext
  intro i
  simp only [F.quotientTopBasis_apply, Basis.reindex_apply]
  rfl

variable [Fintype ι]

noncomputable def reducedSquareFinIndexEquiv (s : ℕ) (ω : ι → ℕ) :
    ReducedSquareBasisIndex s ω ≃
      Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i}) :=
  (reindexWeightSurvivors s (squareBasisWeight ω) (Fintype.equivFin _)).trans (Fintype.equivFin _)

theorem squareTopQuotientModel_basis_reindex (Γ : Subgroup F.squareFiltration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
    (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N) :
    (F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
      (F.squareFinBasis_layers b ω hF) Γ N hN hin hout).basis =
        (F.reducedSquareBasis b ω hF).reindex (reducedSquareFinIndexEquiv s ω) := by
  change (F.squareFiltration.quotientTopBasis (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
    (F.squareFinBasis_layers b ω hF)).reindex (Fintype.equivFin _) = _
  have hb := F.squareFiltration.quotientTopBasis_reindex
    (F.adaptedSquareBasis b ω (hF 2)) (squareBasisWeight ω) (F.adaptedSquareBasis_layers b ω hF)
    (Fintype.equivFin _) (F.squareFinBasis_layers b ω hF)
  calc
    _ = ((F.reducedSquareBasis b ω hF).reindex
        (reindexWeightSurvivors s (squareBasisWeight ω) (Fintype.equivFin _))).reindex
          (Fintype.equivFin _) := congrArg (fun c => c.reindex (Fintype.equivFin _)) hb
    _ = _ := by
      apply DFunLike.ext
      intro i
      simp only [Basis.reindex_apply]
      exact (Basis.reindex_apply (F.reducedSquareBasis b ω hF)
        (reducedSquareFinIndexEquiv s ω) i).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedCoveredInputPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def PrescribedCoveredInputPartitionSpec (s k₀ a C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ (Λ : ∀ i, Subgroup (Q i).filtration.Group) (_hΛ : ∀ i, Λ i ≤ (Q i).lattice)
        (l : ι → ℕ) (hl : ∀ i, 0 < l i)
        (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates (Q i).basis (Λ i))
        (hlout : ∀ i, bchSubgroupCoordinates (Q i).basis (Λ i) ⊆ denominatorGrid (l i)),
      let Q' := fun i => (Q i).withLattice (Λ i) (l i) (hl i) (hlin i) (hlout i)
      ∀ (E : ∀ j, RationalFilteredNilmanifold (K j) s (e j))
        (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i, (Q' i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      let Z := sumFactors E Q'
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := realification_moduleTopology_t2 (pi Z).basis
      letI := (pi Z).metricSpace
      ∃ (I : Type) (inst : Fintype I), letI := inst;
        (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (A : I → ZMod N → ℝ) (label : I → ZMod q),
          (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = label j) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
          ∀ (h : ZMod N) (branch : ι → Fin 2) (η γ : ∀ i, (D i).RealGroup)
            (rSq : ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
            (qSq : ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ i, γ i ∈ (D i).realLattice) →
            (∀ i b, |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((p + 2) ^ k₀)) →
            (∀ i (z : Unit → ℤ),
              (D i).filtration.realSquareFstHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (η i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) (g₀ i) * (γ i)⁻¹ ∧
              (D i).filtration.realSquareSndHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => c i) (g₀ i)) →
            (∀ i, qSq i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)) →
            let G := piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q' g qSq)
            ∀ j b x y,
              x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
              0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
              dist ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => x))
                ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                  Real.exp ((2 * p + 4) ^ 4) * ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedComplementInputPartition
namespace OAI

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def PrescribedAmbientInputPartitionSpec (s k₀ a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) s (e j),
      let Z := sumFactors E Q
      ∀ (Γ : Subgroup (pi Z).filtration.Group) (mΓ : ℕ) (hmΓ : 0 < mΓ)
        (hinΓ : scaledIntegerGrid mΓ ⊆ bchSubgroupCoordinates (pi Z).basis Γ)
        (houtΓ : bchSubgroupCoordinates (pi Z).basis Γ ⊆ denominatorGrid mΓ),
      let W := (pi Z).withLattice Γ mΓ hmΓ hinΓ houtΓ
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := realification_moduleTopology_t2 (pi Z).basis
      letI := W.metricSpace
      ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → (mΓ : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (I : Type) (inst : Fintype I), letI := inst;
        (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (A : I → ZMod N → ℝ) (label : I → ZMod q),
          (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = label j) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
          ∀ (h : ZMod N) (branch : ι → Fin 2) (η γ : ∀ i, (D i).RealGroup)
            (rSq : ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
            (qSq : ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ i, γ i ∈ (D i).realLattice) →
            (∀ i b, |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((p + 2) ^ k₀)) →
            (∀ i (z : Unit → ℤ),
              (D i).filtration.realSquareFstHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (η i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) (g₀ i) * (γ i)⁻¹ ∧
              (D i).filtration.realSquareSndHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => c i) (g₀ i)) →
            (∀ i, qSq i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)) →
            let G := piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q g qSq)
            ∀ j b x y,
              x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
              0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
              dist (W.cyclicOrbitPoint G N (fun _ : Unit => x))
                (W.cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                  Real.exp ((p + B) ^ B) * ε

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def PrescribedComplementInputPartitionSpec (s k₀ a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) s (e j),
      let Z := sumFactors E Q
      ∀ {L₀ : Type} [LieRing L₀] [LieAlgebra ℚ L₀] {d₀ : ℕ}
        (D₀ : RationalFilteredNilmanifold L₀ s d₀),
      let Z₀ := pi (optionComplementFactors D₀ Z)
      ∀ (Γ : Subgroup Z₀.filtration.Group) (mΓ : ℕ) (hmΓ : 0 < mΓ)
        (hinΓ : scaledIntegerGrid mΓ ⊆ bchSubgroupCoordinates Z₀.basis Γ)
        (houtΓ : bchSubgroupCoordinates Z₀.basis Γ ⊆ denominatorGrid mΓ),
      let W := Z₀.withLattice Γ mΓ hmΓ hinΓ houtΓ
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      let KC := ∀ j : {j : Option (κ ⊕ ι) // j ≠ none}, optionLieSpace L₀ KL j.val
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] KC)
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] KC)
      letI := realification_moduleTopology_t2 Z₀.basis
      letI := W.metricSpace
      ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → W.GeometryComplexityLE p → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (I : Type) (inst : Fintype I), letI := inst;
        (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (A : I → ZMod N → ℝ) (label : I → ZMod q),
          (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = label j) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
          ∀ (h : ZMod N) (branch : ι → Fin 2) (η γ : ∀ i, (D i).RealGroup)
            (rSq : ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
            (qSq : ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ i, γ i ∈ (D i).realLattice) →
            (∀ i b, |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((p + 2) ^ k₀)) →
            (∀ i (z : Unit → ℤ),
              (D i).filtration.realSquareFstHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (η i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) (g₀ i) * (γ i)⁻¹ ∧
              (D i).filtration.realSquareSndHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => c i) (g₀ i)) →
            (∀ i, qSq i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)) →
            let G := piRealOrbit (fun i => ((optionComplementFactors D₀ Z) i).filtration)
              (optionComplementOrbits D₀ Z (sumOrbits E Q g qSq))
            ∀ j b x y,
              x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
              0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
              dist (W.cyclicOrbitPoint G N (fun _ : Unit => x))
                (W.cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                  Real.exp ((p + B) ^ B) * ε

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedPartitionExpansionCore
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def SelectedRefilteredProductExpansionSpec (p : ℝ) (q r : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp cost ∧
    ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
      Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
      Q'.GeometryComplexityLE cost ∧
        ∃ Λ : Subgroup Z₀.filtration.Group, Λ ≤ Z₀.lattice ∧
          (Λ.subgroupOf Z₀.lattice).Characteristic ∧ (Λ.subgroupOf Z₀.lattice).Normal ∧
          (Λ.subgroupOf Z₀.lattice).FiniteIndex ∧ (Λ.relIndex Z₀.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Z₀.basis Λ)
            (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid l),
            let V := Z₀.withLattice Λ l hl hin hout
            V.GeometryComplexityLE cost ∧
            letI := V.metricSpace
            let w := fun _ : Unit => 1
            ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ K : ℝ},
                0 < ρ → 0 ≤ K →
                (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
                (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
                (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                (∀ i x y, 0 < A i x → 0 < A i y →
                  dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                ∀ (S : ZMod N → (D a).Niltest w),
                  (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                  (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                    (∀ j, realifyFunctional (freq j a) z.coord = 0) →
                    ∀ x, (S h).observable (z • x) = (S h).observable x) →
                  ∀ (Hsh : Set (ZMod N)) (g : ZMod N → ∀ i, (D i).filtration.realification.PolynomialOrbit w),
                    (∀ h ∈ Hsh, g h a = (S h).orbit) →
                    ∀ (slow middle rat : ZMod N → ((pi D).filtration.realification.adaptedPolynomialFiltration w).Group)
                      (κ : ZMod N → (pi D).RealGroup),
                      (∀ h ∈ Hsh, κ h ∈ (pi D).realLattice) →
                      (∀ h ∈ Hsh, slow h * middle h * rat h * (pi D).filtration.realification.adaptedConstantGroupHom w (κ h) =
                        ⟨⟨(NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).log,
                          (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).property⟩⟩) →
                      (∀ h ∈ Hsh, (pi D).filtration.PolynomialSlowBound (pi D).basis w
                        (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                      (∀ h ∈ Hsh, (pi D).filtration.PolynomialRationalGrid (pi D).basis w q (rat h)) →
                      (∀ h ∈ Hsh, ∀ α, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
                          (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight w α)) →
                      (∀ h ∈ Hsh, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0) →
                      (∀ i j h, h ∈ Hsh → ∀ x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                        0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                        dist (V.cyclicOrbitPoint
                          (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                            (fun i : I₀ => g h i.val)) N (fun _ : Unit => x))
                          (V.cyclicOrbitPoint
                            (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                              (fun i : I₀ => g h i.val)) N (fun _ : Unit => y)) ≤ K * ρ) →
                      ∃ U : I → J → ZMod N → Q'.Niltest w,
                        (∀ i j h, (U i j h).UnitIntervalValued) ∧
                        (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                        (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                          ∀ x, (U i j h).eval x = 0) ∧
                        ∃ err : ZMod N → ZMod N → ℝ,
                          (∀ h ∈ Hsh, ∀ x, ((S h).evalCyclic N (fun _ => x)).re =
                            (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                          ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

def PrescribedPartitionExpansionSpec (s r b₀ k₀ a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) ((s + 1) + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) (s + 1) (e j),
      let Z := sumFactors E Q
      ∀ {L₀ : Type} [LieRing L₀] [LieAlgebra ℚ L₀] {d₀ : ℕ}
        (D₀ : RationalFilteredNilmanifold L₀ (s + 1) d₀),
      let T := optionFactors D₀ Z
      ∀ (W : LieSubalgebra ℚ (pi T).filtration.AssociatedGraded) {dR dQ : ℕ}
        (R : RationalFilteredNilmanifold ((pi T).filtration.gradedRefiltrationSubalgebra W) (s + 1) dR)
        (Q₀ : RationalFilteredNilmanifold
          (((pi T).filtration.gradedRefiltrationSubalgebra W) ⧸ R.filtration.layerIdeal (s + 1)) s dQ)
        [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)] {p cost : ℝ} (q : ℕ),
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → 0 ≤ cost → cost ≤ (p + b₀) ^ b₀ →
      RefilteredProductExpansionSpec T none W R Q₀ p q r cost →
      let H := (pi T).filtration.gradedRefiltrationSubalgebra W
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
      letI := realification_moduleTopology_t2 Q₀.basis
      ∃ Q' : RationalFilteredNilmanifold (H ⧸ R.filtration.layerIdeal (s + 1)) s dQ,
        Q'.filtration = Q₀.filtration ∧ Q'.basis = Q₀.basis ∧ Q'.lattice ≤ Q₀.lattice ∧
        Q'.GeometryComplexityLE cost ∧
        ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (c : ι → ℤ) (N : ℕ) [NeZero N] {ε : ℝ},
        0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
        ∃ (I : Type) (inst : Fintype I), letI := inst;
          (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : I → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} (s + 1 + 1) N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
            ∀ {J₀ : Type} (freq : J₀ → ∀ i, optionLieSpace L₀
              (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi T).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (S : ZMod N → (T none).Niltest (fun _ : Unit => 1)),
                (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                (∀ h z, z ∈ (T none).filtration.realification.subgroup (s + 1) →
                  (∀ j, realifyFunctional (freq j none) z.coord = 0) →
                  ∀ x, (S h).observable (z • x) = (S h).observable x) →
                ∀ (Hsh : Set (ZMod N))
                  (gT : ZMod N → ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (branch : ZMod N → ι → Fin 2) (η γ : ZMod N → ∀ i, (D i).RealGroup)
                  (rSq : ZMod N → ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (qSq : ZMod N → ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                  (∀ h ∈ Hsh, gT h none = (S h).orbit) →
                  (∀ h ∈ Hsh, ∀ i, gT h (some i) = sumOrbits E Q g (qSq h) i) →
                  (∀ h ∈ Hsh, ∀ i, γ h i ∈ (D i).realLattice) →
                  (∀ h ∈ Hsh, ∀ i j, |((D i).basis.baseChange ℝ).repr (η h i).coord j| ≤
                    Real.exp ((p + 2) ^ k₀)) →
                  (∀ h ∈ Hsh, ∀ i (z : Unit → ℤ),
                    (D i).filtration.realSquareFstHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (η h i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => (h.val : ℤ) - ((branch h i).val : ℤ) * N) (g₀ i) * (γ h i)⁻¹ ∧
                    (D i).filtration.realSquareSndHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => c i) (g₀ i)) →
                  (∀ h ∈ Hsh, ∀ i, qSq h i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
                    ((D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)) (t := s + 1) le_rfl (rSq h i)) →
                  ∀ (slow middle rat : ZMod N →
                      ((pi T).filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group)
                    (δ : ZMod N → (pi T).RealGroup),
                    (∀ h ∈ Hsh, δ h ∈ (pi T).realLattice) →
                    (∀ h ∈ Hsh, slow h * middle h * rat h *
                      (pi T).filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) (δ h) =
                        ⟨⟨(piRealOrbit (fun i => (T i).filtration) (gT h)).log,
                          (piRealOrbit (fun i => (T i).filtration) (gT h)).property⟩⟩) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
                      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialRationalGrid (pi T).basis (fun _ : Unit => 1) q (rat h)) →
                    (∀ h ∈ Hsh, ∀ α, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) α ∈
                        (pi T).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ : Unit => 1) α)) →
                    (∀ h ∈ Hsh, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) 0 = 0) →
                    ∃ U : I → I → ZMod N → Q'.Niltest (fun _ : Unit => 1),
                      (∀ i j h, (U i j h).UnitIntervalValued) ∧
                      (∀ i j h, (U i j h).ComplexityLE ((p + C) ^ C)) ∧
                      (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ε ∧ 0 < A i x * A j (x + h)) →
                        ∀ x, (U i j h).eval x = 0) ∧
                      ∃ err : ZMod N → ZMod N → ℝ,
                        (∀ h ∈ Hsh, ∀ x, ((S h).evalCyclic N (fun _ => x)).re =
                          (∑ i, ∑ j, A i x * A j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                        ∀ h, (𝔼 x, |err h x|) ≤ Real.exp ((p + B) ^ B) * ε + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

def PreparedHigherShiftContradictionSpec (s r b₀ k₀ k Dexp : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) ((s + 1) + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) (s + 1) (e j),
      let Z := sumFactors E Q
      ∀ {L₀ : Type} [LieRing L₀] [LieAlgebra ℚ L₀] {d₀ : ℕ}
        (D₀ : RationalFilteredNilmanifold L₀ (s + 1) d₀),
      let T := optionFactors D₀ Z
      ∀ (W : LieSubalgebra ℚ (pi T).filtration.AssociatedGraded) {dR dQ : ℕ}
        (R : RationalFilteredNilmanifold ((pi T).filtration.gradedRefiltrationSubalgebra W) (s + 1) dR)
        (Q₀ : RationalFilteredNilmanifold
          (((pi T).filtration.gradedRefiltrationSubalgebra W) ⧸ R.filtration.layerIdeal (s + 1)) s dQ)
        [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)] {p cost : ℝ} (q : ℕ),
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → 0 ≤ cost → cost ≤ (p + b₀) ^ b₀ →
      RefilteredProductExpansionSpec T none W R Q₀ p q r cost →
        ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (c : ι → ℤ) (N : ℕ) [NeZero N],
        Odd N → Real.exp ((p + 2) ^ Dexp) ≤ N →
        ∀ (f₁ f₂ weight : ZMod N → ℝ) (sigma delta : ℝ),
          Real.exp (-((p + 2) ^ k)) ≤ sigma → Real.exp (-((p + 2) ^ k)) ≤ delta →
          (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
          (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
          (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
            ∀ {J₀ : Type} (freq : J₀ → ∀ i, optionLieSpace L₀
              (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi T).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (S : ZMod N → (T none).Niltest (fun _ : Unit => 1)),
                (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                (∀ h z, z ∈ (T none).filtration.realification.subgroup (s + 1) →
                  (∀ j, realifyFunctional (freq j none) z.coord = 0) →
                  ∀ x, (S h).observable (z • x) = (S h).observable x) →
                ∀ (Hsh : Finset (ZMod N))
                  (gT : ZMod N → ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (branch : ZMod N → ι → Fin 2) (η γ : ZMod N → ∀ i, (D i).RealGroup)
                  (rSq : ZMod N → ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (qSq : ZMod N → ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                  (∀ h ∈ Hsh, gT h none = (S h).orbit) →
                  (∀ h ∈ Hsh, ∀ i, gT h (some i) = sumOrbits E Q g (qSq h) i) →
                  (∀ h ∈ Hsh, ∀ i, γ h i ∈ (D i).realLattice) →
                  (∀ h ∈ Hsh, ∀ i j, |((D i).basis.baseChange ℝ).repr (η h i).coord j| ≤
                    Real.exp ((p + 2) ^ k₀)) →
                  (∀ h ∈ Hsh, ∀ i (z : Unit → ℤ),
                    (D i).filtration.realSquareFstHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (η h i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => (h.val : ℤ) - ((branch h i).val : ℤ) * N) (g₀ i) * (γ h i)⁻¹ ∧
                    (D i).filtration.realSquareSndHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => c i) (g₀ i)) →
                  (∀ h ∈ Hsh, ∀ i, qSq h i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
                    ((D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)) (t := s + 1) le_rfl (rSq h i)) →
                  ∀ (slow middle rat : ZMod N →
                      ((pi T).filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group)
                    (δ : ZMod N → (pi T).RealGroup),
                    (∀ h ∈ Hsh, δ h ∈ (pi T).realLattice) →
                    (∀ h ∈ Hsh, slow h * middle h * rat h *
                      (pi T).filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) (δ h) =
                        ⟨⟨(piRealOrbit (fun i => (T i).filtration) (gT h)).log,
                          (piRealOrbit (fun i => (T i).filtration) (gT h)).property⟩⟩) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
                      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialRationalGrid (pi T).basis (fun _ : Unit => 1) q (rat h)) →
                    (∀ h ∈ Hsh, ∀ α, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) α ∈
                        (pi T).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ : Unit => 1) α)) →
                    (∀ h ∈ Hsh, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) 0 = 0) →
                    sigma * N ≤ (Hsh.card : ℝ) →
                    CyclicNiltestUpperComparison.{0} (s + 2) N ((p + 2) ^ Dexp)
                      (Real.exp (-((p + 2) ^ Dexp))) f₁ f₂ →
                    (∀ h ∈ Hsh, delta < 𝔼 n,
                      (f₁ n - (1 + epsilon) * f₂ n) * weight (n + h) *
                        ((S h).evalCyclic N (fun _ => n)).re) → False

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CertifiedChartBasisBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

theorem certifiedChartMatrix_budget {ι κ : Type*}
    [Fintype ι] [Fintype κ] (matrix : Matrix ι κ ℚ)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hheight : ∀ i j, rationalLogHeight (matrix i j) ≤ ((p + 2) ^ 2 + 2) ^ 63) :
    (∀ i j, |(matrix i j : ℝ)| ≤ Real.exp (((p + 2) ^ 2 + 2) ^ 63)) ∧
    0 < matrixDenominator matrix ∧
    (matrixDenominator matrix : ℝ) ≤ Real.exp ((p + 2) ^ 254) ∧
    ∀ i j, ∃ z : ℤ, (z : ℝ) = (matrixDenominator matrix : ℝ) * (matrix i j : ℝ) := by
  have hcost : ((p + 2) ^ 2 + 2) ^ 63 ≤ (p + 2) ^ 252 := by
    simpa using shifted_power_budget_le hp 2 63
  refine ⟨fun i j => (rational_abs_real_le_numerator (matrix i j)).trans
    ((rationalLogHeight_le_iff _ _).mp (hheight i j)).1,
    matrixDenominator_pos matrix, ?_, ?_⟩
  · apply matrixDenominator_le_exp_power matrix hp 252 hι hκ
    intro i j
    exact ((rationalLogHeight_le_iff _ _).mp (hheight i j)).2.trans
      (Real.exp_le_exp.mpr hcost)
  · intro i j
    obtain ⟨z, hz⟩ := matrixDenominator_mul_entry_real_integral matrix i j
    exact ⟨z, hz.symm⟩

theorem RationalTaggedConstraintCertificate.exists_certified_chart_basis_budget
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] {X : Type*}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (n : Fin m → ℕ) (Ktag : Submodule ℝ ((Σ j, J j) → ℝ))
      (b : Basis (Σ j, Fin (n j)) ℝ Ktag)
      (matrix : (Σ j, Fin (n j)) → (Σ j, J j) → ℚ) (d : ℕ),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      Fintype.card (Σ j, Fin (n j)) ≤ Fintype.card (Σ j, J j) ∧
      (∀ a x, (b a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ)) ∧
      (∀ a x, x.1 ≠ a.1 → matrix a x = 0) ∧
      (∀ a x, rationalLogHeight (matrix a x) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      (∀ a x, RationalHeightLE (matrix a x) ⌈Real.exp (((p + 2) ^ 2 + 2) ^ 63)⌉₊) ∧
      (∀ a x, |(b a : (Σ j, J j) → ℝ) x| ≤ Real.exp (((p + 2) ^ 2 + 2) ^ 63)) ∧
      d = matrixDenominator matrix ∧ 0 < d ∧
      (d : ℝ) ≤ Real.exp ((p + 2) ^ 254) ∧
      (∀ a x, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (b a : (Σ j, J j) → ℝ) x) ∧
      K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} ∧
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
        (∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K) →
        ∀ v : (Σ j, J j) → ℝ, (∀ j, (fun i => v ⟨j, i⟩) ∈ U j) → v ∈ Ktag := by
  classical
  have hdimTag (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ p := by
    have hcard : Fintype.card (J j) ≤ Fintype.card (Σ j, J j) :=
      Fintype.card_le_of_injective (fun i => (⟨j, i⟩ : Σ j, J j)) sigma_mk_injective
    exact (Nat.cast_le.mpr hcard).trans hdim
  obtain ⟨n, Ktag, b, matrix, hn, hentry, hofftag, hheight, hK, hret⟩ :=
    hcert.exists_bounded_chart_tag_basis hp hdimTag hblocks
  have hcard : Fintype.card (Σ j, Fin (n j)) ≤ Fintype.card (Σ j, J j) := by
    simp only [Fintype.card_sigma, Fintype.card_fin]
    exact Finset.sum_le_sum (fun j _ => hn j)
  obtain ⟨habs, hdpos, hdbound, hgrid⟩ := certifiedChartMatrix_budget matrix hp
    ((Nat.cast_le.mpr hcard).trans hdim) hdim hheight
  refine ⟨n, Ktag, b, matrix, matrixDenominator matrix, hn, hcard, hentry,
    hofftag, hheight, fun a x => rationalHeightLE_ceil_exp (hheight a x),
    ?_, rfl, hdpos, hdbound, ?_, hK, hret⟩
  · intro a x
    rw [hentry]
    exact habs a x
  · intro a x
    rw [hentry]
    exact hgrid a x

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullTaggedRationalRetraction
namespace OAI

section

namespace Erdos3

variable {T S : Type*} [Fintype T] [Fintype S]

theorem rationalMatrix_real_range_eq_coordinateSpan (P : Matrix T S ℚ) :
    LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan (LinearMap.range P.mulVecLin) := by
  rw [Matrix.range_mulVecLin P]
  exact (Matrix.range_mulVecLin (Matrix.of (fun i j => (P i j : ℝ)))).trans
    (realRationalCoordinateSpan_span P.col).symm

theorem rationalMatrix_real_fixes_coordinateSpan
    (P : Matrix T T ℚ) (W : Submodule ℚ (T → ℚ))
    (hfix : ∀ x ∈ W, P.mulVecLin x = x)
    (x : T → ℝ) (hx : x ∈ realRationalCoordinateSpan W) :
    Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x := by
  have hspan : Submodule.span ℚ (Set.range (fun w : W => (w : T → ℚ))) = W := by
    have he : Set.range (fun w : W => (w : T → ℚ)) = (W : Set (T → ℚ)) := by
      ext y
      simp
    rw [he, Submodule.span_eq]
  rw [← hspan, realRationalCoordinateSpan_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      funext i
      have he := congrArg (fun z : T → ℚ => (z i : ℝ)) (hfix w w.property)
      change (∑ j, (P i j : ℝ) * ((w : T → ℚ) j : ℝ)) = ((w : T → ℚ) i : ℝ)
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Rat.cast_sum, Rat.cast_mul] using he
  | zero => exact map_zero _
  | add y z _ _ hey hez => rw [map_add, hey, hez]
  | smul a y _ hey => rw [map_smul, hey]

theorem rationalMatrix_real_retraction
    (P : Matrix T T ℚ) (W : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range P.mulVecLin = W)
    (hfix : ∀ x ∈ W, P.mulVecLin x = x) :
    LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
        realRationalCoordinateSpan W ∧
      ∀ x ∈ realRationalCoordinateSpan W,
        Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x := by
  refine ⟨?_, rationalMatrix_real_fixes_coordinateSpan P W hfix⟩
  rw [rationalMatrix_real_range_eq_coordinateSpan, hrange]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_rational_tag_retraction
    {T I : Type*} [Fintype T] [Fintype I]
    (W : Submodule ℚ (T → ℚ)) (b : Basis I ℚ W)
    {p : ℝ} (hp : 0 ≤ p) (hI : (Fintype.card I : ℝ) ≤ p)
    (hb : ∀ a t, rationalLogHeight ((b a : T → ℚ) t) ≤ p) :
    ∃ P : Matrix T T ℚ,
      LinearMap.range P.mulVecLin = W ∧
      (∀ x ∈ W, P *ᵥ x = x) ∧
      P * P = P ∧
      ∀ i j, rationalLogHeight (P i j) ≤ (p + 2) ^ 8 := by
  classical
  let B : Matrix T I ℚ := fun t a => (b a : T → ℚ) t
  let H := ⌊Real.exp p⌋₊
  have hH : 1 ≤ H := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hp)
  have hHp : (H : ℝ) ≤ Real.exp p := Nat.floor_le (Real.exp_nonneg p)
  have hB : ∀ t a, RationalHeightLE (B t a) H := by
    intro t a
    obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff _ _).mp (hb a t)
    exact ⟨Nat.le_floor hn, Nat.le_floor hd⟩
  have hli : LinearIndependent ℚ B.col :=
    b.linearIndependent.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  obtain ⟨C, hCB, hC⟩ := exists_bounded_rational_left_inverse B hli hH hB
  have hBrange : LinearMap.range B.mulVecLin = W := by
    rw [Matrix.range_mulVecLin]
    change Submodule.span ℚ (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hfix : ∀ x ∈ W, (B * C) *ᵥ x = x := by
    intro x hx
    rw [← hBrange] at hx
    obtain ⟨y, rfl⟩ := hx
    change (B * C) *ᵥ (B *ᵥ y) = B *ᵥ y
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hCB, Matrix.mul_one]
  have hmem : ∀ x, (B * C) *ᵥ x ∈ W := by
    intro x
    rw [← hBrange, ← Matrix.mulVec_mulVec]
    exact ⟨C *ᵥ x, rfl⟩
  refine ⟨B * C, ?_, hfix, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hmem y
    · intro hx
      exact ⟨x, hfix x hx⟩
  · calc
      B * C * (B * C) = B * (C * B) * C := by simp only [Matrix.mul_assoc]
      _ = B * C := by rw [hCB, Matrix.mul_one]
  · have hsolve := rationalSolveHeight_le_budget (Fintype.card I) H hp hI hHp
    have hprod : ((H * rationalSolveHeight (Fintype.card I) H : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ 6) := by
      rw [Nat.cast_mul]
      calc
        _ ≤ Real.exp p * Real.exp ((p + 2) ^ 5) :=
          mul_le_mul hHp hsolve (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp (p + (p + 2) ^ 5) := (Real.exp_add _ _).symm
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hp5 := le_power_budget hp (by decide : 1 ≤ 5)
          calc
            _ ≤ 2 * (p + 2) ^ 5 := by linarith
            _ ≤ (p + 2) * (p + 2) ^ 5 :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = (p + 2) ^ 6 := by ring
    intro i j
    apply rationalLogHeight_le_of_height (rationalHeightLE_matrix_mul B C hB hC i j)
    exact rational_sum_cost_le_exp (Fintype.card I)
      (H * rationalSolveHeight (Fintype.card I) H) hp 6 1 hprod
      (by simpa using hI.trans (show p ≤ p + 2 by linarith))

theorem exists_bounded_real_rational_tag_retraction
    {T I : Type*} [Fintype T] [Fintype I]
    (W : Submodule ℚ (T → ℚ)) (b : Basis I ℚ W)
    {p : ℝ} (hp : 0 ≤ p) (hI : (Fintype.card I : ℝ) ≤ p)
    (hb : ∀ a t, rationalLogHeight ((b a : T → ℚ) t) ≤ p) :
    ∃ P : Matrix T T ℚ,
      LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
        realRationalCoordinateSpan W ∧
      (∀ x ∈ realRationalCoordinateSpan W, (fun i j => (P i j : ℝ)) *ᵥ x = x) ∧
      ∀ i j, rationalLogHeight (P i j) ≤ (p + 2) ^ 8 := by
  obtain ⟨P, hrange, hfix, _, hheight⟩ :=
    exists_bounded_rational_tag_retraction W b hp hI hb
  obtain ⟨hrangeR, hfixR⟩ := rationalMatrix_real_retraction P W hrange hfix
  exact ⟨P, hrangeR, hfixR, hheight⟩

theorem exists_bounded_real_rational_tag_retraction_grid
    {T I : Type*} [Fintype T] [Fintype I]
    (W : Submodule ℚ (T → ℚ)) (b : Basis I ℚ W)
    {p : ℝ} (hp : 0 ≤ p) (hT : (Fintype.card T : ℝ) ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ p)
    (hb : ∀ a t, rationalLogHeight ((b a : T → ℚ) t) ≤ p) :
    ∃ (P : Matrix T T ℚ) (D : ℕ),
      LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
        realRationalCoordinateSpan W ∧
      (∀ x ∈ realRationalCoordinateSpan W, (fun i j => (P i j : ℝ)) *ᵥ x = x) ∧
      (∀ i j, rationalLogHeight (P i j) ≤ (p + 2) ^ 8) ∧
      0 < D ∧ (D : ℝ) ≤ Real.exp ((p + 2) ^ 10) ∧
      (∀ i j, ∃ z : ℤ, (D : ℝ) * (P i j : ℝ) = (z : ℝ)) ∧
      ∀ (l : ℕ) (x : T → ℝ), x ∈ realDenominatorGrid l →
        (fun i j => (P i j : ℝ)) *ᵥ x ∈ realDenominatorGrid (D * l) := by
  obtain ⟨P, hrange, hfix, hheight⟩ :=
    exists_bounded_real_rational_tag_retraction W b hp hI hb
  obtain ⟨_, hpos, hden, hint⟩ := rational_matrix_entry_budget P hp 8 hT hT
    (fun i j => (rationalLogHeight_le_iff _ _).mp (hheight i j))
  exact ⟨P, matrixDenominator P, hrange, hfix, hheight, hpos, hden, hint,
    fun l x hx => real_matrix_denominator_grid P l x hx⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical Matrix

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedRealMatrixProjection
    (P : ∀ j, Matrix (J j) (J j) ℚ) (j : Fin m) :
    (J j → ℝ) →ₗ[ℝ] (J j → ℝ) :=
  Matrix.mulVecLin (fun i a => (P j i a : ℝ))

theorem RationalTaggedConstraintCertificate.exists_bounded_rational_retractions
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    let q := p + ((p + 2) ^ 2 + 2) ^ 63
    ∃ (W : ∀ j, Submodule ℚ (J j → ℚ))
      (P : ∀ j, Matrix (J j) (J j) ℚ) (D : Fin m → ℕ),
      K = {x | ∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ realRationalCoordinateSpan (W j)} ∧
      ∀ j,
        LinearMap.range (fullTaggedRealMatrixProjection J P j) = realRationalCoordinateSpan (W j) ∧
        (∀ x ∈ realRationalCoordinateSpan (W j), fullTaggedRealMatrixProjection J P j x = x) ∧
        (∀ i a, rationalLogHeight (P j i a) ≤ (q + 2) ^ 8) ∧
        0 < D j ∧ (D j : ℝ) ≤ Real.exp ((q + 2) ^ 10) ∧
        (∀ i a, ∃ z : ℤ, (D j : ℝ) * (P j i a : ℝ) = (z : ℝ)) ∧
        ∀ (l : ℕ) (x : J j → ℝ), x ∈ realDenominatorGrid l →
          fullTaggedRealMatrixProjection J P j x ∈ realDenominatorGrid (D j * l) := by
  intro q
  obtain ⟨W, n, b, hn, hb, hK⟩ := hcert.exists_bounded_tag_bases_univ hp hdim hblocks
  have hpq : p ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp.trans hpq
  have hheight : ((p + 2) ^ 2 + 2) ^ 63 ≤ q := by dsimp [q]; linarith
  choose P D hP using fun j => exists_bounded_real_rational_tag_retraction_grid
    (W j) (b j) hq ((hdim j).trans hpq)
    (by simpa only [Fintype.card_fin] using ((Nat.cast_le.mpr (hn j)).trans (hdim j)).trans hpq)
    (fun a i => (hb j a i).trans hheight)
  refine ⟨W, P, D, ?_, hP⟩
  rw [hK]
  ext x
  simp only [Set.mem_ofPred_eq]
  simp_rw [realRationalCoordinateSpan_basis (W _) (b _)]

end Erdos3.VectorPolynomial

end

end OAI

end


