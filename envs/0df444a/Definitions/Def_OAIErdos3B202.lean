-- Prove2me | Definitions.Def_OAIErdos3B202
-- name    : OAIErdos3B202
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T14:50:58.545244+00:00
-- url     : https://prove2.me/theorems/4dcb3749-50bb-4a40-8c36-e50540f537af
-- title:
--   OpenAI Erdős-3 split, definitions bundle 203 of 207
-- statement:
--   Definitions bundle 203 of 207 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B201`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 203 available.
--
--   Modules: `OAI.Erdos3.HasBoundedProductCorrelation`, `OAI.Erdos3.HasBoundedProductCorrelation.mono`, `OAI.Erdos3.NativeBoundedMultidegreeFamily`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.eval`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.mono`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.mono_eval`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.slice`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.slice_complexity`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.slice_eval`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.slice_norm`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.slice_observable`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.slice_orbit_eval`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.toNilcharacter`, `OAI.Erdos3.NativeBoundedMultidegreeFamily.toNilcharacter_eval`, `OAI.Erdos3.NativeCommonDerivativeModels.exists_large_common_observable`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_product_with_bounded_family`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_reflected_factor_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_reflected_pair_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.reflected_pair_target_unit`, `OAI.Erdos3.NativeRankRelation.CommonData.HasCommonInducedCorrelationFamily.combineLower`, `OAI.Erdos3.NativeRankRelation.CommonData.HasCoveredInducedCorrelationFamily.combineLower`, `OAI.Erdos3.NativeRankRelation.CommonData.HasUnitRankInducedCorrelationFamily`, `OAI.Erdos3.NativeRankRelation.CommonData.HasUnitRankInducedCorrelationFamily.combineMixed`, `OAI.Erdos3.NativeTwoVariableSplit.second_eval_eq_degree_one`, `OAI.Erdos3.NativeUnitRankFamily.toVerticalFamily`, `OAI.Erdos3.NativeUnitRankFamily.toVerticalFamily_eval`, `OAI.Erdos3.NativeUnitRankFamily.withOrbit_eval`, `OAI.Erdos3.NativeUnitRankFamily.withOrbit_observable`, `OAI.Erdos3.NativeVectorCorrelation.exists_combined_factor_correlation`, `OAI.Erdos3.PositiveShiftBasis.FactoredPositiveShiftContradictionSpec`, `OAI.Erdos3.PositiveShiftBasis.NativeDetectorContradictionSpec`, `OAI.Erdos3.PositiveShiftBasis.NativePartnerContradictionSpec`, `OAI.Erdos3.PositiveShiftBasis.NativePartnerPairContradictionSpec`, `OAI.Erdos3.PositiveShiftBasis.PrescribedCommonFactorizationSpec`, `OAI.Erdos3.PositiveShiftBasis.TwoSiteModelContradictionSpec`, `OAI.Erdos3.QuadraticMarked.affineCoefficient`, `OAI.Erdos3.QuadraticMarked.affineElement`, `OAI.Erdos3.QuadraticMarked.affineElement_phase`, `OAI.Erdos3.QuadraticMarked.centeredElement`, `OAI.Erdos3.QuadraticMarked.centeredElement_phase`, `OAI.Erdos3.QuadraticMarked.centeredElement_retraction_coord`, `OAI.Erdos3.QuadraticMarked.latticeCorrection`, `OAI.Erdos3.QuadraticMarked.latticeCorrection_mem`, `OAI.Erdos3.QuadraticMarked.localCharacter_centeredElement`, `OAI.Erdos3.QuadraticMarked.localOrbit`, `OAI.Erdos3.QuadraticMarked.localOrbit_eval`, `OAI.Erdos3.QuadraticMarked.localOrbit_observable`, `OAI.Erdos3.QuadraticMarked.localOrbit_quotient`, `OAI.Erdos3.QuadraticMarked.localOrbit_right_normalization`, `OAI.Erdos3.QuadraticMarked.parameter`, `OAI.Erdos3.QuadraticMarked.parameter_inv`, `OAI.Erdos3.QuadraticMarked.parameter_mul`, `OAI.Erdos3.QuadraticMarked.projectedLift`, `OAI.Erdos3.QuadraticMarked.projectedLift_mem`, `OAI.Erdos3.QuadraticMarked.projectedLift_phase`, `OAI.Erdos3.QuadraticMarked.projectedLift_pure`, `OAI.Erdos3.QuadraticMarked.pureOrbit`, `OAI.Erdos3.QuadraticMarked.pureOrbit_eval`, `OAI.Erdos3.QuadraticMarked.seedCoordinate`, `OAI.Erdos3.QuadraticMarked.seedCoordinate_seedVector`, `OAI.Erdos3.QuadraticMarked.seedVector`, `OAI.Erdos3.QuadraticMarked.seedVector_mem`, `OAI.Erdos3.QuadraticMarked.shiftedLift_coordinate`, `OAI.Erdos3.QuadraticMarked.sourceLift`, `OAI.Erdos3.QuadraticMarked.sourceLift_eval`, `OAI.Erdos3.QuadraticMarked.sourceLift_shift_coordinate`, `OAI.Erdos3.RationalFilteredNilmanifold.HasBoundedBinaryMultidegreeFamily`, `OAI.Erdos3.RationalFilteredNilmanifold.SquareModelData.fullModel`, `OAI.Erdos3.RationalFilteredNilmanifold.SquareModelData.quotientModel`, `OAI.Erdos3.RationalFilteredNilmanifold.SquareModelData.recOn`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.exists_cyclic_second_difference_models_degree`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.exists_univariate_cyclic_difference_models`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_bounded_binary_multidegree_family`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_bounded_multidegree_product_family`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_common_observable_correlators`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_common_unit_vertical_correlators`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_common_vertical_correlators`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_differenced_rows_degree`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_two_factor_unit_replacement`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_unit_factor_replacement`, `OAI.Erdos3.RationalFilteredNilmanifold.piMultidegree`, `OAI.Erdos3.RationalFilteredNilmanifold.piMultidegree_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.productMultidegreeLayerBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.productMultidegreeLayerBasis_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.productMultidegreeLayerFinBasis`, `OAI.Erdos3.exists_absorb_linear_error`, `OAI.Erdos3.exists_differenced_scalar_expansions`, `OAI.Erdos3.exists_integer_antisymmetric_correlation`, `OAI.Erdos3.exists_iterated_native_derivative_correlations`, `OAI.Erdos3.exists_linear_separated_approximation`, `OAI.Erdos3.exists_many_native_derivative_correlations`, `OAI.Erdos3.exists_native_common_derivative_models`, `OAI.Erdos3.exists_native_correlation_of_sliced_unit_products`, `OAI.Erdos3.exists_native_correlation_of_unit_products`, `OAI.Erdos3.exists_native_derivative_correlators`, `OAI.Erdos3.exists_native_fixed_product_unit_data`, `OAI.Erdos3.exists_native_fixed_product_verticalization`, `OAI.Erdos3.exists_native_mixed_of_bounded`, `OAI.Erdos3.exists_native_product_verticalization`, `OAI.Erdos3.exists_native_sliced_product_correlation`, `OAI.Erdos3.exists_native_vertical_derivative_models`, `OAI.Erdos3.exists_normalized_native_inverse_models`, `OAI.Erdos3.exists_vertical_native_inverse_models`, `OAI.Erdos3.mean_mul_error_le_separate`, `OAI.Erdos3.mean_row_correlation_sq_le_approximated_derivatives`, `OAI.Erdos3.mean_row_correlation_sq_le_derivative_correlation`, `OAI.Erdos3.mean_row_correlation_sq_le_product_derivatives`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B203

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDetectorContradictionSpec
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.PositiveShiftBasis

open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure SquareModelData (D : RationalFilteredNilmanifold L (s + 1) d) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  layers : ∀ i, D.filtration.layer i = Submodule.span ℚ (basis '' {j | i ≤ weight j})
  grid : ℕ
  grid_pos : 0 < grid
  inner : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates
    (D.filtration.squareFinBasis basis weight (layers 2)) (D.filtration.squareLattice D.lattice)
  outer : bchSubgroupCoordinates (D.filtration.squareFinBasis basis weight (layers 2))
    (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid grid

namespace SquareModelData

variable {D : RationalFilteredNilmanifold L (s + 1) d}

noncomputable def fullModel (F : D.SquareModelData) :=
  D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis F.basis F.weight (F.layers 2)) (squareFinWeight F.weight)
    (D.filtration.squareFinBasis_layers F.basis F.weight F.layers)
    (D.filtration.squareLattice D.lattice) F.grid F.grid_pos F.inner F.outer

noncomputable def quotientModel (F : D.SquareModelData) :=
  D.filtration.squareFiltration.topQuotientModel
    (D.filtration.squareFinBasis F.basis F.weight (F.layers 2)) (squareFinWeight F.weight)
    (D.filtration.squareFinBasis_layers F.basis F.weight F.layers)
    (D.filtration.squareLattice D.lattice) F.grid F.grid_pos F.inner F.outer

end SquareModelData
end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators NNReal

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def PrescribedCommonFactorizationSpec (s C : ℕ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {L : (Fin B.count × Bool) → Type u}
        [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Fin B.count × Bool) → ℕ}
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
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
        (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (H : Finset (ZMod N)),
      H ⊆ B.shifts → ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (T i).normBound ≤ 1) →
      ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (T (j, true)).evalCyclic N (fun _ => n) *
          (T (j, false)).evalCyclic N (fun _ => n + h)‖) →
      Real.exp ((p + C) ^ C) ≤ N →
      ∃ F : ∀ i, (D i).SquareModelData,
        (∀ i, (F i).fullModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i, (F i).quotientModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i j k, rationalLogHeight ((D i).basis.repr ((F i).basis j) k) ≤ (p + C) ^ C) ∧
        ∃ h₀ ∈ H, ∃ branches : Fin B.count → Bool × Bool,
          ∃ (A : ∀ j, (F (j, true)).quotientModel.Niltest (fun _ : Unit => 1))
            (R : ZMod N → ∀ j, (F (j, false)).quotientModel.Niltest (fun _ : Unit => 1))
            (η γ : ZMod N → ∀ j, (D (j, false)).RealGroup)
            (rSq : ZMod N → ∀ j,
              (D (j, false)).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ j, (A j).normBound ≤ 1 ∧ (A j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (A j).eval x = (T (j, true)).eval x * star ((T (j, true)).eval x)) ∧
            (∀ h j, γ h j ∈ (D (j, false)).realLattice ∧
              (∀ i, |((D (j, false)).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (∀ x : Unit → ℤ,
                (D (j, false)).filtration.realSquareFstHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (η h j)⁻¹ * (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h (branches j).1) (T (j, false)).orbit * (γ h j)⁻¹ ∧
                (D (j, false)).filtration.realSquareSndHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h₀ (branches j).2) (T (j, false)).orbit) ∧
              (R h j).orbit = (D (j, false)).filtration.squareFiltration.realQuotientPolynomialOrbit
                ((D (j, false)).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq h j) ∧
              (R h j).normBound ≤ 1 ∧ (R h j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (R h j).eval x =
                (T (j, false)).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
                  star ((T (j, false)).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2))) ∧
            Nonempty (B.CommonFactorization (fun j => (F (j, true)).quotientModel)
              (fun j => (F (j, false)).quotientModel) A R h₀ H ((p + C) ^ C))

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

def FactoredPositiveShiftContradictionSpec (s Dexp : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
      {L M : Fin B.count → Type}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
      [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
      (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1 + 1) (e j))
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, T2Space (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      [∀ j, T2Space (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      (Y : ∀ j, (E j).SquareModelData)
      (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
      (R : ZMod N → ∀ j, (Y j).quotientModel.Niltest (fun _ : Unit => 1))
      (anchor : ZMod N) (H : Finset (ZMod N)) {p : ℝ}
      (F : B.CommonFactorization D (fun j => (Y j).quotientModel) A R anchor H p),
      H ⊆ B.shifts → 2 ≤ p → q ≤ p →
      (∀ j, (D j).GeometryComplexityLE p) → (∀ j, (E j).GeometryComplexityLE p) →
      (∀ j, (Y j).fullModel.GeometryComplexityLE p) →
      (∀ j, (Y j).quotientModel.GeometryComplexityLE p) →
      (∀ j i k, rationalLogHeight ((E j).basis.repr ((Y j).basis i) k) ≤ p) →
      ∀ (g₀ : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (branches : Fin B.count → Bool × Bool)
        (η γ : ZMod N → ∀ j, (E j).RealGroup)
        (rSq : ZMod N → ∀ j,
          (E j).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
        (∀ h ∈ F.shifts, ∀ j, γ h j ∈ (E j).realLattice) →
        (∀ h ∈ F.shifts, ∀ j i, |((E j).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp p) →
        (∀ h ∈ F.shifts, ∀ j (x : Unit → ℤ),
          (E j).filtration.realSquareFstHom
            ((E j).filtration.squareFiltration.realification.polynomialOrbitEval
              (fun _ => 1) x (rSq h j)) =
              (η h j)⁻¹ * (E j).filtration.realification.polynomialOrbitEval (fun _ => 1)
                (x + fun _ => cyclicBranchOffset h (branches j).1) (g₀ j) * (γ h j)⁻¹ ∧
          (E j).filtration.realSquareSndHom
            ((E j).filtration.squareFiltration.realification.polynomialOrbitEval
              (fun _ => 1) x (rSq h j)) =
              (E j).filtration.realification.polynomialOrbitEval (fun _ => 1)
                (x + fun _ => cyclicBranchOffset anchor (branches j).2) (g₀ j)) →
        (∀ h ∈ F.shifts, ∀ j, (R h j).orbit =
          (E j).filtration.squareFiltration.realQuotientPolynomialOrbit
            ((E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)) (t := s + 1) le_rfl (rSq h j)) →
        Odd N → Real.exp ((productExpansionBudget p + 2) ^ Dexp) ≤ N →
        (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
        (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
        (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
        CyclicNiltestUpperComparison.{0} (s + 2) N ((productExpansionBudget p + 2) ^ Dexp)
          (Real.exp (-((productExpansionBudget p + 2) ^ Dexp))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def NativePartnerContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight) (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {L : (Fin B.count × Bool) → Type}
        [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Fin B.count × Bool) → ℕ}
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
        (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1 + 1) (d i))
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (H : Finset (ZMod N)),
      H ⊆ B.shifts → ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (T i).normBound ≤ 1) →
      ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1 + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (T (j, true)).evalCyclic N (fun _ => n) *
          (T (j, false)).evalCyclic N (fun _ => n + h)‖) →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def NativePartnerPairContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
      (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {L M : Fin B.count → Type}
        [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
        [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
        [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
        [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
        [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
        [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
        (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1 + 1) (d j))
        (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1 + 1) (e j))
        (V : ∀ j, (D j).Niltest (fun _ : Unit => 1))
        (W : ∀ j, (E j).Niltest (fun _ : Unit => 1)) (H : Finset (ZMod N)),
      H ⊆ B.shifts → ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ j, (V j).ComplexityLE p) → (∀ j, (W j).ComplexityLE p) →
      (∀ j, (V j).normBound ≤ 1) → (∀ j, (W j).normBound ≤ 1) →
      ∀ (χ : ∀ j, (D j).RealGroup → CircleFourier.Circle)
        (χ' : ∀ j, (E j).RealGroup → CircleFourier.Circle),
      (∀ j z, z ∈ (D j).filtration.realification.subgroup (s + 1 + 1) → ∀ x,
        (V j).observable (z • x) = character (χ j z) * (V j).observable x) →
      (∀ j z, z ∈ (E j).filtration.realification.subgroup (s + 1 + 1) → ∀ x,
        (W j).observable (z • x) = character (χ' j z) * (W j).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (V j).evalCyclic N (fun _ => n) *
          (W j).evalCyclic N (fun _ => n + h)‖) →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def TwoSiteModelContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
      (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {I : Type} {K : I → Type} [Fintype I] [∀ i, Fintype (K i)]
        {L : I → Type} {M : ∀ i, K i → Type}
        [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
        [∀ i k, LieRing (M i k)] [∀ i k, LieAlgebra ℚ (M i k)]
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
        [∀ i k, TopologicalSpace (ℝ ⊗[ℚ] M i k)] [∀ i k, IsTopologicalAddGroup (ℝ ⊗[ℚ] M i k)]
        [∀ i k, ContinuousSMul ℝ (ℝ ⊗[ℚ] M i k)] [∀ i k, T2Space (ℝ ⊗[ℚ] M i k)]
        {d : I → ℕ} {e : ∀ i, K i → ℕ}
        (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1 + 1) (d i))
        (E : ∀ i k, RationalFilteredNilmanifold (M i k) (s + 1 + 1) (e i k))
        (Q : ∀ i, (D i).Niltest (fun _ : Unit => 1))
        (R : ∀ i k, (E i k).Niltest (fun _ : Unit => 1))
        (ea : ZMod N → ℂ) (eb : I → ZMod N → ℂ) (c : I → ℂ) (b : ∀ i, K i → ℂ),
      (∀ n, ((f₁ n - (1 + epsilon) * f₂ n : ℝ) : ℂ) =
        (∑ i, c i * (Q i).evalCyclic N (fun _ => n)) + ea n) →
      (∀ i n, (weight n : ℂ) = (∑ k, b i k * (R i k).evalCyclic N (fun _ => n)) + eb i n) →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p →
      (∑ i, ‖c i‖) ≤ Real.exp p → (∀ i, (∑ k, ‖b i k‖) ≤ Real.exp p) →
      (∀ i, (Q i).ComplexityLE p) → (∀ i k, (R i k).ComplexityLE p) →
      (∀ i, (Q i).normBound ≤ 1) → (∀ i k, (R i k).normBound ≤ 1) →
      (shiftTestingSeminorm (fun n => (weight n : ℂ)) B.testingFamily ea +
        ∑ i, ‖c i‖ * shiftTestingSeminorm (fun n => (Q i).evalCyclic N (fun _ => n))
          (translatedTestFamily B.testingFamily) (eb i) ≤ Real.exp (-(2 * q + 2))) →
      (Fintype.card (Sigma K) : ℝ) ≤ Real.exp p →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def NativeDetectorContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
  ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
    (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
    (w : Fin B.dim → ℕ),
    (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
    ∀ {p p₁ p₂ K M beta₁ beta₂ : ℝ},
      2 ≤ p → 2 ≤ p₁ → 2 ≤ p₂ → q ≤ p → p₁ ≤ p → p₂ ≤ p →
      0 < K → 0 < M → 0 < beta₁ → 0 < beta₂ →
      (∀ n, ‖((f₁ n - (1 + epsilon) * f₂ n : ℝ) : ℂ)‖ ≤ M) →
      (∀ n, ‖(weight n : ℂ)‖ ≤ K) →
      2 / beta₁ ≤ Real.exp p → 2 / beta₂ ≤ Real.exp p →
      let eta := Real.exp (-(2 * q + 2))
      (1 + 4 * K ^ 2 / (beta₁ ^ 2 * (eta / 4) ^ 2)) *
        (1 + 4 / (beta₂ ^ 2 * (eta * beta₁ / 8) ^ 2)) ≤ Real.exp p →
      NativeModelDetector (s + 1 + 1) N p₁
        (shiftTestingSeminorm (fun n => (weight n : ℂ)) B.testingFamily) K M beta₁ (eta / 4) →
      (∀ f ∈ nativeCyclicFunctions (s + 1 + 1) N p₁,
        NativeModelDetector (s + 1 + 1) N p₂
          (shiftTestingSeminorm f (translatedTestFamily B.testingFamily))
          1 K beta₂ (eta * beta₁ / 8)) →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeIteratedDifferencing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mean_row_correlation_sq_le_derivative_correlation {H G : Type*}
    [Fintype H] [Nonempty H] [AddCommGroup G] [Fintype G]
    (f g : H → G → ℂ) :
    (𝔼 h, ‖𝔼 n, f h n * star (g h n)‖) ^ 2 ≤
      𝔼 k, 𝔼 h, ‖𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)‖ := by
  let F (h : H) (n : G) := f h n * star (g h n)
  have hid (h : H) :
      (𝔼 k, 𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)).re =
          ‖𝔼 n, f h n * star (g h n)‖ ^ 2 := by
    have heq (k n : G) : crossDerivative (F h) (F h) k n =
        multiplicativeDerivative (f h) k n * star (multiplicativeDerivative (g h) k n) := by
      simp only [crossDerivative, multiplicativeDerivative, F, star_mul, star_star]
      ring
    have hh := congrArg Complex.re (expect_crossDerivative (F h) (F h))
    simpa only [heq, mul_star_re_eq_norm_sq, F] using hh
  have hrow (h : H) : ‖𝔼 n, f h n * star (g h n)‖ ^ 2 ≤
      𝔼 k, ‖𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)‖ := by
    rw [← hid h, expect_re]
    exact Finset.expect_le_expect (fun k _ => Complex.re_le_norm _)
  calc
    _ ≤ 𝔼 h, ‖𝔼 n, f h n * star (g h n)‖ ^ 2 := expect_square_le _
    _ ≤ 𝔼 h, 𝔼 k, ‖𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)‖ :=
      Finset.expect_le_expect (fun h _ => hrow h)
    _ = _ := Finset.expect_comm _ _ _

theorem mean_row_correlation_sq_le_approximated_derivatives {H G : Type*}
    [Fintype H] [Nonempty H] [AddCommGroup G] [Fintype G]
    (f g : H → G → ℂ) (K : G → H → G → ℂ) (hf : ∀ h n, ‖f h n‖ ≤ 1)
    {ε : ℝ} (herr : ∀ k h, (𝔼 n, ‖multiplicativeDerivative (g h) k n - K k h n‖) ≤ ε) :
    (𝔼 h, ‖𝔼 n, f h n * star (g h n)‖) ^ 2 ≤
      (𝔼 k, 𝔼 h, ‖𝔼 n, multiplicativeDerivative (f h) k n * star (K k h n)‖) + ε := by
  have hrow (k : G) (h : H) :
      ‖𝔼 n, multiplicativeDerivative (f h) k n * star (multiplicativeDerivative (g h) k n)‖ ≤
        ‖𝔼 n, multiplicativeDerivative (f h) k n * star (K k h n)‖ + ε := by
    have hfn (n : G) : ‖multiplicativeDerivative (f h) k n‖ ≤ 1 := by
      rw [multiplicativeDerivative, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf h n)).trans (hf h (n + k))
    have he := (norm_correlation_sub_le_mean (multiplicativeDerivative (f h) k)
      (multiplicativeDerivative (g h) k) (K k h) hfn).trans (herr k h)
    have ht := norm_le_norm_add_norm_sub
      (𝔼 n, multiplicativeDerivative (f h) k n * star (K k h n))
      (𝔼 n, multiplicativeDerivative (f h) k n * star (multiplicativeDerivative (g h) k n))
    rw [norm_sub_rev] at ht
    linarith
  apply (mean_row_correlation_sq_le_derivative_correlation f g).trans
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun k _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun h _ => hrow k h))
  simpa only [Finset.expect_add_distrib, Fintype.expect_const] using hm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mean_mul_error_le_separate {X : Type*} [Fintype X]
    (u v U V : X → ℂ) {B ε δ : ℝ} (hB : 0 ≤ B)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hU : ∀ x, ‖U x‖ ≤ B)
    (huerr : (𝔼 x, ‖u x - U x‖) ≤ ε) (hverr : (𝔼 x, ‖v x - V x‖) ≤ δ) :
    (𝔼 x, ‖u x * v x - U x * V x‖) ≤ ε + B * δ := by
  have hpoint (x : X) :
      ‖u x * v x - U x * V x‖ ≤ ‖u x - U x‖ + B * ‖v x - V x‖ := by
    calc
      _ = ‖(u x - U x) * v x + U x * (v x - V x)‖ := by congr 1; ring
      _ ≤ ‖u x - U x‖ * ‖v x‖ + ‖U x‖ * ‖v x - V x‖ := by
        simpa only [norm_mul] using norm_add_le ((u x - U x) * v x) (U x * (v x - V x))
      _ ≤ _ := add_le_add (mul_le_of_le_one_right (norm_nonneg _) (hv x))
        (mul_le_mul_of_nonneg_right (hU x) (norm_nonneg _))
  calc
    _ ≤ 𝔼 x, (‖u x - U x‖ + B * ‖v x - V x‖) :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = (𝔼 x, ‖u x - U x‖) + B * (𝔼 x, ‖v x - V x‖) := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect]
    _ ≤ _ := add_le_add huerr (mul_le_mul_of_nonneg_left hverr hB)

theorem mean_row_correlation_sq_le_product_derivatives {H G : Type*}
    [Fintype H] [Nonempty H] [AddCommGroup G] [Fintype G]
    (f u v : H → G → ℂ) (U V : G → H → G → ℂ) {B ε δ : ℝ}
    (hf : ∀ h n, ‖f h n‖ ≤ 1) (hv : ∀ h n, ‖v h n‖ ≤ 1) (hB : 0 ≤ B)
    (hU : ∀ k h n, ‖U k h n‖ ≤ B)
    (huerr : ∀ k h, (𝔼 n, ‖multiplicativeDerivative (u h) k n - U k h n‖) ≤ ε)
    (hverr : ∀ k h, (𝔼 n, ‖multiplicativeDerivative (v h) k n - V k h n‖) ≤ δ) :
    (𝔼 h, ‖𝔼 n, f h n * star (u h n * v h n)‖) ^ 2 ≤
      (𝔼 k, 𝔼 h, ‖𝔼 n, multiplicativeDerivative (f h) k n * star (U k h n * V k h n)‖) +
        (ε + B * δ) := by
  apply mean_row_correlation_sq_le_approximated_derivatives f
    (fun h n => u h n * v h n) (fun k h n => U k h n * V k h n) hf
  intro k h
  have heq : multiplicativeDerivative (fun n => u h n * v h n) k =
      fun n => multiplicativeDerivative (u h) k n * multiplicativeDerivative (v h) k n := by
    funext n
    simp only [multiplicativeDerivative, star_mul]
    ring
  rw [heq]
  apply mean_mul_error_le_separate _ _ _ _ hB _ (hU k h) (huerr k h) (hverr k h)
  intro n
  simp only [multiplicativeDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hv h n)).trans (hv h (n + k))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_cyclic_second_difference_models_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p e : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Fin 2 => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (i j : I) (k : ZMod N), ∃ K : (Fin 2 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + e + C) ^ C) K) ∧
        ∀ h : ℤ, (𝔼 n : ZMod N,
          ‖cyclicSecondDifference (V.test g i).eval (V.test g j).eval k h n -
            K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, htranslate⟩ := exists_integer_translation_equivalence_budget s
  obtain ⟨B, _, happrox⟩ := exists_cyclicSecondDifference_approximation_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d D p e V g hp hD hI he N _ hN i j k
  let r := (p + A) ^ A
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hmodels (t : ℤ) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r
      (integerSecondDifference (V.test g i).eval (V.test g j).eval t)) := by
    have E := (htranslate D V g hp hD hI 0 ![0, t]).expansion i j
    change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r
      (fun x => (V.test g i).eval (x + 0) * star ((V.test g j).eval (x + ![0, t])))) at E
    have hshift (x : Fin 2 → ℤ) : x + ![0, t] = ![x 0, x 1 + t] := by
      funext a
      fin_cases a <;> simp
    change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r
      (fun x => (V.test g i).eval x * star ((V.test g j).eval ![x 0, x 1 + t])))
    simpa only [add_zero, hshift] using E
  have hcost : (r + e + B) ^ B ≤ (p + e + C) ^ C := by
    have hbase : r ≤ (p + e + A) ^ A := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hb : ((p + e + A) ^ A + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget (p + e) (by linarith)
    exact (pow_le_pow_left₀ (by positivity) (by linarith) B).trans hb
  obtain ⟨K, ⟨E⟩, herr⟩ := happrox hr he hN (V.test g i).eval (V.test g j).eval
    (fun x => (V.test g i).norm_eval_le x) (fun x => (V.test g j).norm_eval_le x) hmodels k
  exact ⟨K, ⟨E.mono hcost⟩, herr⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_differenced_rows_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ZMod N → ℂ, (∀ h n, ‖f h n‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        f h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ K : ZMod N → (Fin 2 → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + C) ^ C) (K k))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          multiplicativeDerivative (f h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
  obtain ⟨A, _, hunit⟩ := exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, hcyclic⟩ := UnitVerticalObservable.exists_cyclic_second_difference_models_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * Q + 2 + Polynomial.C B) ^ B + 3 * Q + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f hf hcorr
  classical
  let q := (p + A) ^ A
  let e := 2 * q + 2
  let r := (3 * q + 2 + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : r + 3 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have heC : e ≤ (p + C) ^ C := by dsimp [e]; linarith
  have hN' : Real.exp (e + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by dsimp [e]; linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D T hp hT
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)]) f hf hcorr
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r K) ∧
      ∀ h : ℤ, (𝔼 n : ZMod N,
        ‖cyclicSecondDifference (V.test T.orbit 0).eval (V.test T.orbit 0).eval k h n -
          K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
    have hh := hcyclic D V T.orbit hq hD hcard he hN' 0 0 k
    have hbudgeteq : ((p + A) ^ A + e + B) ^ B = r := by
      change (q + e + B) ^ B = (3 * q + 2 + B) ^ B
      congr 1
      dsimp [e]
      ring
    simpa only [hbudgeteq] using hh
  choose K hK herror using hmodels
  let g (h n : ZMod N) := (V.test T.orbit 0).eval ![(h.val : ℤ), (n.val : ℤ)]
  have hd := mean_row_correlation_sq_le_approximated_derivatives f g
    (fun k h n => K k ![(h.val : ℤ), (n.val : ℤ)]) hf
    (ε := Real.exp (-e)) (by
      intro k h
      simpa only [g, multiplicativeDerivative, cyclicSecondDifference] using herror k h.val)
  have hlarge : Real.exp (-(2 * q)) ≤
      (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        multiplicativeDerivative (f h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) +
          Real.exp (-e) := by
    have hsquare := (pow_le_pow_left₀ (Real.exp_nonneg (-q)) hVcorr 2).trans hd
    have hexp : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rwa [hexp] at hsquare
  have htwo : 2 * Real.exp (-e) ≤ Real.exp (-(2 * q)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-e) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
  refine ⟨K, fun k => ⟨(Classical.choice (hK k)).mono hrC⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg heC)).trans
  linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_differenced_scalar_expansions (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (T : D.Niltest (fun _ : Unit => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 n, f n * star (T.evalCyclic N (fun _ => n))‖ →
      ∃ K : ZMod N → (Unit → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + C) ^ C) (K k))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k : ZMod N, ‖𝔼 n : ZMod N,
          multiplicativeDerivative f k n * star (K k (fun _ => (n.val : ℤ)))‖) := by
  obtain ⟨A, _, hunit⟩ := RationalFilteredNilmanifold.exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, hcyclic⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_cyclic_second_difference_models_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * Q + 2 + Polynomial.C B) ^ B + 3 * Q + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f hf hcorr
  classical
  let projection : Unit → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let U := T.linearPullbackHom projection
  have hU (n : ZMod N) : U.eval ![0, (n.val : ℤ)] = T.evalCyclic N (fun _ => n) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
    rfl
  let q := (p + A) ^ A
  let e := 2 * q + 2
  let r := (3 * q + 2 + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : r + 3 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have heC : e ≤ (p + C) ^ C := by dsimp [e]; linarith
  have hN' : Real.exp (e + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by dsimp [e]; linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D U hp hT
    (fun (_ : Unit) (n : ZMod N) => ![0, (n.val : ℤ)]) (fun _ => f) (fun _ => hf)
    (by simpa only [hU, Fintype.expect_const] using hcorr)
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r K) ∧
      (𝔼 n : ZMod N, ‖cyclicSecondDifference (V.test U.orbit 0).eval
        (V.test U.orbit 0).eval k 0 n - K ![0, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
    obtain ⟨K, hK, herr⟩ := hcyclic D V U.orbit hq hD hcard he hN' 0 0 k
    have hbudgeteq : ((p + A) ^ A + e + B) ^ B = r := by
      change (q + e + B) ^ B = (3 * q + 2 + B) ^ B
      congr 1
      dsimp [e]
      ring
    exact ⟨K, by simpa only [hbudgeteq] using hK, herr 0⟩
  choose K hK herror using hmodels
  let embedding : Fin 2 → ((Unit → ℤ) →+ ℤ) := fun j =>
    if j = 0 then 0 else
      { toFun := fun x => x (), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hemb (x : Unit → ℤ) : (fun j => embedding j x) = ![0, x ()] := by
    funext j
    fin_cases j <;> simp [embedding]
  let g (n : ZMod N) := (V.test U.orbit 0).eval ![0, (n.val : ℤ)]
  have hc : Real.exp (-q) ≤ ‖𝔼 n : ZMod N, f n * star (g n)‖ := by
    simpa only [Fintype.expect_const] using hVcorr
  have hd := mean_row_correlation_sq_le_approximated_derivatives
    (fun _ : Unit => f) (fun _ : Unit => g)
    (fun k _ n => K k ![0, (n.val : ℤ)]) (fun _ => hf)
    (ε := Real.exp (-e)) (by
      intro k _
      simpa only [g, multiplicativeDerivative, cyclicSecondDifference] using herror k)
  simp only [Fintype.expect_const] at hd
  have hlarge : Real.exp (-(2 * q)) ≤
      (𝔼 k : ZMod N, ‖𝔼 n : ZMod N,
        multiplicativeDerivative f k n * star (K k ![0, (n.val : ℤ)])‖) + Real.exp (-e) := by
    have hsq := (pow_le_pow_left₀ (Real.exp_nonneg (-q)) hc 2).trans hd
    have hexp : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rwa [hexp] at hsq
  have htwo : 2 * Real.exp (-e) ≤ Real.exp (-(2 * q)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-e) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
  refine ⟨fun k x => K k ![0, x ()], ?_, ?_⟩
  · intro k
    have E := ((Classical.choice (hK k)).linearPullbackHom embedding).mono hrC
    simpa only [hemb] using (show Nonempty _ from ⟨E⟩)
  · apply (Real.exp_le_exp.mpr (neg_le_neg heC)).trans
    linarith

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_many_native_derivative_correlations (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      Nonempty (NativeVectorCorrelation (s + 1) N p (fun _ : Unit => f)) →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∀ h ∈ H, Nonempty (NativeVectorCorrelation s N ((p + C) ^ C)
          (fun _ : Unit => multiplicativeDerivative f h)) := by
  obtain ⟨A, _, hdifference⟩ := exists_differenced_scalar_expansions s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * Q + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf ⟨V⟩
  classical
  let q := (p + A) ^ A
  let t := 3 * q + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htotal : 4 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by dsimp [t]; linarith
  have htqC : t + q ≤ (p + C) ^ C := by dsimp [t]; linarith
  obtain ⟨K, hK, hmean⟩ := hdifference V.model V.test hp V.complexity
    ((Real.exp_le_exp.mpr hqC).trans hN) f hf V.correlation
  let c (k : ZMod N) := ‖𝔼 n : ZMod N,
    multiplicativeDerivative f k n * star (K k (fun _ => (n.val : ℤ)))‖
  let z (k : ZMod N) := Real.exp (-(2 * q)) * c k
  have hcap (k : ZMod N) : c k ≤ Real.exp (2 * q) := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (multiplicativeDerivative_norm_le_one f hf k n)).trans
        ((Classical.choice (hK k)).norm_eval_le _)
  have hzcap (k : ZMod N) : z k ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * q)) * Real.exp (2 * q) :=
        mul_le_mul_of_nonneg_left (hcap k) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * q)) ≤ 𝔼 k, z k := by
    change Real.exp (-(3 * q)) ≤ 𝔼 k, Real.exp (-(2 * q)) * c k
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * q)) = Real.exp (-(2 * q)) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmean (Real.exp_nonneg _)
  obtain ⟨H, hHsize, hHcorr⟩ :=
    exists_dense_level_set z (Real.exp_nonneg (-(3 * q))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * q)) / 2 := by
    apply (Real.exp_le_exp.mpr (by dsimp [t]; linarith : -t ≤ -(3 * q) - 1)).trans
    exact exp_sub_one_le_half_exp (-(3 * q))
  have hdense : Real.exp (-t) * N ≤ (H.card : ℝ) := by
    simpa only [ZMod.card] using
      (mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg (Fintype.card (ZMod N)))).trans hHsize
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hH : H.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le (by positivity : 0 < Real.exp (-t) * (N : ℝ)) hdense
  refine ⟨H, hH, (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg htC)) (Nat.cast_nonneg N)).trans hdense, ?_⟩
  intro k hk
  have hzle : z k ≤ c k := mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hc : Real.exp (-t) ≤ c k := hhalf.trans ((hHcorr k hk).trans hzle)
  let E := Classical.choice (hK k)
  obtain ⟨i, hi⟩ := E.select_sample_correlation Finset.univ (fun (n : ZMod N) (_ : Unit) => (n.val : ℤ))
    (multiplicativeDerivative f k) hc
  exact ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono hqC
    coordinate := ()
    correlation := (Real.exp_le_exp.mpr (neg_le_neg htqC)).trans hi }⟩

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_univariate_cyclic_difference_models (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p e : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (i j : I) (k : ZMod N), ∃ K : (Unit → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + e + C) ^ C) K) ∧
        (𝔼 n : ZMod N,
          ‖(V.test g i).eval (fun _ => (n.val : ℤ)) *
              star ((V.test g j).eval (fun _ => ((n + k).val : ℤ))) -
            K (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e) := by
  obtain ⟨C, hC, htwo⟩ := exists_cyclic_second_difference_models_degree s hs
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d D p e V g hp hD hI he N _ hN i j k
  let A : Unit → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let g₂ := ((V.test g i).linearPullbackHom A).orbit
  have heval (l : I) (x : Fin 2 → ℤ) :
      (V.test g₂ l).eval x = (V.test g l).eval (fun _ => x 1) := by
    change ((V.test g l).linearPullbackHom A).eval x = _
    exact (V.test g l).eval_linearPullbackHom A x
  obtain ⟨K, ⟨E⟩, herr⟩ := htwo D V g₂ hp hD hI he hN i j k
  let B : Fin 2 → ((Unit → ℤ) →+ ℤ) :=
    ![0, { toFun := fun x => x (), map_zero' := rfl, map_add' := fun _ _ => rfl }]
  have hB (x : Unit → ℤ) : (fun l => B l x) = ![0, x ()] := by
    funext l
    fin_cases l <;> rfl
  refine ⟨fun x => K ![0, x ()], ?_, ?_⟩
  · exact ⟨by simpa only [hB] using E.linearPullbackHom B⟩
  · simpa only [cyclicSecondDifference, heval, Matrix.cons_val_one, Matrix.cons_val_zero] using herr 0

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_iterated_native_derivative_correlations (k d : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeVectorCorrelation (k + d) N p (fun _ : Unit => f)) →
      ∃ Q : Finset (Fin d → ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ d ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, Nonempty (NativeVectorCorrelation k N ((p + C) ^ C)
          (fun _ : Unit => cubeProduct f (List.ofFn u))) := by
  induction d with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    intro N _ p hp _ f _ ⟨V⟩
    classical
    have hq : 0 ≤ (p + 2) ^ 2 := sq_nonneg _
    have hpq : p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    refine ⟨Finset.univ, Finset.univ_nonempty, ?_, ?_⟩
    · simpa using (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hq))
    · intro u _
      have hfun : (fun _ : Unit => cubeProduct f (List.ofFn u)) = (fun _ : Unit => f) := by
        funext _ x
        simp only [List.ofFn_zero, cubeProduct_nil]
      rw [hfun]
      exact ⟨V.mono hpq⟩
  | succ d ih =>
    obtain ⟨a, _, hstep⟩ := exists_many_native_derivative_correlations (k + d) (by omega)
    obtain ⟨b, _, hiter⟩ := ih
    let X : Polynomial ℕ := Polynomial.X
    let P := (X + Polynomial.C a) ^ a
    let R := (P + Polynomial.C b) ^ b
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
    refine ⟨C, hC, ?_⟩
    intro N _ p hp hN f hf hc
    classical
    let q := (p + a) ^ a
    let r := (q + b) ^ b
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hsum : q + r ≤ (p + C) ^ C := by
      simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
    have hqC : q ≤ (p + C) ^ C := by linarith
    have hrC : r ≤ (p + C) ^ C := by linarith
    obtain ⟨H, hH, hHdense, hHcorr⟩ := hstep hp ((Real.exp_le_exp.mpr hqC).trans hN)
      f hf (by simpa only [Nat.add_assoc] using hc)
    have hdata (h : H) := hiter hq ((Real.exp_le_exp.mpr hrC).trans hN)
      (multiplicativeDerivative f h.val) (multiplicativeDerivative_norm_le_one f hf h.val)
      (hHcorr h.val h.property)
    choose K _hK hKdense hKcorr using hdata
    obtain ⟨Q, hQdense, hQmem⟩ := dense_tuple_fibers d H K (Real.exp_nonneg (-r))
      (by simpa only [ZMod.card] using hHdense)
      (fun h => by simpa only [ZMod.card] using hKdense h)
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    have hQ : Q.Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast lt_of_lt_of_le
        (by positivity : 0 < Real.exp (-q) * Real.exp (-r) * (Fintype.card (ZMod N) : ℝ) ^ (d + 1)) hQdense
    refine ⟨Q, hQ, ?_, ?_⟩
    · have heq : Real.exp (-(q + r)) = Real.exp (-q) * Real.exp (-r) := by rw [neg_add, Real.exp_add]
      have hsmall := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hsum)) (pow_nonneg (Nat.cast_nonneg N) (d + 1))
      rw [heq] at hsmall
      exact hsmall.trans (by simpa only [ZMod.card] using hQdense)
    · intro u hu
      obtain ⟨h, hh, htail⟩ := (hQmem u).mp hu
      have hlist : List.ofFn u = h.val :: List.ofFn (Fin.tail u) := by
        rw [List.ofFn_succ, ← hh]
        rfl
      obtain ⟨V⟩ := hKcorr h (Fin.tail u) htail
      have hfun : (fun _ : Unit => cubeProduct f (List.ofFn u)) =
          (fun _ : Unit => cubeProduct (multiplicativeDerivative f h.val)
            (List.ofFn (Fin.tail u))) := by
        funext _ x
        rw [hlist, cubeProduct_cons_eq_derivative]
      rw [hfun]
      exact ⟨V.mono hrC⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.QuadraticMarkedAffine
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def seedVector (a : ℝ) : ℝ ⊗[ℚ] Seed := a ⊗ₜ[ℚ] generators 0

theorem seedVector_mem (a : ℝ) :
    seedVector a ∈ (markedLieSpan generators weights marked 1 1 1).baseChange ℝ := by
  apply Submodule.tmul_mem_baseChange_of_mem
  simpa only [weights, marked, Bool.true_eq, ite_true] using
    markedLieSpan_leaf generators weights marked (0 : Fin 1)

noncomputable def affineCoefficient (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    (markedPolynomialLayer (σ := Fin t) generators weights marked 1 0 1).baseChange ℝ :=
  ⟨realAffinePolynomial (seedVector a) (fun i => seedVector (b i)),
    realAffinePolynomial_mem_marked generators weights marked
      (Submodule.baseChange_mono ℝ
        (markedLieSpan_antitone generators weights marked le_rfl (by omega) le_rfl)
        (seedVector_mem a)) (fun i => seedVector_mem (b i))⟩

noncomputable def sourceLift (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra filtration generators weights marked t :=
  realMarkedPolynomialLift filtration generators weights marked weight_pos generator_mem t 1 0 1
    (affineCoefficient t a b)

noncomputable def projectedLift (t : ℕ) (a : ℝ) (b : Fin t → ℝ) : ℝ ⊗[ℚ] Algebra t :=
  (lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
    (sourceLift t a b)

theorem sourceLift_eval (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (u : Fin t → ℚ) :
    (markedShiftEval filtration generators weights marked t u).baseChange ℝ (sourceLift t a b) =
      seedVector a + ∑ i, (u i : ℝ) • seedVector (b i) := by
  apply (realMarkedPolynomialLift_eval filtration generators weights marked weight_pos generator_mem
    t 1 0 1 (affineCoefficient t a b) u).trans
  simpa only [affineCoefficient, ← Rat.cast_smul_eq_qsmul ℝ] using
    realAffinePolynomial_eval (seedVector a) (fun i => seedVector (b i)) u

theorem projectedLift_mem (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    projectedLift t a b ∈ (multidegree t).realification.layer (correlationInput 0 1) :=
  realMarkedPolynomialLift_quotient_mem filtration generators weights marked weight_pos generator_mem
    t 1 0 1 (affineCoefficient t a b)

theorem projectedLift_pure (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    projectedLift t a b ∈
      (markedQuotientPolynomialAlgebra filtration generators weights marked t).toSubmodule.baseChange ℝ := by
  change projectedLift t a b ∈
    (LinearMap.ker (markedQuotientPhase filtration generators weights marked t).toLinearMap).baseChange ℝ
  rw [realification_ker, LinearMap.mem_ker]
  change (markedQuotientPhase filtration generators weights marked t).toLinearMap.baseChange ℝ
    ((lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
      (sourceLift t a b)) = 0
  rw [markedQuotientPhase_real_map]
  exact realMarkedPolynomialLift_phase filtration generators weights marked weight_pos generator_mem
    t 1 0 1 (by decide) (affineCoefficient t a b)

theorem projectedLift_phase (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    torusPhaseLinear (phase t m) (projectedLift t a b) = 0 :=
  normalizedMarkedPhase_real_pure filtration generators weights marked t m _
    (projectedLift_pure t a b)

noncomputable def seedCoordinate (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) :
    (ℝ ⊗[ℚ] Seed) →ₗ[ℝ] ℝ :=
  (realifyFunctional η).comp ((lieQuotientMap (⊥ : LieIdeal ℚ Seed)).toLinearMap.baseChange ℝ)

theorem seedCoordinate_seedVector (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0) (a : ℝ) :
    seedCoordinate η (seedVector a) = a := by
  have he : generators (0 : Fin 1) (0 : Fin 1) = 1 := by
    change (Pi.basisFun ℚ (Fin 1)) 0 0 = 1
    simp
  simp only [seedCoordinate, seedVector, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    realifyFunctional_tmul]
  change a * ((η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) (generators 0))) : ℝ) = a
  rw [hη, he, Rat.cast_one, mul_one]

theorem sourceLift_shift_coordinate (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (t : ℕ) (a : ℝ) (b u : Fin t → ℝ) :
    seedCoordinate η ((markedShiftEval filtration generators weights marked t 0).baseChange ℝ
      (realMarkedAffineShift filtration generators weights marked weight_pos generator_mem t u
        (sourceLift t a b))) = a + ∑ i, u i * b i := by
  rw [realMarkedAffineShift_eval_affine filtration generators weights marked weight_pos generator_mem
    t u (sourceLift t a b) (seedVector a) (fun i => seedVector (b i)) (sourceLift_eval t a b)]
  simp only [map_add, map_sum, map_smul, seedCoordinate_seedVector η hη, smul_eq_mul]

theorem shiftedLift_coordinate (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (t : ℕ) (a : ℝ) (b u : Fin t → ℝ) :
    realifyFunctional η ((evaluation t).baseChange ℝ
      ((lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
        (realMarkedAffineShift filtration generators weights marked weight_pos generator_mem t u
          (sourceLift t a b)))) = a + ∑ i, u i * b i := by
  rw [evaluation, markedBaseEvaluation_real_map]
  exact sourceLift_shift_coordinate η hη t a b u

noncomputable def pureOrbit (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    (multidegree t).realification.PolynomialOrbit :=
  (multidegree t).realification.polynomialOrbitOfLog
    (monomial (correlationExponent 0 1) (projectedLift t a b)) (by
      apply (multidegree t).realification.monomial_mem_adaptedSubmodule
      simpa only [correlationExponent_apply] using projectedLift_mem t a b)

theorem pureOrbit_eval (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (h n : ℤ) :
    ((multidegree t).realification.polynomialOrbitEval (correlationInput h n) (pureOrbit t a b)).coord =
      (n : ℝ) • projectedLift t a b := by
  change eval (fun i => ((correlationInput h n i : ℤ) : ℚ))
    (monomial (correlationExponent 0 1) (projectedLift t a b)) = _
  rw [eval_correlation_monomial]
  change ((h : ℚ) ^ 0 * (n : ℚ) ^ 1) • projectedLift t a b = _
  rw [pow_zero, pow_one, one_mul]
  simpa only [Rat.cast_intCast] using
    (Rat.cast_smul_eq_qsmul ℝ (n : ℚ) (projectedLift t a b)).symm

end Erdos3.QuadraticMarked

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ} {bound : σ → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (M : ∀ i, (D i).MultidegreeStructure bound)

noncomputable def productMultidegreeLayerBasis (a : ∀ j, Fin (bound j + 1)) :
    Basis (Σ i, Fin (finrank ℚ ((M i).filtration.layer (fun j => (a j).val)))) ℚ
      ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun j => (a j).val)) :=
  (Pi.basis (fun i => (M i).basis a)).map
    (MultidegreeLieFiltration.piLayerEquiv (fun i => (M i).filtration) (fun j => (a j).val))

noncomputable def productMultidegreeLayerFinBasis (a : ∀ j, Fin (bound j + 1)) :
    Basis (Fin (finrank ℚ
      ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun j => (a j).val)))) ℚ
      ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun j => (a j).val)) :=
  (productMultidegreeLayerBasis D M a).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (productMultidegreeLayerBasis D M a)).symm)

noncomputable def piMultidegree : (pi D).MultidegreeStructure bound where
  filtration := MultidegreeLieFiltration.pi (fun i => (M i).filtration)
  ordinary := congrArg NilpotentLieFiltration.pi (funext (fun i => (M i).ordinary))
  basis := productMultidegreeLayerFinBasis D M

theorem productMultidegreeLayerBasis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hM : ∀ i, (M i).ComplexityLE p) (a : ∀ j, Fin (bound j + 1))
    (j : Σ i, Fin (finrank ℚ ((M i).filtration.layer (fun k => (a k).val))))
    (k : Σ i, Fin (d i)) :
    rationalLogHeight ((Pi.basis (fun i => (D i).basis)).repr
      ((productMultidegreeLayerBasis D M a j).val) k) ≤ p := by
  classical
  rcases j with ⟨j, m⟩
  rcases k with ⟨k, n⟩
  simp only [productMultidegreeLayerBasis, Basis.map_apply, Pi.basis_repr]
  change rationalLogHeight ((D k).basis.repr
    (((Pi.basis (fun i => (M i).basis a)) ⟨j, m⟩ k).val) n) ≤ p
  rw [Pi.basis_apply]
  by_cases hjk : j = k
  · subst k
    rw [Pi.single_eq_same]
    exact (hM j).2 a m n
  · rw [Pi.single_eq_of_ne (Ne.symm hjk)]
    simpa [rationalLogHeight] using hp

theorem piMultidegree_complexity {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hM : ∀ i, (M i).ComplexityLE p) :
    (piMultidegree D M).ComplexityLE ((p + 2) ^ 2) := by
  refine ⟨pi_geometry D hp hι (fun i => (hM i).1), ?_⟩
  intro a j k
  change Fin (finrank ℚ
    ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun i => (a i).val))) at j
  change rationalLogHeight ((productFinBasis D).repr
    ((productMultidegreeLayerFinBasis D M a j).val) k) ≤ (p + 2) ^ 2
  rw [productFinBasis, Basis.repr_reindex_apply, productMultidegreeLayerFinBasis, Basis.reindex_apply]
  exact (productMultidegreeLayerBasis_logHeight D M hp hM a _ _).trans (by nlinarith [sq_nonneg p])

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

theorem exists_bounded_multidegree_product_family
    {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ} {bound : σ → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (M : ∀ i, (D i).MultidegreeStructure bound)
    (g : ∀ i, (M i).filtration.realification.PolynomialOrbit)
    {I : ι → Type*} (V : ∀ i, I i → (D i).Space → ℂ) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hM : ∀ i, (M i).ComplexityLE p)
    (hV : ∀ i j x, ‖V i j x‖ ≤ 1)
    (hLip : ∀ i, letI := (D i).metricSpace;
      ∀ j, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i j)) :
    (piMultidegree D M).ComplexityLE (productNiltestBudget (p + 4)) ∧
    ∃ T : (∀ i, I i) → (pi D).Niltest (fun _ : σ => 1),
      (∀ j, (T j).orbit = (piMultidegree D M).orbitToOrdinary
        (MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g)) ∧
      (∀ j, (T j).normBound = 1) ∧
      (∀ j, (T j).ComplexityLE (productNiltestBudget (p + 4))) ∧
      (∀ j x, (T j).observable x = ∏ i, V i (j i) (productProjection D i x)) ∧
      ∀ j x, (T j).eval x =
        ∏ i, V i (j i) (QuotientGroup.mk ((M i).filtration.realification.polynomialOrbitEval x (g i))) := by
  classical
  have hpq : p ≤ p + 4 := by linarith
  have hq : 0 ≤ p + 4 := by linarith
  let K (i : ι) (j : I i) : (D i).Niltest (fun _ : σ => 1) := {
    orbit := (M i).orbitToOrdinary (g i)
    observable := V i j
    normBound := 1
    lipBound := ⟨Real.exp p, Real.exp_nonneg _⟩
    norm_le := hV i j
    lipschitz := hLip i j
  }
  have hK (i : ι) (j : I i) : (K i j).ComplexityLE (p + 4) := by
    refine ⟨(hM i).1.mono (D i) hpq, ?_⟩
    change Real.log (2 + 1 + Real.exp p) ≤ p + 4
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    calc
      _ ≤ 4 * Real.exp p := by linarith [Real.one_le_exp hp]
      _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  let o := (piMultidegree D M).orbitToOrdinary
    (MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g)
  let T (j : ∀ i, I i) := (unitBoundedPiNiltest D (fun i => K i (j i)) hq (hι.trans hpq)
    (fun i => hK i (j i)) (fun _ => le_rfl)).withOrbit o
  refine ⟨(piMultidegree_complexity D M hq (hι.trans hpq)
      (fun i => (hM i).mono (M i) hpq)).mono _ (productNiltestBudget_geometry hq),
    T, (fun _ => rfl), (fun _ => rfl),
    (fun j => unitBoundedPiNiltest_complexity D (fun i => K i (j i)) hq (hι.trans hpq)
      (fun i => hK i (j i)) (fun _ => le_rfl)),
    (fun _ _ => rfl), ?_⟩
  intro j x
  change (∏ i, V i (j i) (productProjection D i
    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x o)))) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_mk]
  apply congrArg (fun z : (D i).RealGroup => V i (j i) (QuotientGroup.mk z))
  exact (congrArg (productProjectionHom D i)
    ((piMultidegree D M).orbitToOrdinary_eval
      (MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g) x)).trans
        (MultidegreeLieFiltration.piRealOrbit_eval (fun i => (M i).filtration) g x i)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

def HasBoundedBinaryMultidegreeFamily
    {σ I J : Type*} {L₀ L₁ : Type u} [Fintype σ]
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    {s d₀ d₁ : ℕ} {bound : σ → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀) (D₁ : RationalFilteredNilmanifold L₁ s d₁)
    (M₀ : D₀.MultidegreeStructure bound) (M₁ : D₁.MultidegreeStructure bound)
    (g₀ : M₀.filtration.realification.PolynomialOrbit) (g₁ : M₁.filtration.realification.PolynomialOrbit)
    (V₀ : I → D₀.Space → ℂ) (V₁ : J → D₁.Space → ℂ) (p : ℝ) : Prop :=
    let P := optionProduct D₀ (fun _ : Unit => D₁)
    ∃ M : P.MultidegreeStructure bound, M.ComplexityLE (productNiltestBudget (p + 4)) ∧
      ∃ g : M.filtration.realification.PolynomialOrbit,
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i)) :=
            IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 P.basis
         ∃ T : I × J → P.Niltest (fun _ : σ => 1),
           (∀ ij, (T ij).orbit = M.orbitToOrdinary g) ∧
           (∀ ij, (T ij).normBound = 1) ∧
           (∀ ij, (T ij).ComplexityLE (productNiltestBudget (p + 4))) ∧
           ∀ ij x, (T ij).eval x =
             V₀ ij.1 (QuotientGroup.mk (M₀.filtration.realification.polynomialOrbitEval x g₀)) *
             V₁ ij.2 (QuotientGroup.mk (M₁.filtration.realification.polynomialOrbitEval x g₁)))

theorem exists_bounded_binary_multidegree_family
    {σ I J : Type*} {L₀ L₁ : Type u} [Fintype σ]
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    {s d₀ d₁ : ℕ} {bound : σ → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀) (D₁ : RationalFilteredNilmanifold L₁ s d₁)
    (M₀ : D₀.MultidegreeStructure bound) (M₁ : D₁.MultidegreeStructure bound)
    (g₀ : M₀.filtration.realification.PolynomialOrbit) (g₁ : M₁.filtration.realification.PolynomialOrbit)
    (V₀ : I → D₀.Space → ℂ) (V₁ : J → D₁.Space → ℂ) {p : ℝ}
    (hp : 2 ≤ p) (hM₀ : M₀.ComplexityLE p) (hM₁ : M₁.ComplexityLE p)
    (hV₀ : ∀ i x, ‖V₀ i x‖ ≤ 1) (hV₁ : ∀ j x, ‖V₁ j x‖ ≤ 1)
    (hLip₀ : letI := D₀.metricSpace; ∀ i, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V₀ i))
    (hLip₁ : letI := D₁.metricSpace; ∀ j, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V₁ j)) :
    HasBoundedBinaryMultidegreeFamily D₀ D₁ M₀ M₁ g₀ g₁ V₀ V₁ p := by
  unfold HasBoundedBinaryMultidegreeFamily
  dsimp only
  let P := optionProduct D₀ (fun _ : Unit => D₁)
  let D := optionFactors D₀ (fun _ : Unit => D₁)
  let M : ∀ i : Option Unit, (D i).MultidegreeStructure bound
    | none => M₀
    | some _ => M₁
  let g : ∀ i : Option Unit, (M i).filtration.realification.PolynomialOrbit
    | none => g₀
    | some _ => g₁
  let : ∀ i : Option Unit, TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (TopologicalSpace (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (TopologicalSpace (ℝ ⊗[ℚ] L₁))
  let : ∀ i : Option Unit, IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁))
  let : ∀ i : Option Unit, ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁))
  let : ∀ i : Option Unit, T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (T2Space (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (T2Space (ℝ ⊗[ℚ] L₁))
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 P.basis
  let V : ∀ i : Option Unit, (I × J) → (D i).Space → ℂ
    | none => fun ij => V₀ ij.1
    | some _ => fun ij => V₁ ij.2
  have hM : ∀ i, (M i).ComplexityLE p := fun i => by
    match i with
    | none => exact hM₀
    | some _ => exact hM₁
  have hV : ∀ i ij x, ‖V i ij x‖ ≤ 1 := fun i => by
    match i with
    | none => exact fun ij x => hV₀ ij.1 x
    | some _ => exact fun ij x => hV₁ ij.2 x
  have hLip : ∀ i, letI := (D i).metricSpace;
      ∀ ij, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i ij) := fun i => by
    match i with
    | none => exact fun ij => hLip₀ ij.1
    | some _ => exact fun ij => hLip₁ ij.2
  obtain ⟨hprod, T, hTo, hTn, hTc, _, hTe⟩ :=
    exists_bounded_multidegree_product_family D M g V (by linarith) (by simpa using hp) hM hV hLip
  refine ⟨piMultidegree D M, hprod, MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g,
    (fun ij => T (fun _ => ij)), (fun ij => hTo (fun _ => ij)),
    (fun ij => hTn (fun _ => ij)), (fun ij => hTc (fun _ => ij)), ?_⟩
  intro ij x
  have he := hTe (fun _ => ij) x
  rw [Fintype.prod_option, Fintype.prod_unique] at he
  exact he

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

structure NativeBoundedMultidegreeFamily {σ : Type*} [Fintype σ]
    (bound : σ → ℕ) (I : Type*) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L (∑ i, bound i) dim
  multi : model.MultidegreeStructure bound
  complexity : multi.ComplexityLE p
  orbit : multi.filtration.realification.PolynomialOrbit
  test : I → model.Niltest (fun _ : σ => 1)
  test_orbit : ∀ i, (test i).orbit = multi.orbitToOrdinary orbit
  test_norm : ∀ i, (test i).normBound = 1
  test_complexity : ∀ i, (test i).ComplexityLE p

attribute [local instance] NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

namespace NativeBoundedMultidegreeFamily

variable {σ I : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (F : NativeBoundedMultidegreeFamily bound I p)

noncomputable def eval (i : I) (x : σ → ℤ) : ℂ := (F.test i).eval x

noncomputable def mono (hpq : p ≤ q) : NativeBoundedMultidegreeFamily bound I q :=
  { F with
    complexity := F.complexity.mono F.multi hpq
    test_complexity := fun i => (F.test_complexity i).mono hpq }

@[simp] theorem mono_eval (hpq : p ≤ q) (i : I) (x : σ → ℤ) :
    (F.mono hpq).eval i x = F.eval i x := rfl

end NativeBoundedMultidegreeFamily

namespace NativeMultidegreeNilcharacter

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem exists_product_with_bounded_family
    {σ J : Type*} [Fintype σ] {bound : σ → ℕ} {p B : ℝ}
    (W : NativeMultidegreeNilcharacter bound p)
    {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (M : D.MultidegreeStructure bound) (hstep : s = ∑ i, bound i)
    (g : M.filtration.realification.PolynomialOrbit)
    (G : J → D.Space → ℂ) (hB : 0 ≤ B) (hM : M.ComplexityLE B)
    (hG : ∀ j x, ‖G j x‖ ≤ 2)
    (hLip : letI := D.metricSpace; ∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) :
    ∃ F : NativeBoundedMultidegreeFamily bound (Fin W.outputDim × J)
        (productNiltestBudget (p + B + 2 + 4)),
      ∀ ij x, F.eval ij x = W.eval ij.1 x *
        G ij.2 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) / 2 := by
  subst hstep
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpP : p ≤ p + B + 2 := by linarith
  have hBP : B ≤ p + B + 2 := by linarith
  let G' (j : J) (x : D.Space) := G j x / 2
  have hGn (j : J) (x : D.Space) : ‖G' j x‖ ≤ 1 := by
    dsimp only [G']
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    linarith [hG j x]
  have hGL : letI := D.metricSpace;
      ∀ j, LipschitzWith ⟨Real.exp (p + B + 2), Real.exp_nonneg _⟩ (G' j) := by
    let := D.metricSpace
    intro j
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (G j x / 2) (G j y / 2) ≤ _
    rw [dist_eq_norm, ← sub_div, norm_div]
    norm_num only [Complex.norm_ofNat]
    have h := (hLip j).dist_le_mul x y
    rw [dist_eq_norm] at h
    exact (div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 2)).trans
      (h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hBP) dist_nonneg))
  have hWL : letI := W.model.metricSpace;
      ∀ i, LipschitzWith ⟨Real.exp (p + B + 2), Real.exp_nonneg _⟩ (W.vertical.observable i) := by
    let := W.model.metricSpace
    intro i
    exact (W.vertical.lipschitz i).weaken
      (show W.vertical.lipBound ≤ ⟨Real.exp (p + B + 2), Real.exp_nonneg _⟩ from
        W.vertical.lip_bound.trans (Real.exp_le_exp.mpr hpP))
  obtain ⟨MP, hMP, gP, htests⟩ := exists_bounded_binary_multidegree_family
    W.model D W.multi M W.orbit g W.vertical.observable G' (by linarith : 2 ≤ p + B + 2)
    (W.complexity.mono W.multi hpP) (hM.mono M hBP) W.vertical.norm hGn hWL hGL
  let P := optionProduct W.model (fun _ : Unit => D)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace W.L (fun _ : Unit => L) i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace W.L (fun _ : Unit => L) i)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 P.basis
  obtain ⟨T, hTo, hTn, hTc, hTe⟩ := htests
  let F : NativeBoundedMultidegreeFamily bound (Fin W.outputDim × J)
      (productNiltestBudget (p + B + 2 + 4)) := {
    L := ∀ i : Option Unit, optionLieSpace W.L (fun _ : Unit => L) i
    dim := Fintype.card (Σ i : Option Unit, Fin (optionDimension W.dim (fun _ : Unit => d) i))
    model := P
    multi := MP
    complexity := hMP
    orbit := gP
    test := T
    test_orbit := hTo
    test_norm := hTn
    test_complexity := hTc
  }
  refine ⟨F, ?_⟩
  intro ij x
  change (T ij).eval x = _
  rw [hTe]
  change W.eval ij.1 x * (G ij.2 _ / 2) = _
  rw [mul_div_assoc]

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeBoundedMultidegreeFamily

open scoped TensorProduct

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

noncomputable def slice {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p)
    (i : I) (h : ℤ) : F.model.Niltest (fun _ : Unit => 1) :=
  (F.test i).affinePullback (fun j _ => correlationInput 0 1 j) (correlationInput h 0)

theorem slice_eval {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p)
    (i : I) (h : ℤ) (x : Unit → ℤ) :
    (F.slice i h).eval x = F.eval i (correlationInput h (x ())) := by
  rw [slice, RationalFilteredNilmanifold.Niltest.eval_affinePullback]
  apply congrArg (F.test i).eval
  funext j
  refine Fin.cases ?_ (fun _ => ?_) j <;> simp [integerAffineMap, correlationInput]

theorem slice_orbit_eval {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p)
    (i : I) (h : ℤ) (x : Unit → ℤ) :
    F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (F.slice i h).orbit =
      F.multi.filtration.realification.polynomialOrbitEval (correlationInput h (x ())) F.orbit := by
  let A : Fin 2 → Unit → ℤ := fun j _ => correlationInput 0 1 j
  let b := correlationInput h 0
  have heq : integerAffineMap A b x = correlationInput h (x ()) := by
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp [A, b, integerAffineMap, correlationInput]
  have he := F.model.filtration.realification.polynomialOrbitSubstitute_eval
    (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)
    (F.test i).orbit x (integerAffineMap A b x) (integerAffinePolynomial_eval A b x)
  change F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (F.slice i h).orbit =
    F.model.filtration.realification.polynomialOrbitEval (fun _ : Fin 2 => 1)
      (integerAffineMap A b x) (F.test i).orbit at he
  rw [he, heq, F.test_orbit, F.multi.orbitToOrdinary_eval]

theorem slice_norm {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I) (h : ℤ) :
    (F.slice i h).normBound = 1 := F.test_norm i

theorem slice_complexity {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I) (h : ℤ) :
    (F.slice i h).ComplexityLE p := F.test_complexity i

theorem slice_observable {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I) (h : ℤ) :
    (F.slice i h).observable = (F.test i).observable := rfl

end Erdos3.NativeBoundedMultidegreeFamily

namespace Erdos3.NativeUnitRankFamily

open scoped TensorProduct

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem withOrbit_eval {σ τ I : Type*} [Fintype I] {w : σ → ℕ} {s r : ℕ} {p : ℝ}
    (F : NativeUnitRankFamily w s r τ I p) (i : I) (t : τ) (x : σ → ℤ) :
    ((F.test i).withOrbit (F.orbit t)).eval x = F.eval t i x := rfl

end Erdos3.NativeUnitRankFamily

end

section

namespace Erdos3

open scoped TensorProduct

namespace NativeUnitRankFamily

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

variable {τ τ' I : Type*} [Fintype I] {s r : ℕ} {p q : ℝ}
  (F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ I p)
  (e : τ' → τ) (hpq : p ≤ q) {n : ℕ} (hn : (n + 1 : ℝ) ≤ Real.exp q)
  (V : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s) (Fin (n + 1)) q)

noncomputable def toVerticalFamily : NativeDegreeRankFamily s r τ' q where
  L := F.L
  dim := F.dim
  model := F.model
  rank := F.rank
  complexity := F.complexity.mono F.rank hpq
  orbit := fun t => F.orbit (e t)
  normalized := fun t => F.normalized (e t)
  outputDim := n + 1
  output_pos := Nat.succ_pos n
  output_bound := by simpa only [Nat.cast_add, Nat.cast_one] using hn
  vertical := {
    V with
    vertical := fun i z hz x => V.vertical i z (F.rank.realSubgroup_le_degree s r hz) x
    integral := fun z hz hL => V.integral z (F.rank.realSubgroup_le_degree s r hz) hL
  }

theorem toVerticalFamily_eval (i : Fin (n + 1)) (t : τ') (x : ℤ) :
    (F.toVerticalFamily e hpq hn V).eval i t x = V.observable i (QuotientGroup.mk
      (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => x) (F.orbit (e t)))) := rfl

end NativeUnitRankFamily

namespace NativeBoundedMultidegreeFamily

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

variable {σ I : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (M : NativeBoundedMultidegreeFamily bound I p) (hpq : p ≤ q)
  {n : ℕ} (hn : (n + 1 : ℝ) ≤ Real.exp q)
  (V : M.model.UnitVerticalObservable
    (M.model.filtration.realification.subgroup (∑ i, bound i)) (Fin (n + 1)) q)

noncomputable def toNilcharacter : NativeMultidegreeNilcharacter bound q where
  L := M.L
  dim := M.dim
  model := M.model
  multi := M.multi
  complexity := M.complexity.mono M.multi hpq
  orbit := M.orbit
  outputDim := n + 1
  output_pos := Nat.succ_pos n
  output_bound := by simpa only [Nat.cast_add, Nat.cast_one] using hn
  vertical := {
    V with
    vertical := fun i z hz x => V.vertical i z (M.multi.realSubgroup_top ▸ hz) x
    integral := fun z hz hL => V.integral z (M.multi.realSubgroup_top ▸ hz) hL
  }

theorem toNilcharacter_eval (i : Fin (n + 1)) (x : σ → ℤ) :
    (M.toNilcharacter hpq hn V).eval i x = V.observable i (QuotientGroup.mk
      (M.multi.filtration.realification.polynomialOrbitEval x M.orbit)) := rfl

end NativeBoundedMultidegreeFamily

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_correlation_of_unit_products
    {I K : Type} [Fintype I] {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    (J : Finset (ZMod N))
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
    (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
    (H : Finset {h // h ∈ J}) (hH : H.Nonempty)
    (hdense : Real.exp (-q) * N ≤ (H.card : ℝ)) (hpq : p ≤ q)
    {n₁ n₂ : ℕ} (hn₁ : (n₁ + 1 : ℝ) ≤ Real.exp q) (hn₂ : (n₂ + 1 : ℝ) ≤ Real.exp q)
    (V₁ : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s)
      (Fin (n₁ + 1)) q)
    (V₂ : M.model.UnitVerticalObservable
      (M.model.filtration.realification.subgroup (∑ i, mixedCorrelationDegree s i)) (Fin (n₂ + 1)) q)
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N q (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
        (M.multi.filtration.realification.polynomialOrbitEval
          (correlationInput (h.val.val : ℤ) (x.val : ℤ)) M.orbit))) *
        star (V₁.observable 0 (QuotientGroup.mk
          (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
            (fun _ => (x.val : ℤ)) (F.orbit h))))))) :
    Nonempty (NativeCorrelationStructure s r N q f) := by
  classical
  obtain ⟨h₀, hh₀⟩ := hH
  let e (h : ZMod N) : {h // h ∈ J} := if hh : h ∈ J then ⟨h, hh⟩ else h₀
  have he (h : {h // h ∈ J}) : e h.val = h := by
    simp only [e, dif_pos h.property]
  let family := F.toVerticalFamily e hpq hn₁ V₁
  let mixed := M.toNilcharacter hpq hn₂ V₂
  let shifts := H.image Subtype.val
  have hcard : shifts.card = H.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨{
    shifts := shifts
    nonempty := (show H.Nonempty from ⟨h₀, hh₀⟩).image _
    density := by simpa only [ZMod.card, hcard] using hdense
    mixed := mixed
    family := family
    correlation := ?_
  }⟩
  intro h hh
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨Wh⟩ := hcorr z hz
  refine ⟨Wh.mapCoordinates _ (fun _ => ((0 : Fin (n₂ + 1)), (0 : Fin (n₁ + 1)))) ?_⟩
  intro i x
  have hinput : (fun j => ((correlationInput z.val x j).val : ℤ)) =
      correlationInput (z.val.val : ℤ) (x.val : ℤ) :=
    map_correlationInput (fun a : ZMod N => (a.val : ℤ)) z.val x
  have hmixed : mixed.evalCyclic N (0 : Fin (n₂ + 1)) (correlationInput z.val x) = V₂.observable 0 (QuotientGroup.mk
      (M.multi.filtration.realification.polynomialOrbitEval
        (correlationInput (z.val.val : ℤ) (x.val : ℤ)) M.orbit)) := by
    change (M.toNilcharacter hpq hn₂ V₂).eval (0 : Fin (n₂ + 1)) (fun j => ((correlationInput z.val x j).val : ℤ)) = _
    rw [hinput, M.toNilcharacter_eval]
  have hfamily : family.evalCyclic N (0 : Fin (n₁ + 1)) z.val x = V₁.observable 0 (QuotientGroup.mk
      (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (F.orbit z))) := by
    change (F.toVerticalFamily e hpq hn₁ V₁).eval (0 : Fin (n₁ + 1)) z.val (x.val : ℤ) = _
    rw [F.toVerticalFamily_eval, he]
  change nativeCorrelationResidual f mixed family z.val ((0 : Fin (n₂ + 1)), (0 : Fin (n₁ + 1))) x = _
  simp only [nativeCorrelationResidual, hmixed, hfamily]

end Erdos3

end

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def parameter (t : ℕ) (v : Fin t → ℝ) : (multidegree t).realification.Group :=
  realMarkedParameterElement filtration generators weights marked weight_pos generator_mem t v

theorem parameter_mul (t : ℕ) (v w : Fin t → ℝ) :
    parameter t v * parameter t w = parameter t (v + w) :=
  realMarkedParameterElement_mul filtration generators weights marked weight_pos generator_mem t v w

theorem parameter_inv (t : ℕ) (v : Fin t → ℝ) : (parameter t v)⁻¹ = parameter t (-v) :=
  realMarkedParameterElement_inv filtration generators weights marked weight_pos generator_mem t v

noncomputable def affineElement (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) :
    (multidegree t).realification.Group := ⟨n • projectedLift t a b⟩

theorem affineElement_phase (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) :
    torusPhaseLinear (phase t m) (affineElement t a b n).coord = 0 := by
  change torusPhaseLinear (phase t m) (n • projectedLift t a b) = 0
  rw [map_smul, projectedLift_phase, smul_zero]

noncomputable def centeredElement (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    (multidegree t).realification.Group :=
  affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n * parameter t ((m : ℝ) • -v)

theorem centeredElement_phase {t d : ℕ} (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    torusPhaseLinear (phase t m) (centeredElement t m a b n v).coord = -v := by
  rw [centeredElement, torusPhaseLinear_mul D, affineElement_phase, zero_add]
  exact normalizedMarkedPhase_real_scaled_parameter filtration generators weights marked t m hm (-v)

theorem centeredElement_retraction_coord {t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    (normalizedMarkedRetraction filtration generators weights marked weight_pos generator_mem t m D
      (centeredElement t m a b n v)).coord =
        (lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
          (realMarkedAffineShift filtration generators weights marked weight_pos generator_mem t ((m : ℝ) • v)
            (n • sourceLift t a (fun i => (m : ℝ)⁻¹ * b i))) := by
  let f := affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n
  have heq : normalizedMarkedRetraction filtration generators weights marked weight_pos generator_mem t m D
      (centeredElement t m a b n v) = parameter t ((m : ℝ) • v) * f *
        (parameter t ((m : ℝ) • v))⁻¹ := by
    change parameter t ((m : ℝ) • -(torusPhaseLinear (phase t m)
      (centeredElement t m a b n v).coord)) *
        (f * parameter t ((m : ℝ) • -v)) = _
    rw [centeredElement_phase D m hm, neg_neg, smul_neg, ← parameter_inv]
    exact (mul_assoc _ _ _).symm
  rw [heq]
  change conjugationCoord (parameter t ((m : ℝ) • v)) (n • projectedLift t a _) = _
  have hlift : n • projectedLift t a (fun i => (m : ℝ)⁻¹ * b i) =
      (lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
        (n • sourceLift t a (fun i => (m : ℝ)⁻¹ * b i)) := (map_smul _ _ _).symm
  rw [hlift]
  exact realMarkedAffineShift_conjugation filtration generators weights marked weight_pos generator_mem
    t (by decide) ((m : ℝ) • v) _

theorem localCharacter_centeredElement {t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    localCharacter m D η (centeredElement t m a b n v) =
      CircleFourier.character ((n * (a + ∑ i, v i * b i) : ℝ) : CircleFourier.Circle) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsum : a + ∑ i, ((m : ℝ) • v) i * ((m : ℝ)⁻¹ * b i) = a + ∑ i, v i * b i := by
    apply congrArg (a + ·)
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [localCharacter, centeredElement_retraction_coord D m hm]
  simp only [map_smul, smul_eq_mul]
  rw [shiftedLift_coordinate η hη, hsum]

end Erdos3.QuadraticMarked

end

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped BigOperators

noncomputable def localOrbit {N : ℕ} (t m : ℕ) (a : ℝ) (b u c : Fin t → ℝ) (h₀ : ZMod N) :
    (multidegree t).realification.PolynomialOrbit :=
  Mul.mul (α := (multidegree t).realification.PolynomialOrbit)
    (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i))
    (realMarkedParameterOrbit filtration generators weights marked weight_pos generator_mem t
      (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i))

theorem localOrbit_eval {N : ℕ} (t m : ℕ) (a : ℝ) (b u c : Fin t → ℝ)
    (h₀ h : ZMod N) (n : ℤ) :
    (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (localOrbit t m a b u c h₀) =
        affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n *
          parameter t (fun i => -(m : ℝ) * (((h.val : ℝ) - h₀.val) * u i - c i)) := by
  have he : (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i)) =
        affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n :=
    NilpotentLieBCHGroup.ext (pureOrbit_eval t a _ h.val n)
  let E := (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
  let P : (multidegree t).realification.PolynomialOrbit :=
    realMarkedParameterOrbit filtration generators weights marked weight_pos generator_mem t
      (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i)
  have hmul : E (localOrbit t m a b u c h₀) =
      E (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i)) * E P := E.map_mul _ _
  apply hmul.trans
  change E (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i)) = _ at he
  rw [he]
  apply congrArg (affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n * ·)
  apply (realMarkedParameterOrbit_eval filtration generators weights marked weight_pos generator_mem t
    (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i) h.val n).trans
  apply congrArg (parameter t)
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_natCast]
  ring

noncomputable def latticeCorrection {N : ℕ} (t m : ℕ) (u c : Fin t → ℝ) (h₀ h : ZMod N) :
    (multidegree t).realification.Group :=
  parameter t ((m : ℝ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℝ))

theorem latticeCorrection_mem {N t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d) (m : ℕ)
    (hlat : ∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
      filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice)
    (u c : Fin t → ℝ) (h₀ h : ZMod N) : latticeCorrection t m u c h₀ h ∈ D.realLattice :=
  realMarkedParameterElement_scaled_integer_mem filtration generators weights marked weight_pos generator_mem
    t m D hlat (fun i => -affineCyclicTorusCarry u c h₀ h i)

theorem localOrbit_right_normalization {N : ℕ} (t m : ℕ) (a : ℝ) (b u c : Fin t → ℝ)
    (h₀ h : ZMod N) (n : ℤ) :
    (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (localOrbit t m a b u c h₀) * (latticeCorrection t m u c h₀ h)⁻¹ =
        centeredElement t m a b n (affineCyclicTorusLocalLift u c h₀ h) := by
  rw [localOrbit_eval, latticeCorrection, parameter_inv, mul_assoc, parameter_mul]
  apply congrArg (affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n * ·)
  apply congrArg (parameter t)
  funext i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Int.cast_neg,
    affineCyclicTorusLocalLift_eq_sub_carry]
  ring

theorem localOrbit_quotient {N t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d) (m : ℕ)
    (hlat : ∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
      filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice)
    (a : ℝ) (b u c : Fin t → ℝ) (h₀ h : ZMod N) (n : ℤ) :
    (QuotientGroup.mk ((multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (localOrbit t m a b u c h₀)) : D.Space) =
        QuotientGroup.mk (centeredElement t m a b n (affineCyclicTorusLocalLift u c h₀ h)) := by
  have hc := latticeCorrection_mem D m hlat u c h₀ h
  calc
    _ = QuotientGroup.mk ((multidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n) (localOrbit t m a b u c h₀) *
          (latticeCorrection t m u c h₀ h)⁻¹) :=
      (quotient_mk_mul_mem D.realLattice _ ⟨_, D.realLattice.inv_mem hc⟩).symm
    _ = _ := congrArg QuotientGroup.mk (localOrbit_right_normalization t m a b u c h₀ h n)

theorem localOrbit_observable {N t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (m : ℕ) (hm : 0 < m)
    (hlat : ∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
      filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice)
    (G : D.Space → ℂ)
    (hG : ∀ g : D.RealGroup, (∀ i, |torusPhaseLinear (phase t m) g.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk g) = localCharacter m D η g)
    (a : ℝ) (b u c : Fin t → ℝ) (h₀ h : ZMod N)
    (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) (n : ℤ) :
    G (QuotientGroup.mk ((multidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (localOrbit t m a b u c h₀))) =
        CircleFourier.character (((n : ℝ) * (a + ∑ i, affineCyclicTorusLocalLift u c h₀ h i * b i) : ℝ) :
          CircleFourier.Circle) := by
  rw [localOrbit_quotient D m hlat]
  apply (hG _ ?_).trans
    (localCharacter_centeredElement D η hη m hm a b n (affineCyclicTorusLocalLift u c h₀ h))
  intro i
  rw [centeredElement_phase D m hm]
  simpa only [Pi.neg_apply, abs_neg] using hsmall i

end Erdos3.QuadraticMarked

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.InducedUnitRankFamily
namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

theorem exists_combined_factor_correlation {A I J K : Type*}
    {degree N : ℕ} [NeZero N] {p : ℝ}
    (f : A → ZMod N → ℂ) (g : K → ZMod N → ℂ)
    (a : I → ZMod N → ℂ) (b : J → ZMod N → ℂ)
    (c : I × J → ZMod N → ℂ) (j : J → K)
    (hc : ∀ ij x, c ij x = a ij.1 x * b ij.2 x)
    (W : NativeVectorCorrelation degree N p (fun z : A × (I × J) => fun x =>
      f z.1 x * star (g (j z.2.2) x) * star (a z.2.1 x) * star (b z.2.2 x))) :
    Nonempty (NativeVectorCorrelation degree N p (fun z : (A × K) × (I × J) => fun x =>
      f z.1.1 x * star (g z.1.2 x) * star (c z.2 x))) := by
  refine ⟨W.mapCoordinates _ (fun z => ((z.1, j z.2.2), z.2)) ?_⟩
  intro z x
  rw [hc, star_mul]
  ring

end Erdos3.NativeVectorCorrelation

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {τ K I : Type} [Fintype I] {s r N n degree : ℕ} [NeZero N]
  {b p q P Z : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
  {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
  (D : R.CommonData P) (t : ℕ)
  (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
  (f : τ → K → ZMod N → ℂ)

def HasUnitRankInducedCorrelationFamily (B C : ℝ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp B ∧
    ∃ F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ
        ((I × I) × (I × Fin k)) C,
      ∃ (m : ℕ) (_hm : 0 < m), (m : ℝ) ≤ Real.exp B ∧
        ∃ d : ℕ, ∃ E : RationalFilteredNilmanifold
          (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
          ∃ M : E.MultidegreeStructure (mixedCorrelationDegree s),
            M.filtration = D.markedQuotientMultidegree t ∧ M.ComplexityLE B ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
               D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
               D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
                  IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 E.basis
             letI := E.metricSpace
             ∃ G : Fin k → E.Space → ℂ,
               (∀ j z, ‖G j z‖ ≤ 2) ∧
               (∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) ∧
               ∀ z, Nonempty (NativeVectorCorrelation degree N B
                 (fun ij : (K × Fin k) × ((I × I) × (I × Fin k)) => fun a =>
                   f z ij.1.1 a * star (G ij.1.2 (QuotientGroup.mk
                     ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
                       (correlationInput ((h z).val : ℤ) (a.val : ℤ))
                       (D.localPhaseMarkedOrbit t x y u c h₀ m)))) *
                   star (F.eval z ij.2 (fun _ => (a.val : ℤ))))))

theorem HasCommonInducedCorrelationFamily.combineLower
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    {e k : ℕ} (Q : RationalFilteredNilmanifold D.DependentQuotient s e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T (Fin k) Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    {B C : ℝ} (hk : 0 < k) (hkB : (k : ℝ) ≤ Real.exp B)
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ ((I × I) × (I × Fin k)) C)
    (hF : ∀ z ij w, F.eval z ij w =
      (V.observable ij.1.1 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (v z))) *
        star (V.observable ij.1.2 (QuotientGroup.mk
          (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (a z))))) *
      mapDifferenceObservable V U D.dependentQuotientMap hφ ij.2 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (a z))))
    (hcommon : D.HasCommonInducedCorrelationFamily (degree := degree)
      t A Q V U hφ x y u c h₀ h a v f B) :
    D.HasUnitRankInducedCorrelationFamily (I := I) (degree := degree) t x y u c h₀ h f B C := by
  obtain ⟨m, hm, hmB, d₁, _, E₁, M, hMF, hM, hdata⟩ := hcommon
  refine ⟨k, hk, hkB, F, m, hm, hmB, d₁, E₁, M, hMF, hM, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E₁.basis
  let := E₁.metricSpace
  obtain ⟨G, hGn, hGL, hcorr⟩ := hdata
  refine ⟨G, hGn, hGL, ?_⟩
  intro z
  exact NativeVectorCorrelation.exists_combined_factor_correlation (f z)
    (fun j w => G j (QuotientGroup.mk
      ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput ((h z).val : ℤ) (w.val : ℤ))
        (D.localPhaseMarkedOrbit t x y u c h₀ m))))
    (fun (ij : I × I) w => V.observable ij.1 (QuotientGroup.mk
      (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (w.val : ℤ)) (v z))) *
      star (V.observable ij.2 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (w.val : ℤ)) (a z)))))
    (fun (ij : I × Fin k) w => mapDifferenceObservable V U D.dependentQuotientMap hφ ij
      (QuotientGroup.mk (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (w.val : ℤ)) (a z))))
    (fun ij w => F.eval z ij (fun _ => (w.val : ℤ))) Prod.snd
    (fun ij w => hF z ij (fun _ => (w.val : ℤ))) (Classical.choice (hcorr z))

variable (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : A.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z)
  (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))

theorem HasCoveredInducedCorrelationFamily.combineLower
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hcovered : D.HasCoveredInducedCorrelationFamily (degree := degree)
      t A T V x y u c h₀ h a v f B)
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    (E : RationalFilteredNilmanifold L s d) (U : E.DegreeRankStructure (r + 1))
    (hfirst : E.HasLowerRankOrbitFamily U (fun _ : Unit => 1)
      (fun z (ij : I × I) w => V.observable ij.1 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (v z))) *
        star (V.observable ij.2 (QuotientGroup.mk
          (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (a z))))) C) :
    D.HasUnitRankInducedCorrelationFamily (I := I) (degree := degree)
      t x y u c h₀ h f B (productNiltestBudget (C + B + 2)) := by
  obtain ⟨Λ, _, l, hl, hin, hout, _, e, _, Q, S, _, _, hφ, V₀, _, hVobs, hcoeff⟩ := hcovered
  let A₀ := A.withLattice Λ l hl hin hout
  let T₀ := T.withLattice Λ l hl hin hout
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨k, hk, hkB, U₀, hcommon, hsecond⟩ := hcoeff
  obtain ⟨F, _, hF⟩ := exists_binary_lower_rank_unit_family (p := C + B + 2) E A₀ U T₀
    (fun _ : Unit => 1) _ _ (by linarith : 2 ≤ C + B + 2)
    (hfirst.mono (show C ≤ C + B + 2 by linarith))
    (hsecond.mono (show B ≤ C + B + 2 by linarith))
  apply HasCommonInducedCorrelationFamily.combineLower D t x y u c h₀ h f
    A₀ Q V₀ U₀ hφ a v hk hkB F ?_ hcommon
  intro z ij w
  rw [hF]
  have hvalue (i : I) (o : A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) :
      V₀.observable i (QuotientGroup.mk
        (A₀.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w o)) =
      V.observable i (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w o)) := hVobs i _
  simp only [hvalue]
  rfl

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductVerticalization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_common_vertical_correlators :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ (H' : Finset G) (S : G → D.Niltest (fun _ : Unit => 1)) (eta : L →ₗ[ℚ] ℚ),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        (∀ i, rationalLogHeight (eta (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ h, (S h).orbit = (T h).orbit ∧ (S h).normBound ≤ 1 ∧
          (S h).ComplexityLE ((p + C) ^ C)) ∧
        (∀ h k, (S h).observable = (S k).observable) ∧
        (∀ h z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          (S h).observable (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * (S h).observable x) ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional eta z.coord = n) ∧
        ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  classical
  obtain ⟨a, _, hverticalBudget⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 1 + (X + 1 + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ s d D T H hH p hp hT hcap hsame N _ weight hweight hcorr
  obtain ⟨h₀, hh₀⟩ := hH
  let q := (p + 1 + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : p + 1 + q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p + 1 ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hVq : verticalDecompositionBudget (p + 1) ≤ q := hverticalBudget (p + 1) (by linarith)
  have hrho : 0 < Real.exp (-p) / 2 := by positivity
  have hrhoinv : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div, Real.exp_neg]; field_simp
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨J, inst, eta, V, hcard, hheight, hV, hvert, hint, happ, _⟩ :=
    (T h₀).exists_vertical_decomposition_preserving_bounds (by linarith : 0 ≤ p + 1)
      ((hT h₀ hh₀).mono (by linarith : p ≤ p + 1)) hrho hrhoinv
  let := inst
  have hcardq : (Fintype.card J : ℝ) ≤ Real.exp q := hcard.trans (Real.exp_le_exp.mpr hVq)
  let U (h : G) (j : J) : D.Niltest (fun _ : Unit => 1) := { V j with orbit := (T h).orbit }
  have hchoose (h : {h // h ∈ H}) : ∃ j : J,
      Real.exp (-p) / (2 * Real.exp q) ≤
        ‖𝔼 x, weight h.val x * star ((U h.val j).evalCyclic N (fun _ => x))‖ := by
    apply exists_correlating_summand Finset.univ_nonempty (weight h.val)
      (fun x => (T h.val).evalCyclic N (fun _ => x))
      (fun j x => (U h.val j).evalCyclic N (fun _ => x))
      (Real.exp_pos (-p)) (Real.exp_pos q) hcardq
      (fun x _ => hweight h.val h.property x) _ (hcorr h.val h.property)
    intro x _
    change ‖(∑ j, (V j).observable (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ => 1)
        (fun _ => (x.val : ℤ)) (T h.val).orbit))) -
      (T h.val).observable (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ => 1)
          (fun _ => (x.val : ℤ)) (T h.val).orbit))‖ ≤ _
    rw [hsame h.val h₀]
    exact happ _
  choose choice hchoice using hchoose
  let code : G → J := fun h => if hh : h ∈ H then choice ⟨h, hh⟩ else choice ⟨h₀, hh₀⟩
  obtain ⟨j, _, H', hsub, hnonempty, hconstant, hdense⟩ :=
    exists_exponential_constant_fiber H ⟨h₀, hh₀⟩ code Set.univ (Set.toFinite _)
      (fun _ _ => Set.mem_univ _) (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hcardq)
  have hselected (h : G) (hh : h ∈ H') : Real.exp (-p) / (2 * Real.exp q) ≤
      ‖𝔼 x, weight h x * star ((U h j).evalCyclic N (fun _ => x))‖ := by
    have hcode : choice ⟨h, hsub hh⟩ = j := by
      simpa only [code, dif_pos (hsub hh)] using hconstant h hh
    simpa only [hcode] using hchoice ⟨h, hsub hh⟩
  have hne : ∃ x, (V j).observable x ≠ 0 := by
    by_contra! hz
    obtain ⟨h, hh⟩ := hnonempty
    have hc := hselected h hh
    have hzero (x : ZMod N) : (U h j).evalCyclic N (fun _ => x) = 0 := hz _
    simp only [hzero, star_zero, mul_zero, Finset.expect_const_zero, norm_zero] at hc
    exact (not_le_of_gt (by positivity : 0 < Real.exp (-p) / (2 * Real.exp q))) hc
  refine ⟨H', fun h => U h j, eta j, hsub, hnonempty, ?_, ?_, ?_, fun _ _ => rfl,
    fun _ z hz x => hvert j z hz x, hint j hne, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro i
    exact (hheight j i).trans (hVq.trans hqC)
  · intro h
    refine ⟨rfl, ?_, ?_⟩
    · change (V j).normBound ≤ 1
      rw [(hV j).2.2.1]
      exact hcap h₀ hh₀
    · exact (hV j).1.mono hpC
  · intro h hh
    apply le_trans _ (hselected h hh)
    calc
      _ ≤ Real.exp (-(p + q) - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(p + q)) / 2 := exp_sub_one_le_half_exp _
      _ = Real.exp (-p) / (2 * Real.exp q) := by
        rw [show -(p + q) = -p - q by ring, Real.exp_sub]
        ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

theorem exists_common_unit_vertical_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
              (Fin (n + 1)) ((p + C) ^ C),
            ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 x, weight h x * star (V.observable 0 (QuotientGroup.mk
                (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                  (fun _ => (x.val : ℤ)) (T h).orbit)))‖ := by
  obtain ⟨a, _, hvertical⟩ := exists_common_vertical_correlators
  obtain ⟨b, _, hcomplete⟩ := exists_native_unit_vertical_completion s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + Q + (Q + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hT hnorm hsame N _ weight hweight hcorr
  let q := (p + a) ^ a
  let q₂ := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
  have htotal : p + q + q₂ + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, q₂, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hq₂C : q₂ ≤ (p + C) ^ C := by linarith
  obtain ⟨H', S, eta, hsub, hH', hdense, hheight, hS, hSsame, hvert, hint, hScorr⟩ :=
    hvertical D T H hH hp hT hnorm hsame weight hweight hcorr
  obtain ⟨h₀, hh₀⟩ := hH'
  have hmean : Real.exp (-q) ≤ 𝔼 x, ‖(S h₀).evalCyclic N (fun _ => x)‖ := by
    apply (hScorr h₀ hh₀).trans
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le_expect
    intro x _
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (hweight h₀ (hsub hh₀) x)
  obtain ⟨x₀, _, hx₀⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  let y : D.Space := QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
    (fun _ => (x₀.val : ℤ)) (S h₀).orbit)
  obtain ⟨n, hn, hnq, K, hK, v, hv0, hvunit, hvnorm, hvLip, hvvertical⟩ :=
    hcomplete D (S h₀) hq (hS h₀).2.2 (hS h₀).2.1 eta (hvert h₀) y hx₀
  let V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
      (Fin (n + 1)) ((p + C) ^ C) := {
    observable := v
    unit := hvunit
    norm := hvnorm
    lipBound := K
    lip_bound := hK.trans (Real.exp_le_exp.mpr hq₂C)
    lipschitz := hvLip
    frequency := eta
    height := fun i => (hheight i).trans hqC
    vertical := hvvertical
    integral := hint
  }
  refine ⟨H', hsub, ⟨h₀, hh₀⟩,
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC)) (Nat.cast_nonneg _)).trans hdense,
    n, hn, hnq.trans (Real.exp_le_exp.mpr hq₂C), V, ?_⟩
  intro h hh
  have hvalue (x : ZMod N) : V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)) = (S h).evalCyclic N (fun _ => x) / 2 := by
    change v 0 _ = _
    rw [hv0, hSsame h₀ h]
    change (S h).observable _ / 2 = (S h).observable _ / 2
    rw [(hS h).1]
  have heq : (𝔼 x, weight h x * star (V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)))) =
      (𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))) / 2 := by
    simp only [hvalue, star_div₀, star_ofNat, ← mul_div_assoc, ← Finset.expect_div]
  rw [heq, norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  apply le_trans _ (div_le_div_of_nonneg_right (hScorr h hh) (by norm_num : (0 : ℝ) ≤ 2))
  apply le_trans _ (exp_sub_one_le_half_exp (-q))
  apply Real.exp_le_exp.mpr
  linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_native_vertical_derivative_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ},
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → (B : NativeCommonDerivativeModels s N p f) →
      (∀ h, B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
        (B.test h).orbit = 1) →
      ∃ R : NativeCommonDerivativeModels s N ((p + C) ^ C) f,
        Nonempty (NativeVerticalDerivativeData R) := by
  obtain ⟨a, _, hvertical⟩ := RationalFilteredNilmanifold.exists_common_vertical_correlators
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro s N _ p f hp hf B hnormalized
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨H, S, eta, _, hH, hdense, hheight, hS, hsame, hvert, hint, hcorr⟩ :=
    hvertical B.model B.test B.shifts B.nonempty hp (fun h _ => B.complexity h)
      (fun h _ => B.norm h) B.common_observable (fun h x => multiplicativeDerivative f h x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h x) B.correlation
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + (p + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)
      _ = Real.exp (-((p + a) ^ a)) * (Real.exp (-p) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((p + a) ^ a)) * B.shifts.card :=
        mul_le_mul_of_nonneg_left B.density (Real.exp_nonneg _)
      _ ≤ _ := hdense
  let R : NativeCommonDerivativeModels s N ((p + C) ^ C) f := {
    L := B.L
    dim := B.dim
    model := B.model
    geometry := B.geometry.mono B.model hpC
    shifts := H
    nonempty := hH
    density := hfinaldensity
    test := S
    norm := fun h => (hS h).2.1
    complexity := fun h => (hS h).2.2.mono hqC
    common_observable := hsame
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh) }
  refine ⟨R, ⟨{
    normalized := ?_
    frequency := eta
    height := fun i => (hheight i).trans hqC
    vertical := hvert
    integral := hint }⟩⟩
  intro h
  change B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (S h).orbit = 1
  rw [(hS h).1]
  exact hnormalized h

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_native_unit_factor_replacement (s degree : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      ∀ {N : ℕ} [NeZero N] (f : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation degree N p
        (fun _ : Unit => fun x => f h x * star ((T h).evalCyclic N (fun _ => x))))) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
              (Fin (n + 1)) ((p + C) ^ C),
            ∀ h ∈ H', Nonempty (NativeVectorCorrelation degree N ((p + C) ^ C)
              (fun _ : Unit => fun x => f h x * star (V.observable 0 (QuotientGroup.mk
                (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                  (fun _ => (x.val : ℤ)) (T h).orbit))))) := by
  classical
  obtain ⟨a, _, hselect⟩ := exists_common_unit_vertical_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (2 * X + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hT hnorm hsame N _ f hf hcorr
  let W (h : {h // h ∈ H}) := Classical.choice (hcorr h.val h.property)
  let weight (h : G) (x : ZMod N) : ℂ :=
    if hh : h ∈ H then
      f h x * star (((W ⟨h, hh⟩).test.expNormalize p).evalCyclic N (fun _ => x)) else 0
  have hweight (h : G) (hh : h ∈ H) (x : ZMod N) : ‖weight h x‖ ≤ 1 := by
    simp only [weight, dif_pos hh, norm_mul, norm_star]
    have hn : ‖((W ⟨h, hh⟩).test.expNormalize p).evalCyclic N (fun _ => x)‖ ≤ 1 := by
      apply (((W ⟨h, hh⟩).test.expNormalize p).norm_evalCyclic_le N (fun _ => x)).trans
      exact_mod_cast (W ⟨h, hh⟩).test.expNormalize_norm (W ⟨h, hh⟩).complexity
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h hh x)).trans hn
  have hweightcorr (h : G) (hh : h ∈ H) : Real.exp (-(2 * p + 2)) ≤
      ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖ := by
    let Wh := W ⟨h, hh⟩
    have hscale (x : ZMod N) : (Wh.test.expNormalize p).evalCyclic N (fun _ => x) =
        (Real.exp (-p) : ℂ) * Wh.test.evalCyclic N (fun _ => x) := rfl
    have heq : (𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))) =
        (Real.exp (-p) : ℂ) * (𝔼 x, (f h x * star ((T h).evalCyclic N (fun _ => x))) *
          star (Wh.test.evalCyclic N (fun _ => x))) := by
      simp only [weight, dif_pos hh]
      change (𝔼 x, (f h x * star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x))) *
        star ((T h).evalCyclic N (fun _ => x))) = _
      simp only [hscale, star_mul, Complex.star_def, Complex.conj_ofReal, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    rw [heq, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
    calc
      _ ≤ Real.exp (-p) * Real.exp (-p) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left Wh.correlation (Real.exp_nonneg _)
  obtain ⟨H', hsub, hH', hdense, n, hn, hnq, V, hVc⟩ :=
    hselect D T H hH (by linarith : 0 ≤ 2 * p + 2)
      (fun h hh => (hT h hh).mono (by linarith : p ≤ 2 * p + 2)) hnorm hsame
      weight hweight hweightcorr
  let q := (2 * p + 2 + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  refine ⟨H', hsub, hH',
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC)) (Nat.cast_nonneg _)).trans hdense,
    n, hn, hnq.trans (Real.exp_le_exp.mpr hqC), V.mono hqC, ?_⟩
  intro h hh
  let Wh := W ⟨h, hsub hh⟩
  refine ⟨{
    L := Wh.L
    dim := Wh.dim
    model := Wh.model
    test := Wh.test.expNormalize p
    complexity := (Wh.test.expNormalize_complexity Wh.complexity).mono hpC
    coordinate := ()
    correlation := ?_
  }⟩
  have hc := (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hVc h hh)
  have hweightval (x : ZMod N) : weight h x =
      f h x * star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x)) := by
    simp only [weight, dif_pos (hsub hh), Wh]
  change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x,
    (f h x * star (V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)))) *
      star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x))‖
  have heq : (𝔼 x, (f h x * star (V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)))) *
        star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x))) =
      (𝔼 x, weight h x * star (V.observable 0 (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (T h).orbit)))) := by
    simp only [hweightval]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [heq]
  exact hc

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_native_two_factor_unit_replacement (s t degree : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra ℚ L₁]
      [LieRing L₂] [LieAlgebra ℚ L₂]
      [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₂)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂)] [T2Space (ℝ ⊗[ℚ] L₂)] {d₁ d₂ : ℕ}
      (D₁ : RationalFilteredNilmanifold L₁ s d₁) (D₂ : RationalFilteredNilmanifold L₂ t d₂)
      (T : G → D₁.Niltest (fun _ : Unit => 1)) (S : G → D₂.Niltest (fun _ : Unit => 1))
      (H : Finset G), H.Nonempty → ∀ {p : ℝ}, 0 ≤ p →
      (∀ h ∈ H, (T h).ComplexityLE p) → (∀ h ∈ H, (S h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) → (∀ h ∈ H, (S h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      (∀ h k, (S h).observable = (S k).observable) →
      ∀ {N : ℕ} [NeZero N] (f : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation degree N p (fun _ : Unit => fun x =>
        f h x * star ((S h).evalCyclic N (fun _ => x)) * star ((T h).evalCyclic N (fun _ => x))))) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n₁ : ℕ, 0 < n₁ ∧ (n₁ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V₁ : D₁.UnitVerticalObservable (D₁.filtration.realification.subgroup s)
              (Fin (n₁ + 1)) ((p + C) ^ C),
            ∃ n₂ : ℕ, 0 < n₂ ∧ (n₂ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ V₂ : D₂.UnitVerticalObservable (D₂.filtration.realification.subgroup t)
                  (Fin (n₂ + 1)) ((p + C) ^ C),
                ∀ h ∈ H', Nonempty (NativeVectorCorrelation degree N ((p + C) ^ C)
                  (fun _ : Unit => fun x => f h x *
                    star (V₂.observable 0 (QuotientGroup.mk
                      (D₂.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) (S h).orbit))) *
                    star (V₁.observable 0 (QuotientGroup.mk
                      (D₁.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) (T h).orbit))))) := by
  obtain ⟨a, _, hfirst⟩ := exists_native_unit_factor_replacement s degree
  obtain ⟨b, _, hsecond⟩ := exists_native_unit_factor_replacement t degree
  let X : Polynomial ℕ := Polynomial.X
  let Q₁ : Polynomial ℕ := (X + Polynomial.C a) ^ a
  let P₂ : Polynomial ℕ := X + Q₁ + 2
  let Q₂ : Polynomial ℕ := (P₂ + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q₁ + Q₂ + 2)
  refine ⟨C, hC, ?_⟩
  intro G L₁ L₂ _ _ _ _ _ _ _ _ _ _ _ _ d₁ d₂ D₁ D₂ T S H hH p hp
    hT hS hnT hnS hcT hcS N _ f hf hcorr
  have hfS (h : G) (hh : h ∈ H) (x : ZMod N) :
      ‖f h x * star ((S h).evalCyclic N (fun _ => x))‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    have hn : ‖(S h).evalCyclic N (fun _ => x)‖ ≤ 1 := by
      apply ((S h).norm_evalCyclic_le N (fun _ => x)).trans
      exact_mod_cast hnS h hh
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h hh x)).trans hn
  obtain ⟨H₁, hH₁H, hH₁, hdense₁, n₁, hn₁, hcount₁, V₁, hcorr₁⟩ :=
    hfirst D₁ T H hH hp hT hnT hcT
      (fun h x => f h x * star ((S h).evalCyclic N (fun _ => x))) hfS hcorr
  let q₁ := (p + a) ^ a
  let p₂ := p + q₁ + 2
  let q₂ := (p₂ + b) ^ b
  have hq₁ : 0 ≤ q₁ := by dsimp [q₁]; positivity
  have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
  have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
  have hpp₂ : p ≤ p₂ := by dsimp [p₂]; linarith
  have hq₁p₂ : q₁ ≤ p₂ := by dsimp [p₂]; linarith
  let f₂ (h : G) (x : ZMod N) := f h x * star (V₁.observable 0 (QuotientGroup.mk
    (D₁.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      (fun _ => (x.val : ℤ)) (T h).orbit)))
  have hf₂ (h : G) (hh : h ∈ H₁) (x : ZMod N) : ‖f₂ h x‖ ≤ 1 := by
    change ‖f h x * star (V₁.observable 0 _)‖ ≤ 1
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h (hH₁H hh) x)).trans (V₁.norm 0 _)
  have hcorr₂ (h : G) (hh : h ∈ H₁) : Nonempty (NativeVectorCorrelation degree N p₂
      (fun _ : Unit => fun x => f₂ h x * star ((S h).evalCyclic N (fun _ => x)))) := by
    obtain ⟨Wh⟩ := hcorr₁ h hh
    refine ⟨(Wh.mono hq₁p₂).mapCoordinates _ id ?_⟩
    intro i x
    dsimp only [id_eq, f₂]
    ring
  obtain ⟨H₂, hH₂H₁, hH₂, hdense₂, n₂, hn₂, hcount₂, V₂, hfinal⟩ :=
    hsecond D₂ S H₁ hH₁ hp₂ (fun h hh => (hS h (hH₁H hh)).mono hpp₂)
      (fun h hh => hnS h (hH₁H hh)) hcS f₂ hf₂ hcorr₂
  have htotal : p + q₁ + q₂ + 2 ≤ (p + C) ^ C := by
    simpa [X, Q₁, P₂, Q₂, q₁, p₂, q₂, Polynomial.eval₂_pow] using hbudget p hp
  have hq₁C : q₁ ≤ (p + C) ^ C := by linarith
  have hq₂C : q₂ ≤ (p + C) ^ C := by linarith
  refine ⟨H₂, hH₂H₁.trans hH₁H, hH₂, ?_, n₁, hn₁,
    hcount₁.trans (Real.exp_le_exp.mpr hq₁C), V₁.mono hq₁C, n₂, hn₂,
    hcount₂.trans (Real.exp_le_exp.mpr hq₂C), V₂.mono hq₂C, ?_⟩
  · calc
      _ ≤ Real.exp (-(q₁ + q₂)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-q₂) * (Real.exp (-q₁) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q₂) * H₁.card := mul_le_mul_of_nonneg_left hdense₁ (Real.exp_nonneg _)
      _ ≤ _ := hdense₂
  · intro h hh
    obtain ⟨Wh⟩ := hfinal h hh
    refine ⟨(Wh.mono hq₂C).mapCoordinates _ id ?_⟩
    intro i x
    change f h x * star (V₂.observable 0 _) * star (V₁.observable 0 _) =
      f₂ h x * star (V₂.observable 0 _)
    dsimp only [f₂]
    ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_mixed_of_bounded (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ H : Finset (ZMod N), H.Nonempty → Real.exp (-p) * N ≤ (H.card : ℝ) →
      ∀ (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I),
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (F.eval i (correlationInput (h.val : ℤ) (n.val : ℤ)))‖) →
      Nonempty (NativeMixedCorrelation s N ((p + C) ^ C) f) := by
  obtain ⟨A, _, hselect⟩ := RationalFilteredNilmanifold.exists_common_unit_vertical_correlators
    (∑ j, mixedCorrelationDegree s j)
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q + 2)
  refine ⟨C, hC, ?_⟩
  intro I N _ p hp f hf H hH hdense F i hcorr
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpR : p ≤ (p + C) ^ C := by linarith
  have hqR : q ≤ (p + C) ^ C := by linarith
  have htwo : 2 ≤ (p + C) ^ C := by linarith
  let T (h : ZMod N) := F.slice i (h.val : ℤ)
  have hweight (h x : ZMod N) : ‖multiplicativeDerivative f h x‖ ≤ 1 := by
    simp only [multiplicativeDerivative, norm_mul, norm_star]
    exact (mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hTcorr (h : ZMod N) (hh : h ∈ H) : Real.exp (-p) ≤
      ‖𝔼 x : ZMod N, multiplicativeDerivative f h x * star ((T h).evalCyclic N (fun _ => x))‖ := by
    simpa only [T, RationalFilteredNilmanifold.Niltest.evalCyclic, NativeBoundedMultidegreeFamily.slice_eval]
      using hcorr h hh
  obtain ⟨J, hJH, hJ, hJdense, n, _, hn, V, hVcorr⟩ :=
    hselect F.model T H hH hp (fun h _ => F.slice_complexity i h.val)
      (fun h _ => (F.slice_norm i h.val).le)
      (fun h k => (F.slice_observable i h.val).trans (F.slice_observable i k.val).symm)
      (multiplicativeDerivative f) (fun h _ x => hweight h x) hTcorr
  have hnR : (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) := hn.trans (Real.exp_le_exp.mpr hqR)
  let M := F.toNilcharacter hpR hnR (V.mono hqR)
  have hMeval (h x : ZMod N) : M.evalCyclic N (0 : Fin (n + 1)) (correlationInput h x) =
      V.observable 0 (QuotientGroup.mk (F.model.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (T h).orbit)) := by
    have hinput : (fun j => ((correlationInput h x j).val : ℤ)) =
        correlationInput (h.val : ℤ) (x.val : ℤ) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    change M.eval (0 : Fin (n + 1)) (fun j => ((correlationInput h x j).val : ℤ)) = _
    rw [hinput]
    change V.observable 0 (QuotientGroup.mk (F.multi.filtration.realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) (x.val : ℤ)) F.orbit)) = _
    rw [F.slice_orbit_eval i (h.val : ℤ)]
  refine ⟨{ shifts := J, nonempty := hJ, density := ?_, mixed := M, correlation := ?_ }⟩
  · simp only [ZMod.card]
    calc
      Real.exp (-((p + C) ^ C)) * N ≤ Real.exp (-(p + q)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H.card := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ J.card := hJdense
  · intro h hh
    apply NativeVectorCorrelation.exists_of_mean (s - 1) N (nativeMixedResidual f M h) htwo
    refine ⟨(0 : Fin (n + 1)), ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤
      ‖𝔼 x : ZMod N, multiplicativeDerivative f h x *
        star (M.evalCyclic N (0 : Fin (n + 1)) (correlationInput h x))‖
    simp only [hMeval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqR)).trans (hVcorr h hh)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem NativeUnitRankFamily.withOrbit_observable
    {σ τ I : Type*} [Fintype I] {w : σ → ℕ} {s r : ℕ} {p : ℝ}
    (F : NativeUnitRankFamily w s r τ I p) (i : I) (t : τ) :
    ((F.test i).withOrbit (F.orbit t)).observable = (F.test i).observable := rfl

theorem exists_native_correlation_of_sliced_unit_products
    {I K : Type} [Fintype I] {s r N : ℕ} [NeZero N] {p q P : ℝ} {f : ZMod N → ℂ}
    (J : Finset (ZMod N))
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
    (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
    (iM : K) (H : Finset {h // h ∈ J}) (hH : H.Nonempty)
    (hdense : Real.exp (-P) * N ≤ (H.card : ℝ)) (hpP : p ≤ P) (hqP : q ≤ P)
    {n₁ n₂ : ℕ} (hn₁ : (n₁ + 1 : ℝ) ≤ Real.exp q) (hn₂ : (n₂ + 1 : ℝ) ≤ Real.exp q)
    (V₁ : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s)
      (Fin (n₁ + 1)) q)
    (V₂ : M.model.UnitVerticalObservable
      (M.model.filtration.realification.subgroup (∑ i, mixedCorrelationDegree s i)) (Fin (n₂ + 1)) q)
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N q (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
        (M.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (M.slice iM (h.val.val : ℤ)).orbit))) *
        star (V₁.observable 0 (QuotientGroup.mk
          (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
            (fun _ => (x.val : ℤ)) (F.orbit h))))))) :
    Nonempty (NativeCorrelationStructure s r N P f) := by
  apply exists_native_correlation_of_unit_products J F M H hH hdense hpP
    (hn₁.trans (Real.exp_le_exp.mpr hqP)) (hn₂.trans (Real.exp_le_exp.mpr hqP))
    (V₁.mono hqP) (V₂.mono hqP)
  intro h hh
  obtain ⟨Wh⟩ := hcorr h hh
  refine ⟨(Wh.mono hqP).mapCoordinates _ id ?_⟩
  intro i x
  change multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
    (M.multi.filtration.realification.polynomialOrbitEval
      (correlationInput (h.val.val : ℤ) (x.val : ℤ)) M.orbit))) *
      star (V₁.observable 0 (QuotientGroup.mk
        (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (F.orbit h)))) =
    multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
      (M.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (M.slice iM (h.val.val : ℤ)).orbit))) *
      star (V₁.observable 0 (QuotientGroup.mk
        (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (F.orbit h))))
  rw [M.slice_orbit_eval]

theorem exists_native_sliced_product_correlation
    {I K : Type} [Fintype I] {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    {J : Finset (ZMod N)}
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
    (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
    (iF : I) (iM : K) (h : {h // h ∈ J})
    (hcorr : Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x * star (M.eval iM
        (correlationInput (h.val.val : ℤ) (x.val : ℤ))) *
        star (F.eval h iF (fun _ => (x.val : ℤ)))))) :
    Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x *
        star ((M.slice iM (h.val.val : ℤ)).evalCyclic N (fun _ => x)) *
        star (((F.test iF).withOrbit (F.orbit h)).evalCyclic N (fun _ => x)))) := by
  obtain ⟨Wh⟩ := hcorr
  refine ⟨Wh.mapCoordinates _ id ?_⟩
  intro i x
  change multiplicativeDerivative f h.val x *
    star ((M.slice iM (h.val.val : ℤ)).eval (fun _ => (x.val : ℤ))) *
    star (((F.test iF).withOrbit (F.orbit h)).eval (fun _ => (x.val : ℤ))) = _
  rw [M.slice_eval, F.withOrbit_eval]

theorem exists_native_fixed_product_unit_data (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I K : Type} [Fintype I] {r N : ℕ} [NeZero N]
      {p : ℝ} {f : ZMod N → ℂ} (J : Finset (ZMod N))
      (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
      (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
      (iF : I) (iM : K) (H : Finset {h // h ∈ J}), H.Nonempty →
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
        multiplicativeDerivative f h.val x * star (M.eval iM
          (correlationInput (h.val.val : ℤ) (x.val : ℤ))) *
          star (F.eval h iF (fun _ => (x.val : ℤ)))))) →
      ∃ H' : Finset {h // h ∈ J}, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n₁ : ℕ, 0 < n₁ ∧ (n₁ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V₁ : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s)
              (Fin (n₁ + 1)) ((p + C) ^ C),
            ∃ n₂ : ℕ, 0 < n₂ ∧ (n₂ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ V₂ : M.model.UnitVerticalObservable
                  (M.model.filtration.realification.subgroup (∑ i, mixedCorrelationDegree s i))
                  (Fin (n₂ + 1)) ((p + C) ^ C),
                ∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                  (fun _ : Unit => fun x => multiplicativeDerivative f h.val x *
                    star (V₂.observable 0 (QuotientGroup.mk
                      (M.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) (M.slice iM (h.val.val : ℤ)).orbit))) *
                    star (V₁.observable 0 (QuotientGroup.mk
                      (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) ((F.test iF).withOrbit (F.orbit h)).orbit))))) := by
  obtain ⟨C, hC, hselect⟩ := exists_native_two_factor_unit_replacement s
    (∑ i, mixedCorrelationDegree s i) (s - 1)
  refine ⟨C, hC, ?_⟩
  intro I K _ r N _ p f J F M iF iM H hH hp hf hcorr
  let T (h : {h // h ∈ J}) := (F.test iF).withOrbit (F.orbit h)
  let S (h : {h // h ∈ J}) := M.slice iM (h.val.val : ℤ)
  have hmodels := by
    as_aux_lemma =>
      exact hselect (G := {h // h ∈ J}) F.model M.model
  have htests := by
    as_aux_lemma =>
      exact hmodels T S H hH hp
  have hbounded := by
    as_aux_lemma =>
      exact htests
        (fun h _ => ((F.test iF).withOrbit_complexity (F.orbit h) p).mpr (F.test_complexity iF))
        (fun h _ => M.slice_complexity iM (h.val.val : ℤ))
        (fun _ _ => (F.test_norm iF).le) (fun h _ => (M.slice_norm iM (h.val.val : ℤ)).le)
  have hcommon := by
    as_aux_lemma =>
      exact hbounded (N := N)
        (fun h k => (F.withOrbit_observable iF h).trans (F.withOrbit_observable iF k).symm)
        (fun h k => (M.slice_observable iM (h.val.val : ℤ)).trans
          (M.slice_observable iM (k.val.val : ℤ)).symm)
  have hweights := by
    as_aux_lemma =>
      exact hcommon (fun h x => multiplicativeDerivative f h.val x)
        (fun h _ x => multiplicativeDerivative_norm_le_one f hf h.val x)
  apply hweights
  intro h hh
  exact exists_native_sliced_product_correlation F M iF iM h (hcorr h hh)

theorem exists_native_fixed_product_verticalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I K : Type} [Fintype I] {r N : ℕ} [NeZero N]
      {p : ℝ} {f : ZMod N → ℂ} (J : Finset (ZMod N))
      (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
      (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
      (iF : I) (iM : K) (H : Finset {h // h ∈ J}), H.Nonempty →
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
        multiplicativeDerivative f h.val x * star (M.eval iM
          (correlationInput (h.val.val : ℤ) (x.val : ℤ))) *
          star (F.eval h iF (fun _ => (x.val : ℤ)))))) →
      Nonempty (NativeCorrelationStructure s r N ((p + C) ^ C) f) := by
  obtain ⟨a, _, hselect⟩ := exists_native_fixed_product_unit_data s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q + 2)
  refine ⟨C, hC, ?_⟩
  intro I K _ r N _ p f J F M iF iM H hH hp hf hdense hcorr
  obtain ⟨H₁, _, hH₁, hdense₁, n₁, _, hcount₁, V₁, n₂, _, hcount₂, V₂, hunit⟩ :=
    hselect J F M iF iM H hH hp hf hcorr
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * N ≤ (H₁.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + q)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H.card := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hdense₁
  exact exists_native_correlation_of_sliced_unit_products J F M iM H₁ hH₁
    hfinaldensity hpC hqC hcount₁ hcount₂ V₁ V₂ hunit

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

def HasBoundedProductCorrelation {τ I : Type} [Fintype I]
    {s r degree N : ℕ} [NeZero N] (h : τ → ZMod N) (f : τ → ZMod N → ℂ)
    (mixedDim : ℕ) (B C Q : ℝ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp B ∧
    ∃ F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ ((I × I) × (I × Fin k)) C,
      ∃ M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) (Fin mixedDim × Fin k) Q,
        ∀ z, Nonempty (NativeVectorCorrelation degree N (B + 1)
          (fun ij : (Fin mixedDim × Fin k) × ((I × I) × (I × Fin k)) => fun a =>
            f z a * star (M.eval ij.1 (correlationInput ((h z).val : ℤ) (a.val : ℤ))) *
              star (F.eval z ij.2 (fun _ => (a.val : ℤ)))))

theorem HasBoundedProductCorrelation.mono {τ I : Type} [Fintype I]
    {s r degree N : ℕ} [NeZero N] {h : τ → ZMod N} {f : τ → ZMod N → ℂ}
    {mixedDim : ℕ} {B C Q B' C' Q' : ℝ}
    (hfamily : HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := degree)
      h f mixedDim B C Q) (hBB' : B ≤ B') (hCC' : C ≤ C') (hQQ' : Q ≤ Q') :
    HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := degree)
      h f mixedDim B' C' Q' := by
  obtain ⟨k, hk, hkB, F, M, hcorr⟩ := hfamily
  refine ⟨k, hk, hkB.trans (Real.exp_le_exp.mpr hBB'), F.mono hCC', M.mono hQQ', ?_⟩
  intro z
  obtain ⟨Cz⟩ := hcorr z
  exact ⟨Cz.mono (show B + 1 ≤ B' + 1 by linarith)⟩

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem HasUnitRankInducedCorrelationFamily.combineMixed
    {τ I : Type} [Fintype I] {s r N degree : ℕ} [NeZero N]
    {b p q P B C Q : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
    {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (f : τ → ZMod N → ℂ) (χ : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) Q)
    (hB : 0 ≤ B)
    (hfamily : D.HasUnitRankInducedCorrelationFamily (I := I) (degree := degree)
      t x y u c h₀ h
      (fun z i a => f z a * star (χ.evalCyclic N i (correlationInput (h z) a))) B C) :
    HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := degree)
      h f χ.outputDim B C (productNiltestBudget (Q + B + 2 + 4)) := by
  obtain ⟨k, hk, hkB, F, m, hm, hmB, d, E, M, hMF, hM, hdata⟩ := hfamily
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := E.metricSpace
  obtain ⟨G, hGn, hGL, hcorr⟩ := hdata
  let F₀ := (D.markedQuotientMultidegree t).realification
  have hF : F₀ = M.filtration.realification := congrArg MultidegreeLieFiltration.realification hMF.symm
  let g := F₀.orbitEquivOfEq hF (D.localPhaseMarkedOrbit t x y u c h₀ m)
  obtain ⟨Ω, hΩ⟩ := χ.exists_product_with_bounded_family E M
    (mixedCorrelationDegree_sum s).symm g G hB hM hGn hGL
  refine ⟨k, hk, hkB, F, Ω, ?_⟩
  have hprod (ij : Fin χ.outputDim × Fin k) (a : Fin 2 → ℤ) :
      Ω.eval ij a = χ.eval ij.1 a * G ij.2 (QuotientGroup.mk
        (F₀.polynomialOrbitEval a (D.localPhaseMarkedOrbit t x y u c h₀ m))) / 2 :=
    (hΩ ij a).trans (congrArg (fun v : E.RealGroup => χ.eval ij.1 a * G ij.2 (QuotientGroup.mk v) / 2)
      (F₀.orbitEquivOfEq_eval hF (D.localPhaseMarkedOrbit t x y u c h₀ m) a))
  have hchi (i : Fin χ.outputDim) (z : τ) (a : ZMod N) :
      χ.evalCyclic N i (correlationInput (h z) a) =
        χ.eval i (correlationInput ((h z).val : ℤ) (a.val : ℤ)) := by
    unfold NativeMultidegreeNilcharacter.evalCyclic
    exact congrArg (χ.eval i) (map_correlationInput (fun z : ZMod N => (z.val : ℤ)) (h z) a)
  intro z
  obtain ⟨Cz⟩ := hcorr z
  obtain ⟨Dz⟩ := Cz.exists_half_signal
  refine ⟨Dz.mapCoordinates _ id ?_⟩
  intro ij a
  simp only [id_eq, hprod, hchi, star_div₀, star_mul, star_ofNat]
  ring

end NativeRankRelation.CommonData

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_product_verticalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type} [Fintype I] {r N : ℕ} [NeZero N]
      {p : ℝ} {f : ZMod N → ℂ} (J : Finset (ZMod N)) (mixedDim : ℕ),
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → J.Nonempty →
      Real.exp (-p) * N ≤ (J.card : ℝ) →
      (mixedDim : ℝ) ≤ Real.exp p → (Fintype.card I : ℝ) ≤ Real.exp p →
      HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := s - 1)
        (fun h : {h // h ∈ J} => h.val) (fun h x => multiplicativeDerivative f h.val x)
        mixedDim p p p →
      Nonempty (NativeCorrelationStructure s r N ((p + C) ^ C) f) := by
  obtain ⟨a, _, hselect⟩ := exists_native_fixed_product_verticalization s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (7 * X + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro I _ r N _ p f J mixedDim hp hf hJ hdense hmixed hI hproduct
  classical
  obtain ⟨k, hk, hkB, F, M, hcorr⟩ := hproduct
  let G := {h // h ∈ J}
  have hG : (Finset.univ : Finset G).Nonempty := by
    obtain ⟨h, hh⟩ := hJ
    exact ⟨⟨h, hh⟩, Finset.mem_univ _⟩
  have hlabels : (Fintype.card ((Fin mixedDim × Fin k) × ((I × I) × (I × Fin k))) : ℝ) ≤
      Real.exp (6 * p) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ (Real.exp p * Real.exp p) *
          ((Real.exp p * Real.exp p) * (Real.exp p * Real.exp p)) := by gcongr
      _ = Real.exp (6 * p) := by
        repeat rw [← Real.exp_add]
        congr 1
        ring
  obtain ⟨ij, H₀, _, hH₀, hdense₀, hfixed⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    (p := p + 1) (Finset.univ : Finset G) hG _ hlabels (fun h _ => hcorr h)
  rcases ij with ⟨iM, iF⟩
  let P := 7 * p + 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpP : p ≤ P := by dsimp [P]; linarith
  have hp₁P : p + 1 ≤ P := by dsimp [P]; linarith
  have hfinal : (P + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, P, Polynomial.eval₂_pow] using hbudget p hp
  have hfiber : Real.exp (-(6 * p)) * J.card ≤ (H₀.card : ℝ) := by
    simpa only [G, Finset.card_univ, Fintype.card_coe] using hdense₀
  have hfixeddensity : Real.exp (-P) * N ≤ (H₀.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(7 * p)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by dsimp [P]; linarith))
          (Nat.cast_nonneg _)
      _ = Real.exp (-(6 * p)) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(6 * p)) * J.card :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hfiber
  have hselected := hselect J (F.mono hpP) (M.mono hpP) iF iM H₀ hH₀ hP hf hfixeddensity
  have hselected' : Nonempty (NativeCorrelationStructure s r N ((P + a) ^ a) f) := by
    apply hselected
    intro h hh
    obtain ⟨Wh⟩ := hfixed h hh
    exact ⟨Wh.mono hp₁P⟩
  obtain ⟨W⟩ := hselected'
  exact ⟨W.mono hfinal⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticAntisymmetricCorrelation
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_reflected_factor_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z : ℤ),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (correlationInput (x 0) (z - x 0 - x 1)))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (correlationInput (x 0) (z - x 0)) *
            star (W.eval k.2 (correlationInput (x 0) (x 1)))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence (mixedCorrelationDegree 1)
  refine ⟨C, hC, ?_⟩
  intro p W z
  let A : Option (Fin 2) → Fin 2 → ℤ := fun j => match j with
    | none => ![0, 1]
    | some i => if i = 0 then ![1, 0] else ![-1, -1]
  let b : Option (Fin 2) → ℤ := fun j => match j with
    | none => 0
    | some i => if i = 0 then 0 else z
  have hinput (x : Fin 2 → ℤ) : integerAffineMap A b x =
      coordinatePairInput (1 : Fin 2) (z - x 0 - x 1) (x 1) (x 0) := by
    funext j
    cases j with
    | none => simp [integerAffineMap, A, b, coordinatePairInput, Fin.sum_univ_two]
    | some i =>
      fin_cases i
      · simp [integerAffineMap, A, b, coordinatePairInput, coordinateConstantInput,
          Fin.sum_univ_two]
      · simp [integerAffineMap, A, b, coordinatePairInput, coordinateConstantInput,
          Fin.sum_univ_two]
        ring
  have hcoordinate (a n : ℤ) : coordinateConstantInput (1 : Fin 2) a n =
      correlationInput n a := by
    funext i
    fin_cases i <;> rfl
  have hdegree : (∑ i, mixedCorrelationDegree 1 i) - 1 = 1 := by
    rw [Fin.sum_univ_two]
    rfl
  have E := (hadd W (1 : Fin 2) rfl).affinePullback A b
  have E' : NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
      (fun k (x : Fin 2 → ℤ) => W.eval k (correlationInput (x 0) (z - x 0)))
      (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval k.1 (correlationInput (x 0) (z - x 0 - x 1)) *
          W.eval k.2 (correlationInput (x 0) (x 1))) := by
    simpa only [hdegree, coordinateSumVector, coordinateTensorVector, hinput,
      coordinatePairInput_sum, coordinatePairInput_left, coordinatePairInput_right,
      sub_add_cancel, hcoordinate] using E
  refine ⟨E'.left_dimension, E'.right_dimension, ?_⟩
  intro i k
  obtain ⟨R⟩ := E'.symm.expansion (i, k.2) k.1
  have heq : (fun x : Fin 2 → ℤ =>
      (W.eval i (correlationInput (x 0) (z - x 0 - x 1)) *
        W.eval k.2 (correlationInput (x 0) (x 1))) *
          star (W.eval k.1 (correlationInput (x 0) (z - x 0)))) =
      (fun x => W.eval i (correlationInput (x 0) (z - x 0 - x 1)) *
        star (W.eval k.1 (correlationInput (x 0) (z - x 0)) *
          star (W.eval k.2 (correlationInput (x 0) (x 1))))) := by
    funext x
    simp only [star_mul, star_star]
    ring
  exact ⟨heq ▸ R⟩

theorem exists_reflected_pair_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z : ℤ),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x : Fin 2 → ℤ =>
          W.eval k.1 (correlationInput (x 0) (z - x 0 - x 1)) *
            star (W.eval k.2 (correlationInput (x 1) (z - x 0 - x 1))))
        (fun k : (Fin W.outputDim × Fin W.outputDim) ×
            (Fin W.outputDim × Fin W.outputDim) => fun x =>
          W.eval k.1.1 (correlationInput (x 0) (z - x 0)) *
            star (W.eval k.2.1 (correlationInput (x 1) (z - x 1))) *
            star (W.eval k.1.2 (correlationInput (x 0) (x 1))) *
            W.eval k.2.2 (correlationInput (x 1) (x 0))) := by
  obtain ⟨a, _, hfactor⟩ := exists_reflected_factor_equivalence
  obtain ⟨b, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W z
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have E := hfactor W z
  have F := (E.coordinatePullback (![1, 0] : Fin 2 → Fin 2)).conjugate
  have R := htensor hq E F
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hsub (x : Fin 2 → ℤ) : z - x 1 - x 0 = z - x 0 - x 1 := by abel
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hsub, star_mul, star_star,
    mul_assoc, mul_comm, mul_left_comm] using R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem NativeTwoVariableSplit.second_eval_eq_degree_one {d : ℕ} {p epsilon : ℝ}
    {f : (Fin 2 → ℤ) → ℂ} (R : NativeTwoVariableSplit 1 d p epsilon f)
    (j : Fin R.count) (x y : Fin 2 → ℤ) (hxy : x 0 = y 0) :
    (R.test true j).eval x = (R.test true j).eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [R.test_orbit true j, (R.multi true).orbitToOrdinary_eval,
    (R.multi true).orbitToOrdinary_eval]
  apply congrArg (R.test true j).observable
  apply congrArg QuotientGroup.mk
  apply (R.multi true).filtration.realification.polynomialOrbitEval_eq_of_zero_coordinate
    1 (show totalDegreeSplitBound 1 true 1 = 0 from rfl) (R.orbit true) x y
  intro i hi
  fin_cases i
  · exact hxy
  · exact (hi rfl).elim

theorem exists_linear_separated_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L 1 d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 2 => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) →
      ∃ r : ℕ, 0 < r ∧ (r : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A B : Fin r → ℤ → ℂ,
          (∀ j x, ‖A j x‖ ≤ 1) ∧ (∀ j y, ‖B j y‖ ≤ 1) ∧
          ∀ x y, ‖T.eval ![x, y] - ∑ j, A j x * B j y‖ ≤ epsilon := by
  obtain ⟨C, hC, hsplit⟩ := exists_totalDegree_niltest_splitting 1 2
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  obtain ⟨R⟩ := hsplit T hT hnorm epsilon hepsilon hscale
  let A (j : Fin R.count) (x : ℤ) := (R.test true j).eval ![x, 0]
  let B (j : Fin R.count) (y : ℤ) := (R.test false j).eval ![0, y]
  refine ⟨R.count, R.count_pos, R.count_bound, A, B, ?_, ?_, ?_⟩
  · intro j x
    exact ((R.test true j).norm_eval_le _).trans
      (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
  · intro j y
    exact ((R.test false j).norm_eval_le _).trans
      (show ((R.test false j).normBound : ℝ) ≤ 1 from R.test_norm false j)
  · intro x y
    have heq (j : Fin R.count) :
        (R.test false j).eval ![x, y] * (R.test true j).eval ![x, y] = A j x * B j y := by
      rw [R.first_eval_eq j ![x, y] ![0, y] rfl,
        R.second_eval_eq_degree_one j ![x, y] ![x, 0] rfl]
      exact mul_comm _ _
    simpa only [heq] using R.approximation ![x, y]

theorem exists_absorb_linear_error :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L 1 d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 2 => 1)), T.ComplexityLE p →
      ∀ {X : Type*} (S : Finset X), S.Nonempty → ∀ (x y : X → ℤ) (F : X → ℂ),
        (∀ u ∈ S, ‖F u‖ ≤ 1) →
        Real.exp (-p) ≤ ‖𝔼 u ∈ S, F u * T.eval ![x u, y u]‖ →
        ∃ A B : ℤ → ℂ, (∀ x, ‖A x‖ ≤ 1) ∧ (∀ y, ‖B y‖ ≤ 1) ∧
          Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 u ∈ S, F u * A (x u) * B (y u)‖ := by
  obtain ⟨a, _, hsplit⟩ := exists_linear_separated_approximation
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * X + (X + Polynomial.C a) ^ a + 1)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT Ω S hS x y F hF hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let U := T.conjugate.expNormalize p
  let epsilon := Real.exp (-(2 * p + 1))
  have hscale : 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg p]
  obtain ⟨r, _, hr, A, B, hA, hB, happ⟩ := hsplit U
    (T.conjugate.expNormalize_complexity hT) (T.conjugate.expNormalize_norm hT)
    epsilon (Real.exp_pos _) hscale
  have hmean : (𝔼 u ∈ S, F u * star (U.eval ![x u, y u])) =
      (Real.exp (-p) : ℂ) * (𝔼 u ∈ S, F u * T.eval ![x u, y u]) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro u _
    simp only [U, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
      RationalFilteredNilmanifold.Niltest.eval_conjugate, star_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hnorm : Real.exp (-(2 * p)) ≤ ‖𝔼 u ∈ S, F u * star (U.eval ![x u, y u])‖ := by
    rw [hmean, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  have hepsilon : epsilon ≤ Real.exp (-(2 * p)) / 2 := by
    simpa only [epsilon, show -(2 * p + 1) = -(2 * p) - 1 by ring] using
      exp_sub_one_le_half_exp (-(2 * p))
  obtain ⟨j, hj⟩ := exists_correlating_summand hS F (fun u => U.eval ![x u, y u])
    (fun j u => A j (x u) * B j (y u)) (Real.exp_pos (-(2 * p)))
    (Real.exp_pos ((p + a) ^ a)) (by simpa only [Fintype.card_fin] using hr) hF
    (fun u _ => by rw [norm_sub_rev]; exact (happ (x u) (y u)).trans hepsilon) hnorm
  have hcost : 2 * p + (p + a) ^ a + 1 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hsmall : Real.exp (-((p + C) ^ C)) ≤
      Real.exp (-(2 * p)) / (2 * Real.exp ((p + a) ^ a)) := by
    calc
      _ ≤ Real.exp (-(2 * p + (p + a) ^ a) - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(2 * p + (p + a) ^ a)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [show -(2 * p + (p + a) ^ a) = -(2 * p) - (p + a) ^ a by ring,
        Real.exp_sub]; ring
  refine ⟨(fun x => star (A j x)), (fun y => star (B j y)), ?_, ?_, ?_⟩
  · intro x
    simpa only [norm_star] using hA j x
  · intro y
    simpa only [norm_star] using hB j y
  · simpa only [finiteCorrelation, star_mul, mul_assoc, mul_comm, mul_left_comm] using hsmall.trans hj

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem NativeMultidegreeNilcharacter.reflected_pair_target_unit {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z a b : ℤ) :
    (∑ k : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim),
      ‖W.eval k.1.1 (correlationInput a (z - a)) *
        star (W.eval k.2.1 (correlationInput b (z - b))) *
        star (W.eval k.1.2 (correlationInput a b)) *
        W.eval k.2.2 (correlationInput b a)‖ ^ 2) = 1 := by
  calc
    _ = ∑ k : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim),
        ‖(W.eval k.1.1 (correlationInput a (z - a)) *
          star (W.eval k.1.2 (correlationInput a b))) *
          star (W.eval k.2.1 (correlationInput b (z - b)) *
            star (W.eval k.2.2 (correlationInput b a)))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      simp only [star_mul, star_star]
      ring
    _ = 1 := by
      simp only [norm_mul, norm_star, mul_pow, Fintype.sum_prod_type,
        ← Finset.mul_sum, W.unit_eval, mul_one]

theorem exists_integer_antisymmetric_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z : ℤ)
      (i j : Fin W.outputDim) {Ω : Type*} (S : Finset Ω), S.Nonempty →
      ∀ (x y : Ω → ℤ) (a b : ℤ → ℂ), (∀ n, ‖a n‖ ≤ 1) → (∀ n, ‖b n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ S,
        W.eval i (correlationInput (x u) (z - x u - y u)) *
          star (W.eval j (correlationInput (y u) (z - x u - y u))) * a (x u) * b (y u)‖ →
      ∃ (i' j' : Fin W.outputDim) (A B : ℤ → ℂ),
        (∀ n, ‖A n‖ ≤ 1) ∧ (∀ n, ‖B n‖ ≤ 1) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 u ∈ S,
          star (W.eval i' (correlationInput (x u) (y u))) *
            W.eval j' (correlationInput (y u) (x u)) * A (x u) * B (y u)‖ := by
  obtain ⟨c, _, hcompare⟩ := NativeMultidegreeNilcharacter.exists_reflected_pair_equivalence
  obtain ⟨d, _, habsorb⟩ := exists_absorb_linear_error
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C c) ^ c
  let R := X + 2 * Q + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C d) ^ d)
  refine ⟨C, hC, ?_⟩
  intro p W z i j Ω S hS x y a b ha hb hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + c) ^ c
  let r := p + 2 * q + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpr : p + 2 * q ≤ r := by dsimp [r]; linarith
  let E := (hcompare W z).conjugate
  have hunit (u : Ω) : (∑ k : (Fin W.outputDim × Fin W.outputDim) ×
      (Fin W.outputDim × Fin W.outputDim), ‖star (W.eval k.1.1 (correlationInput (x u) (z - x u)) *
      star (W.eval k.2.1 (correlationInput (y u) (z - y u))) *
      star (W.eval k.1.2 (correlationInput (x u) (y u))) *
      W.eval k.2.2 (correlationInput (y u) (x u)))‖ ^ 2) = 1 := by
    simpa only [norm_star] using W.reflected_pair_target_unit z (x u) (y u)
  obtain ⟨k, l, htransfer⟩ := E.transfer_sample_correlation S (fun u => ![x u, y u])
    (i, j) (fun u => a (x u) * b (y u)) (fun u _ => hunit u)
    (by simpa only [star_star, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_assoc, mul_comm, mul_left_comm] using hcorr)
  let T := (E.selectedExpansion (i, j) k).test l
  let a₀ (n : ℤ) := W.eval k.1.1 (correlationInput n (z - n)) * a n
  let b₀ (n : ℤ) := star (W.eval k.2.1 (correlationInput n (z - n))) * b n
  let F (u : Ω) := (star (W.eval k.1.2 (correlationInput (x u) (y u))) *
    W.eval k.2.2 (correlationInput (y u) (x u))) * a₀ (x u) * b₀ (y u)
  have ha₀ (n : ℤ) : ‖a₀ n‖ ≤ 1 := by
    rw [show a₀ n = W.eval k.1.1 (correlationInput n (z - n)) * a n from rfl, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (ha n)
  have hb₀ (n : ℤ) : ‖b₀ n‖ ≤ 1 := by
    simp only [b₀, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (hb n)
  have hF (u : Ω) : ‖F u‖ ≤ 1 := by
    simp only [F, norm_mul, norm_star]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb₀ _)
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (ha₀ _)
    exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)
  have hT : T.conjugate.ComplexityLE r := ((E.selectedExpansion (i, j) k).complexity l).mono hqr
  have hFcorr : Real.exp (-r) ≤ ‖𝔼 u ∈ S, F u * T.conjugate.eval ![x u, y u]‖ := by
    have hlarge := (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans htransfer
    simpa only [F, a₀, b₀, T, E, RationalFilteredNilmanifold.Niltest.eval_conjugate,
      Matrix.cons_val_zero, Matrix.cons_val_one, star_star,
      mul_assoc, mul_comm, mul_left_comm] using hlarge
  obtain ⟨A, B, hA, hB, hAB⟩ := habsorb T.conjugate hT S hS x y F (fun u _ => hF u) hFcorr
  have hcost : (r + d) ^ d ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨k.1.2, k.2.2, (fun n => a₀ n * A n), (fun n => b₀ n * B n), ?_, ?_, ?_⟩
  · intro n
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha₀ n)).trans (hA n)
  · intro n
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hb₀ n)).trans (hB n)
  · simpa only [F, mul_assoc, mul_comm, mul_left_comm] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hAB

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_derivative_correlators {s C N : ℕ} [NeZero N]
    (hI : CyclicNativeInverse s C) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) (hG : Real.exp (-p) ≤ gowersNorm (s + 2) f) :
    ∃ H : Finset (ZMod N), H.Nonempty ∧
      Real.exp (-derivativeInverseBudget s p) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
      ∃ (g : {h // h ∈ H} → ZMod N → ℂ)
        (_F : ∀ h, NativeCyclicModel s N ((derivativeInverseBudget s p + C) ^ C) (g h)),
        ∀ h, Real.exp (-((derivativeInverseBudget s p + C) ^ C)) ≤
          ‖𝔼 x, multiplicativeDerivative f h.val x * star (g h x)‖ := by
  classical
  obtain ⟨H, hH, hdense, hlarge⟩ := exists_many_large_gowers_derivatives s f hf hp hG
  have hchoose (h : {h // h ∈ H}) :
      ∃ g ∈ nativeCyclicFunctions s N ((derivativeInverseBudget s p + C) ^ C),
        Real.exp (-((derivativeInverseBudget s p + C) ^ C)) ≤
          ‖𝔼 x, multiplicativeDerivative f h.val x * star (g x)‖ :=
    hI (derivativeInverseBudget_ge_two s hp) (multiplicativeDerivative f h.val)
      (multiplicativeDerivative_norm_le_one f hf h.val) (hlarge h.val h.property)
  choose g hg hcorr using hchoose
  exact ⟨H, hH, hdense, g, (fun h => Classical.choice (hg h)), hcorr⟩

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_common_observable_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : G → ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s (d h))
      (T : ∀ h, (D h).Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) → ∀ {N : ℕ} [NeZero N]
      (weight : G → ZMod N → ℂ), (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s (d h₀),
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (H' : Finset G) (S : G → E.Niltest (fun _ : Unit => 1)),
          H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          (∀ h, (S h).normBound ≤ 1 ∧ (S h).UnitIntervalValued ∧
            (S h).ComplexityLE ((p + C) ^ C)) ∧
          (∀ h k, (S h).observable = (S k).observable) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  obtain ⟨c, _, hmodels⟩ := exists_common_variable_dimension_niltest_model s
  obtain ⟨k, _, hfixed⟩ := exists_fixed_observable_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C k) ^ k + (X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hT hcap N _ weight hweight hcorr
  let q := p + (p + c) ^ c + 2
  have hpow : 0 ≤ (p + c) ^ c := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hmodelq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hfixed0 : 0 ≤ (q + k) ^ k := by positivity
  have hcost : q + (q + k) ^ k + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfixedC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  have hmodelC : (p + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨h₀, hh₀, E, hE, H₁, P, hsub₁, hh₀', hlarge₁, hP⟩ :=
    hmodels D T H hH hp hT
  have hPeval (h : G) (hh : h ∈ H₁) (x : ZMod N) :
      (P h).evalCyclic N (fun _ => x) = (T h).evalCyclic N (fun _ => x) :=
    (hP h hh).2.2.1 _
  obtain ⟨H₂, S, hsub₂, hH₂, hlarge₂, hS, hsame, hcorrS⟩ :=
    hfixed E P H₁ ⟨h₀, hh₀'⟩ hq (hE.mono E hmodelq)
      (fun h hh => (hP h hh).1.mono hmodelq)
      (fun h hh => by rw [(hP h hh).2.1]; exact hcap h (hsub₁ hh)) weight
      (fun h hh x => hweight h (hsub₁ hh) x)
      (fun h hh => by
        simp_rw [hPeval h hh]
        exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hcorr h (hsub₁ hh)))
  refine ⟨h₀, hh₀, E, hE.mono E hmodelC, H₂, S, hsub₂.trans hsub₁, hH₂, ?_,
    fun h => ⟨(hS h).2.1, (hS h).2.2.1, (hS h).2.2.2.mono hfixedC⟩, hsame, ?_⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤
          Real.exp (-((q + k) ^ k + (p + c) ^ c)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (by linarith)))
          (Nat.cast_nonneg _)
      _ = Real.exp (-((q + k) ^ k)) * (Real.exp (-((p + c) ^ c)) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((q + k) ^ k)) * H₁.card :=
        mul_le_mul_of_nonneg_left hlarge₁ (Real.exp_nonneg _)
      _ ≤ _ := hlarge₂
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hfixedC)).trans (hcorrS h hh)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

namespace NativeUnitVerticalData

variable {s N : ℕ}
  [NeZero N]
  {p q : ℝ}
  {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f}
  {V : NativeVerticalDerivativeData B}

end NativeUnitVerticalData

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_common_derivative_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ gowersNorm (s + 2) f →
      Nonempty (NativeCommonDerivativeModels s N ((p + D) ^ D) f) := by
  classical
  obtain ⟨a, _, hcommon⟩ := RationalFilteredNilmanifold.exists_common_observable_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q := Polynomial.C (2 ^ (s + 2)) * X + 2
  let R := (Q + Polynomial.C C) ^ C
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (R + Polynomial.C a) ^ a + 2)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  let q := derivativeInverseBudget s p
  let r := (q + C) ^ C
  have hq : 0 ≤ q := by dsimp [q, derivativeInverseBudget]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hshared : 0 ≤ (r + a) ^ a := by positivity
  have hcost : q + (r + a) ^ a + 2 ≤ (p + D) ^ D := by
    simpa [Q, R, X, q, r, derivativeInverseBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hsharedD : (r + a) ^ a ≤ (p + D) ^ D := by linarith
  obtain ⟨H, hH, hdense, g, F, hcorr⟩ := exists_native_derivative_correlators hI f hf hp hG
  let J := {h // h ∈ H}
  have hJ : (Finset.univ : Finset J).Nonempty := by
    obtain ⟨h, hh⟩ := hH
    exact ⟨⟨h, hh⟩, Finset.mem_univ _⟩
  obtain ⟨h₀, _, E, hE, H₁, S, _, hH₁, hdense₁, hS, hsame, hcS⟩ :=
    hcommon (fun h : J => (F h).model) (fun h => (F h).test) Finset.univ hJ hr
      (fun h => (F h).complexity) (fun h _ => (F h).norm)
      (fun h x => multiplicativeDerivative f h.val x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h.val x)
      (fun h _ => by simpa only [← (F h).eval] using hcorr h)
  let H' := H₁.image Subtype.val
  let selected (h : ZMod N) : J := if hh : h ∈ H then ⟨h, hh⟩ else h₀
  have hcard : H'.card = H₁.card := Finset.card_image_of_injective _ Subtype.val_injective
  have huniv : (Finset.univ : Finset J).card = H.card := by simp [J]
  have hfinaldensity : Real.exp (-((p + D) ^ D)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(q + (r + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (by linarith)))
          (Nat.cast_nonneg _)
      _ = Real.exp (-((r + a) ^ a)) * (Real.exp (-q) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((r + a) ^ a)) * H.card :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := by simpa only [hcard, huniv] using hdense₁
  refine ⟨{
    L := (F h₀).L
    dim := (F h₀).dim
    model := E
    geometry := hE.mono E hsharedD
    shifts := H'
    nonempty := hH₁.image _
    density := hfinaldensity
    test := fun h => S (selected h)
    norm := fun h => (hS (selected h)).1
    complexity := fun h => (hS (selected h)).2.2.mono hsharedD
    common_observable := fun h k => hsame (selected h) (selected k)
    correlation := ?_ }⟩
  intro h hh
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
  have hselect : selected j.val = j := by simp only [selected, dif_pos j.property]
  rw [hselect]
  exact (Real.exp_le_exp.mpr (neg_le_neg hsharedD)).trans (hcS j hj)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem NativeCommonDerivativeModels.exists_large_common_observable {s N : ℕ} [NeZero N]
    {p : ℝ} {f : ZMod N → ℂ} (B : NativeCommonDerivativeModels s N p f)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ y : B.model.Space, Real.exp (-p) ≤ ‖(B.test 0).observable y‖ := by
  obtain ⟨h, hh⟩ := B.nonempty
  have hmean : Real.exp (-p) ≤ 𝔼 x, ‖(B.test h).evalCyclic N (fun _ => x)‖ := by
    apply (B.correlation h hh).trans
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le_expect
    intro x _
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (multiplicativeDerivative_norm_le_one f hf h x)
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  refine ⟨QuotientGroup.mk (B.model.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (B.test h).orbit), ?_⟩
  rw [B.common_observable 0 h]
  exact hx

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_normalized_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ R : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
        ∀ h, R.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
          (R.test h).orbit = 1 := by
  obtain ⟨a, _, hmodels⟩ := exists_native_common_derivative_models hI
  obtain ⟨b, _, hnormalize⟩ := exists_normalized_native_common_models s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨B⟩ := hmodels hp f hf hG
  obtain ⟨R, hR⟩ := hnormalize hq hf B
  exact ⟨R.mono hcost, hR⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_vertical_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ R : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
        Nonempty (NativeVerticalDerivativeData R) := by
  obtain ⟨a, _, hmodels⟩ := exists_normalized_native_inverse_models hI
  obtain ⟨b, _, hvertical⟩ := exists_native_vertical_derivative_models
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨B, hB⟩ := hmodels hp f hf hG
  obtain ⟨R, ⟨V⟩⟩ := hvertical hq hf B hB
  exact ⟨R.mono hcost, ⟨V.mono hcost⟩⟩

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end


