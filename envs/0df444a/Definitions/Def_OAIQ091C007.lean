-- Prove2me | Definitions.Def_OAIQ091C007
-- name    : OAIQ091C007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:53:42.34797+00:00
-- url     : https://prove2.me/theorems/4f96285a-7e22-48f2-abcf-d889913babc1
-- title:
--   Definitions bundle OAIQ091C007 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 224 declarations of OpenAI's Lean: 99 definitions, 1 inductive type or structure, 3 instances and 121 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Angular.normalEvaluation`, `OAI.PositiveEinsteinFour.Angular.normalVector`, `OAI.PositiveEinsteinFour.Angular.twoFormNormal`, `OAI.PositiveEinsteinFour.Bianchi.Shape.rho`, `OAI.PositiveEinsteinFour.Bianchi.Shape.sigma`, `OAI.PositiveEinsteinFour.Bianchi.Shape.skewMoment`, `OAI.PositiveEinsteinFour.Bianchi.Shape.squareWeight`, `OAI.PositiveEinsteinFour.Bianchi.Shape.tilde`, `OAI.PositiveEinsteinFour.Bianchi.Tensor.bianchi`, `OAI.PositiveEinsteinFour.Bianchi.Tensor.divergence`, `OAI.PositiveEinsteinFour.Bianchi.Tensor.pairing`, `OAI.PositiveEinsteinFour.Bianchi.Tensor.squaredNorm`, `OAI.PositiveEinsteinFour.Bianchi.Tensor.traceFree`, `OAI.PositiveEinsteinFour.Bianchi.coordinateNorm`, `OAI.PositiveEinsteinFour.Bianchi.coordinatePairing`, `OAI.PositiveEinsteinFour.Bianchi.costCoefficientCoordinates`, `OAI.PositiveEinsteinFour.Bianchi.costParameters`, `OAI.PositiveEinsteinFour.Bianchi.costShape`, `OAI.PositiveEinsteinFour.Bianchi.cubicContraction`, `OAI.PositiveEinsteinFour.Bianchi.curvatureAction`, `OAI.PositiveEinsteinFour.Bianchi.curvatureActionK`, `OAI.PositiveEinsteinFour.Bianchi.curvatureActionL`, `OAI.PositiveEinsteinFour.Bianchi.curvatureActionP`, `OAI.PositiveEinsteinFour.Bianchi.curvatureBilinear`, `OAI.PositiveEinsteinFour.Bianchi.curvatureContraction`, `OAI.PositiveEinsteinFour.Bianchi.derivativeMatrix`, `OAI.PositiveEinsteinFour.Bianchi.diagonalCurvatureAction`, `OAI.PositiveEinsteinFour.Bianchi.diagonalGradientPairing`, `OAI.PositiveEinsteinFour.Bianchi.generalMatrixAction`, `OAI.PositiveEinsteinFour.Bianchi.generalMixedAction`, `OAI.PositiveEinsteinFour.Bianchi.generatorCoordinates`, `OAI.PositiveEinsteinFour.Bianchi.gradientCoupling`, `OAI.PositiveEinsteinFour.Bianchi.gradientCouplingKernel`, `OAI.PositiveEinsteinFour.Bianchi.gradientProjection`, `OAI.PositiveEinsteinFour.Bianchi.hessianTensorForm`, `OAI.PositiveEinsteinFour.Bianchi.matrixCurvatureTensor`, `OAI.PositiveEinsteinFour.Bianchi.normalizedCurvatureForm`, `OAI.PositiveEinsteinFour.Bianchi.quaternionCombination`, `OAI.PositiveEinsteinFour.Bianchi.radialCoordinate`, `OAI.PositiveEinsteinFour.Bianchi.rawBianchiProjection` and 60 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_AngularCurvature`, `EinsteinFour_Bianchi`, `EinsteinFour_BianchiCubic`, `EinsteinFour_BianchiCurvature`, `EinsteinFour_BianchiCurvatureProjection`, `EinsteinFour_BianchiHessian`, `EinsteinFour_ChartMetricTransition`, `EinsteinFour_CoupledOperator`, `EinsteinFour_CubicWeight`, `EinsteinFour_CurvatureSecondBianchi`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_FrameBundle`, `EinsteinFour_FrameFlow`, `EinsteinFour_GeneralMatrixCompression`, `EinsteinFour_GradientCasimir`, `EinsteinFour_GradientCoordinateModel`, `EinsteinFour_GradientMixedPairing`, `EinsteinFour_GradientPairing`, `EinsteinFour_GradientProjection`, `EinsteinFour_HighestHessian`, `EinsteinFour_HighestProjection`, `EinsteinFour_MatrixSlotOperator`, `EinsteinFour_OrientationCoverCharts`, `EinsteinFour_OrientationCoverCore`, `EinsteinFour_OrientationCoverDeckMetric`, `EinsteinFour_OrientationCoverMetric`, `EinsteinFour_OrientationCoverProjection`, `EinsteinFour_OrientationCoverSmoothLift`, `EinsteinFour_OrientationCoverTangent`, `EinsteinFour_OrientationCoverTopology`, `EinsteinFour_RealVectorCost`, `EinsteinFour_RealVectorProjection`, `EinsteinFour_TensorPairing`, `EinsteinFour_TraceHessian`, `EinsteinFour_WeylDerivative`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylLaplacian`, `EinsteinFour_WeylMatrixEquation`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C000` and `OAIQ091C001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C013`, `OAIQ091C014`, `OAIQ091C015` and `OAIQ091C016`; the statements `OAI.PositiveEinsteinFour.Bianchi.costCoefficient_norm`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_0_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_0_2`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_0`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_2`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_0`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_2`, `OAI.PositiveEinsteinFour.Bianchi.generator_coordinates`, `OAI.PositiveEinsteinFour.Bianchi.generator_coordinates_2_1`, `OAI.PositiveEinsteinFour.Bianchi.generator_coordinates_2_2`, `OAI.PositiveEinsteinFour.Bianchi.generator_norm_0`, `OAI.PositiveEinsteinFour.Bianchi.generator_norm_1`, `OAI.PositiveEinsteinFour.Bianchi.generator_norm_2`, `OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_1`, `OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_2`, `OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi` and `OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_matrix`; the proofs of `OAI.PositiveEinsteinFour.Bianchi.costCoefficient_norm`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_0_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_0_2`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_0`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_2`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_0`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_2`, `OAI.PositiveEinsteinFour.Bianchi.generator_coordinates`, `OAI.PositiveEinsteinFour.Bianchi.generator_coordinates_2_1`, `OAI.PositiveEinsteinFour.Bianchi.generator_coordinates_2_2`, `OAI.PositiveEinsteinFour.Bianchi.generator_norm_0`, `OAI.PositiveEinsteinFour.Bianchi.generator_norm_1`, `OAI.PositiveEinsteinFour.Bianchi.generator_norm_2`, `OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_1` and `OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_2`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C000
import Definitions.Def_OAIQ091C001

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Bianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete four-vector coordinates for a Bianchi gradient

The three quaternion actions are left multiplication by `i,j,k` on the real
four-dimensional Euclidean space. A symmetric matrix of four-vectors is
encoded by its three diagonal and three off-diagonal entries. Its divergence
constraint is the actual quaternionic Bianchi constraint of Section 2.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

theorem quaternion_injective (i : Fin 3) : Function.Injective (quaternion i) := by
  intro p q h
  have hh := congrArg (quaternion i) h
  simpa using hh

theorem difference_sum (s : Fin 3 → ℝ) : ∑ i, difference s i = 0 := by
  simp [difference, next, previous, Fin.sum_univ_succ]
  ring

theorem Shape.difference_square (S : Shape) : ∑ i, difference S.s i ^ 2 = 18 := by
  have ht := S.trace
  have hn := S.square
  simp [Fin.sum_univ_succ] at ht hn
  simp [difference, next, previous, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (S.s 0 + S.s 1 + S.s 2)]

theorem difference_orthogonal (s : Fin 3 → ℝ) : ∑ i, s i * difference s i = 0 := by
  simp [difference, next, previous, Fin.sum_univ_succ]
  ring

theorem Shape.difference_next_sub_previous (S : Shape) (i : Fin 3) :
    difference S.s (next i) - difference S.s (previous i) = -3 * S.s i := by
  have ht := S.trace
  simp [Fin.sum_univ_succ] at ht
  fin_cases i <;> simp [difference, next, previous] <;> linarith

def Tensor.traceFree (T : Tensor) : Prop := ∑ i, T.diagonal i = 0

/-- Quaternionic divergence in each matrix column. -/
def Tensor.divergence (T : Tensor) (i : Fin 3) : Vec :=
  quaternion i (T.diagonal i) + quaternion (next i) (T.off (previous i)) +
    quaternion (previous i) (T.off (next i))

/-- The concrete divergence is contraction of the quaternion action with
an actual matrix column. -/
theorem Tensor.divergence_eq_sum (T : Tensor) (i : Fin 3) :
    T.divergence i = ∑ j, quaternion j (T.matrix j i) := by
  fin_cases i <;> simp [Tensor.divergence, Tensor.matrix, next, previous,
    Fin.sum_univ_succ] <;> module

def Tensor.bianchi (T : Tensor) : Prop := ∀ i, T.divergence i = 0

/-- Multiplying the divergence equation by the corresponding complex
structure gives the elementary cyclic constraint. -/
theorem Tensor.quaternion_divergence (T : Tensor) (i : Fin 3) :
    quaternion i (T.divergence i) =
      -(T.diagonal i + T.auxiliary (next i) - T.auxiliary (previous i)) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Tensor.divergence, Tensor.auxiliary, quaternion, next, previous] <;> ring

theorem Tensor.bianchi_iff (T : Tensor) : T.bianchi ↔
    ∀ i, T.diagonal i + T.auxiliary (next i) - T.auxiliary (previous i) = 0 := by
  constructor
  · intro h i
    have hh := congrArg (quaternion i) (h i)
    rw [T.quaternion_divergence, quaternion_zero] at hh
    exact neg_eq_zero.mp hh
  · intro h i
    apply quaternion_injective i
    rw [T.quaternion_divergence, h i, quaternion_zero, neg_zero]

/-- Radial coordinate recovered directly from the diagonal entries. -/
def radialCoordinate (S : Shape) (T : Tensor) : Vec :=
  (1 / 6 : ℝ) • ∑ i, S.s i • T.diagonal i

/-- Orthogonal diagonal coordinate recovered directly from the entries. -/
def secondCoordinate (S : Shape) (T : Tensor) : Vec :=
  (-1 / 18 : ℝ) • ∑ i, difference S.s i • T.diagonal i

/-- The final free coordinate is the common residual in the three off-diagonal
quaternion coordinates. -/
def thirdCoordinate (S : Shape) (T : Tensor) : Vec :=
  T.auxiliary 0 - S.s 0 • secondCoordinate S T -
    (difference S.s 0 / 3) • radialCoordinate S T

/-- More transparent defining expression for the third coordinate. -/
theorem thirdCoordinate_eq (S : Shape) (T : Tensor) :
    thirdCoordinate S T = T.auxiliary 0 - S.s 0 • secondCoordinate S T -
      (difference S.s 0 / 3) • radialCoordinate S T := by
  unfold thirdCoordinate
  module

/-- Squared Hilbert--Schmidt norm of the symmetric vector-valued matrix. -/
def Tensor.squaredNorm (T : Tensor) : ℝ := ∑ i, ∑ j, ‖T.matrix i j‖ ^ 2

theorem Tensor.squaredNorm_eq (T : Tensor) :
    T.squaredNorm = (∑ i, ‖T.diagonal i‖ ^ 2) + 2 * ∑ i, ‖T.off i‖ ^ 2 := by
  simp [Tensor.squaredNorm, Tensor.matrix, Fin.sum_univ_succ]
  ring

theorem sum_norm_two (a b : Fin 3 → ℝ) (p k : Vec) :
    (∑ i, ‖a i • p + b i • k‖ ^ 2) =
      (∑ i, a i ^ 2) * ‖p‖ ^ 2 + 2 * (∑ i, a i * b i) * inner ℝ p k +
        (∑ i, b i ^ 2) * ‖k‖ ^ 2 := by
  simp only [Fin.sum_univ_succ, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

theorem sum_norm_three (a b : Fin 3 → ℝ) (l k p : Vec) :
    (∑ i, ‖l + a i • k + b i • p‖ ^ 2) =
      3 * ‖l‖ ^ 2 + 2 * (∑ i, a i) * inner ℝ l k +
      2 * (∑ i, b i) * inner ℝ l p + (∑ i, a i ^ 2) * ‖k‖ ^ 2 +
      2 * (∑ i, a i * b i) * inner ℝ k p + (∑ i, b i ^ 2) * ‖p‖ ^ 2 := by
  simp only [Fin.sum_univ_succ, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_add_left, real_inner_smul_left, real_inner_smul_right]
  ring

theorem parameters_diagonal_energy (S : Shape) (p k l : Vec) :
    (∑ i, ‖(parameters S p k l).diagonal i‖ ^ 2) = 6 * ‖p‖ ^ 2 + 18 * ‖k‖ ^ 2 := by
  have h := sum_norm_two S.s (fun i => -difference S.s i) p k
  simp only [neg_smul, ← sub_eq_add_neg, mul_neg, neg_sq,
    Finset.sum_neg_distrib, S.square, difference_orthogonal, S.difference_square] at h
  simpa [parameters] using h

theorem parameters_off_energy (S : Shape) (p k l : Vec) :
    (∑ i, ‖(parameters S p k l).off i‖ ^ 2) =
      3 * ‖l‖ ^ 2 + 6 * ‖k‖ ^ 2 + 2 * ‖p‖ ^ 2 := by
  have hb : ∑ i, difference S.s i / 3 = 0 := by
    rw [← Finset.sum_div, difference_sum]
    norm_num
  have hb2 : ∑ i, (difference S.s i / 3) ^ 2 = 2 := by
    simp only [div_pow]
    rw [← Finset.sum_div, S.difference_square]
    norm_num
  have hab : ∑ i, S.s i * (difference S.s i / 3) = 0 := by
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div, difference_orthogonal]
    norm_num
  have h := sum_norm_three S.s (fun i => difference S.s i / 3) l k p
  simp only [S.trace, hb, S.square, hab, hb2, mul_zero, zero_mul, add_zero] at h
  change (∑ i, ‖-quaternion i (l + S.s i • k + (difference S.s i / 3) • p)‖ ^ 2) = _
  simp only [norm_neg, quaternion_norm]
  exact h

/-- The exact energy identity in (2), including the multiplicity of the
symmetric off-diagonal entries. -/
theorem parameters_energy (S : Shape) (p k l : Vec) :
    (parameters S p k l).squaredNorm / 6 =
      (5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 := by
  rw [Tensor.squaredNorm_eq, parameters_diagonal_energy, parameters_off_energy]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed trace component of the Bianchi Hessian

The arrays are real tensors. The lift is the explicit formula for the
restricted trace adjoint in Section 5; its Bianchi constraint, trace and
squared norm follow by direct calculation in the fixed quaternion frame. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

theorem quaternionMatrix_apply (s : Fin 3) (q : Vec) (i : Fin 4) :
    ∑ j, quaternionMatrix s i j * q j = quaternion s q i := by
  fin_cases s <;> fin_cases i <;>
    simp [quaternionMatrix, quaternion, Fin.sum_univ_succ]

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularCurvature
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal Jacobi form of the actual quaternion curvature decomposition. -/

namespace PositiveEinsteinFour.Angular

open Matrix TraceHessian

noncomputable section

def normalVector (q : Directions) (i : Fin 3) (a : Fin 4) : ℝ :=
  ∑ b, quaternionMatrix i a b * q.val b

def twoFormNormal (Q : Mat4) (q : Directions) (i : Fin 3) : ℝ :=
  ∑ a, ∑ b, Q a b * normalVector q i a * q.val b

/-- Evaluate `<R(I_i q,q)q,I_j q>` as a linear functional on four-tensors. -/
def normalEvaluation (q : Directions) (i j : Fin 3) : CurvatureArray →ₗ[ℝ] ℝ where
  toFun R := ∑ a, ∑ b, ∑ c, ∑ d,
    R a b c d * normalVector q i a * q.val b * q.val c * normalVector q j d
  map_add' R S := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r R := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

theorem normalEvaluation_product (P Q : Mat4) (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (twoFormProduct P Q) =
      twoFormNormal P q i * twoFormNormal Q q j := by
  change (∑ a, ∑ b, ∑ c, ∑ d,
    P a b * Q d c * normalVector q i a * q.val b * q.val c * normalVector q j d) = _
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c,
        P a b * Q d c * normalVector q i a * q.val b * q.val c * normalVector q j d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [twoFormNormal]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem normalEvaluation_blockTensor (A : Mat3) (Q : Fin 3 → Mat4)
    (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (blockTensor A Q) =
      (1 / 2 : ℝ) * ∑ s, ∑ t,
        A s t * (twoFormNormal (Q s) q i * twoFormNormal (Q t) q j) := by
  simp only [blockTensor, map_smul, map_sum, smul_eq_mul, normalEvaluation_product]

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiCurvature
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Curvature contractions of the concrete Bianchi tensor

The normalized spectral moments and the matrix-slot contraction are computed
from the actual symmetric matrix of Euclidean four-vectors in `Bianchi`.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

/-- Normalized cubic spectral moment. -/
def Shape.sigma (S : Shape) : ℝ := (∑ i, S.s i ^ 3) / 6

/-- Rational form of `ρ / √3`. -/
def Shape.skewMoment (S : Shape) : ℝ := (∑ i, S.s i ^ 2 * difference S.s i) / 18

/-- The oriented companion spectral moment. -/
def Shape.rho (S : Shape) : ℝ := Real.sqrt 3 * S.skewMoment

/-- The normalized quarter-turn spectral vector. -/
def Shape.tilde (S : Shape) (i : Fin 3) : ℝ := difference S.s i / Real.sqrt 3

theorem Shape.trace_coordinates (S : Shape) : S.s 2 = -S.s 0 - S.s 1 := by
  have h := S.trace
  simp [Fin.sum_univ_succ] at h
  linarith

theorem Shape.norm_coordinates (S : Shape) :
    S.s 0 ^ 2 + S.s 0 * S.s 1 + S.s 1 ^ 2 = 3 := by
  have h := S.square
  simp [Fin.sum_univ_succ, S.trace_coordinates] at h
  nlinarith

theorem Shape.sigma_skew_circle (S : Shape) : S.sigma ^ 2 + 3 * S.skewMoment ^ 2 = 1 := by
  have h := S.norm_coordinates
  unfold Shape.sigma Shape.skewMoment
  simp [Fin.sum_univ_succ, difference, next, previous]
  rw [S.trace_coordinates]
  linear_combination
    (S.s 0 ^ 4 + 2 * S.s 0 ^ 3 * S.s 1 + 3 * S.s 0 ^ 2 * S.s 1 ^ 2 +
      3 * S.s 0 ^ 2 + 2 * S.s 0 * S.s 1 ^ 3 + 3 * S.s 0 * S.s 1 +
      S.s 1 ^ 4 + 3 * S.s 1 ^ 2 + 9) / 27 * h

/-- The exact normalized identity used by every spectral matrix estimate. -/
theorem Shape.sigma_rho_circle (S : Shape) : S.rho ^ 2 = 1 - S.sigma ^ 2 := by
  unfold Shape.rho
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  linarith [S.sigma_skew_circle]

/-- Direct matrix-slot quadratic contraction with diagonal Weyl block `v*s`.
The second sum is the off-diagonal contribution, because the spectral trace
vanishes. -/
def curvatureContraction (S : Shape) (v : ℝ) (T : Tensor) : ℝ :=
  (v / 6) * ((∑ i, S.s i * ‖T.diagonal i‖ ^ 2) - ∑ i, S.s i * ‖T.off i‖ ^ 2)

/-- The normalized eigenvalues of the trace-free square of the Weyl block. -/
def Shape.squareWeight (S : Shape) (i : Fin 3) : ℝ := S.s i ^ 2 - 2

/-- The actual matrix-slot contraction with `N = (T²)₀`. -/
def squareCurvatureContraction (S : Shape) (v : ℝ) (T : Tensor) : ℝ :=
  (v ^ 2 / 6) * ((∑ i, S.squareWeight i * ‖T.diagonal i‖ ^ 2) -
    ∑ i, S.squareWeight i * ‖T.off i‖ ^ 2)

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Hessian matrix on actual quaternionic Bianchi tensors

The energy pairing and the matrix-slot operator are transported through the
proved bijective parametrization. Thus the squared-operator term uses the
inverse energy metric automatically.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

/-- The normalized Hilbert--Schmidt pairing. -/
def Tensor.pairing (T U : Tensor) : ℝ := (∑ i, ∑ j, inner ℝ (T.matrix i j) (U.matrix i j)) / 6

def curvatureActionP (S : Shape) (v : ℝ) (p k : Vec) : Vec :=
  v • (((4 / 5) * S.sigma) • p - ((12 / 5) * S.skewMoment) • k)

def curvatureActionK (S : Shape) (v : ℝ) (p k l : Vec) : Vec :=
  v • ((-(4 / 5) * S.skewMoment) • p - ((4 / 5) * S.sigma) • k - (1 / 5 : ℝ) • l)

def curvatureActionL (v : ℝ) (k : Vec) : Vec := (-v) • k

/-- The matrix-slot curvature operator on the concrete Bianchi space. -/
def curvatureAction (S : Shape) (v : ℝ) (p k l : Vec) : Tensor :=
  parameters S (curvatureActionP S v p k) (curvatureActionK S v p k l) (curvatureActionL v k)

/-- The first-derivative Hessian form expressed directly using concrete matrix
contractions and the actual inverse-energy-metric operator. -/
def hessianTensorForm (S : Shape) (v b : ℝ) (p k l : Vec) : ℝ :=
  (-42 - 3 * b ^ 2 - (10 / 3) * v ^ 2) * ((parameters S p k l).squaredNorm / 6) +
    75 * curvatureContraction S v (parameters S p k l) +
    (25 / 3) * squareCurvatureContraction S v (parameters S p k l) -
    (100 / 3) * ((curvatureAction S v p k l).squaredNorm / 6) + 5 * v ^ 2 * ‖p‖ ^ 2

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiCubic
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The sharp cubic contraction in a normalized diagonal frame

The contraction is defined from the actual symmetric matrix of four-vectors.
The displayed diagonal-frame hypothesis is the pointwise spectral-frame
condition used in the curvature calculation, and is not a differential-geometric input.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

def normalizedCurvatureForm (S : Shape) (p k l : Vec) : ℝ :=
  (4 / 3) * S.sigma * ‖p‖ ^ 2 - 8 * S.skewMoment * inner ℝ p k -
    4 * S.sigma * ‖k‖ ^ 2 - 2 * inner ℝ k l

/-- The literal matrix contraction `tr(Z_a Σ_j Z_j²)/6`. Each inner product
contracts the derivative (four-vector) index. -/
def cubicContraction (a : Vec) (T : Tensor) : ℝ :=
  (∑ i, ∑ j, ∑ k, inner ℝ a (T.matrix i j) *
    inner ℝ (T.matrix j k) (T.matrix k i)) / 6

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCasimir
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Bianchi coupling operator on first derivatives. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The coupling in the Bianchi projector `(6-C)/10`. -/
def gradientCoupling (Z : Tensor) (a b : Fin 3) : Vec :=
  ∑ s, quaternion s (matrixRotation s Z a b)

theorem diagonal_zero_from_bianchi (Z : Tensor) (hb : Z.bianchi) :
    Z.diagonal 0 = Z.auxiliary 2 - Z.auxiliary 1 := by
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  simpa [next, previous] using (Z.bianchi_iff.mp hb) 0

theorem diagonal_one_from_bianchi (Z : Tensor) (hb : Z.bianchi) :
    Z.diagonal 1 = Z.auxiliary 0 - Z.auxiliary 2 := by
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  simpa [next, previous] using (Z.bianchi_iff.mp hb) 1

theorem diagonal_two_from_bianchi (Z : Tensor) (hb : Z.bianchi) :
    Z.diagonal 2 = Z.auxiliary 1 - Z.auxiliary 0 := by
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  simpa [next, previous] using (Z.bianchi_iff.mp hb) 2

theorem gradientCoupling_zero (Z : Tensor) (hb : Z.bianchi) (b : Fin 3) :
    gradientCoupling Z 0 b = (-4 : ℝ) • Z.matrix 0 b := by
  have h0 := diagonal_zero_from_bianchi Z hb
  have h1 := diagonal_one_from_bianchi Z hb
  have h2 := diagonal_two_from_bianchi Z hb
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [gradientCoupling, matrixRotation, TraceHessian.rotation, Tensor.matrix,
      Fin.sum_univ_succ, h0, h1, h2, Tensor.auxiliary, quaternion]
  all_goals ring

theorem gradientCoupling_one (Z : Tensor) (hb : Z.bianchi) (b : Fin 3) :
    gradientCoupling Z 1 b = (-4 : ℝ) • Z.matrix 1 b := by
  have h0 := diagonal_zero_from_bianchi Z hb
  have h1 := diagonal_one_from_bianchi Z hb
  have h2 := diagonal_two_from_bianchi Z hb
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [gradientCoupling, matrixRotation, TraceHessian.rotation, Tensor.matrix,
      Fin.sum_univ_succ, h0, h1, h2, Tensor.auxiliary, quaternion]
  all_goals ring

theorem gradientCoupling_two (Z : Tensor) (hb : Z.bianchi) (b : Fin 3) :
    gradientCoupling Z 2 b = (-4 : ℝ) • Z.matrix 2 b := by
  have h0 := diagonal_zero_from_bianchi Z hb
  have h1 := diagonal_one_from_bianchi Z hb
  have h2 := diagonal_two_from_bianchi Z hb
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [gradientCoupling, matrixRotation, TraceHessian.rotation, Tensor.matrix,
      Fin.sum_univ_succ, h0, h1, h2, Tensor.auxiliary, quaternion]
  all_goals ring

/-- The Bianchi equation puts every gradient in the actual `C=-4` subspace. -/
theorem gradientCoupling_eq (Z : Tensor) (hb : Z.bianchi) (a b : Fin 3) :
    gradientCoupling Z a b = (-4 : ℝ) • Z.matrix a b := by
  fin_cases a
  · exact gradientCoupling_zero Z hb b
  · exact gradientCoupling_one Z hb b
  · exact gradientCoupling_two Z hb b

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compressed derivative generator in the actual quaternion model. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The matrix-slot curvature operator for a diagonal trace-free curvature block. -/
def diagonalCurvatureAction (t : Fin 3 → ℝ) (M : Mat) : Mat := fun a b =>
  (t a + t b) / 2 * M a b -
    if a = b then (∑ c, t c * M c c) / 3 else 0


/-- The polynomial expression for the orthogonal Bianchi projector. -/
def gradientProjection (Z : Tensor) (a b : Fin 3) : Vec :=
  (1 / 10 : ℝ) • ((6 : ℝ) • Z.matrix a b - gradientCoupling Z a b)

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TensorPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skew matrix actions on the actual four tensor slots. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

def tensorCoordinates (X : Hessian) (p : TensorIndex) : ℝ :=
  X p.1 p.2.1 p.2.2.1 p.2.2.2

theorem rotation_skew (s : Fin 3) (i j : Fin 3) :
    rotation s i j = -rotation s j i := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;> norm_num [rotation]

/-- Matrix-slot Frobenius pairing. -/
def matrixPairing (M N : Mat) : ℝ := ∑ a, ∑ b, M a b * N a b

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.QuaternionFrame.fieldRaw_rawField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear compression on the actual Bianchi gradient space. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

def rawCoordinates (Z : RawGradient) (p : GradientIndex) : ℝ := Z p.2.1 p.2.2 p.1

def rawPairing (Z W : RawGradient) : ℝ :=
  ∑ p : GradientIndex, rawCoordinates Z p * rawCoordinates W p

theorem rawPairing_vectors (Z W : RawGradient) :
    rawPairing Z W = ∑ a, ∑ b, inner ℝ (Z a b) (W a b) := by
  simp only [rawPairing, rawCoordinates, Fintype.sum_prod_type,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  calc
    _ = ∑ a : Fin 3, ∑ j : Fin 4, ∑ b : Fin 3, Z a b j * W a b j :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [mul_comm]

def rawCoupling (Z : RawGradient) : RawGradient := fun a b =>
  ∑ s : Fin 3, quaternion s (rawMatrixRotation s Z a b)

def gradientCouplingKernel (p q : GradientIndex) : ℝ := ∑ s : Fin 3,
  quaternionMatrix s p.1 q.1 *
    ((if p.2.2 = q.2.2 then rotation s p.2.1 q.2.1 else 0) +
      (if p.2.1 = q.2.1 then rotation s p.2.2 q.2.2 else 0))

theorem rawCoupling_coordinates (Z : RawGradient) (p : GradientIndex) :
    rawCoordinates (rawCoupling Z) p =
      ∑ q : GradientIndex, gradientCouplingKernel p q * rawCoordinates Z q := by
  rcases p with ⟨j, a, b⟩
  simp only [gradientCouplingKernel, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold rawCoupling rawCoordinates
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [← quaternionMatrix_apply]
  simp [Fintype.sum_prod_type, rawMatrixRotation,
    add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    ]
  have hneg (k : Fin 4) :
      (∑ c, quaternionMatrix s j k * rotation s c b * Z a c k) =
        -(∑ c, quaternionMatrix s j k * rotation s b c * Z a c k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [rotation_skew s c b]
    ring
  change (∑ k : Fin 4,
      quaternionMatrix s j k * ((∑ c, rotation s a c * Z c b k) -
        ∑ c, rotation s c b * Z a c k)) =
    (∑ k : Fin 4, ∑ c, quaternionMatrix s j k * rotation s a c * Z c b k) +
      ∑ k : Fin 4, ∑ c, quaternionMatrix s j k * rotation s b c * Z a c k
  calc
    _ = (∑ k : Fin 4, ∑ c, quaternionMatrix s j k * rotation s a c * Z c b k) -
        ∑ k : Fin 4, ∑ c, quaternionMatrix s j k * rotation s c b * Z a c k := by
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]
    _ = _ := by
      simp only [hneg, Finset.sum_neg_distrib]
      ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiCurvatureProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matrix-slot curvature form and its Bianchi compression. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The uncompressed matrix-slot operator, specialized to the diagonal
curvature block `v * S.s`. -/
def matrixCurvatureTensor (S : Shape) (v : ℝ) (Z : Tensor) : Tensor where
  diagonal a := v • (S.s a • Z.diagonal a -
    (1 / 3 : ℝ) • (∑ c, S.s c • Z.diagonal c))
  off a := (-(v * S.s a) / 2) • Z.off a

/-- The symmetric bilinear version of the actual matrix contraction. -/
def curvatureBilinear (S : Shape) (v : ℝ) (Z W : Tensor) : ℝ :=
  (v / 6) * ((∑ a, S.s a * inner ℝ (Z.diagonal a) (W.diagonal a)) -
    ∑ a, S.s a * inner ℝ (Z.off a) (W.off a))

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ChartMetricTransition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual metric pullback matrix in a chart. The tangent coordinates
at the image point use its own centered chart, so this congruence is the
zeroth-order part of the curvature coordinate-change calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartTransition (c d : M) (z : FourSpace) : FourSpace :=
  chartAt FourSpace d ((chartAt FourSpace c).symm z)

def chartTransitionMatrix (c d : M) (z : FourSpace) : Mat4 :=
  fun i j => fderiv ℝ (chartTransition c d) z (coordinateVector j) i

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual highest Hessian has the twenty-one displayed coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Extract the fifty independent entries of a derivative-symmetric tensor. -/
def coordinates (X : Hessian) : Fin 50 → ℝ :=
  ![X 0 0 0 0, X 0 0 1 1, X 0 0 0 1, X 0 0 0 2, X 0 0 1 2, X 0 1 0 0, X 0 1 1 1, X 0 1 0 1, X 0 1 0 2, X 0 1 1 2, X 0 2 0 0, X 0 2 1 1, X 0 2 0 1, X 0 2 0 2, X 0 2 1 2, X 0 3 0 0, X 0 3 1 1, X 0 3 0 1, X 0 3 0 2, X 0 3 1 2, X 1 1 0 0, X 1 1 1 1, X 1 1 0 1, X 1 1 0 2, X 1 1 1 2, X 1 2 0 0, X 1 2 1 1, X 1 2 0 1, X 1 2 0 2, X 1 2 1 2, X 1 3 0 0, X 1 3 1 1, X 1 3 0 1, X 1 3 0 2, X 1 3 1 2, X 2 2 0 0, X 2 2 1 1, X 2 2 0 1, X 2 2 0 2, X 2 2 1 2, X 2 3 0 0, X 2 3 1 1, X 2 3 0 1, X 2 3 0 2, X 2 3 1 2, X 3 3 0 0, X 3 3 1 1, X 3 3 0 1, X 3 3 0 2, X 3 3 1 2]


@[simp] theorem coordinates_0 (X : Hessian) :
    coordinates X 0 = X 0 0 0 0 := rfl

@[simp] theorem coordinates_1 (X : Hessian) :
    coordinates X 1 = X 0 0 1 1 := rfl

@[simp] theorem coordinates_2 (X : Hessian) :
    coordinates X 2 = X 0 0 0 1 := rfl

@[simp] theorem coordinates_3 (X : Hessian) :
    coordinates X 3 = X 0 0 0 2 := rfl

@[simp] theorem coordinates_4 (X : Hessian) :
    coordinates X 4 = X 0 0 1 2 := rfl

@[simp] theorem coordinates_5 (X : Hessian) :
    coordinates X 5 = X 0 1 0 0 := rfl

@[simp] theorem coordinates_6 (X : Hessian) :
    coordinates X 6 = X 0 1 1 1 := rfl

@[simp] theorem coordinates_7 (X : Hessian) :
    coordinates X 7 = X 0 1 0 1 := rfl

@[simp] theorem coordinates_8 (X : Hessian) :
    coordinates X 8 = X 0 1 0 2 := rfl

@[simp] theorem coordinates_9 (X : Hessian) :
    coordinates X 9 = X 0 1 1 2 := rfl

@[simp] theorem coordinates_10 (X : Hessian) :
    coordinates X 10 = X 0 2 0 0 := rfl

@[simp] theorem coordinates_11 (X : Hessian) :
    coordinates X 11 = X 0 2 1 1 := rfl

@[simp] theorem coordinates_12 (X : Hessian) :
    coordinates X 12 = X 0 2 0 1 := rfl

@[simp] theorem coordinates_13 (X : Hessian) :
    coordinates X 13 = X 0 2 0 2 := rfl

@[simp] theorem coordinates_14 (X : Hessian) :
    coordinates X 14 = X 0 2 1 2 := rfl

@[simp] theorem coordinates_15 (X : Hessian) :
    coordinates X 15 = X 0 3 0 0 := rfl

@[simp] theorem coordinates_16 (X : Hessian) :
    coordinates X 16 = X 0 3 1 1 := rfl

@[simp] theorem coordinates_17 (X : Hessian) :
    coordinates X 17 = X 0 3 0 1 := rfl

@[simp] theorem coordinates_18 (X : Hessian) :
    coordinates X 18 = X 0 3 0 2 := rfl

@[simp] theorem coordinates_19 (X : Hessian) :
    coordinates X 19 = X 0 3 1 2 := rfl

@[simp] theorem coordinates_20 (X : Hessian) :
    coordinates X 20 = X 1 1 0 0 := rfl

@[simp] theorem coordinates_21 (X : Hessian) :
    coordinates X 21 = X 1 1 1 1 := rfl

@[simp] theorem coordinates_22 (X : Hessian) :
    coordinates X 22 = X 1 1 0 1 := rfl

@[simp] theorem coordinates_23 (X : Hessian) :
    coordinates X 23 = X 1 1 0 2 := rfl

@[simp] theorem coordinates_24 (X : Hessian) :
    coordinates X 24 = X 1 1 1 2 := rfl

@[simp] theorem coordinates_25 (X : Hessian) :
    coordinates X 25 = X 1 2 0 0 := rfl

@[simp] theorem coordinates_26 (X : Hessian) :
    coordinates X 26 = X 1 2 1 1 := rfl

@[simp] theorem coordinates_27 (X : Hessian) :
    coordinates X 27 = X 1 2 0 1 := rfl

@[simp] theorem coordinates_28 (X : Hessian) :
    coordinates X 28 = X 1 2 0 2 := rfl

@[simp] theorem coordinates_29 (X : Hessian) :
    coordinates X 29 = X 1 2 1 2 := rfl

@[simp] theorem coordinates_30 (X : Hessian) :
    coordinates X 30 = X 1 3 0 0 := rfl

@[simp] theorem coordinates_31 (X : Hessian) :
    coordinates X 31 = X 1 3 1 1 := rfl

@[simp] theorem coordinates_32 (X : Hessian) :
    coordinates X 32 = X 1 3 0 1 := rfl

@[simp] theorem coordinates_33 (X : Hessian) :
    coordinates X 33 = X 1 3 0 2 := rfl

@[simp] theorem coordinates_34 (X : Hessian) :
    coordinates X 34 = X 1 3 1 2 := rfl

@[simp] theorem coordinates_35 (X : Hessian) :
    coordinates X 35 = X 2 2 0 0 := rfl

@[simp] theorem coordinates_36 (X : Hessian) :
    coordinates X 36 = X 2 2 1 1 := rfl

@[simp] theorem coordinates_37 (X : Hessian) :
    coordinates X 37 = X 2 2 0 1 := rfl

@[simp] theorem coordinates_38 (X : Hessian) :
    coordinates X 38 = X 2 2 0 2 := rfl

@[simp] theorem coordinates_39 (X : Hessian) :
    coordinates X 39 = X 2 2 1 2 := rfl

@[simp] theorem coordinates_40 (X : Hessian) :
    coordinates X 40 = X 2 3 0 0 := rfl

@[simp] theorem coordinates_41 (X : Hessian) :
    coordinates X 41 = X 2 3 1 1 := rfl

@[simp] theorem coordinates_42 (X : Hessian) :
    coordinates X 42 = X 2 3 0 1 := rfl

@[simp] theorem coordinates_43 (X : Hessian) :
    coordinates X 43 = X 2 3 0 2 := rfl

@[simp] theorem coordinates_44 (X : Hessian) :
    coordinates X 44 = X 2 3 1 2 := rfl

@[simp] theorem coordinates_45 (X : Hessian) :
    coordinates X 45 = X 3 3 0 0 := rfl

@[simp] theorem coordinates_46 (X : Hessian) :
    coordinates X 46 = X 3 3 1 1 := rfl

@[simp] theorem coordinates_47 (X : Hessian) :
    coordinates X 47 = X 3 3 0 1 := rfl

@[simp] theorem coordinates_48 (X : Hessian) :
    coordinates X 48 = X 3 3 0 2 := rfl

@[simp] theorem coordinates_49 (X : Hessian) :
    coordinates X 49 = X 3 3 1 2 := rfl

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal projection is constructed from the actual tensor subspace. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

def hessianVector (X : Hessian) : HessianSpace := WithLp.toLp 2 (tensorCoordinates X)

def vectorHessian (v : HessianSpace) : Hessian := fun i j a b => v (i, j, a, b)

@[simp] theorem vectorHessian_hessianVector (X : Hessian) :
    vectorHessian (hessianVector X) = X := rfl

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoupledOperator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real coupled operator used for the plus projection. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The matrix kernel of `Σ I_outer,s (I_inner,s + Σ_s)`. -/
def couplingKernel (p q : TensorIndex) : ℝ := ∑ s : Fin 3,
  quaternionMatrix s p.1 q.1 *
    ((if p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
        then quaternionMatrix s p.2.1 q.2.1 else 0) +
      (if p.2.1 = q.2.1 ∧ p.2.2.2 = q.2.2.2
        then rotation s p.2.2.1 q.2.2.1 else 0) +
      (if p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1
        then rotation s p.2.2.2 q.2.2.2 else 0))

def coupledOperator (X : Hessian) : Hessian := fun i j a b =>
  ∑ q : TensorIndex, couplingKernel (i, j, a, b) q * tensorCoordinates X q

@[simp] theorem coupledOperator_coordinates (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (coupledOperator X) p =
      ∑ q : TensorIndex, couplingKernel p q * tensorCoordinates X q := by
  rcases p with ⟨i, j, a, b⟩
  rfl

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameBundle
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual orthonormal frames with the topology inherited from tangent
vectors. Using the tangent-bundle topology is essential: chart coordinates
at varying base points do not give a global product trivialization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

instance instMeasurableSpaceFrameBundle (g : SmoothMetric M) : MeasurableSpace (FrameBundle g) :=
  borel (FrameBundle g)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylDerivative
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate covariant derivatives of the actual curvature tensor. The
scalar-curvature contribution is subtracted in the Ricci=3g normalization.
The definitions retain all tensor slots until after differentiation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The induced Levi-Civita derivative on covariant coordinate tensors. The
leading slot records the direction of differentiation. -/
def covariantDerivative {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace) :
    CovariantCoordinates (n + 1) := fun a =>
  partialDeriv (fun w => T w (fun i => a i.succ)) (a 0) z -
    ∑ i : Fin n, ∑ b : Fin 4,
      christoffel g c z b (a 0) (a i.succ) *
        T z (Function.update (fun i => a i.succ) i b)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameFlow
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frame-flow action on the actual normal-curvature fields. The
measure-preserving continuous action is the precise part of Brin--Karcher,
Section 1, used here; no ergodicity or curvature-energy bound is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

structure FrameFlow (g : SmoothMetric M) (μ : Measure (FrameBundle g)) where
  map : ℝ → FrameBundle g ≃ᵐ FrameBundle g
  continuous : Continuous (fun p : ℝ × FrameBundle g => map p.1 p.2)
  preserves : ∀ t, MeasurePreserving (map t) μ μ

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixSlotOperator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying matrix-slot curvature coefficient as an actual bounded
operator. The extension to all matrix arrays is self-adjoint; on trace-free
arrays it is the trace-free anticommutator used in the Weyl equation. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

local instance instNormedAddCommGroupMat_r2196d1_1 : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealMat_r2196d1_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
/-- The uncompressed trace-free anticommutator on a matrix. -/
def matrixSlotAction (A M : Mat) : Mat := fun a b =>
  (1 / 2 : ℝ) * ((∑ c, A a c * M c b) + ∑ c, M a c * A c b) -
    if a = b then (∑ c, ∑ d, A c d * M d c) / 3 else 0

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CubicWeight
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the actual cubic trace and its squared-weight contribution. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian

noncomputable section

/-- The matrix of derivatives in a fixed tangent direction. -/
def derivativeMatrix (T : Tensor) (d : Fin 4) : Mat :=
  fun i j => T.matrix i j d

/-- The trace appearing in the varying matrix-slot coefficient. -/
def weightedCubicTrace (a : Vec) (T : Tensor) : ℝ :=
  ∑ d, a d * Matrix.trace (derivativeMatrix T d *
    (∑ j, derivativeMatrix T j * derivativeMatrix T j))

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureSecondBianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate second Bianchi identity. The matrix algebra separates
the commuting second derivatives from the Jacobi cancellation. -/

namespace PositiveEinsteinFour.CovariantBianchi

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem curvature_skew (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat) (i j : Fin 4) :
    curvature C D i j = -curvature C D j i := by
  unfold curvature
  noncomm_ring

def curvatureDerivative (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat) (i j k : Fin 4) : Mat :=
  E i j k - E i k j + D i j * C k + C j * D i k - D i k * C j - C k * D i j

def covariantCurvatureDerivative (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat) (i j k : Fin 4) : Mat :=
  curvatureDerivative C D E i j k + C i * curvature C D j k - curvature C D j k * C i

theorem cyclic_identity_of_commuting_derivatives
    (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat)
    (hE : ∀ i j k, E i j k = E j i k) (i j k : Fin 4) :
    covariantCurvatureDerivative C D E i j k +
      covariantCurvatureDerivative C D E j k i +
      covariantCurvatureDerivative C D E k i j = 0 := by
  unfold covariantCurvatureDerivative curvatureDerivative curvature
  rw [hE j i k, hE k i j, hE k j i]
  noncomm_ring

def lowerSlotCorrection (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (i j k : Fin 4) : Mat :=
  ∑ p, (C i p j • curvature C D p k + C i p k • curvature C D j p)

theorem lowerSlotCorrection_cyclic
    (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (hC : ∀ i j p, C i p j = C j p i) (i j k : Fin 4) :
    lowerSlotCorrection C D i j k + lowerSlotCorrection C D j k i +
      lowerSlotCorrection C D k i j = 0 := by
  unfold lowerSlotCorrection
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro p _
  rw [hC j i p, hC k i p, hC k j p,
    curvature_skew C D p i, curvature_skew C D k p, curvature_skew C D p j]
  module

def tensorCurvatureDerivative (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat) (i j k : Fin 4) : Mat :=
  covariantCurvatureDerivative C D E i j k - lowerSlotCorrection C D i j k

theorem tensorCurvatureDerivative_cyclic
    (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat)
    (hC : ∀ i j p, C i p j = C j p i)
    (hE : ∀ i j k, E i j k = E j i k) (i j k : Fin 4) :
    tensorCurvatureDerivative C D E i j k +
      tensorCurvatureDerivative C D E j k i +
      tensorCurvatureDerivative C D E k i j = 0 := by
  have hc := cyclic_identity_of_commuting_derivatives C D E hE i j k
  have hl := lowerSlotCorrection_cyclic C D hC i j k
  unfold tensorCurvatureDerivative
  calc
    _ = (covariantCurvatureDerivative C D E i j k +
        covariantCurvatureDerivative C D E j k i +
        covariantCurvatureDerivative C D E k i j) -
        (lowerSlotCorrection C D i j k + lowerSlotCorrection C D j k i +
        lowerSlotCorrection C D k i j) := by abel
    _ = 0 := by rw [hc, hl]; simp

end
end PositiveEinsteinFour.CovariantBianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCoordinateModel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed twelve real coordinates for the inner generators in the cost calculation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian
set_option maxHeartbeats 1000000

def costShape : Shape where
  s := ![-1, -1, 2]
  trace := by simp [Fin.sum_univ_three] <;> norm_num
  square := by simp [Fin.sum_univ_three] <;> norm_num

/-- Only this fixed frame is needed for the invariant real-vector cost. -/
def costParameters (v : Fin 3 → Vec) : Tensor := parameters costShape (v 0) (v 1) (v 2)

def generatorCoordinates (s : Fin 3) (v : Fin 3 → Vec) : Fin 3 → Vec := fun i =>
  quaternion s (∑ j, generatorCoefficients s i j • v j)

/-- The actual Frobenius norm in these twelve real coordinates. -/
def coordinateNorm (v : Fin 3 → Vec) : ℝ :=
  10 * ‖v 0‖ ^ 2 + 30 * ‖v 1‖ ^ 2 + 6 * ‖v 2‖ ^ 2

/-- The three quaternion coefficients of the total action on `(7-K)L`. -/
def costCoefficientCoordinates (s r : Fin 3) (v : Fin 3 → Vec) : Fin 3 → Vec :=
  if r = s then (7 : ℝ) • v - generatorCoordinates s (generatorCoordinates s v)
  else if r = next s then
    generatorCoordinates (previous s) v -
      generatorCoordinates s (generatorCoordinates (next s) v)
  else -generatorCoordinates (next s) v -
      generatorCoordinates s (generatorCoordinates (previous s) v)

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylLaplacian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar contraction of the commuted Weyl equation. The compression
coefficient is derived on the actual Bianchi tensor, not taken from a
representation label or assumed as the manuscript's differential equation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

def totalGradientTensor (s : Fin 3) (Z : Tensor) : Tensor where
  diagonal a := rawGradientGenerator s Z.matrix a a
  off a := rawGradientGenerator s Z.matrix (next a) (previous a)

end

end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeneralMatrixCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bianchi compression for an arbitrary symmetric trace-free Weyl matrix,
with no choice of a moving diagonal frame. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The actual trace-free anticommutator, acting on the two matrix indices. -/
def generalMatrixAction (A : Mat) (Z : RawGradient) : RawGradient :=
  fun a b => WithLp.toLp 2 (fun j => matrixSlotAction A (fun c d => Z c d j) a b)

/-- Mixed derivative/matrix action, retaining the full matrix of coefficients. -/
def generalMixedAction (A : Mat) (Z : RawGradient) : RawGradient :=
  fun a b => ∑ r, ∑ s, A r s • quaternion r (rawMatrixRotation s Z a b)


/-- The polynomial formula for the actual orthogonal Bianchi compression. -/
def rawBianchiProjection (Z : RawGradient) : RawGradient :=
  (1 / 10 : ℝ) • ((6 : ℝ) • Z - rawCoupling Z)

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RealVectorProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-vector norm calculation behind the plus projection cost. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The coupled action on a real rank-one weight tensor. -/
def weightCoupling (a : Vec) (Z : Tensor) : Hessian := fun i j b c =>
  ∑ s : Fin 3, quaternion s a i * gradientGenerator s Z b c j

/-- The explicit polynomial `(7-K)(a ⊗ Z)/12`, where
`K = Σ I_outer,s ⊗ (I_inner,s + Σ_s)`. -/
def weightPlusPart (a : Vec) (Z : Tensor) : Hessian := fun i j b c =>
  (7 * a i * Z.matrix b c j - weightCoupling a Z i j b c) / 12

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RealVectorCost
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second real-vector projection identity in actual tensor coordinates. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian HighestHessian

/-- Frobenius norm of an arbitrary matrix of real four-vectors. -/
def rawNorm (Z : RawGradient) : ℝ := ∑ b, ∑ c, ‖Z b c‖ ^ 2

@[simp] theorem rawNorm_matrix (Z : Tensor) : rawNorm Z.matrix = Z.squaredNorm := rfl

/-- Quaternion coefficient of the total derivative of `(7-K)L`. -/
def rawCostCoefficient (s r : Fin 3) (Z : RawGradient) : RawGradient :=
  if r = s then (7 : ℝ) • Z - rawGradientGenerator s (rawGradientGenerator s Z)
  else if r = next s then
    rawGradientGenerator (previous s) Z -
      rawGradientGenerator s (rawGradientGenerator (next s) Z)
  else -rawGradientGenerator (next s) Z -
      rawGradientGenerator s (rawGradientGenerator (previous s) Z)

/-- A real outer quaternion combination, keeping all inner correlations. -/
def quaternionCombination (a : Vec) (Z : RawGradient)
    (C : Fin 3 → RawGradient) : Hessian := fun i j b c =>
  a i * Z b c j + ∑ s : Fin 3, quaternion s a i * C s b c j

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientMixedPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear matrix-slot compression on two actual Bianchi gradients. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The diagonal matrix-slot form keeps both Bianchi arguments. -/
def diagonalGradientPairing (t : Fin 3 → ℝ) (Z W : Tensor) : ℝ :=
  ∑ s, t s * (∑ b, inner ℝ (Z.matrix s b) (W.matrix s b))

/-- The actual trace-free anticommutator, applied independently in each
derivative direction. -/
def rawMatrixCurvature (t : Fin 3 → ℝ) (Z : Tensor) : RawGradient := fun a b =>
  ((t a + t b) / 2) • Z.matrix a b -
    if a = b then (1 / 3 : ℝ) • (∑ c, t c • Z.diagonal c) else 0

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylMatrixEquation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Weyl matrix equation in an arbitrary orthonormal frame. This
derivation uses the actual Bianchi Hessian and curvature commutator, so
no eigenframe is differentiated. -/

namespace PositiveEinsteinFour.TraceHessian

open scoped BigOperators
open Matrix
open HighestHessian

noncomputable section

/-- Curvature acting on the matrix bundle in the Ric=3g normalization.
The row `M r s` is the Weyl block in the same fixed frame. -/
def bundleCurvatureAction (M : Mat) (i j : Fin 4) (N : Mat) : Mat :=
  (1 / 2 : ℝ) • ∑ r, quaternionMatrix r i j •
    (matrixAction r N + ∑ s, M r s • matrixAction s N)

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Contract the two ordinary covariant commutation identities. These are
the slotwise Ricci identities of Petersen, Section 3.1.1; the new compressed
gradient equation is a consequence, not an assumed differential equation. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

def rawMatrixSlice (Z : RawGradient) (j : Fin 4) : Mat := fun a b => Z a b j

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contract the raw bundle and covector actions appearing in the
derivative-slot Green identity. These are finite tensor contractions,
before integration and before any estimate. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi PositiveEinsteinFour.Geometry

noncomputable section

def matrixPairingLinear (N : Mat) : Mat →ₗ[ℝ] ℝ where
  toFun M := matrixPairing M N
  map_add' M P := by
    simp only [matrixPairing, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r M := by
    simp only [matrixPairing, Matrix.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum, RingHom.id_apply]

def covectorGreenContraction (A R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (Z : Tensor) : ℝ :=
  ∑ l, ∑ h, ((1 / 2 : ℝ) * ∑ j, ∑ i, ∑ k, A i k j l * R i k j h) *
    matrixPairing (rawMatrixSlice Z.matrix h) (rawMatrixSlice Z.matrix l)

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! The complete raw Ricci commutator in the derivative-slot Green
integrand. The bundle and covector contractions are both retained. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi PositiveEinsteinFour.Geometry MeasureTheory

noncomputable section

theorem matrixPairing_sum_smul_left {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (A : ι → Mat) (N : Mat) :
    matrixPairing (∑ i, c i • A i) N = ∑ i, c i * matrixPairing (A i) N := by
  change matrixPairingLinear N _ = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

def derivativeGreenContraction
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (C : Fin 4 → Fin 4 → Fin 4 → Mat) (Z : Tensor) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ k, ∑ j, ∑ l, A i k j l *
    matrixPairing (C i k j) (rawMatrixSlice Z.matrix l)

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! Curvature contractions with the entire symmetric Weyl matrix.
No moving eigenframe enters these identities. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open Matrix TraceHessian Bianchi PositiveEinsteinFour.Geometry

noncomputable section

def generalGradientForm (A : Mat) (Z : Tensor) : ℝ :=
  rawPairing (generalMatrixAction A Z.matrix) Z.matrix

/-- Both matrix indices are kept in the actual curvature coefficient. -/
def generalCoefficient (Q : Fin 3 → Mat4) (A : Mat)
    (i k j l : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ r, ∑ s, A r s * Q r i k * Q s j l

def generalBundleGreenContraction
    (K : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Mat) (Z : Tensor) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, ∑ l, ∑ i, ∑ k, K i k j l *
    matrixPairing (bundleCurvatureAction A i k (rawMatrixSlice Z.matrix j))
      (rawMatrixSlice Z.matrix l)

def generalEinsteinCoefficient (A U : Mat) (i k j l : Fin 4) : ℝ :=
  generalCoefficient quaternionMatrix (1 + A) i k j l +
    generalCoefficient Angular.oppositeMatrix (1 + U) i k j l


/-- The two raw curvature actions in the commutator of a covariant
Weyl gradient, with an arbitrary matrix in the Weyl bundle slot. -/
def generalRawCurvatureCommutator (A : Mat)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (Z : Tensor)
    (i k j : Fin 4) : Mat :=
  bundleCurvatureAction A i k (rawMatrixSlice Z.matrix j) +
    ∑ h, R i k j h • rawMatrixSlice Z.matrix h

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! Polarized real-vector cost identities in twelve Bianchi coordinates,
including the three off-diagonal generator pairs. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian HighestHessian

noncomputable section

def coordinatePairing (v w : Fin 3 → Vec) : ℝ :=
  10 * inner ℝ (v 0) (w 0) + 30 * inner ℝ (v 1) (w 1) + 6 * inner ℝ (v 2) (w 2)

end
end PositiveEinsteinFour.Bianchi
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A four-column Gram--Schmidt normalizer with entrywise smooth dependence
on the positive metric matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def metricPair (G : Mat4) (u v : CoordinateColumn) : ℝ :=
  ∑ i, ∑ j, u i * G i j * v j

def gramColumnZero (_G : Mat4) : CoordinateColumn := Pi.single 0 1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local orthonormal frames obtained from smooth coordinate vectors
by the explicit four-column normalizer. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev ChartTarget (c : M) := {z : FourSpace // z ∈ (chartAt FourSpace c).target}

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverCore
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual orientation double cover, obtained by applying the determinant
sign representation to the tangent bundle's transition functions. Its two-point
fibers are glued by the genuine derivatives of chart changes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter _root_.Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev TC := tangentBundleCore I4 M
abbrev CI := atlas FourSpace M

/-- Determinant of the actual tangent transition, from chart `i` to chart `j`. -/
def orientationTransitionDet (i j : CI (M := M)) (x : M) : ℝ :=
  ((TC (M := M)).coordChange i j x).det

theorem orientationTransitionDet_self (i : CI (M := M)) {x : M}
    (hx : x ∈ i.val.source) : orientationTransitionDet i i x = 1 := by
  have h : (TC (M := M)).coordChange i i x = ContinuousLinearMap.id ℝ FourSpace := by
    apply ContinuousLinearMap.ext
    intro v
    exact (TC (M := M)).coordChange_self i x hx v
  unfold orientationTransitionDet
  rw [h]
  exact LinearMap.det_id

theorem orientationTransitionDet_comp (i j k : CI (M := M)) {x : M}
    (hx : x ∈ i.val.source ∩ j.val.source ∩ k.val.source) :
    orientationTransitionDet i k x =
      orientationTransitionDet j k x * orientationTransitionDet i j x := by
  have h := (TC (M := M)).coordChange_linear_comp i j k x hx
  unfold orientationTransitionDet
  rw [← h]
  exact LinearMap.det_comp _ _

theorem orientationTransitionDet_ne_zero (i j : CI (M := M)) {x : M}
    (hx : x ∈ i.val.source ∩ j.val.source) : orientationTransitionDet i j x ≠ 0 := by
  have h := orientationTransitionDet_comp i j i (show x ∈ i.val.source ∩ j.val.source ∩ i.val.source from ⟨hx, hx.1⟩)
  rw [orientationTransitionDet_self i hx.1] at h
  intro hz
  rw [hz, mul_zero] at h
  exact one_ne_zero h

theorem orientationTransitionDet_continuousOn (i j : CI (M := M)) :
    ContinuousOn (orientationTransitionDet i j) (i.val.source ∩ j.val.source) :=
  ContinuousLinearMap.continuous_det.comp_continuousOn ((TC (M := M)).continuousOn_coordChange i j)

theorem orientationTransition_continuousOn (i j : CI (M := M)) :
    ContinuousOn (fun p : M × Bool => orientationSignChange (orientationTransitionDet i j p.1) p.2)
      ((i.val.source ∩ j.val.source) ×ˢ univ) := by
  intro p hp
  have hd : ContinuousWithinAt (fun q : M × Bool => orientationTransitionDet i j q.1)
      ((i.val.source ∩ j.val.source) ×ˢ univ) p :=
    ((orientationTransitionDet_continuousOn i j).comp continuousOn_fst
      (fun _ h => h.1)) p hp
  by_cases hpos : 0 < orientationTransitionDet i j p.1
  · apply continuousWithinAt_snd.congr_of_eventuallyEq
    · filter_upwards [hd.eventually (Ioi_mem_nhds hpos)] with q hq
      exact ite_eq_left hq
    · exact ite_eq_left hpos
  · have hn : orientationTransitionDet i j p.1 < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) (orientationTransitionDet_ne_zero i j hp.1)
    have hc : Continuous (fun q : M × Bool => !q.2) := by fun_prop
    apply hc.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [hd.eventually (Iio_mem_nhds hn)] with q hq
      exact ite_eq_right (not_lt.mpr hq.le)
    · exact ite_eq_right hpos

/-- The orientation cover is a bundle with the determinant-sign cocycle. -/
def orientationCoverCore : FiberBundleCore (CI (M := M)) M Bool where
  baseSet i := i.val.source
  isOpen_baseSet i := i.val.open_source
  indexAt := (TC (M := M)).indexAt
  mem_baseSet_at := (TC (M := M)).mem_baseSet_at
  coordChange i j x := orientationSignChange (orientationTransitionDet i j x)
  coordChange_self i x hx s := by
    rw [orientationTransitionDet_self i hx]
    simp [orientationSignChange]
  continuousOn_coordChange := orientationTransition_continuousOn
  coordChange_comp i j k x hx s := by
    rw [orientationTransitionDet_comp i j k hx]
    exact orientationSignChange_mul (orientationTransitionDet_ne_zero i j hx.1)
      (orientationTransitionDet_ne_zero j k ⟨hx.1.2, hx.2⟩) s

abbrev OrientationCover (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] := (orientationCoverCore (M := M)).TotalSpace

/-- The projection has exactly two sheets, with actual bundle trivializations. -/
theorem orientationCover_isCoveringMap :
    IsCoveringMap (orientationCoverCore (M := M)).proj := by
  apply IsCoveringMap.mk (orientationCoverCore (M := M)).proj (fun _ : M => Bool)
    (fun x => (orientationCoverCore (M := M)).localTrivAt x)
  exact (orientationCoverCore (M := M)).mem_baseSet_at

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverTopology
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual orientation cover has a continuous free deck involution and
exactly two points over each base point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter _root_.Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev orientationCoverProjection : OrientationCover M → M :=
  (orientationCoverCore (M := M)).proj

def orientationCoverDeck (x : OrientationCover M) : OrientationCover M := ⟨x.proj, !x.snd⟩

@[simp] theorem orientationCoverDeck_proj (x : OrientationCover M) :
    (orientationCoverDeck x).proj = x.proj := rfl

@[simp] theorem orientationCoverDeck_deck (x : OrientationCover M) :
    orientationCoverDeck (orientationCoverDeck x) = x := by
  cases x with
  | mk a s => exact congrArg (TotalSpace.mk a) (Bool.not_not s)

theorem orientationCoverDeck_localTriv (i : atlas FourSpace M) (x : OrientationCover M) :
    (orientationCoverCore (M := M)).localTriv i (orientationCoverDeck x) =
      ((orientationCoverCore (M := M)).localTriv i x).map id Bool.not := by
  let d := orientationTransitionDet ((orientationCoverCore (M := M)).indexAt x.proj) i x.proj
  change (x.proj, if 0 < d then !x.snd else !(!x.snd)) =
    (x.proj, !(if 0 < d then x.snd else !x.snd))
  by_cases h : 0 < d <;> simp [h]


theorem continuous_orientationCoverDeck : Continuous (orientationCoverDeck (M := M)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let Z := orientationCoverCore (M := M)
  let e := Z.localTrivAt x.proj
  have hx : x ∈ e.source := Z.mk_mem_localTrivAt_source x.proj x.snd
  have hdx : orientationCoverDeck x ∈ e.source :=
    Z.mk_mem_localTrivAt_source x.proj (!x.snd)
  let N : M × Bool → M × Bool := fun p => (p.1, !p.2)
  have hN : Continuous N := continuous_fst.prodMk (by fun_prop)
  have he : e (orientationCoverDeck x) = N (e x) :=
    orientationCoverDeck_localTriv _ x
  have htarget : N (e x) ∈ e.target := he ▸ e.map_source hdx
  have hec : ContinuousAt (fun y => e y) x := e.toOpenPartialHomeomorph.continuousAt hx
  have hNc : ContinuousAt (fun y => N (e y)) x := hN.continuousAt.comp hec
  have hic : ContinuousAt (fun p => e.toOpenPartialHomeomorph.symm p) (N (e x)) :=
    e.toOpenPartialHomeomorph.symm.continuousAt htarget
  have hcomp : ContinuousAt (fun y => e.toOpenPartialHomeomorph.symm (N (e y))) x :=
    ContinuousAt.comp (f := fun y => N (e y)) (g := fun p => e.toOpenPartialHomeomorph.symm p) hic hNc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  have hdy : orientationCoverDeck y ∈ e.source := hy
  have hcomm : e (orientationCoverDeck y) = N (e y) := orientationCoverDeck_localTriv _ y
  rw [← hcomm]
  exact (e.toOpenPartialHomeomorph.left_inv hdy).symm

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverCharts
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth local coordinates on the actual orientation cover. The projection
identifies each sheet with a base chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def orientationCoverLocal (x : OrientationCover M) : OpenPartialHomeomorph (OrientationCover M) M :=
  (orientationCover_isCoveringMap.isLocalHomeomorph.localInverseAt x).symm

@[simp] theorem orientationCoverLocal_apply (x y : OrientationCover M) :
    orientationCoverLocal x y = y.proj := by
  exact congrFun (orientationCover_isCoveringMap.isLocalHomeomorph.localInverseAt_symm x) y

theorem orientationCoverLocal_mem (x : OrientationCover M) :
    x ∈ (orientationCoverLocal x).source :=
  orientationCover_isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target

def orientationCoverChart (x : OrientationCover M) :
    OpenPartialHomeomorph (OrientationCover M) FourSpace :=
  (orientationCoverLocal x).trans (chartAt FourSpace x.proj)

@[simp] theorem orientationCoverChart_apply (x y : OrientationCover M) :
    orientationCoverChart x y = chartAt FourSpace x.proj y.proj := by
  change chartAt FourSpace x.proj (orientationCoverLocal x y) = _
  rw [orientationCoverLocal_apply]

theorem orientationCoverChart_mem (x : OrientationCover M) :
    x ∈ (orientationCoverChart x).source :=
  ⟨orientationCoverLocal_mem x, by change orientationCoverLocal x x ∈ (chartAt FourSpace x.proj).source; rw [orientationCoverLocal_apply]; exact mem_chart_source FourSpace x.proj⟩

theorem orientationCoverChart_inverse_proj (x : OrientationCover M) {z : FourSpace}
    (hz : z ∈ (orientationCoverChart x).target) :
    ((orientationCoverChart x).symm z).proj = (chartAt FourSpace x.proj).symm z := by
  change ((orientationCoverLocal x).symm ((chartAt FourSpace x.proj).symm z)).proj = _
  have h := (orientationCoverLocal x).right_inv hz.2
  simpa only [orientationCoverLocal_apply] using h

instance orientationCover_chartedSpace : ChartedSpace FourSpace (OrientationCover M) where
  atlas := range (orientationCoverChart (M := M))
  chartAt := orientationCoverChart
  mem_chart_source := orientationCoverChart_mem
  chart_mem_atlas x := mem_range_self x

/-- Each change of sheets uses precisely the base chart transition. -/
theorem orientationCover_transition_eq (x y : OrientationCover M) {z : FourSpace}
    (hz : z ∈ ((orientationCoverChart x).symm.trans (orientationCoverChart y)).source) :
    ((orientationCoverChart x).symm.trans (orientationCoverChart y)) z =
      chartAt FourSpace y.proj ((chartAt FourSpace x.proj).symm z) := by
  change orientationCoverChart y ((orientationCoverChart x).symm z) = _
  rw [orientationCoverChart_apply, orientationCoverChart_inverse_proj x hz.1]

theorem orientationCover_transition_source (x y : OrientationCover M) :
    ((orientationCoverChart x).symm.trans (orientationCoverChart y)).source ⊆
      ((chartAt FourSpace x.proj).symm.trans (chartAt FourSpace y.proj)).source := by
  intro z hz
  refine ⟨hz.1.1, ?_⟩
  have h := hz.2.2
  change orientationCoverLocal y ((orientationCoverChart x).symm z) ∈
    (chartAt FourSpace y.proj).source at h
  rwa [orientationCoverLocal_apply, orientationCoverChart_inverse_proj x hz.1] at h

instance orientationCover_isManifold : IsManifold I4 ∞ (OrientationCover M) := by
  apply isManifold_of_contDiffOn I4 ∞
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simp only [I4, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, preimage_id, range_id, inter_univ]
  change ContDiffOn ℝ ∞
    (fun z => orientationCoverChart y ((orientationCoverChart x).symm z))
    ((orientationCoverChart x).symm.trans (orientationCoverChart y)).source
  have hcompat := (contDiffGroupoid ∞ I4).compatible
    (chart_mem_atlas FourSpace x.proj) (chart_mem_atlas FourSpace y.proj)
  obtain ⟨hbase, _⟩ := hcompat
  change ContDiffOn ℝ ∞
    (I4 ∘ ((chartAt FourSpace x.proj).symm.trans (chartAt FourSpace y.proj)) ∘ I4.symm)
    (I4.symm ⁻¹' ((chartAt FourSpace x.proj).symm.trans (chartAt FourSpace y.proj)).source ∩ range I4) at hbase
  simp only [I4, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, preimage_id, range_id, inter_univ] at hbase
  apply (hbase.mono (orientationCover_transition_source x y)).congr
  intro z hz
  exact orientationCover_transition_eq x y hz

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The projection of the actual orientation cover is smooth and its derivative
is the identity in the preferred tangent coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter _root_.Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_projection_inCharts (x : OrientationCover M) :
    writtenInExtChartAt I4 I4 x orientationCoverProjection =ᶠ[
      𝓝 (extChartAt I4 x x)] id := by
  have hx : orientationCoverChart x x ∈ (orientationCoverChart x).target :=
    (orientationCoverChart x).map_source (orientationCoverChart_mem x)
  have hcenter : extChartAt I4 x x = orientationCoverChart x x := by
    simp only [extChartAt_coe, I4, modelWithCornersSelf_coe, Function.comp_apply, id_eq]
    rfl
  rw [hcenter]
  filter_upwards [(orientationCoverChart x).open_target.mem_nhds hx] with z hz
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, I4,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
  change chartAt FourSpace x.proj (((orientationCoverChart x).symm z).proj) = z
  rw [orientationCoverChart_inverse_proj x hz]
  exact (chartAt FourSpace x.proj).right_inv hz.1

theorem orientationCover_projection_smooth :
    ContMDiff I4 I4 ∞ (orientationCoverProjection (M := M)) := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨orientationCover_isCoveringMap.continuous.continuousAt, ?_⟩
  have h : ContDiffAt ℝ ∞ (writtenInExtChartAt I4 I4 x orientationCoverProjection)
      (extChartAt I4 x x) :=
    contDiffAt_id.congr_of_eventuallyEq (orientationCover_projection_inCharts x)
  exact h.contDiffWithinAt

theorem orientationCover_projection_hasMFDerivAt (x : OrientationCover M) :
    HasMFDerivAt I4 I4 orientationCoverProjection x (ContinuousLinearMap.id ℝ FourSpace) := by
  refine ⟨orientationCover_isCoveringMap.continuous.continuousAt, ?_⟩
  have h := (hasFDerivAt_id (𝕜 := ℝ) (extChartAt I4 x x)).congr_of_eventuallyEq
    (orientationCover_projection_inCharts x)
  exact h.hasFDerivWithinAt

@[simp] theorem orientationCover_projection_mfderiv (x : OrientationCover M) :
    mfderiv I4 I4 orientationCoverProjection x = ContinuousLinearMap.id ℝ FourSpace :=
  (orientationCover_projection_hasMFDerivAt x).mfderiv

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverTangent
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tangent trivializations on each sheet agree with the base trivializations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_tangent_trivialization (x y : OrientationCover M)
    (hy : y ∈ (chartAt FourSpace x).source) :
    (trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x).continuousLinearMapAt ℝ y =
      (trivializationAt FourSpace (TangentSpace I4 : M → Type _) x.proj).continuousLinearMapAt ℝ y.proj := by
  have hb : y.proj ∈ (chartAt FourSpace x.proj).source := by
    have h : orientationCoverLocal x y ∈ (chartAt FourSpace x.proj).source := hy.2
    simpa only [orientationCoverLocal_apply] using h
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy,
    TangentBundle.continuousLinearMapAt_trivializationAt hb]
  have he : (extChartAt I4 x : OrientationCover M → FourSpace) =
      extChartAt I4 x.proj ∘ orientationCoverProjection := by
    funext z
    simp only [extChartAt_coe, Function.comp_apply]
    rw [show chartAt FourSpace x z = chartAt FourSpace x.proj z.proj from
      orientationCoverChart_apply x z]
  rw [he, mfderiv_comp y (mdifferentiableAt_extChartAt hb)
    (orientationCover_projection_hasMFDerivAt y).mdifferentiableAt,
    orientationCover_projection_mfderiv]
  rfl

theorem orientationCover_tangent_inverse_trivialization (x y : OrientationCover M)
    (hy : y ∈ (chartAt FourSpace x).source) :
    (trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x).symmL ℝ y =
      (trivializationAt FourSpace (TangentSpace I4 : M → Type _) x.proj).symmL ℝ y.proj := by
  let a := trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x
  let b := trivializationAt FourSpace (TangentSpace I4 : M → Type _) x.proj
  have ha : y ∈ a.baseSet := hy
  have hb : y.proj ∈ b.baseSet := by
    change y.proj ∈ (chartAt FourSpace x.proj).source
    have h : orientationCoverLocal x y ∈ (chartAt FourSpace x.proj).source := hy.2
    simpa only [orientationCoverLocal_apply] using h
  have hf := orientationCover_tangent_trivialization x y hy
  apply ContinuousLinearMap.ext
  intro v
  have h₁ : b.symmL ℝ y.proj (b.continuousLinearMapAt ℝ y.proj (a.symmL ℝ y v)) =
      a.symmL ℝ y v := b.symmL_continuousLinearMapAt hb _
  have h₂ : b.continuousLinearMapAt ℝ y.proj (a.symmL ℝ y v) = v := by
    rw [← hf]
    exact a.continuousLinearMapAt_symmL ha v
  exact h₁.symm.trans (congrArg (fun z : FourSpace => b.symmL ℝ y.proj z) h₂)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverMetric
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pullback Riemannian metric on the orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set Filter _root_.Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local notation "V" => FourSpace
local notation "B" => (V →L[ℝ] V →L[ℝ] ℝ)

theorem orientationCover_bilinear_coordinates (x y : OrientationCover M)
    (hy : y ∈ (chartAt V x).source) (b : B) :
    (trivializationAt B (fun z : OrientationCover M => TangentSpace I4 z →L[ℝ]
      TangentSpace I4 z →L[ℝ] ℝ) x ⟨y, b⟩).2 =
    (trivializationAt B (fun z : M => TangentSpace I4 z →L[ℝ]
      TangentSpace I4 z →L[ℝ] ℝ) x.proj ⟨y.proj, b⟩).2 := by
  have hb : y.proj ∈ (chartAt V x.proj).source := by
    have h : orientationCoverLocal x y ∈ (chartAt V x.proj).source := hy.2
    simpa only [orientationCoverLocal_apply] using h
  simp only [hom_trivializationAt_apply]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have h₁ := inCoordinates_apply_eq₂ (ϕ :=
    (show TangentSpace I4 y →L[ℝ] TangentSpace I4 y →L[ℝ] ℝ from b))
    (v := v) (w := w)
    (show y ∈ (trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x).baseSet from hy)
    (show y ∈ (trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x).baseSet from hy)
    (show y ∈ (trivializationAt ℝ (Bundle.Trivial (OrientationCover M) ℝ) x).baseSet from by simp)
  have h₂ := inCoordinates_apply_eq₂ (ϕ :=
    (show TangentSpace I4 y.proj →L[ℝ] TangentSpace I4 y.proj →L[ℝ] ℝ from b))
    (v := v) (w := w)
    (show y.proj ∈ (trivializationAt V (TangentSpace I4 : M → Type _) x.proj).baseSet from hb)
    (show y.proj ∈ (trivializationAt V (TangentSpace I4 : M → Type _) x.proj).baseSet from hb)
    (show y.proj ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) x.proj).baseSet from by simp)
  apply h₁.trans
  apply Eq.trans _ h₂.symm
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_apply]
  change b ((trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x).symm y v)
    ((trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x).symm y w) =
    b ((trivializationAt V (TangentSpace I4 : M → Type _) x.proj).symm y.proj v)
    ((trivializationAt V (TangentSpace I4 : M → Type _) x.proj).symm y.proj w)
  simp only [← Trivialization.symmL_apply (R := ℝ)
    (trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x) hy,
    ← Trivialization.symmL_apply (R := ℝ)
      (trivializationAt V (TangentSpace I4 : M → Type _) x.proj) hb,
    orientationCover_tangent_inverse_trivialization x y hy]
  rfl



/-- In the preferred coordinates the derivative of the covering projection is
identity, so the pullback inner product is the actual base inner product. -/
def orientationCoverMetric (g : SmoothMetric M) : SmoothMetric (OrientationCover M) where
  inner x := g.inner x.proj
  symm x := g.symm x.proj
  pos x := g.pos x.proj
  isVonNBounded x := g.isVonNBounded x.proj
  contMDiff := by
    intro x
    apply (contMDiffAt_section (s := fun y : OrientationCover M =>
      (show TangentSpace I4 y →L[ℝ] TangentSpace I4 y →L[ℝ] ℝ from g.inner y.proj)) x).mpr
    have hg := (contMDiffAt_section (s := g.inner) x.proj).mp (g.contMDiff x.proj)
    have hc := hg.comp x (orientationCover_projection_smooth x)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(chartAt V x).open_source.mem_nhds (mem_chart_source V x)] with y hy
    exact orientationCover_bilinear_coordinates x y hy (g.inner y.proj)

@[simp] theorem orientationCoverMetric_inner (g : SmoothMetric M) (x : OrientationCover M)
    (v w : FourSpace) : (orientationCoverMetric g).inner x v w = g.inner x.proj v w := rfl

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverSmoothLift
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous lift through the orientation cover inherits smoothness from
its projection, because its local chart is exactly the base chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter _root_.Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] {n : ℕ∞ω}

theorem contMDiffAt_orientationCover_lift {f : N → OrientationCover M} {x : N}
    (hc : ContinuousAt f x)
    (hf : ContMDiffAt J I4 n (orientationCoverProjection ∘ f) x) :
    ContMDiffAt J I4 n f x := by
  obtain ⟨_, hd⟩ := contMDiffAt_iff.mp hf
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  have he : writtenInExtChartAt J I4 x f =
      writtenInExtChartAt J I4 x (orientationCoverProjection ∘ f) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe]
    exact congrArg I4 (orientationCoverChart_apply (f x) (f ((extChartAt J x).symm z)))
  change ContDiffWithinAt ℝ n (writtenInExtChartAt J I4 x f) (range J) (extChartAt J x x)
  rw [he]
  exact hd

theorem contMDiff_orientationCover_lift {f : N → OrientationCover M}
    (hc : Continuous f) (hf : ContMDiff J I4 n (orientationCoverProjection ∘ f)) :
    ContMDiff J I4 n f :=
  fun x => contMDiffAt_orientationCover_lift hc.continuousAt (hf x)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverDeckMetric
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sheet exchange is an actual smooth isometry for the pullback metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_deck_smooth : ContMDiff I4 I4 ∞ (orientationCoverDeck (M := M)) := by
  apply contMDiff_orientationCover_lift continuous_orientationCoverDeck
  simpa only [Function.comp_def, orientationCoverDeck_proj] using
    (orientationCover_projection_smooth (M := M))

@[simp] theorem orientationCover_deck_mfderiv (x : OrientationCover M) :
    mfderiv I4 I4 orientationCoverDeck x = ContinuousLinearMap.id ℝ FourSpace := by
  have h := mfderiv_comp x
    (orientationCover_projection_hasMFDerivAt (orientationCoverDeck x)).mdifferentiableAt
    (orientationCover_deck_smooth.mdifferentiable (by simp) x)
  have he : orientationCoverProjection ∘ orientationCoverDeck =
      (orientationCoverProjection (M := M)) := rfl
  rw [he, orientationCover_projection_mfderiv, orientationCover_projection_mfderiv] at h
  exact h.symm

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual normalized Weyl tensors and their first three covariant derivatives
have the same chart transition law in every slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

def unitMatrixTensor (G : Mat4) : CovariantCoordinates 4 := fun a =>
  G (a 1) (a 2) * G (a 0) (a 3) - G (a 0) (a 2) * G (a 1) (a 3)

theorem matrix_pairing_expansion (J H : Mat4) (i j : Fin 4) :
    (Jᵀ * H * J) i j = ∑ p, ∑ q, J p i * H p q * J q j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual continuous right action of orthogonal matrices on frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def orientedToOrthogonal (Q : OrientedOrthogonalFour) : OrthogonalFour :=
  ⟨Q.val, by
    have h := (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1
    rwa [Matrix.mem_orthogonalGroup_iff'] at h⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Weyl and scalar parallel differentiation from the coordinate
velocity and Levi-Civita frame ODE. No curvature derivative is an input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

local instance parallelFlowNormedRing : NormedRing Mat3 := Matrix.frobeniusNormedRing
local instance parallelFlowNormedSpace : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local horizontal frame vector field is smooth and preserves the
metric Gram matrix. The defining equations are ordinary finite-dimensional
ODEs in one coordinate chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem hasDerivAt_matrix_mul_entry (A B : ℝ → Mat4)
    (A' B' : Mat4) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : Fin 4) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  have h := HasDerivAt.fun_sum (fun r (_ : r ∈ Finset.univ) =>
    (hA i r).mul (hB r j))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib,
    Pi.mul_apply] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Weyl calculus is forced by reflection of the existing
parallel flow. It supplies no additional published tensor identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance oppositeParallelDataInstance1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance oppositeParallelDataInstance2 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature field and its derivative are linear contractions
of the two actual Weyl blocks along the first parallel frame direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

local instance parallelCurvatureCalculusInstance1 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance parallelCurvatureCalculusInstance2 : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


