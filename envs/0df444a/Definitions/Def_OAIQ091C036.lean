-- Prove2me | Definitions.Def_OAIQ091C036
-- name    : OAIQ091C036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:01:30.461264+00:00
-- url     : https://prove2.me/theorems/f8600ab8-99eb-4b3d-b91a-0720c83b8f9d
-- title:
--   Definitions bundle OAIQ091C036 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 4 definitions, 1 instance and 11 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Angular.normalDerivative`, `OAI.PositiveEinsteinFour.Angular.normalDeviation`, `OAI.PositiveEinsteinFour.Angular.weightedMixingMoment`, `OAI.PositiveEinsteinFour.Geometry.normalizedBlockNorm`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_AngularClifford`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularClifford.lean), [`EinsteinFour_AngularDerivativeMoments`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularDerivativeMoments.lean), [`EinsteinFour_AngularGradient`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularGradient.lean), [`EinsteinFour_AngularNormal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularNormal.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean), [`EinsteinFour_WeylGeometry`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylGeometry.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundle `OAIQ091C035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C013`, `OAIQ091C014`, `OAIQ091C015`, `OAIQ091C053` and `OAIQ091C054`; the proofs of `OAI_PositiveEinsteinFour_Geometry_MetricGreenData_jointTraceEnergy_le_hessian`, `OAI_PositiveEinsteinFour_Geometry_smooth_weighted_variance_ae` and `OAI_PositiveEinsteinFour_MomentObstruction_two_constrained_moments`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C035

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylGeometry
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete orthonormal frames and curvature blocks of the metric in the
classification statement, defined from its chart curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The normalized Weyl norm, written without a choice of eigenvectors. -/
def normalizedBlockNorm (T : Mat3) : ℝ :=
  Real.sqrt ((∑ i, ∑ j, T i j ^ 2) / 6)

theorem normalizedBlockNorm_sq (T : Mat3) :
    normalizedBlockNorm T ^ 2 = (∑ i, ∑ j, T i j ^ 2) / 6 := by
  apply Real.sq_sqrt
  positivity

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularClifford
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quaternion matrix identities for the sixth-moment mixed contraction. -/

namespace PositiveEinsteinFour.Angular

open Matrix TraceHessian

noncomputable section

theorem quaternionMatrix_anticommutator (i j : Fin 3) :
    quaternionMatrix i * quaternionMatrix j + quaternionMatrix j * quaternionMatrix i =
      (if i = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [quaternionMatrix, Fin.sum_univ_succ]

theorem oppositeMatrix_anticommutator_one (j : Fin 3) :
    oppositeMatrix 1 * oppositeMatrix j + oppositeMatrix j * oppositeMatrix 1 =
      (if (1 : Fin 3) = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      Fin.sum_univ_succ] <;> norm_num

theorem mixingCoefficient_product (i j k l : Fin 3) :
    mixingCoefficient i k * mixingCoefficient j l =
      quaternionMatrix i * quaternionMatrix j * oppositeMatrix k * oppositeMatrix l := by
  unfold mixingCoefficient
  rw [quaternionMatrix_transpose, quaternionMatrix_transpose]
  calc
    (-quaternionMatrix i * oppositeMatrix k) * (-quaternionMatrix j * oppositeMatrix l) =
        quaternionMatrix i * (oppositeMatrix k * quaternionMatrix j) * oppositeMatrix l := by
      noncomm_ring
    _ = _ := by rw [oppositeMatrix_commute]; noncomm_ring

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise and averaged normal Jacobi curvature form. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

/-- The curvature deviation in the normal basis `I_s q`. -/
def normalDeviation (T U : Mat3) (q : Directions) : Mat3 :=
  (1 / 2 : ℝ) • (T + rotated U q)

theorem squareNorm_eq_trace (T : Mat3) : squareNorm T = (Tᵀ * T).trace := by
  simp only [squareNorm, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [pow_two]

theorem squareNorm_conjugate (O U : Mat3) (hO : O * Oᵀ = 1) :
    squareNorm (O * U * Oᵀ) = squareNorm U := by
  have hOT : Oᵀ * O = 1 := mul_eq_one_comm.mp hO
  rw [squareNorm_eq_trace, squareNorm_eq_trace]
  have hp : (O * U * Oᵀ)ᵀ * (O * U * Oᵀ) = O * (Uᵀ * U) * Oᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      (O * (Uᵀ * Oᵀ)) * (O * U * Oᵀ) = O * Uᵀ * (Oᵀ * O) * U * Oᵀ := by
        noncomm_ring
      _ = _ := by rw [hOT, mul_one]; noncomm_ring
  rw [hp, Matrix.trace_mul_cycle, hOT, one_mul]

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularGradient
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The directional-derivative part of the angular average. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

def normalDerivative (Z W : Gradient) (q : Directions) : Mat3 :=
  normalDeviation (directional Z q) (directional W q) q

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularDerivativeMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite Weyl blocks have zero mixed directional energy. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

def weightedMixingMoment (a b : Fin 4) (i j k l : Fin 3) : ℝ :=
  ∫ q, q.val a * q.val b * (mixing i k q * mixing j l q) ∂sphereMeasure

end

end PositiveEinsteinFour.Angular

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

/-! Compactness of the four-dimensional orthogonal matrix parameter used
in the local orthonormal-frame trivializations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators

noncomputable section

theorem orthogonalFour_entry_bound (S : OrthogonalFour) (i j : Fin 4) :
    -1 ≤ S.val i j ∧ S.val i j ≤ 1 := by
  have hsum : ∑ k, S.val k j * S.val k j = 1 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] using
      congrArg (fun A : Mat4 => A j j) S.property
  have hsq : S.val i j * S.val i j ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg (S.val k j)) (Finset.mem_univ i)
  constructor <;> nlinarith [sq_nonneg (S.val i j + 1), sq_nonneg (S.val i j - 1)]

theorem isCompact_orthogonalFour : IsCompact {S : Mat4 | Sᵀ * S = 1} := by
  have hclosed : IsClosed {S : Mat4 | Sᵀ * S = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_Icc : IsCompact (Icc (fun _ _ : Fin 4 => (-1 : ℝ))
    (fun _ _ : Fin 4 => (1 : ℝ)))).of_isClosed_subset hclosed
  intro S hS
  constructor <;> intro i j
  · exact (orthogonalFour_entry_bound ⟨S, hS⟩ i j).1
  · exact (orthogonalFour_entry_bound ⟨S, hS⟩ i j).2

instance instCompactSpaceOrthogonalFour : CompactSpace OrthogonalFour :=
  isCompact_iff_compactSpace.mp isCompact_orthogonalFour

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

theorem parallelGram_rate_zero (G U E : Mat4) :
    (-(U * E))ᵀ * G * E + Eᵀ * (Uᵀ * G + G * U) * E +
      Eᵀ * G * (-(U * E)) = 0 := by
  simp only [Matrix.transpose_neg, Matrix.transpose_mul]
  noncomm_ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The primitive horizontal ODE is invariant under actual coordinate
changes. This uses the proved Christoffel transformation, before any tensor
specialization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem weightedConnection_frame (J E : Mat4) (C : Fin 4 → Mat4) (k : Fin 4) :
    (∑ r, E r k • weightedConnection J C r) =
      ∑ a, (J * E) a k • C a := by
  simp only [weightedConnection, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A positive scalar change of metric transports the actual clopen
orientation of the orthonormal frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frame_scaling_identity (E G : Mat4) (a : ℝ) :
    (a • E)ᵀ * G * (a • E) = Eᵀ * ((a ^ 2) • G) * E := by
  simp only [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


