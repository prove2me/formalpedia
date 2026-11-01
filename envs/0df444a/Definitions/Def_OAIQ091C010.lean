-- Prove2me | Definitions.Def_OAIQ091C010
-- name    : OAIQ091C010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:58:17.191473+00:00
-- url     : https://prove2.me/theorems/3394e66f-90ba-4d68-aa1e-b4b7c90ed079
-- title:
--   Definitions bundle OAIQ091C010 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 267 declarations of OpenAI's Lean: 60 definitions, 1 inductive type or structure, 1 instance and 205 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.coordinateEnergyBoundaryRate`, `OAI.PositiveEinsteinFour.Geometry.coordinateEnergySecondDensity`, `OAI.PositiveEinsteinFour.Geometry.coordinateIndexDensity`, `OAI.PositiveEinsteinFour.Geometry.frameEnergyTransferInstance1`, `OAI.PositiveEinsteinFour.Geometry.geometricVolumeNormedAddCommGroup`, `OAI.PositiveEinsteinFour.Geometry.gradientTensor`, `OAI.PositiveEinsteinFour.Geometry.gradientVector`, `OAI.PositiveEinsteinFour.Geometry.gradientVectorMap`, `OAI.PositiveEinsteinFour.Geometry.heatSignedTraceLinear`, `OAI.PositiveEinsteinFour.Geometry.jacobiCovariantSecondJet`, `OAI.PositiveEinsteinFour.Geometry.jacobiMetricPair`, `OAI.PositiveEinsteinFour.Geometry.matrixEntryMap`, `OAI.PositiveEinsteinFour.Geometry.matrixVector`, `OAI.PositiveEinsteinFour.Geometry.matrixVectorMap`, `OAI.PositiveEinsteinFour.Geometry.metricTraceNormedRing`, `OAI.PositiveEinsteinFour.Geometry.metricTraceNormedSpace`, `OAI.PositiveEinsteinFour.Geometry.projectorNormedRing`, `OAI.PositiveEinsteinFour.Geometry.projectorNormedSpace`, `OAI.PositiveEinsteinFour.Geometry.reflectedGradient`, `OAI.PositiveEinsteinFour.Geometry.thirdBianchiNormedRing`, `OAI.PositiveEinsteinFour.Geometry.thirdBianchiNormedSpace`, `OAI.PositiveEinsteinFour.Geometry.traceEnergy`, `OAI.PositiveEinsteinFour.Geometry.weylRadialSquare`, `OAI.PositiveEinsteinFour.Jacobi.RegularJacobi.growth`, `OAI.PositiveEinsteinFour.Jacobi.RegularJacobi.localError`, `OAI.PositiveEinsteinFour.Jacobi.RegularJacobi.positionError`, `OAI.PositiveEinsteinFour.Jacobi.RegularJacobi.velocityError`, `OAI.PositiveEinsteinFour.Jacobi.blockAt`, `OAI.PositiveEinsteinFour.Jacobi.conjugateIndexAction`, `OAI.PositiveEinsteinFour.Jacobi.conjugateLeftField`, `OAI.PositiveEinsteinFour.Jacobi.conjugateLeftRate`, `OAI.PositiveEinsteinFour.Jacobi.conjugateRightField`, `OAI.PositiveEinsteinFour.Jacobi.conjugateRightRate`, `OAI.PositiveEinsteinFour.Jacobi.curvatureDirichlet`, `OAI.PositiveEinsteinFour.Jacobi.dirichletMatrix`, `OAI.PositiveEinsteinFour.Jacobi.jacobiPivot`, `OAI.PositiveEinsteinFour.Jacobi.lowerBidiagonal`, `OAI.PositiveEinsteinFour.Jacobi.meshCurvature`, `OAI.PositiveEinsteinFour.Jacobi.mulVecRightLinear`, `OAI.PositiveEinsteinFour.Jacobi.normalIndexDensity` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_CurvatureTensors02`, `EinsteinFour_DirichletFactorization`, `EinsteinFour_DirichletMatrix`, `EinsteinFour_FourHeatAwayBound`, `EinsteinFour_FourHeatGaussianApproximation`, `EinsteinFour_GeodesicGeometry04`, `EinsteinFour_GeodesicGeometry12`, `EinsteinFour_GeodesicJacobiSecondVariationAlgebra`, `EinsteinFour_HeatKernels10`, `EinsteinFour_HighestVectorSpace`, `EinsteinFour_HodgeTheory08`, `EinsteinFour_JacobiCompression`, `EinsteinFour_JacobiDirichletPositivity`, `EinsteinFour_JacobiMeshError`, `EinsteinFour_JacobiODEPositivity`, `EinsteinFour_JacobiPivots`, `EinsteinFour_JacobiPreconjugate`, `EinsteinFour_JacobiScheme`, `EinsteinFour_JacobiSchemeError`, `EinsteinFour_JacobiSchemeMatrix`, `EinsteinFour_JacobiSchemeRatios`, `EinsteinFour_JacobiWronskian`, `EinsteinFour_MetricBianchi`, `EinsteinFour_MetricCurvatureGreen`, `EinsteinFour_MetricHessian`, `EinsteinFour_ModeCompression`, `EinsteinFour_QuaternionLifts`, `EinsteinFour_QuaternionReflections`, `EinsteinFour_ReferenceCompression`, `EinsteinFour_ScalarRegularity07`, `EinsteinFour_TensorPairing`, `EinsteinFour_TraceAdjoint`, `EinsteinFour_TraceCurvature`, `EinsteinFour_TraceDecomposition`, `EinsteinFour_TraceHessian`, `EinsteinFour_WeightedAreaInequality`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylMatrixEquation`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C000`, `OAIQ091C001` and `OAIQ091C002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C014`, `OAIQ091C015` and `OAIQ091C016`; the statements `OAI_PositiveEinsteinFour_QuarticClosed_quartic_energy_bound_closed` and `OAI_PositiveEinsteinFour_Quartic_zero_defect_quartic_bound`; the proof of `OAI_PositiveEinsteinFour_Quartic_zero_defect_quartic_bound`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C000
import Definitions.Def_OAIQ091C001
import Definitions.Def_OAIQ091C002

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
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

theorem coordinates_eq (M : Mat) (hs : symmetric M) (ht : traceFree M) :
    ofCoordinates (M 0 0) (M 1 1) (M 0 1) (M 0 2) (M 1 2) = M := by
  have hd : M 2 2 = -M 0 0 - M 1 1 := by
    have h := ht
    simp [traceFree, Fin.sum_univ_succ] at h
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates, hd]
  all_goals exact hs _ _

def matrixNormSq (M : Mat) : ℝ := ∑ a, ∑ b, M a b ^ 2

/-- The explicit trace lift `3/5 δij S + 1/10 Σ I_s,ij Σ_s S`. -/
def traceLift (M : Mat) : Hessian := fun i j a b =>
  (if i = j then (3 / 5 : ℝ) * M a b else 0) +
    (1 / 10 : ℝ) * ∑ s, quaternionMatrix s i j * matrixAction s M a b

def hessianTrace (X : Hessian) : Mat := ∑ i, X i i

/-- Entry-first order is a permutation of the usual Frobenius sum. -/
def hessianNormSq (X : Hessian) : ℝ := ∑ a, ∑ b, ∑ i, ∑ j, X i j a b ^ 2

theorem quaternionMatrix_diagonal (s : Fin 3) (i : Fin 4) :
    quaternionMatrix s i i = 0 := by
  fin_cases s <;> fin_cases i <;> rfl

/-- Trace followed by its lift gives exactly `12/5 Id`. -/
theorem trace_traceLift (M : Mat) : hessianTrace (traceLift M) = (12 / 5 : ℝ) • M := by
  ext a b
  simp [hessianTrace, traceLift, quaternionMatrix_diagonal, Fin.sum_univ_succ]
  ring

/-- The actual Bianchi divergence of an inner-gradient slice of the lift. -/
def liftDivergence (M : Mat) (i : Fin 4) (r : Fin 3) : Vec :=
  ∑ s, quaternion s (WithLp.toLp 2 (fun j => traceLift M i j s r))

theorem traceLift_bianchi_0_0 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 0 0 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_0_1 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 0 1 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_0_2 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 0 2 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_1_0 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 1 0 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_1_1 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 1 1 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_1_2 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 1 2 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_2_0 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 2 0 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_2_1 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 2 1 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_2_2 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 2 2 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_3_0 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 3 0 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_3_1 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 3 1 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

theorem traceLift_bianchi_3_2 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 3 2 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

/-- Every lifted trace belongs to the constrained inner-gradient space. -/
theorem traceLift_bianchi (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (i : Fin 4) (r : Fin 3) : liftDivergence M i r = 0 := by
  rw [← coordinates_eq M hs ht]
  fin_cases i <;> fin_cases r
  · exact traceLift_bianchi_0_0 _ _ _ _ _
  · exact traceLift_bianchi_0_1 _ _ _ _ _
  · exact traceLift_bianchi_0_2 _ _ _ _ _
  · exact traceLift_bianchi_1_0 _ _ _ _ _
  · exact traceLift_bianchi_1_1 _ _ _ _ _
  · exact traceLift_bianchi_1_2 _ _ _ _ _
  · exact traceLift_bianchi_2_0 _ _ _ _ _
  · exact traceLift_bianchi_2_1 _ _ _ _ _
  · exact traceLift_bianchi_2_2 _ _ _ _ _
  · exact traceLift_bianchi_3_0 _ _ _ _ _
  · exact traceLift_bianchi_3_1 _ _ _ _ _
  · exact traceLift_bianchi_3_2 _ _ _ _ _

/-- The prescribed trace component of an actual Hessian. -/
def traceComponent (M : Mat) : Hessian := fun i j => (5 / 12 : ℝ) • traceLift M i j

theorem trace_traceComponent (M : Mat) : hessianTrace (traceComponent M) = M := by
  unfold hessianTrace traceComponent
  rw [← Finset.smul_sum]
  change (5 / 12 : ℝ) • hessianTrace (traceLift M) = M
  rw [trace_traceLift]
  module

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletMatrix
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite block matrices for the Jacobi determinant approximation. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix OrderDual

noncomputable section

/-- The normal-space matrix at one pair of mesh nodes. -/
def blockAt {N : ℕ} (M : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ)
    (i j : Fin N) : NormalMatrix := fun a b => M (a, i) (b, j)

theorem blockAt_mul {N : ℕ}
    (A B : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) (i j : Fin N) :
    blockAt (A * B) i j = ∑ k, blockAt A i k * blockAt B k j := by
  ext a b
  simp only [blockAt, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  rw [Finset.sum_comm]

theorem blockAt_transpose {N : ℕ}
    (A : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) (i j : Fin N) :
    blockAt A.transpose i j = (blockAt A j i).transpose := rfl

theorem blockAt_diagonal {N : ℕ} (S : Fin N → NormalMatrix) (i j : Fin N) :
    blockAt (Matrix.blockDiagonal S) i j = if i = j then S i else 0 := by
  ext a b
  by_cases h : i = j
  · subst j
    simp [blockAt]
  · simp [blockAt, Matrix.blockDiagonal_apply, h]

theorem blockAt_mul_diagonal {N : ℕ}
    (A : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) (S : Fin N → NormalMatrix)
    (i j : Fin N) :
    blockAt (A * Matrix.blockDiagonal S) i j = blockAt A i j * S j := by
  rw [blockAt_mul]
  simp_rw [blockAt_diagonal, mul_ite, mul_zero]
  simp

theorem blockDiagonal_quadratic {N : ℕ} (S : Fin N → NormalMatrix)
    (x : Fin 3 × Fin N → ℝ) :
    star x ⬝ᵥ (Matrix.blockDiagonal S *ᵥ x) =
      ∑ i, star (fun a => x (a, i)) ⬝ᵥ (S i *ᵥ fun a => x (a, i)) := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [Finset.sum_comm]

/-- Positive pivots give a positive block-diagonal form. -/
theorem blockDiagonal_posDef {N : ℕ} {S : Fin N → NormalMatrix}
    (hS : ∀ i, (S i).PosDef) : (Matrix.blockDiagonal S).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (Matrix.blockDiagonal S).conjTranspose = Matrix.blockDiagonal S
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext i
    exact (hS i).isHermitian.eq
  · intro x hx
    rw [blockDiagonal_quadratic]
    have hn : ∃ i, (fun a => x (a, i)) ≠ 0 := by
      by_contra! hn
      apply hx
      funext p
      exact congrFun (hn p.2) p.1
    obtain ⟨i, hi⟩ := hn
    apply Finset.sum_pos'
    · intro j _
      exact (hS j).posSemidef.dotProduct_mulVec_nonneg _
    · exact ⟨i, Finset.mem_univ _, (hS i).dotProduct_mulVec_pos hi⟩

/-- A unit lower bidiagonal matrix, with arbitrary noncommuting blocks. -/
def lowerBidiagonal {N : ℕ} (A : Fin N → NormalMatrix) :
    Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ := fun i j =>
  if i.2 = j.2 then (1 : NormalMatrix) i.1 j.1
  else if j.2.val + 1 = i.2.val then A j.2 i.1 j.1 else 0

theorem lowerBidiagonal_triangular {N : ℕ} (A : Fin N → NormalMatrix) :
    (lowerBidiagonal A).BlockTriangular (fun i => toDual i.2) := by
  intro i j hij
  have hlt : i.2 < j.2 := hij
  have hne : i.2 ≠ j.2 := ne_of_lt hlt
  have hstep : ¬(j.2.val + 1 = i.2.val) := by omega
  simp [lowerBidiagonal, hne, hstep]

theorem lowerBidiagonal_block_det {N : ℕ} (A : Fin N → NormalMatrix)
    (i : (Fin N)ᵒᵈ) :
    ((lowerBidiagonal A).toSquareBlock (fun j => toDual j.2) i).det = 1 := by
  let e := nodeBlockEquiv i
  rw [← Matrix.det_reindex_self e]
  have heq : ((lowerBidiagonal A).toSquareBlock (fun j => toDual j.2) i).reindex
      e e = (1 : NormalMatrix) := by
    ext k l
    simp [Matrix.reindex_apply, Matrix.toSquareBlock, Matrix.toSquareBlockProp,
      lowerBidiagonal, e, nodeBlockEquiv]
  rw [heq, Matrix.det_one]

/-- Elimination by these factors never changes a block determinant. -/
theorem det_lowerBidiagonal {N : ℕ} (A : Fin N → NormalMatrix) :
    (lowerBidiagonal A).det = 1 := by
  rw [(lowerBidiagonal_triangular A).det_fintype]
  simp only [lowerBidiagonal_block_det, Finset.prod_const_one]

/-- Positive pivots give a positive discrete Jacobi form after the
unit triangular change of variables. -/
theorem bidiagonal_factorization_posDef {N : ℕ} (A S : Fin N → NormalMatrix)
    (hS : ∀ i, (S i).PosDef) :
    (lowerBidiagonal A * Matrix.blockDiagonal S * (lowerBidiagonal A).transpose).PosDef := by
  have hunit : IsUnit ((lowerBidiagonal A).transpose) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose, det_lowerBidiagonal]
    exact isUnit_one
  have h := (blockDiagonal_posDef hS).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hunit)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using h

/-- The Jacobi recurrence is exactly the Schur-complement recurrence.
The order of the factors follows from right division by the Jacobi matrix. -/
theorem jacobi_pivot_recurrence {Yprev Y Ynext D : NormalMatrix}
    (hprev : IsUnit Yprev.det) (hY : IsUnit Y.det)
    (hrec : Ynext = D * Y - Yprev) :
    Ynext * Y⁻¹ = D - (Y * Yprev⁻¹)⁻¹ := by
  let : Invertible Yprev := ((Matrix.isUnit_iff_isUnit_det _).mpr hprev).invertible
  rw [hrec, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hY,
    Matrix.mul_one, Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceAdjoint
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit trace lift is the actual adjoint on the Bianchi subspace. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

/-- Frobenius pairing on all four tensor slots. -/
def hessianPairing (X Y : Hessian) : ℝ :=
  ∑ a, ∑ b, ∑ i, ∑ j, X i j a b * Y i j a b

theorem hessianPairing_self (X : Hessian) :
    hessianPairing X X = hessianNormSq X := by
  simp only [hessianPairing, hessianNormSq, pow_two]

end
end PositiveEinsteinFour.TraceHessian

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

theorem quaternionMatrix_skew (s : Fin 3) (i j : Fin 4) :
    quaternionMatrix s i j = -quaternionMatrix s j i := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;> norm_num [quaternionMatrix]

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricBianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.QuaternionFrame.rawField_fieldRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Weyl gradient, with its derivative index treated as a tangent
vector. These changes of coordinate retain every component: neither the
Bianchi equation nor a differential estimate is built into the definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular Bianchi TraceHessian
open scoped Manifold ContDiff

noncomputable section

/-- Reorder the derivative slot of a symmetric matrix gradient. -/
def gradientTensor (Z : Gradient) : Tensor where
  diagonal a := WithLp.toLp 2 (fun i => Z i a a)
  off a := WithLp.toLp 2 (fun i => Z i (next a) (previous a))

theorem gradientTensor_matrix (Z : Gradient) (hs : ∀ i, symmetric (Z i))
    (a b : Fin 3) :
    (gradientTensor Z).matrix a b = WithLp.toLp 2 (fun i => Z i a b) := by
  ext i
  fin_cases a <;> fin_cases b <;> simp [gradientTensor, Tensor.matrix, next, previous]
  all_goals exact hs i _ _

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted rough-Laplacian identity for the metric's actual Weyl
gradient. Differentiation takes place in the coordinate connection before
the parallel frame is applied. The integration identity follows from
frame-flow invariance, rather than an assumed Hessian integral formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular TraceHessian
open scoped Manifold ContDiff

noncomputable section

def gradientVector (Z : Gradient) : GradientVector :=
  WithLp.toLp 2 (fun p => Z p.1 p.2.1 p.2.2)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionReflections
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pure quaternion lifts of the reflections needed to choose a local
spectral frame. Only their concrete action on the two quaternion triples
is used; no global eigenframe or representation theorem is assumed. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def axisReflection (u : Fin 3 → ℝ) : Mat :=
  fun r s => 2 * u r * u s - if r = s then 1 else 0

theorem combination_square_expansion (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) :
    imaginaryCombination Q u * imaginaryCombination Q u =
      ∑ r, ∑ s, (u r * u s) • (Q r * Q s) := by
  simp only [imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

theorem combination_square_symmetrized (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) :
    (2 : ℝ) • (imaginaryCombination Q u * imaginaryCombination Q u) =
      ∑ r, ∑ s, (u r * u s) • (Q r * Q s + Q s * Q r) := by
  have hs : (∑ r, ∑ s, (u r * u s) • (Q s * Q r)) =
      ∑ r, ∑ s, (u r * u s) • (Q r * Q s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_comm (u s) (u r)]
  rw [combination_square_expansion]
  simp only [smul_add, Finset.sum_add_distrib, hs]
  module

/-- The square of a pure quaternion is minus its real squared norm. -/
theorem imaginaryCombination_square
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4)) (u : Fin 3 → ℝ) :
    imaginaryCombination Q u * imaginaryCombination Q u =
      (-(∑ r, u r ^ 2)) • (1 : Mat4) := by
  have h := combination_square_symmetrized Q u
  simp_rw [hQ] at h
  simp only [smul_smul] at h
  simp only [mul_ite, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true] at h
  have hs : (∑ r, (u r * u r * (-2)) • (1 : Mat4)) =
      (-2 * ∑ r, u r ^ 2) • (1 : Mat4) := by
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hs] at h
  have hh := congrArg (fun M : Mat4 => (1 / 2 : ℝ) • M) h
  have hscalar : (1 / 2 : ℝ) * (-2 * ∑ r, u r ^ 2) = -(∑ r, u r ^ 2) := by ring
  simpa only [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
    one_smul, hscalar] using hh

theorem imaginaryCombination_transpose
    (Q : Fin 3 → Mat4) (hQ : ∀ r, (Q r)ᵀ = -Q r) (u : Fin 3 → ℝ) :
    (imaginaryCombination Q u)ᵀ = -imaginaryCombination Q u := by
  ext i j
  simp only [imaginaryCombination, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : Mat4 => M i j) (hQ r)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [h]
  ring

theorem imaginaryCombination_anticommutator
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (u : Fin 3 → ℝ) (s : Fin 3) :
    imaginaryCombination Q u * Q s + Q s * imaginaryCombination Q u =
      (-2 * u s) • (1 : Mat4) := by
  simp only [imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← smul_add, hQ]
  simp only [smul_smul]
  simp only [mul_ite, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  congr 1
  ring

/-- The lifted spectral change sends each imaginary basis element to
its line reflection. -/
theorem axisReflection_combination (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) (s : Fin 3) :
    (∑ r, axisReflection u r s • Q r) =
      (2 * u s) • imaginaryCombination Q u - Q s := by
  simp only [axisReflection, sub_smul, Finset.sum_sub_distrib,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  congr 1
  simp only [imaginaryCombination, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  ring

/-- A unit pure quaternion is an orthogonal four-frame transformation. -/
theorem imaginaryCombination_orthogonal
    (Q : Fin 3 → Mat4)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (hskew : ∀ r, (Q r)ᵀ = -Q r)
    (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) :
    (imaginaryCombination Q u)ᵀ * imaginaryCombination Q u = 1 := by
  rw [imaginaryCombination_transpose Q hskew, Matrix.neg_mul,
    imaginaryCombination_square Q hanti, hu]
  norm_num

/-- The explicit intertwining law for the imaginary basis, with the
line reflection represented by a unit pure quaternion. -/
theorem imaginaryCombination_intertwines
    (Q : Fin 3 → Mat4)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) (s : Fin 3) :
    imaginaryCombination Q u * Q s =
      (∑ r, axisReflection u r s • Q r) * imaginaryCombination Q u := by
  have h := imaginaryCombination_anticommutator Q hanti u s
  rw [axisReflection_combination, Matrix.sub_mul, Matrix.smul_mul,
    imaginaryCombination_square Q hanti, hu]
  simp only [smul_smul, mul_neg, mul_one]
  simpa only [neg_mul] using eq_sub_of_add_eq h

/-- The unit pure-quaternion lifts preserve four-dimensional orientation. -/
theorem imaginaryLeft_matrix (u : Fin 3 → ℝ) :
    imaginaryCombination quaternionMatrix u =
      ![![0, -u 0, -u 1, -u 2], ![u 0, 0, -u 2, u 1],
        ![u 1, u 2, 0, -u 0], ![u 2, -u 1, u 0, 0]] := by
  ext i j
  change (∑ r, u r * quaternionMatrix r i j) = _
  fin_cases i <;> fin_cases j <;>
    simp [imaginaryCombination, quaternionMatrix, Fin.sum_univ_three] <;> norm_num

theorem imaginaryLeft_det (u : Fin 3 → ℝ) :
    Matrix.det (imaginaryCombination quaternionMatrix u) = (∑ r, u r ^ 2) ^ 2 := by
  let L : Mat4 := ![![0, -u 0, -u 1, -u 2], ![u 0, 0, -u 2, u 1],
    ![u 1, u 2, 0, -u 0], ![u 2, -u 1, u 0, 0]]
  have hL : imaginaryCombination quaternionMatrix u = L := imaginaryLeft_matrix u
  rw [hL, Matrix.det_succ_row_zero L]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [L, Fin.sum_univ_three, Fin.succAbove, Fin.lt_def]
  ring

theorem imaginaryLeft_det_one (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) :
    Matrix.det (imaginaryCombination quaternionMatrix u) = 1 := by
  rw [imaginaryLeft_det, hu, one_pow]

/-- The coefficient matrix is precisely the ordinary line reflection
that occurs as minus a Cartan–Dieudonné plane reflection. -/
theorem axisReflection_apply (u x : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ = 1) :
    WithLp.toLp 2 (axisReflection u *ᵥ (x : Fin 3 → ℝ)) =
      (Submodule.reflection (ℝ ∙ u)) x := by
  rw [Submodule.reflection_singleton_apply, hu]
  ext i
  simp only [axisReflection, Matrix.mulVec, dotProduct, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  norm_num [Fin.sum_univ_three]
  ring

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionLifts
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composition of the concrete quaternion frame changes.  These identities
keep the action on both Weyl blocks, so they can be used at a single point
without selecting a moving eigenframe. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- A concrete oriented four-frame lift of a change in one quaternion basis.
The opposite quaternion basis is fixed. -/
structure QuaternionLift (Q O : Fin 3 → Mat4) (A : Mat) where
  matrix : Mat4
  orthogonal : matrixᵀ * matrix = 1
  orientation : Matrix.det matrix = 1
  intertwines : ∀ s, matrix * Q s = (∑ r, A r s • Q r) * matrix
  opposite : ∀ s, matrix * O s = O s * matrix

/-- The generator intertwining identity extends to every imaginary quaternion. -/
theorem intertwines_combination (Q : Fin 3 → Mat4) (A : Mat) (P : Mat4)
    (hP : ∀ s, P * Q s = (∑ r, A r s • Q r) * P) (u : Fin 3 → ℝ) :
    P * imaginaryCombination Q u = imaginaryCombination Q (A *ᵥ u) * P := by
  simp only [imaginaryCombination, Matrix.mul_sum, Matrix.mul_smul, hP,
    Matrix.sum_mul, Matrix.smul_mul, Finset.smul_sum, smul_smul,
    Finset.sum_smul, Matrix.mulVec, dotProduct]
  change (∑ s, ∑ r, (u s * A r s) • (Q r * P)) =
    ∑ r, ∑ s, (A r s * u s) • (Q r * P)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  ring

/-- Products of four-frame lifts induce the corresponding product of
three-dimensional coefficient changes. -/
def QuaternionLift.mul {Q O : Fin 3 → Mat4} {A B : Mat}
    (P : QuaternionLift Q O A) (R : QuaternionLift Q O B) : QuaternionLift Q O (A * B) where
  matrix := P.matrix * R.matrix
  orthogonal := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P.matrixᵀ,
      P.orthogonal, Matrix.one_mul, R.orthogonal]
  orientation := by rw [Matrix.det_mul, P.orientation, R.orientation, one_mul]
  intertwines := by
    intro s
    calc
      (P.matrix * R.matrix) * Q s = P.matrix * (R.matrix * Q s) := Matrix.mul_assoc _ _ _
      _ = P.matrix * ((∑ r, B r s • Q r) * R.matrix) := by rw [R.intertwines]
      _ = (P.matrix * imaginaryCombination Q (fun r => B r s)) * R.matrix := by
        rw [← Matrix.mul_assoc]
        rfl
      _ = (imaginaryCombination Q (A *ᵥ (fun r => B r s)) * P.matrix) * R.matrix := by
        rw [intertwines_combination Q A P.matrix P.intertwines]
      _ = (∑ r, (A * B) r s • Q r) * (P.matrix * R.matrix) := by
        rw [Matrix.mul_assoc]
        rfl
  opposite := by
    intro s
    rw [Matrix.mul_assoc, R.opposite, ← Matrix.mul_assoc, P.opposite,
      Matrix.mul_assoc]

/-- The identity frame lifts the identity change in a quaternion basis. -/
def QuaternionLift.one (Q O : Fin 3 → Mat4) : QuaternionLift Q O 1 where
  matrix := 1
  orthogonal := by simp
  orientation := Matrix.det_one
  intertwines := by
    intro s
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.one_apply, ite_smul,
      one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  opposite := by intro s; rw [Matrix.one_mul, Matrix.mul_one]

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestVectorSpace
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the concrete highest-Hessian coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem entries_add_0 (c d : Fin 21 → ℝ) :
    entries (c + d) 0 = entries c 0 + entries d 0 := by
  ext i j
  change entries (c + d) 0 i j = entries c 0 i j + entries d 0 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add_1 (c d : Fin 21 → ℝ) :
    entries (c + d) 1 = entries c 1 + entries d 1 := by
  ext i j
  change entries (c + d) 1 i j = entries c 1 i j + entries d 1 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add_2 (c d : Fin 21 → ℝ) :
    entries (c + d) 2 = entries c 2 + entries d 2 := by
  ext i j
  change entries (c + d) 2 i j = entries c 2 i j + entries d 2 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add_3 (c d : Fin 21 → ℝ) :
    entries (c + d) 3 = entries c 3 + entries d 3 := by
  ext i j
  change entries (c + d) 3 i j = entries c 3 i j + entries d 3 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add_4 (c d : Fin 21 → ℝ) :
    entries (c + d) 4 = entries c 4 + entries d 4 := by
  ext i j
  change entries (c + d) 4 i j = entries c 4 i j + entries d 4 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add_5 (c d : Fin 21 → ℝ) :
    entries (c + d) 5 = entries c 5 + entries d 5 := by
  ext i j
  change entries (c + d) 5 i j = entries c 5 i j + entries d 5 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add_6 (c d : Fin 21 → ℝ) :
    entries (c + d) 6 = entries c 6 + entries d 6 := by
  ext i j
  change entries (c + d) 6 i j = entries c 6 i j + entries d 6 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add_7 (c d : Fin 21 → ℝ) :
    entries (c + d) 7 = entries c 7 + entries d 7 := by
  ext i j
  change entries (c + d) 7 i j = entries c 7 i j + entries d 7 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add_8 (c d : Fin 21 → ℝ) :
    entries (c + d) 8 = entries c 8 + entries d 8 := by
  ext i j
  change entries (c + d) 8 i j = entries c 8 i j + entries d 8 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add_9 (c d : Fin 21 → ℝ) :
    entries (c + d) 9 = entries c 9 + entries d 9 := by
  ext i j
  change entries (c + d) 9 i j = entries c 9 i j + entries d 9 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_0 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 0 = r • entries c 0 := by
  ext i j
  change entries (r • c) 0 i j = r * entries c 0 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_1 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 1 = r • entries c 1 := by
  ext i j
  change entries (r • c) 1 i j = r * entries c 1 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_2 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 2 = r • entries c 2 := by
  ext i j
  change entries (r • c) 2 i j = r * entries c 2 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_3 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 3 = r • entries c 3 := by
  ext i j
  change entries (r • c) 3 i j = r * entries c 3 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_4 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 4 = r • entries c 4 := by
  ext i j
  change entries (r • c) 4 i j = r * entries c 4 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_5 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 5 = r • entries c 5 := by
  ext i j
  change entries (r • c) 5 i j = r * entries c 5 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_6 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 6 = r • entries c 6 := by
  ext i j
  change entries (r • c) 6 i j = r * entries c 6 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_7 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 7 = r • entries c 7 := by
  ext i j
  change entries (r • c) 7 i j = r * entries c 7 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_8 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 8 = r • entries c 8 := by
  ext i j
  change entries (r • c) 8 i j = r * entries c 8 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_smul_9 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 9 = r • entries c 9 := by
  ext i j
  change entries (r • c) 9 i j = r * entries c 9 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add (c d : Fin 21 → ℝ) : entries (c + d) = entries c + entries d := by
  funext k
  fin_cases k
  · exact entries_add_0 c d
  · exact entries_add_1 c d
  · exact entries_add_2 c d
  · exact entries_add_3 c d
  · exact entries_add_4 c d
  · exact entries_add_5 c d
  · exact entries_add_6 c d
  · exact entries_add_7 c d
  · exact entries_add_8 c d
  · exact entries_add_9 c d

theorem entries_smul (r : ℝ) (c : Fin 21 → ℝ) : entries (r • c) = r • entries c := by
  funext k
  fin_cases k
  · exact entries_smul_0 r c
  · exact entries_smul_1 r c
  · exact entries_smul_2 r c
  · exact entries_smul_3 r c
  · exact entries_smul_4 r c
  · exact entries_smul_5 r c
  · exact entries_smul_6 r c
  · exact entries_smul_7 r c
  · exact entries_smul_8 r c
  · exact entries_smul_9 r c


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceCurvature
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The curvature commutator retained by the complete trace component. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

/-- The trace component retains its complete skew derivative part. -/
theorem traceComponent_skew (M : Mat) (i j : Fin 4) (a b : Fin 3) :
    traceComponent M i j a b - traceComponent M j i a b =
      (1 / 12) * ∑ s, quaternionMatrix s i j * matrixAction s M a b := by
  have hd : (if i = j then (3 / 5 : ℝ) * M a b else 0) =
      (if j = i then (3 / 5 : ℝ) * M a b else 0) := by simp [eq_comm]
  have hs (s : Fin 3) : quaternionMatrix s j i = -quaternionMatrix s i j :=
    quaternionMatrix_skew s j i
  change (5 / 12 : ℝ) * traceLift M i j a b -
      (5 / 12 : ℝ) * traceLift M j i a b = _
  unfold traceLift
  rw [← hd]
  simp_rw [hs, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceDecomposition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local tensor identities imply the highest-Hessian constraints. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem matrixAction_symmetric (s : Fin 3) (M : Mat)
    (hs : symmetric M) (ht : traceFree M) : symmetric (matrixAction s M) := by
  rw [← coordinates_eq M hs ht]
  intro a b
  fin_cases s <;> fin_cases a <;> fin_cases b <;>
    simp [matrixAction, TraceHessian.rotation, ofCoordinates, Fin.sum_univ_succ]
  all_goals ring

theorem traceComponent_symmetric (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (i j : Fin 4) : symmetric (traceComponent M i j) := by
  intro a b
  have h (s : Fin 3) : matrixAction s M a b = matrixAction s M b a :=
    matrixAction_symmetric s M hs ht a b
  change (5 / 12 : ℝ) * traceLift M i j a b =
    (5 / 12 : ℝ) * traceLift M i j b a
  simp only [traceLift, h, hs a b]

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricCurvatureGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivative-slot integration for the actual metric Weyl Hessian. The
coefficient and its derivative are both the concrete quaternion curvature
block. The only differential premises are parallel differentiation and
the classical divergence and skew identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian Angular
open scoped Manifold ContDiff

noncomputable section

def matrixVector (A : Mat) : MatrixVector := WithLp.toLp 2 (fun p => A p.1 p.2)

end
end PositiveEinsteinFour.Geometry

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

def traceFreeSquare (M : Mat) : Mat :=
  M * M - (Matrix.trace (M * M) / 3) • (1 : Mat)

def weylLaplacian (M : Mat) : Mat := (6 : ℝ) • (M - traceFreeSquare M)

theorem traceFreeSquare_symmetric (M : Mat) (hs : symmetric M) :
    symmetric (traceFreeSquare M) := by
  have hm : Mᵀ = M := by ext a b; exact hs b a
  have hsq : (traceFreeSquare M)ᵀ = traceFreeSquare M := by
    simp only [traceFreeSquare, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_smul, Matrix.transpose_one, hm]
  intro a b
  exact congrArg (fun N : Mat => N b a) hsq

theorem traceFreeSquare_traceFree (M : Mat) : traceFree (traceFreeSquare M) := by
  change Matrix.trace (traceFreeSquare M) = 0
  simp only [traceFreeSquare, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat]
  ring

theorem weylLaplacian_symmetric (M : Mat) (hs : symmetric M) :
    symmetric (weylLaplacian M) := by
  intro a b
  change 6 * (M a b - traceFreeSquare M a b) =
    6 * (M b a - traceFreeSquare M b a)
  rw [hs a b, traceFreeSquare_symmetric M hs a b]

theorem weylLaplacian_traceFree (M : Mat) (ht : traceFree M) :
    traceFree (weylLaplacian M) := by
  change (∑ a, 6 * (M a a - traceFreeSquare M a a)) = 0
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ht, traceFreeSquare_traceFree]
  ring

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

/-! Differentiate the invariant matrix Weyl equation before choosing a
diagonal frame. The derivative of its quadratic term is exactly twice
the concrete matrix-slot operator. -/

namespace PositiveEinsteinFour.TraceHessian

open Matrix PositiveEinsteinFour.Geometry
open scoped BigOperators

noncomputable section

local instance instNormedRingMat : NormedRing Mat := Matrix.frobeniusNormedRing
local instance instNormedSpaceRealMat : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

local instance instNormedAlgebraRealMat_r60322b_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def matrixTraceMap : Mat →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap

theorem hasDerivAt_matrixTrace {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) :
    HasDerivAt (fun r => Matrix.trace (T r)) (Matrix.trace Z) t := by
  convert! (matrixTraceMap.hasFDerivAt.comp_hasDerivAt t hT) using 1
  all_goals try with_reducible_and_instances rfl

end
end PositiveEinsteinFour.TraceHessian
end


section

/-! The full prescribed-trace Green identity for the actual metric,
derived by differentiating its invariant polynomial coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricTraceNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricTraceNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

local instance metricTraceNormedAlgebra_r60322b_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def matrixVectorMap : Mat →L[ℝ] MatrixVector :=
  ({ toFun := matrixVector
     map_add' := fun A B => by ext p; rfl
     map_smul' := fun r A => by ext p; rfl } : Mat →ₗ[ℝ] MatrixVector).toContinuousLinearMap

theorem hasDerivAt_matrixVector {T : ℝ → Mat} {Z : Mat} {r : ℝ}
    (hT : HasDerivAt T Z r) :
    HasDerivAt (fun t => matrixVector (T t)) (matrixVector Z) r := by
  convert! matrixVectorMap.hasFDerivAt.comp_hasDerivAt r hT using 1
  all_goals try with_reducible_and_instances rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! A pointwise spectral basis in the positive Weyl block lifts to an
orientation-preserving orthogonal change in four dimensions. The harmless
common sign in the three-dimensional basis cancels from matrix conjugation. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem frameMatrix_mul (φ ψ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) :
    frameMatrix (φ * ψ) = frameMatrix φ * frameMatrix ψ := by
  exact LinearMap.toMatrix_mul _ φ.toLinearMap ψ.toLinearMap

theorem frameMatrix_apply (φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (i j : Fin 3) :
    frameMatrix φ i j = φ ((EuclideanSpace.basisFun (Fin 3) ℝ) j) i := by
  simp only [frameMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rfl

theorem frameMatrix_axisReflection (u : ThreeSpace) (hu : ‖u‖ = 1) :
    frameMatrix (Submodule.reflection (ℝ ∙ u)) = axisReflection u := by
  ext i j
  rw [frameMatrix_apply]
  have h := congrArg (fun x : ThreeSpace => x i)
    (axisReflection_apply u ((EuclideanSpace.basisFun (Fin 3) ℝ) j) hu)
  simpa [Matrix.mulVec, dotProduct] using h.symm

theorem frameMatrix_orthogonalReflection (u : ThreeSpace) (hu : ‖u‖ = 1) :
    frameMatrix (Submodule.reflection (ℝ ∙ u)ᗮ) = -axisReflection u := by
  ext i j
  rw [frameMatrix_apply, Submodule.reflection_orthogonal_apply]
  change -Submodule.reflection (ℝ ∙ u) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) i = _
  rw [← frameMatrix_apply, frameMatrix_axisReflection u hu]
  rfl

theorem normalized_span (v : ThreeSpace) (hv : v ≠ 0) :
    (ℝ ∙ ((‖v‖⁻¹ : ℝ) • v)) = ℝ ∙ v := by
  exact Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hv))) v

theorem signed_matrix_mul (c d : ℝ) (A B : Mat) :
    (c • A) * (d • B) = (c * d) • (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Differentiate the actual Hessian constraints to show that its rough
Laplacian remains a symmetric trace-free Bianchi gradient. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance thirdBianchiNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance thirdBianchiNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

local instance thirdBianchiNormedAlgebra_r60322b_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def matrixEntryMap (a b : Fin 3) : Mat →L[ℝ] ℝ :=
  ({ toFun := fun A => A a b
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Mat →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem hasDerivAt_matrixEntry {A : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hA : HasDerivAt A Z t) (a b : Fin 3) :
    HasDerivAt (fun r => A r a b) (Z a b) t := by
  convert! (matrixEntryMap a b).hasFDerivAt.comp_hasDerivAt t hA using 1
  all_goals try with_reducible_and_instances rfl

theorem symmetric_of_hasDerivAt {A : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hA : HasDerivAt A Z t) (hs : ∀ r, symmetric (A r)) : symmetric Z := by
  intro a b
  have h1 := hasDerivAt_matrixEntry hA a b
  have h2 := hasDerivAt_matrixEntry hA b a
  have heq : (fun r => A r a b) = fun r => A r b a := funext (fun r => hs r a b)
  rw [heq] at h1
  exact h1.unique h2

theorem traceFree_of_hasDerivAt {A : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hA : HasDerivAt A Z t) (ht : ∀ r, traceFree (A r)) : traceFree Z := by
  have h := hasDerivAt_matrixTrace hA
  have heq : (fun r => Matrix.trace (A r)) = fun _ => (0 : ℝ) := funext ht
  rw [heq] at h
  exact h.unique (hasDerivAt_const t 0)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full trace Green term as invariant polynomial contractions.
This expression has no division by a Weyl norm and is valid at its zeros. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance traceScalarNormedRing_r60322b_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance traceScalarNormedSpace_r60322b_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance traceScalarNormedAlgebra_r60322b_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def weylRadialSquare (A : Mat) (Z : Fin 4 → Mat) : ℝ :=
  (∑ i, Matrix.trace (A * Z i) ^ 2) / 36

end
end PositiveEinsteinFour.Geometry
end


section

/-! The raw classical parallel-frame calculus used by the weighted Green
argument. Every field refers to the actual metric tensors. No compressed
Ricci equation or integral estimate is a field of this structure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance greenDataNormedRing_r60322b_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance greenDataNormedSpace_r60322b_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance greenDataNormedAlgebra_r60322b_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- Reindexing the derivative and matrix components is continuous. -/
def gradientVectorMap : (Fin 4 → Mat) →L[ℝ] GradientVector :=
  ({ toFun := gradientVector
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : (Fin 4 → Mat) →ₗ[ℝ] GradientVector).toContinuousLinearMap

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity of the actual weighted-Hessian integrands. The orthogonal
projection is the already constructed projection, not a chosen eigenframe. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

section Continuous

variable {Ω : Type*} [TopologicalSpace Ω]

local instance hessianContinuityNormedRing_r60322b_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianContinuityNormedSpace_r60322b_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianContinuityNormedAlgebra_r60322b_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuous_weylRadialSquare {A : Ω → Mat} {Z : Ω → Fin 4 → Mat}
    (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => weylRadialSquare (A x) (Z x)) := by
  simp only [weylRadialSquare, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  fun_prop

end Continuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! All five Green integrals for the actual Weyl Hessian. The result has
only first derivatives and the constructed orthogonal-projection cost. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

section Continuous

variable {Ω : Type*} [TopologicalSpace Ω]

local instance hessianAssemblyNormedRing_r60322b_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianAssemblyNormedSpace_r60322b_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianAssemblyNormedAlgebra_r60322b_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuous_weylLaplacian : Continuous weylLaplacian := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [weylLaplacian, traceFreeSquare, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag, smul_eq_mul]
  fun_prop

theorem continuous_traceFreeSquare : Continuous traceFreeSquare := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [traceFreeSquare, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.smul_apply, Matrix.trace, Matrix.diag, smul_eq_mul]
  fun_prop

end Continuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Bianchi triple becomes the positive triple after
reflecting only the derivative index. This gives the same invariant Kato
bound for the actual opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def reflectedGradient (Z : Angular.Gradient) : Angular.Gradient :=
  fun i => orientationSign i • Z i

end
end PositiveEinsteinFour.Geometry
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

/-! Contract the actual Weyl equation with the Weyl tensor. The cubic
trace is its determinant, so the result uses the canonical shape even
where the Weyl block is zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators

noncomputable section

theorem traceCube_eq_three_det (A : Mat3) (hs : symmetric A) (ht : traceFree A) :
    Matrix.trace (A * (A * A)) = 3 * A.det := by
  rw [← coordinates_eq A hs ht]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.det_fin_three, Fin.sum_univ_three]
  norm_num [ofCoordinates]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive trace-free Hessian energy behind the integral addition
in equation (16). The entire prescribed trace component is subtracted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def traceEnergy (A : Mat) : ℝ := (5 / 36 : ℝ) * matrixNormSq (weylLaplacian A)

theorem continuous_traceEnergy : Continuous traceEnergy := by
  unfold traceEnergy matrixNormSq
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  exact (((matrixEntryMap a b).continuous.comp continuous_weylLaplacian).pow 2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orientation distinguishes the two explicit quaternionic two-form spaces. -/

namespace PositiveEinsteinFour.QuaternionFrame

open Matrix TraceHessian PositiveEinsteinFour.Geometry
open Angular (oppositeMatrix)
open scoped BigOperators

noncomputable section

theorem quaternion_orthogonal (s : Fin 3) :
    (quaternionMatrix s)ᵀ * quaternionMatrix s = 1 := by
  ext i j
  change (∑ k, quaternionMatrix s k i * quaternionMatrix s k j) = if i = j then 1 else 0
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [quaternionMatrix, Fin.sum_univ_four]

theorem opposite_orthogonal (s : Fin 3) :
    (oppositeMatrix s)ᵀ * oppositeMatrix s = 1 := by
  ext i j
  change (∑ k, oppositeMatrix s k i * oppositeMatrix s k j) = if i = j then 1 else 0
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [oppositeMatrix, oppositeQuaternion, quaternionMatrix, Fin.sum_univ_four]

theorem conjugate_skew (P A : Mat4) (hsk : Aᵀ = -A) :
    ∀ i j, (P * A * Pᵀ) i j = -(P * A * Pᵀ) j i := by
  have h : (P * A * Pᵀ)ᵀ = -(P * A * Pᵀ) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsk,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  intro i j
  have hi := congrArg (fun B : Mat4 => B j i) h
  simpa only [Matrix.transpose_apply, Matrix.neg_apply] using hi

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The infinitesimal orthonormal-frame action on two-forms preserves the
Hodge splitting and the fiber inner product. This is the local algebra
needed for the induced Levi-Civita connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormSkewAction_hodge (b a : TwoFormFour) :
    twoFormSkewAction b (twoFormHodge a) = twoFormHodge (twoFormSkewAction b a) := by
  ext i
  fin_cases i <;> simp [twoFormSkewAction, twoFormHodge, twoFormHodgeLinear] <;> ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletFactorization
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tridiagonal Jacobi matrix and its ordered Schur pivots. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- The Dirichlet matrix with diagonal blocks `D` and both off-diagonals `-1`. -/
def dirichletMatrix {N : ℕ} (D : Fin N → NormalMatrix) :
    Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ := fun i j =>
  if i.2 = j.2 then D i.2 i.1 j.1
  else if i.2.val + 1 = j.2.val ∨ j.2.val + 1 = i.2.val then
    -(1 : NormalMatrix) i.1 j.1 else 0

/-- The diagonal determined by the pivots. The predecessor sum has at most
one term; its use also covers the first node without a separate convention. -/
def pivotDiagonal {N : ℕ} (S : Fin N → NormalMatrix) (i : Fin N) : NormalMatrix :=
  S i + ∑ k, if k.val + 1 = i.val then (S k)⁻¹ else 0

theorem blockAt_lower {N : ℕ} (A : Fin N → NormalMatrix) (i k : Fin N) :
    blockAt (lowerBidiagonal A) i k =
      if i = k then 1 else if k.val + 1 = i.val then A k else 0 := by
  ext a b
  by_cases h : i = k
  · simp [blockAt, lowerBidiagonal, h]
  · by_cases hs : k.val + 1 = i.val <;> simp [blockAt, lowerBidiagonal, h, hs]

theorem blockAt_dirichlet {N : ℕ} (D : Fin N → NormalMatrix) (i j : Fin N) :
    blockAt (dirichletMatrix D) i j =
      if i = j then D i else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  ext a b
  by_cases h : i = j
  · simp [blockAt, dirichletMatrix, h]
  · by_cases hs : i.val + 1 = j.val ∨ j.val + 1 = i.val <;>
      simp [blockAt, dirichletMatrix, h, hs]

theorem pivot_left_block {N : ℕ} (S : Fin N → NormalMatrix)
    (hS : ∀ k, IsUnit (S k).det) (i k : Fin N) :
    blockAt (lowerBidiagonal (fun k => -(S k)⁻¹) * Matrix.blockDiagonal S) i k =
      if i = k then S k else if k.val + 1 = i.val then -1 else 0 := by
  rw [blockAt_mul_diagonal, blockAt_lower]
  by_cases h : i = k
  · simp [h]
  · by_cases hs : k.val + 1 = i.val
    · simp [h, hs, Matrix.nonsing_inv_mul _ (hS k)]
    · simp [h, hs]

theorem pivot_right_block {N : ℕ} (S : Fin N → NormalMatrix)
    (hS : ∀ k, (S k).transpose = S k) (j k : Fin N) :
    blockAt (lowerBidiagonal (fun k => -(S k)⁻¹)).transpose k j =
      if j = k then 1 else if k.val + 1 = j.val then -(S k)⁻¹ else 0 := by
  rw [blockAt_transpose, blockAt_lower]
  by_cases h : j = k
  · simp [h]
  · by_cases hs : k.val + 1 = j.val
    · simp [h, hs, Matrix.transpose_nonsing_inv, hS]
    · simp [h, hs]

theorem pivot_summand {N : ℕ} (S : Fin N → NormalMatrix)
    (hS : ∀ k, IsUnit (S k).det) (i j k : Fin N) :
    (if i = k then S k else if k.val + 1 = i.val then -1 else 0) *
      (if j = k then 1 else if k.val + 1 = j.val then -(S k)⁻¹ else 0) =
    (if i = k ∧ j = k then S k else 0) +
      (if i = k ∧ k.val + 1 = j.val then -1 else 0) +
      (if j = k ∧ k.val + 1 = i.val then -1 else 0) +
      (if k.val + 1 = i.val ∧ k.val + 1 = j.val then (S k)⁻¹ else 0) := by
  by_cases hik : i = k <;> by_cases hjk : j = k <;>
    by_cases hki : k.val + 1 = i.val <;> by_cases hkj : k.val + 1 = j.val
  all_goals simp_all [Matrix.mul_nonsing_inv _ (hS k)]

/-- The precise block formula before the predecessor sums are collapsed. -/
theorem pivot_factorization_blocks {N : ℕ} (S : Fin N → NormalMatrix)
    (hunit : ∀ k, IsUnit (S k).det) (hsym : ∀ k, (S k).transpose = S k)
    (i j : Fin N) :
    blockAt (lowerBidiagonal (fun k => -(S k)⁻¹) * Matrix.blockDiagonal S *
      (lowerBidiagonal (fun k => -(S k)⁻¹)).transpose) i j =
    (∑ k, if i = k ∧ j = k then S k else 0) +
      (∑ k, if i = k ∧ k.val + 1 = j.val then -1 else 0) +
      (∑ k, if j = k ∧ k.val + 1 = i.val then -1 else 0) +
      (∑ k, if k.val + 1 = i.val ∧ k.val + 1 = j.val then (S k)⁻¹ else 0) := by
  rw [blockAt_mul]
  simp_rw [pivot_left_block S hunit, pivot_right_block S hsym, pivot_summand S hunit,
    Finset.sum_add_distrib]

theorem pivot_sum_collapse {N : ℕ} (S : Fin N → NormalMatrix) (i j : Fin N) :
    (∑ k, if i = k ∧ j = k then S k else 0) +
      (∑ k, if i = k ∧ k.val + 1 = j.val then -1 else 0) +
      (∑ k, if j = k ∧ k.val + 1 = i.val then -1 else 0) +
      (∑ k, if k.val + 1 = i.val ∧ k.val + 1 = j.val then (S k)⁻¹ else 0) =
    if i = j then pivotDiagonal S i
      else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hbad (k : Fin N) : ¬(i = k ∧ k.val + 1 = i.val) := by omega
    simp [hbad, pivotDiagonal]
  · have hfirst (k : Fin N) : ¬(i = k ∧ j = k) := by
      rintro ⟨hi, hj⟩
      exact hij (hi.trans hj.symm)
    have hlast (k : Fin N) : ¬(k.val + 1 = i.val ∧ k.val + 1 = j.val) := by omega
    simp only [hfirst, hlast, ite_false, if_false, Finset.sum_const_zero, zero_add, add_zero]
    have hsecond : (∑ k : Fin N, if i = k ∧ k.val + 1 = j.val then (-1 : NormalMatrix) else 0) =
        if i.val + 1 = j.val then -1 else 0 := by simp [ite_and]
    have hthird : (∑ k : Fin N, if j = k ∧ k.val + 1 = i.val then (-1 : NormalMatrix) else 0) =
        if j.val + 1 = i.val then -1 else 0 := by simp [ite_and]
    rw [hsecond, hthird, ite_eq_right hij]
    by_cases hf : i.val + 1 = j.val
    · have hb : ¬j.val + 1 = i.val := by omega
      simp [hf, hb]
    · by_cases hb : j.val + 1 = i.val <;> simp [hf, hb]

/-- The full tridiagonal matrix is the `L D Lᵀ` factorization of its Schur
pivots, with neither time ordering nor matrix multiplication commuted. -/
theorem dirichlet_pivot_factorization {N : ℕ} (S : Fin N → NormalMatrix)
    (hunit : ∀ k, IsUnit (S k).det) (hsym : ∀ k, (S k).transpose = S k) :
    dirichletMatrix (pivotDiagonal S) =
      lowerBidiagonal (fun k => -(S k)⁻¹) * Matrix.blockDiagonal S *
        (lowerBidiagonal (fun k => -(S k)⁻¹)).transpose := by
  have hb (i j : Fin N) :
      blockAt (dirichletMatrix (pivotDiagonal S)) i j =
      blockAt (lowerBidiagonal (fun k => -(S k)⁻¹) * Matrix.blockDiagonal S *
        (lowerBidiagonal (fun k => -(S k)⁻¹)).transpose) i j := by
    rw [blockAt_dirichlet, pivot_factorization_blocks S hunit hsym, pivot_sum_collapse]
  ext ⟨a, i⟩ ⟨b, j⟩
  exact congrFun (congrFun (hb i j) a) b

theorem dirichlet_pivots_posDef {N : ℕ} (S : Fin N → NormalMatrix)
    (hS : ∀ i, (S i).PosDef) : (dirichletMatrix (pivotDiagonal S)).PosDef := by
  have hunit (i : Fin N) : IsUnit (S i).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hS i).isUnit
  have hsym (i : Fin N) : (S i).transpose = S i := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (hS i).isHermitian.eq
  rw [dirichlet_pivot_factorization S hunit hsym]
  exact bidiagonal_factorization_posDef _ _ hS

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatAwayBound
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.vector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian derivative scale is uniformly O(t) away from the center.
This is the bound used for the normal-chart cutoff commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour

noncomputable section

theorem fourHeatGaussian_weighted_inverse_time (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    ‖x‖ ^ 8 * (fourHeatGaussian t x / t) ≤ (384 / Real.pi ^ 2) * t := by
  let z := ‖x‖ ^ 2 / (4 * t)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hb : z ^ 4 * Real.exp (-z) ≤ 24 := by
    simpa only [show ((4 : ℕ).factorial : ℝ) = 24 by norm_num] using
      fourHeatPolynomial_absorption 4 z hz
  have he : ‖x‖ ^ 8 * (fourHeatGaussian t x / t) =
      ((16 / Real.pi ^ 2) * t) * (z ^ 4 * Real.exp (-z)) := by
    have harg : -(4 * t)⁻¹ * ‖x‖ ^ 2 = -z := by dsimp [z]; ring
    unfold fourHeatGaussian
    rw [harg]
    dsimp [z]
    field_simp
    ring
  rw [he]
  calc
    _ ≤ ((16 / Real.pi ^ 2) * t) * 24 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianApproximation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian dilation and its actual approximate-identity limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped _root_.Topology

noncomputable section

theorem fourHeatGaussian_rescaled_measurable (f : FourSpace → ℝ) (hf : Continuous f)
    (x : FourSpace) (t : ℝ) : AEStronglyMeasurable
    (fun z : FourSpace => fourHeatGaussian 1 z * f (x - Real.sqrt t • z)) volume := by
  have hs : Continuous (fun z : FourSpace => Real.sqrt t • z) :=
    (ContinuousLinearMap.lsmul ℝ ℝ (E := FourSpace) (Real.sqrt t)).continuous
  have hx : Continuous (fun z : FourSpace => x - Real.sqrt t • z) :=
    continuous_const.sub hs
  have hfx : Continuous (fun z : FourSpace => f (x - Real.sqrt t • z)) := hf.comp hx
  exact ((fourHeatGaussian_continuous 1).mul hfx).aestronglyMeasurable

theorem fourHeatGaussian_rescaled_pointwise (f : FourSpace → ℝ) (hf : Continuous f)
    (x z : FourSpace) :
    Tendsto (fun t : ℝ => fourHeatGaussian 1 z * f (x - Real.sqrt t • z))
      (𝓝 0) (𝓝 (fourHeatGaussian 1 z * f x)) := by
  have hs : Tendsto (fun t : ℝ => x - Real.sqrt t • z) (𝓝 0) (𝓝 x) := by
    simpa only [Real.sqrt_zero, zero_smul, sub_zero] using
      (tendsto_const_nhds.sub (Real.continuous_sqrt.continuousAt.tendsto.smul
        tendsto_const_nhds) : Tendsto (fun t : ℝ => x - Real.sqrt t • z)
          (𝓝 0) (𝓝 (x - Real.sqrt 0 • z)))
  exact tendsto_const_nhds.mul ((hf.tendsto x).comp hs)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiPivots
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Dirichlet determinant is the determinant of the discrete
Jacobi solution, on the nonsingular range used before conjugacy. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def jacobiPivot (D : ℕ → NormalMatrix) : ℕ → NormalMatrix
  | 0 => D 0
  | n + 1 => D (n + 1) - (jacobiPivot D n)⁻¹

theorem jacobiPivot_eq_ratio (D Y : ℕ → NormalMatrix)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (n : ℕ) (hunit : ∀ i, 1 ≤ i → i ≤ n + 1 → IsUnit (Y i).det) :
    jacobiPivot D n = Y (n + 2) * (Y (n + 1))⁻¹ := by
  induction n with
  | zero => simp [jacobiPivot, hrec 0, h0, h1]
  | succ n ih =>
      have hn := ih (fun i hi hin => hunit i hi (by omega))
      rw [jacobiPivot, hn]
      exact (jacobi_pivot_recurrence (hunit (n + 1) (by omega) (by omega))
        (hunit (n + 2) (by omega) (by omega)) (hrec (n + 1))).symm

theorem predecessor_sum_succ {N m : ℕ} (hm : m + 1 < N)
    (S : Fin N → NormalMatrix) :
    (∑ k, if k.val + 1 = m + 1 then (S k)⁻¹ else 0) =
      (S ⟨m, by omega⟩)⁻¹ := by
  let p : Fin N := ⟨m, by omega⟩
  rw [Finset.sum_eq_single p]
  · simp [p]
  · intro k _ hkp
    have hne : k.val ≠ m := by
      intro heq
      apply hkp
      apply Fin.ext
      dsimp [p]
      omega
    simp [hne]
  · simp

theorem pivotDiagonal_jacobiPivot (D : ℕ → NormalMatrix) {N : ℕ} (i : Fin N) :
    pivotDiagonal (fun k : Fin N => jacobiPivot D k.val) i = D i.val := by
  rcases i with ⟨m, hm⟩
  cases m with
  | zero => simp [pivotDiagonal, jacobiPivot]
  | succ m =>
      change jacobiPivot D (m + 1) +
        (∑ k : Fin N, if k.val + 1 = m + 1 then (jacobiPivot D k.val)⁻¹ else 0) = D (m + 1)
      rw [predecessor_sum_succ hm, jacobiPivot]
      exact sub_add_cancel _ _

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiScheme
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete noncommuting kick-drift scheme and its Jacobi recurrence. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R]

theorem discreteVelocity_succ (A : ℕ → R) (h : ℝ) (n : ℕ) :
    discreteVelocity A h (n + 1) = discreteVelocity A h n -
      h • (A n * discretePosition A h n) := rfl

theorem discretePosition_succ (A : ℕ → R) (h : ℝ) (n : ℕ) :
    discretePosition A h (n + 1) = discretePosition A h n +
      h • discreteVelocity A h (n + 1) := rfl

/-- Matrix multiplication stays in its original order in the second-order
recurrence. The curvature is sampled at the interior node. -/
theorem discretePosition_recurrence (A : ℕ → R) (h : ℝ) (n : ℕ) :
    discretePosition A h (n + 2) =
      ((2 : ℝ) • (1 : R) - h ^ 2 • A (n + 1)) * discretePosition A h (n + 1) -
        discretePosition A h n := by
  rw [discretePosition_succ A h (n + 1), discreteVelocity_succ A h (n + 1)]
  have hp := discretePosition_succ A h n
  simp only [sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul, pow_two]
  rw [show (2 : ℝ) • discretePosition A h (n + 1) =
    discretePosition A h (n + 1) + discretePosition A h (n + 1) by module]
  rw [hp]
  abel

def normalizedDiscrete (A : ℕ → R) (h : ℝ) (n : ℕ) : R :=
  h⁻¹ • discretePosition A h n

@[simp] theorem normalizedDiscrete_zero (A : ℕ → R) (h : ℝ) :
    normalizedDiscrete A h 0 = 0 := by simp [normalizedDiscrete]

@[simp] theorem normalizedDiscrete_one (A : ℕ → R) {h : ℝ} (hh : h ≠ 0) :
    normalizedDiscrete A h 1 = 1 := by
  simp [normalizedDiscrete, smul_smul, hh]

theorem normalizedDiscrete_recurrence (A : ℕ → R) (h : ℝ) (n : ℕ) :
    normalizedDiscrete A h (n + 2) =
      ((2 : ℝ) • (1 : R) - h ^ 2 • A (n + 1)) * normalizedDiscrete A h (n + 1) -
        normalizedDiscrete A h n := by
  simp only [normalizedDiscrete, discretePosition_recurrence, smul_sub, mul_smul_comm]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace calculations for normalizing the finite Jacobi matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def scalarLift {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ :=
  Matrix.kronecker (1 : NormalMatrix) G

theorem scalarLift_one (N : ℕ) : scalarLift (1 : Matrix (Fin N) (Fin N) ℝ) = 1 :=
  Matrix.one_kronecker_one

theorem blockAt_scalarLift {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    blockAt (scalarLift G) i j = G i j • (1 : NormalMatrix) := by
  ext a b
  change (1 : NormalMatrix) a b * G i j = G i j * (1 : NormalMatrix) a b
  ring

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ModeCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression onto a common scalar time mode in the three normal directions. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem mul_modeEmbedding {N : ℕ}
    (M : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ)
    (w : Fin N → ℝ) (a b : Fin 3) (i : Fin N) :
    (M * modeEmbedding w) (a, i) b = ∑ j, blockAt M i j a b * w j := by
  simp [Matrix.mul_apply, modeEmbedding, Fintype.sum_prod_type, blockAt]

theorem mode_compression_apply {N : ℕ}
    (M : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ)
    (w : Fin N → ℝ) (a b : Fin 3) :
    ((modeEmbedding w)ᵀ * M * modeEmbedding w) a b =
      ∑ i, ∑ j, w i * w j * blockAt M i j a b := by
  rw [Matrix.mul_assoc]
  calc
    _ = ∑ i, w i * (M * modeEmbedding w) (a, i) b := by
      change (∑ k, (modeEmbedding w) k a * (M * modeEmbedding w) k b) = _
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [modeEmbedding]
    _ = _ := by
      simp_rw [mul_modeEmbedding, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem mode_compression_diagonal {N : ℕ} (A : Fin N → NormalMatrix)
    (w : Fin N → ℝ) :
    (modeEmbedding w)ᵀ * Matrix.blockDiagonal A * modeEmbedding w =
      ∑ i, w i ^ 2 • A i := by
  ext a b
  rw [mode_compression_apply]
  simp only [blockAt_diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.ite_apply, Matrix.zero_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  congr 1
  funext i
  ring

theorem mode_compression_scalar {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (w : Fin N → ℝ) :
    (modeEmbedding w)ᵀ * scalarLift G * modeEmbedding w =
      (∑ i, ∑ j, w i * G i j * w j) • (1 : NormalMatrix) := by
  ext a b
  rw [mode_compression_apply]
  simp only [blockAt_scalarLift, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  congr 1
  funext i
  congr 1
  funext j
  ring

/-- Every unit time mode yields three orthonormal columns. -/
theorem modeEmbedding_orthonormal {N : ℕ} (w : Fin N → ℝ)
    (hw : ∑ i, w i ^ 2 = 1) :
    (modeEmbedding w)ᵀ * modeEmbedding w = 1 := by
  have h := mode_compression_scalar (1 : Matrix (Fin N) (Fin N) ℝ) w
  rw [scalarLift_one, Matrix.mul_one] at h
  simpa [Matrix.one_apply, mul_ite, mul_zero, ← pow_two, hw] using h

/-- Trace-free Weyl blocks give a trace-free compressed perturbation. -/
theorem trace_mode_compression_defect {N : ℕ} (A : Fin N → NormalMatrix)
    (w : Fin N → ℝ) (hA : ∀ i, (A i).trace = 0) :
    ((modeEmbedding w)ᵀ * Matrix.blockDiagonal A * modeEmbedding w).trace = 0 := by
  rw [mode_compression_diagonal, Matrix.trace_sum]
  simp [Matrix.trace_smul, hA]

theorem scalarLift_mode_eigenvector {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (w : Fin N → ℝ) (g : ℝ) (heigen : G *ᵥ w = g • w) :
    scalarLift G * modeEmbedding w = g • modeEmbedding w := by
  ext ⟨a, i⟩ b
  rw [mul_modeEmbedding]
  simp only [blockAt_scalarLift, Matrix.smul_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst b
    simpa [modeEmbedding, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.smul_apply,
      smul_eq_mul] using congrFun heigen i
  · simp [modeEmbedding, hab]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ReferenceCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the finite comparison to the actual scalar Dirichlet reference. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def curvatureDirichlet {N : ℕ} (t : ℝ) (A : Fin N → NormalMatrix) :
    Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ :=
  scalarLift (referenceMatrix t N) - (t / (N + 1)) ^ 2 • Matrix.blockDiagonal A

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSchemeMatrix
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the concrete Jacobi recurrence with the finite curvature matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem scalarLift_sub_diagonal {N : ℕ} (d a : ℝ) (A : Fin N → NormalMatrix) :
    scalarLift (scalarDirichlet N d) - a • Matrix.blockDiagonal A =
      dirichletMatrix (fun i => d • (1 : NormalMatrix) - a • A i) := by
  ext ⟨u, i⟩ ⟨v, j⟩
  by_cases hij : i = j
  · subst j
    simp [scalarLift, Matrix.kronecker, Matrix.kroneckerMap, scalarDirichlet,
      dirichletMatrix, Matrix.blockDiagonal, mul_comm]
  · by_cases hf : i.val + 1 = j.val
    · have hb : ¬j.val + 1 = i.val := by omega
      simp [scalarLift, Matrix.kronecker, Matrix.kroneckerMap, scalarDirichlet,
        dirichletMatrix, Matrix.blockDiagonal, hij, hf, hb]
    · by_cases hb : j.val + 1 = i.val <;>
        simp [scalarLift, Matrix.kronecker, Matrix.kroneckerMap, scalarDirichlet,
          dirichletMatrix, Matrix.blockDiagonal, hij, hf, hb]

theorem curvatureDirichlet_eq (t : ℝ) {N : ℕ} (A : Fin N → NormalMatrix) :
    curvatureDirichlet t A = dirichletMatrix (fun i =>
      (2 : ℝ) • (1 : NormalMatrix) - (t / (N + 1)) ^ 2 • (1 + A i)) := by
  rw [curvatureDirichlet, referenceMatrix, scalarLift_sub_diagonal]
  congr 1
  funext i
  module

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSchemeRatios
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact normalized coefficient in a discrete Jacobi pivot. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem relativeDiscretePosition_pos (R : ℕ → NormalMatrix) (h : ℝ) {i : ℕ}
    (hi : 0 < i) : relativeDiscretePosition R h i =
      ((i : ℝ) * h)⁻¹ • discretePosition R h i := by
  simp only [relativeDiscretePosition, ite_eq_right hi.ne']

theorem matrix_inverse_divided_time (s : ℝ) (hs : s ≠ 0) (X : NormalMatrix)
    (hX : IsUnit X.det) : (s⁻¹ • X)⁻¹ = s • X⁻¹ := by
  let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs)
  rw [Matrix.inv_smul X s⁻¹ hX, invOf_eq_inv, inv_inv]

/-- Rescaling the discrete solution does not change any pivot ratio. -/
theorem normalizedDiscrete_ratio (R : ℕ → NormalMatrix) {h : ℝ} (hh : h ≠ 0)
    (i : ℕ) (hX : IsUnit (discretePosition R h i).det) :
    normalizedDiscrete R h (i + 1) * (normalizedDiscrete R h i)⁻¹ =
      discretePosition R h (i + 1) * (discretePosition R h i)⁻¹ := by
  simp only [normalizedDiscrete, matrix_inverse_divided_time h hh _ hX,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hh, one_smul]

/-- The pivot is `1 + P/i`, with `P` the discrete velocity times the
inverse of position divided by time. This identity explains the uniform
near-zero positivity criterion without introducing a time cutoff. -/
theorem discretePosition_ratio (R : ℕ → NormalMatrix) {h : ℝ} (hh : h ≠ 0)
    {i : ℕ} (hi : 0 < i) (hX : IsUnit (discretePosition R h i).det) :
    discretePosition R h (i + 1) * (discretePosition R h i)⁻¹ =
      1 + ((1 : ℝ) / i) • (discreteVelocity R h (i + 1) *
        (relativeDiscretePosition R h i)⁻¹) := by
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  rw [relativeDiscretePosition_pos R h hi,
    matrix_inverse_divided_time _ (mul_ne_zero hi' hh) _ hX,
    discretePosition_succ, add_mul, Matrix.mul_nonsing_inv _ hX]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  congr 1
  field_simp

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiMeshError
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error bounds at all nodes, including normalization through time zero. -/

namespace PositiveEinsteinFour.Jacobi

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem relative_discrete_error {R : ℕ → NormalMatrix} {J : ℝ → NormalMatrix}
    {h t C K : ℝ} {N : ℕ} (hh : 0 < h) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hNt : ((N + 1 : ℕ) : ℝ) * h ≤ t)
    (hJ0 : J 0 = 0) (hJ : HasDerivAt J 1 0)
    (herr : ∀ i : ℕ, i ≤ N + 1 →
      ‖discretePosition R h i - J (i * h)‖ ≤ C * i * h ^ 2 * Real.exp (K * i * h)) :
    ∀ i : ℕ, i ≤ N + 1 →
      ‖relativeDiscretePosition R h i - normalizedJacobi J (i * h)‖ ≤
        C * h * Real.exp (K * t) := by
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp only [relativeDiscretePosition_zero, Nat.cast_zero, zero_mul,
      normalizedJacobi_zero hJ, sub_self, norm_zero]
    positivity
  · have hip : 0 < i := Nat.pos_of_ne_zero hi0
    have hip' : (0 : ℝ) < i := by exact_mod_cast hip
    have hs : 0 < (i : ℝ) * h := mul_pos hip' hh
    have hit : (i : ℝ) * h ≤ t :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh.le).trans hNt
    rw [relativeDiscretePosition_pos R h hip, normalizedJacobi_pos hJ0 hs.ne']
    have he := relative_position_error hip hh (herr i hi)
    simp only [one_div] at he
    exact he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith : K * i * h ≤ K * t)) (mul_nonneg hC hh.le))

/-- The velocity used in a pivot is the next backward velocity. Its
distance from the velocity at the current node also tends to zero. -/
theorem next_discrete_velocity_error {R : ℕ → NormalMatrix} {V : ℝ → NormalMatrix}
    {h t C K L : ℝ} {N : ℕ} (hh : 0 < h) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (_hL : 0 ≤ L) (hNt : ((N + 1 : ℕ) : ℝ) * h ≤ t)
    (herr : ∀ i : ℕ, i ≤ N + 1 →
      ‖discreteVelocity R h i - V (i * h)‖ ≤ C * i * h ^ 2 * Real.exp (K * i * h))
    (hLip : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t, ‖V s - V r‖ ≤ L * |s - r|) :
    ∀ i : ℕ, i ≤ N →
      ‖discreteVelocity R h (i + 1) - V (i * h)‖ ≤
        (C * t * Real.exp (K * t) + L) * h := by
  have ht : 0 ≤ t := (by positivity : 0 ≤ ((N + 1 : ℕ) : ℝ) * h).trans hNt
  have hmem (k : ℕ) (hk : k ≤ N + 1) : (k : ℝ) * h ∈ Set.Icc 0 t := by
    exact ⟨by positivity,
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le).trans hNt⟩
  intro i hi
  have hin : i + 1 ≤ N + 1 := Nat.add_le_add_right hi 1
  have hb : ‖discreteVelocity R h (i + 1) - V ((i + 1 : ℕ) * h)‖ ≤
      C * t * h * Real.exp (K * t) := by
    calc
      _ ≤ C * (i + 1 : ℕ) * h ^ 2 * Real.exp (K * (i + 1 : ℕ) * h) := herr _ hin
      _ = (C * h) * (((i + 1 : ℕ) : ℝ) * h) *
          Real.exp (K * (((i + 1 : ℕ) : ℝ) * h)) := by ring_nf
      _ ≤ (C * h) * t * Real.exp (K * t) := by
        gcongr
        · exact (hmem _ hin).2
        · exact (hmem _ hin).2
      _ = _ := by ring_nf
  have hl := hLip _ (hmem _ hin) _ (hmem i (hi.trans (Nat.le_succ N)))
  have hdiff : |((i + 1 : ℕ) : ℝ) * h - (i : ℝ) * h| = h := by
    have heq : ((i + 1 : ℕ) : ℝ) * h - (i : ℝ) * h = h := by
      push_cast
      ring_nf
    rw [heq, abs_of_pos hh]
  rw [hdiff] at hl
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (discreteVelocity R h (i + 1)) (V ((i + 1 : ℕ) * h)) (V (i * h))
  nlinarith

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiDirichletPositivity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Jacobi pivot ratios give the actual finite curvature matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- The positive ratios are the ordered Schur pivots of the concrete
curvature Dirichlet matrix. No commutation between time samples is used. -/
theorem curvatureDirichlet_posDef_of_ratios {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix)
    (hunit : ∀ i, 1 ≤ i → i ≤ N + 1 →
      IsUnit (normalizedDiscrete R (t / (N + 1)) i).det)
    (hpos : ∀ i, 1 ≤ i → i ≤ N →
      (normalizedDiscrete R (t / (N + 1)) (i + 1) *
        (normalizedDiscrete R (t / (N + 1)) i)⁻¹).PosDef) :
    (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).PosDef := by
  let h : ℝ := t / (N + 1)
  let D : ℕ → NormalMatrix := fun i => (2 : ℝ) • 1 - h ^ 2 • R (i + 1)
  let Y : ℕ → NormalMatrix := normalizedDiscrete R h
  let S : Fin N → NormalMatrix := fun i => jacobiPivot D i.val
  have hh : h ≠ 0 := div_ne_zero ht (by positivity)
  have hY0 : Y 0 = 0 := normalizedDiscrete_zero R h
  have hY1 : Y 1 = 1 := normalizedDiscrete_one R hh
  have hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i :=
    normalizedDiscrete_recurrence R h
  have hp (i : Fin N) : (S i).PosDef := by
    have hr : S i = Y (i.val + 2) * (Y (i.val + 1))⁻¹ :=
      jacobiPivot_eq_ratio D Y hY0 hY1 hrec i.val
        (fun k hk hki => hunit k hk (by omega))
    rw [hr]
    exact hpos (i.val + 1) (by omega) (by omega)
  have hdiag : (fun i : Fin N => D i.val) = pivotDiagonal S := by
    funext i
    exact (pivotDiagonal_jacobiPivot D i).symm
  rw [curvatureDirichlet_eq]
  simp only [add_sub_cancel]
  change (dirichletMatrix (fun i : Fin N => D i.val)).PosDef
  rw [hdiag]
  exact dirichlet_pivots_posDef S hp

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiWronskian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetry of the discrete Jacobi ratios from their preserved Wronskian. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem kick_wronskian (X V A : NormalMatrix) (h : ℝ)
    (hA : Aᵀ = A) (hXV : Xᵀ * V = Vᵀ * X) :
    Xᵀ * (V - h • (A * X)) = (V - h • (A * X))ᵀ * X := by
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hA, hXV, Matrix.mul_assoc]

theorem drift_wronskian (X W : NormalMatrix) (h : ℝ)
    (hXW : Xᵀ * W = Wᵀ * X) :
    (X + h • W)ᵀ * W = Wᵀ * (X + h • W) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, add_mul, mul_add,
    mul_smul_comm, smul_mul_assoc, hXW]

theorem discrete_wronskian (R : ℕ → NormalMatrix) (h : ℝ)
    (hR : ∀ i, (R i)ᵀ = R i) (i : ℕ) :
    (discretePosition R h i)ᵀ * discreteVelocity R h i =
      (discreteVelocity R h i)ᵀ * discretePosition R h i := by
  induction i with
  | zero => simp
  | succ i hi =>
      have hw := kick_wronskian (discretePosition R h i) (discreteVelocity R h i)
        (R i) h (hR i) hi
      rw [← discreteVelocity_succ] at hw
      simpa only [discretePosition_succ] using
        drift_wronskian (discretePosition R h i) (discreteVelocity R h (i + 1)) h hw

theorem next_discrete_wronskian (R : ℕ → NormalMatrix) (h : ℝ)
    (hR : ∀ i, (R i)ᵀ = R i) (i : ℕ) :
    (discretePosition R h i)ᵀ * discreteVelocity R h (i + 1) =
      (discreteVelocity R h (i + 1))ᵀ * discretePosition R h i := by
  rw [discreteVelocity_succ]
  exact kick_wronskian _ _ _ _ (hR i) (discrete_wronskian R h hR i)

theorem ratio_symmetric_of_wronskian {X V : NormalMatrix}
    (hX : IsUnit X.det) (hXV : Xᵀ * V = Vᵀ * X) :
    (V * X⁻¹)ᵀ = V * X⁻¹ := by
  have hleft : X⁻¹ᵀ * Xᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hX, Matrix.transpose_one]
  have hh := congrArg (fun A : NormalMatrix => X⁻¹ᵀ * A * X⁻¹) hXV
  have hl : X⁻¹ᵀ * (Xᵀ * V) * X⁻¹ = V * X⁻¹ := by
    rw [← Matrix.mul_assoc X⁻¹ᵀ Xᵀ V, hleft, one_mul]
  have hr : X⁻¹ᵀ * (Vᵀ * X) * X⁻¹ = X⁻¹ᵀ * Vᵀ := by
    rw [Matrix.mul_assoc X⁻¹ᵀ, Matrix.mul_assoc Vᵀ, Matrix.mul_nonsing_inv _ hX,
      mul_one]
  rw [hl, hr] at hh
  rw [Matrix.transpose_mul]
  exact hh.symm

theorem discrete_ratio_symmetric (R : ℕ → NormalMatrix) (h : ℝ)
    (hR : ∀ i, (R i)ᵀ = R i) (i : ℕ)
    (hX : IsUnit (discretePosition R h i).det) :
    (discretePosition R h (i + 1) * (discretePosition R h i)⁻¹)ᵀ =
      discretePosition R h (i + 1) * (discretePosition R h i)⁻¹ := by
  have hw := next_discrete_wronskian R h hR i
  have hv := ratio_symmetric_of_wronskian hX hw
  rw [discretePosition_succ, add_mul, Matrix.mul_nonsing_inv _ hX, smul_mul_assoc]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hv]

def pivotCoefficient (R : ℕ → NormalMatrix) (h : ℝ) (i : ℕ) : NormalMatrix :=
  discreteVelocity R h (i + 1) * (relativeDiscretePosition R h i)⁻¹

/-- Symmetry also holds for the totalized coefficient before the mesh is
known to be preconjugate: a singular position has inverse zero. -/
theorem one_add_pivotCoefficient_symmetric (R : ℕ → NormalMatrix) {h : ℝ}
    (hh : h ≠ 0) (hR : ∀ i, (R i)ᵀ = R i) (i : ℕ) :
    ((1 : NormalMatrix) + ((1 : ℝ) / i) • pivotCoefficient R h i)ᵀ =
      1 + ((1 : ℝ) / i) • pivotCoefficient R h i := by
  by_cases hi : i = 0
  · subst i
    simp
  · have hip : 0 < i := Nat.pos_of_ne_zero hi
    by_cases hX : IsUnit (discretePosition R h i).det
    · rw [pivotCoefficient, ← discretePosition_ratio R hh hip hX]
      exact discrete_ratio_symmetric R h hR i hX
    · have hx0 : (discretePosition R h i).det = 0 := by
        simpa only [isUnit_iff_ne_zero, not_not] using hX
      have hb0 : (relativeDiscretePosition R h i).det = 0 := by
        rw [relativeDiscretePosition_pos R h hip, Matrix.det_smul, hx0, mul_zero]
      have hb : ¬IsUnit (relativeDiscretePosition R h i).det := by simp [hb0]
      simp only [pivotCoefficient, Matrix.nonsing_inv_apply_not_isUnit _ hb,
        mul_zero, smul_zero, add_zero, Matrix.transpose_one]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiPreconjugate
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From uniform preconjugate approximation to positive curvature matrices. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The exact Wronskian, uniform inverse bounds and endpoint normalization
give positivity of the full discrete curvature matrix on a fine mesh. -/
theorem curvatureDirichlet_eventually_posDef_of_approximation
    {t : ℝ} (ht : 0 < t) (R : ℕ → ℕ → NormalMatrix)
    (hR : ∀ N i, (R N i)ᵀ = R N i)
    {B V : ℝ → NormalMatrix}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hV : ContinuousOn V (Set.Icc 0 t))
    (hB0 : B 0 = 1) (hV0 : V 0 = 1)
    (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s))
    {eB eV : ℕ → ℝ} (heB : Tendsto eB atTop (nhds 0)) (heV : Tendsto eV atTop (nhds 0))
    (hb : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N + 1 →
      ‖relativeDiscretePosition (R N) (t / (N + 1)) i -
        B ((i : ℝ) * (t / (N + 1)))‖ ≤ eB N)
    (hv : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N →
      ‖discreteVelocity (R N) (t / (N + 1)) (i + 1) -
        V ((i : ℝ) * (t / (N + 1)))‖ ≤ eV N) :
    ∀ᶠ N : ℕ in atTop,
      (curvatureDirichlet t (fun i : Fin N => R N (i.val + 1) - 1)).PosDef := by
  let C : ℝ → NormalMatrix := fun s => V s * Ring.inverse (B s)
  have hC : ContinuousOn C (Set.Icc 0 t) := inverse_product_continuousOn hB hV hunit
  have hC0 : C 0 = 1 := by simp [C, hB0, hV0, Ring.inverse_one]
  obtain ⟨e, he, hcoef⟩ := mesh_inverse_product_converges ht.le hB hV hunit heB heV hb hv
  have happrox : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ‖pivotCoefficient (R N) (t / (N + 1)) i -
        C ((i : ℝ) * (t / (N + 1)))‖ ≤ e N := by
    filter_upwards [hcoef] with N hN i _ hi
    simpa only [pivotCoefficient, Matrix.nonsing_inv_eq_ringInverse, C] using (hN i hi).2
  have hsym : ∀ N i : ℕ,
      ((1 : NormalMatrix) + ((1 : ℝ) / i) • pivotCoefficient (R N) (t / (N + 1)) i)ᵀ =
        1 + ((1 : ℝ) / i) • pivotCoefficient (R N) (t / (N + 1)) i := by
    intro N i
    exact one_add_pivotCoefficient_symmetric (R N)
      (ne_of_gt (div_pos ht (by positivity))) (hR N) i
  have hpos := eventually_matrix_ratio_posDef ht hC hC0 he happrox hsym
  obtain ⟨K, _, hinv⟩ := eventually_mesh_inverse_bounds ht.le hB hunit heB hb
  filter_upwards [hpos, hinv] with N hp hi
  let h : ℝ := t / (N + 1)
  have hh : 0 < h := div_pos ht (by positivity)
  have hxunit (i : ℕ) (hi0 : 1 ≤ i) (hiN : i ≤ N + 1) :
      IsUnit (discretePosition (R N) h i) := by
    have hbi := (hi i hiN).1
    rw [relativeDiscretePosition_pos _ _ (by omega)] at hbi
    exact isUnit_of_divided_time (mul_ne_zero (by exact_mod_cast (by omega : i ≠ 0)) hh.ne') hbi
  have hyunit (i : ℕ) (hi0 : 1 ≤ i) (hiN : i ≤ N + 1) :
      IsUnit (normalizedDiscrete (R N) h i).det := by
    have hs : IsUnit (algebraMap ℝ NormalMatrix h⁻¹) :=
      (isUnit_iff_ne_zero.mpr (inv_ne_zero hh.ne')).map (algebraMap ℝ NormalMatrix)
    have hu : IsUnit (normalizedDiscrete (R N) h i) := by
      simpa only [normalizedDiscrete, Algebra.smul_def] using hs.mul (hxunit i hi0 hiN)
    exact (Matrix.isUnit_iff_isUnit_det _).mp hu
  apply curvatureDirichlet_posDef_of_ratios ht.ne' (R N) hyunit
  intro i hi0 hiN
  have hxdet := (Matrix.isUnit_iff_isUnit_det _).mp (hxunit i hi0 (hiN.trans (Nat.le_succ N)))
  rw [normalizedDiscrete_ratio _ hh.ne' i hxdet,
    discretePosition_ratio _ hh.ne' (by omega) hxdet]
  exact hp i (by omega) hiN

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSchemeError
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform error bounds for the concrete noncommuting Jacobi recurrence. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]

theorem discreteJacobi_error {R J V : ℝ → E} {t h K Lx Lv F : ℝ} {n : ℕ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hnh : (n : ℝ) * h ≤ t)
    (hK : 0 ≤ K) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv) (hF : 0 ≤ F)
    (hJ0 : J 0 = 0) (hV0 : V 0 = 1)
    (hR : ∀ s ∈ Set.Icc 0 t, ‖R s‖ ≤ K)
    (hJ : ∀ s ∈ Set.Icc 0 t, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 t, HasDerivAt V (-(R s * J s)) s)
    (hvelocity : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t,
      ‖V s - V r‖ ≤ Lx * |s - r|)
    (hacceleration : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t,
      ‖-(R s * J s) - -(R r * J r)‖ ≤ Lv * |s - r|)
    (hforce : ∀ s ∈ Set.Icc 0 t, ‖R s * J s‖ ≤ F) :
    ‖discretePosition (fun i => R (i * h)) h n - J (n * h)‖ +
      ‖discreteVelocity (fun i => R (i * h)) h n - V (n * h)‖ ≤
        (Lx + Lv + F) * n * h ^ 2 * Real.exp ((1 + 2 * K) * n * h) := by
  let A : ℕ → E := fun i => R (i * h)
  let C : ℕ → E →L[ℝ] E := fun i => ContinuousLinearMap.mul ℝ E (A i)
  have hmem (i : ℕ) (hi : i ≤ n) : (i : ℝ) * h ∈ Set.Icc 0 t := by
    constructor
    · positivity
    · exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh).trans hnh
  apply kick_drift_global_error (R := C)
    (x := discretePosition A h) (v := discreteVelocity A h)
    (X := fun i => J (i * h)) (V := fun i => V (i * h))
    hh hh1 hK (by positivity)
  · intro i hi
    exact (ContinuousLinearMap.opNorm_mul_apply_le ℝ E (A i)).trans (hR _ (hmem i hi.le))
  · simpa using hJ0.symm
  · simpa using hV0.symm
  · intro i _
    exact discretePosition_succ A h i
  · intro i _
    exact discreteVelocity_succ A h i
  · intro i hi
    have hsub (s : ℝ) (hs : s ∈ Set.Icc (i * h) (i * h + h)) : s ∈ Set.Icc 0 t := by
      constructor
      · exact (hmem i hi.le).1.trans hs.1
      · have hs' : s ≤ ((i + 1 : ℕ) : ℝ) * h := by
          simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hs.2
        exact hs'.trans (hmem (i + 1) hi).2
    have hc := kick_drift_consistency (R := fun s => ContinuousLinearMap.mul ℝ E (R s))
      (X := J) (V := V) (a := i * h) hh hLx hLv
      (fun s hs => hJ s (hsub s hs)) (fun s hs => hV s (hsub s hs))
      (fun s hs => by
        simpa only [abs_of_nonneg (sub_nonneg.mpr hs.1)] using
          hvelocity s (hsub s hs) (i * h) (hmem i hi.le))
      (fun s hs => by
        simpa only [ContinuousLinearMap.mul_apply',
          abs_of_nonneg (sub_nonneg.mpr hs.1)] using
          hacceleration s (hsub s hs) (i * h) (hmem i hi.le))
      (hforce _ (hmem i hi.le))
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hc

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiODEPositivity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preconjugate positivity from the Jacobi ODE. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

def meshCurvature (R : ℝ → NormalMatrix) (t : ℝ) (N i : ℕ) : NormalMatrix :=
  R ((i : ℝ) * meshStep t N)

namespace RegularJacobi

variable {t : ℝ} (d : RegularJacobi t)

def localError : ℝ := d.Lx + d.Lv + d.F

def growth : ℝ := 1 + 2 * d.K

def positionError (N : ℕ) : ℝ := d.localError * meshStep t N * Real.exp (d.growth * t)

def velocityError (N : ℕ) : ℝ :=
  (d.localError * t * Real.exp (d.growth * t) + d.Lx) * meshStep t N

theorem positionError_tendsto : Tendsto d.positionError atTop (nhds 0) := by
  change Tendsto (fun N : ℕ => d.localError * meshStep t N * Real.exp (d.growth * t))
    atTop (nhds 0)
  simpa only [positionError, mul_zero, zero_mul] using
    ((meshStep_tendsto t).const_mul d.localError).mul_const (Real.exp (d.growth * t))

theorem velocityError_tendsto : Tendsto d.velocityError atTop (nhds 0) := by
  change Tendsto (fun N : ℕ =>
    (d.localError * t * Real.exp (d.growth * t) + d.Lx) * meshStep t N) atTop (nhds 0)
  simpa only [velocityError, mul_zero] using
    (meshStep_tendsto t).const_mul (d.localError * t * Real.exp (d.growth * t) + d.Lx)

theorem uniform_errors (ht : 0 < t) :
    ∀ᶠ N : ℕ in atTop,
      (∀ i : ℕ, i ≤ N + 1 →
        ‖relativeDiscretePosition (meshCurvature d.R t N) (meshStep t N) i -
          normalizedJacobi d.J ((i : ℝ) * meshStep t N)‖ ≤ d.positionError N) ∧
      (∀ i : ℕ, i ≤ N →
        ‖discreteVelocity (meshCurvature d.R t N) (meshStep t N) (i + 1) -
          d.V ((i : ℝ) * meshStep t N)‖ ≤ d.velocityError N) := by
  have hc : 0 ≤ d.localError := add_nonneg (add_nonneg d.Lx_nonneg d.Lv_nonneg) d.F_nonneg
  have hk : 0 ≤ d.growth := by dsimp [growth]; linarith [d.K_nonneg]
  have hd0 : HasDerivAt d.J 1 0 := by
    simpa only [d.initial_velocity] using d.position_derivative 0 ⟨le_rfl, ht.le⟩
  filter_upwards [(meshStep_tendsto t).eventually (gt_mem_nhds zero_lt_one)] with N hN
  have hh : 0 < meshStep t N := div_pos ht (by positivity)
  have htmesh : ((N + 1 : ℕ) : ℝ) * meshStep t N = t := by
    simp only [meshStep, Nat.cast_add, Nat.cast_one]
    field_simp
  have herr (i : ℕ) (hi : i ≤ N + 1) :
      ‖discretePosition (meshCurvature d.R t N) (meshStep t N) i -
        d.J (i * meshStep t N)‖ +
      ‖discreteVelocity (meshCurvature d.R t N) (meshStep t N) i -
        d.V (i * meshStep t N)‖ ≤
        d.localError * i * meshStep t N ^ 2 * Real.exp (d.growth * i * meshStep t N) := by
    have hit : (i : ℝ) * meshStep t N ≤ t := by
      calc
        _ ≤ ((N + 1 : ℕ) : ℝ) * meshStep t N :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh.le
        _ = t := htmesh
    exact discreteJacobi_error hh.le hN.le hit d.K_nonneg d.Lx_nonneg d.Lv_nonneg
      d.F_nonneg d.initial_position d.initial_velocity d.curvature_bound
      d.position_derivative d.velocity_derivative d.velocity_lipschitz
      d.acceleration_lipschitz d.force_bound
  constructor
  · apply relative_discrete_error hh hc hk htmesh.le d.initial_position hd0
    intro i hi
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (herr i hi)
  · apply next_discrete_velocity_error hh hc hk d.Lx_nonneg htmesh.le
    · intro i hi
      exact (le_add_of_nonneg_left (norm_nonneg _)).trans (herr i hi)
    · exact d.velocity_lipschitz

/-- The Jacobi ODE implies positivity of the finite curvature matrices. -/
theorem curvatureDirichlet_eventually_posDef (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    ∀ᶠ N : ℕ in atTop,
      (curvatureDirichlet t (fun i : Fin N =>
        d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N) - 1)).PosDef := by
  have hcJ : ContinuousOn d.J (Set.Icc 0 t) := fun s hs =>
    (d.position_derivative s hs).continuousAt.continuousWithinAt
  have hcV : ContinuousOn d.V (Set.Icc 0 t) := fun s hs =>
    (d.velocity_derivative s hs).continuousAt.continuousWithinAt
  have hd0 : HasDerivAt d.J 1 0 := by
    simpa only [d.initial_velocity] using d.position_derivative 0 ⟨le_rfl, ht.le⟩
  have he := d.uniform_errors ht
  exact curvatureDirichlet_eventually_posDef_of_approximation ht (meshCurvature d.R t)
    (fun N i => d.symmetric _) (normalizedJacobi_continuousOn hcJ hd0) hcV
    (normalizedJacobi_zero hd0) d.initial_velocity
    (normalizedJacobi_isUnit d.initial_position hd0 hpre)
    d.positionError_tendsto d.velocityError_tendsto
    (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)

end RegularJacobi

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeightedAreaInequality
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The noninjective change-of-variables inequality, with the target
volume density retained. This is the local coordinate inequality needed
for the exponential's image. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

theorem weighted_area_inequality {f : FourSpace → FourSpace}
    {D : FourSpace → FourSpace →L[ℝ] FourSpace} {s : Set FourSpace}
    (hs : MeasurableSet s) (hf : Measurable f)
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x)
    (W : FourSpace → ℝ≥0∞) (hW : Measurable W) :
    ∫⁻ y in f '' s, W y ≤
      ∫⁻ x in s, ENNReal.ofReal |(D x).det| * W (f x) := by
  let J := fun x => ENNReal.ofReal |(D x).det|
  have hJ : AEMeasurable J (volume.restrict s) :=
    aemeasurable_ofReal_abs_det_fderivWithin volume hs hd
  have hmeasure : volume.restrict (f '' s) ≤
      Measure.map f ((volume.restrict s).withDensity J) := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.restrict_apply hA, Measure.map_apply hf hA,
      withDensity_apply _ (hf hA), Measure.restrict_restrict (hf hA)]
    rw [← image_preimage_inter f s A]
    exact addHaar_image_le_lintegral_abs_det_fderiv volume ((hf hA).inter hs)
      (fun x hx => (hd x hx.2).mono inter_subset_right)
  have h := lintegral_mono' hmeasure (le_rfl : W ≤ W)
  have hcomp : AEMeasurable (fun x => W (f x)) (volume.restrict s) :=
    (hW.comp hf).aemeasurable
  rw [lintegral_map hW hf] at h
  rw [lintegral_withDensity_eq_lintegral_mul₀ hJ hcomp] at h
  exact h

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicJacobiSecondVariationAlgebra
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite metric algebra for the second variation of energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def jacobiMetricPair (G : Mat4) (v w : JacobiCoordinateVector) : ℝ :=
  v ⬝ᵥ (G *ᵥ w)

theorem jacobiMetricPair_symm {G : Mat4} (hG : G.IsSymm)
    (v w : JacobiCoordinateVector) : jacobiMetricPair G v w = jacobiMetricPair G w v :=
  by
    have hv := Matrix.vecMul_transpose G v
    rw [hG] at hv
    unfold jacobiMetricPair
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, hv]

theorem jacobiMetricPair_add_left (G : Mat4) (u v w : JacobiCoordinateVector) :
    jacobiMetricPair G (u + v) w = jacobiMetricPair G u w + jacobiMetricPair G v w := by
  exact add_dotProduct _ _ _

theorem jacobiMetricPair_add_right (G : Mat4) (u v w : JacobiCoordinateVector) :
    jacobiMetricPair G u (v + w) = jacobiMetricPair G u v + jacobiMetricPair G u w := by
  simp only [jacobiMetricPair, Matrix.mulVec_add, dotProduct_add]

theorem jacobiMetricPair_smul_right (G : Mat4) (u v : JacobiCoordinateVector) (r : ℝ) :
    jacobiMetricPair G u (r • v) = r * jacobiMetricPair G u v := by
  simp only [jacobiMetricPair, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem jacobiMetricPair_neg_left (G : Mat4) (u v : JacobiCoordinateVector) :
    jacobiMetricPair G (-u) v = -jacobiMetricPair G u v := by
  exact neg_dotProduct _ _

theorem jacobiMetricPair_matrix_add (G H : Mat4) (v w : JacobiCoordinateVector) :
    jacobiMetricPair (G + H) v w = jacobiMetricPair G v w + jacobiMetricPair H v w := by
  simp only [jacobiMetricPair, Matrix.add_mulVec, dotProduct_add]

theorem jacobiMetricPair_left_product (G A : Mat4) (v w : JacobiCoordinateVector) :
    jacobiMetricPair (Aᵀ * G) v w = jacobiMetricPair G (A *ᵥ v) w := by
  simp only [jacobiMetricPair, ← Matrix.mulVec_mulVec,
    dotProduct_transpose_mulVec A v (G *ᵥ w), dotProduct_comm]

theorem jacobiMetricPair_right_product (G A : Mat4) (v w : JacobiCoordinateVector) :
    jacobiMetricPair (G * A) v w = jacobiMetricPair G v (A *ᵥ w) := by
  simp only [jacobiMetricPair, Matrix.mulVec_mulVec]

theorem jacobiMetricRate_pair (G A : Mat4) (v w : JacobiCoordinateVector) :
    jacobiMetricPair (jacobiMetricRate G A) v w =
      jacobiMetricPair G (A *ᵥ v) w + jacobiMetricPair G v (A *ᵥ w) := by
  rw [jacobiMetricRate, jacobiMetricPair_matrix_add,
    jacobiMetricPair_left_product, jacobiMetricPair_right_product]

theorem jacobiMetricSecondRate_pair_self {G : Mat4} (hG : G.IsSymm)
    (B C : Mat4) (v : JacobiCoordinateVector) :
    (1 / 2 : ℝ) * jacobiMetricPair (jacobiMetricSecondRate G B C) v v =
      jacobiMetricPair G v (C *ᵥ v) + jacobiMetricPair G (B *ᵥ v) (B *ᵥ v) +
        jacobiMetricPair G v (B *ᵥ (B *ᵥ v)) := by
  have hsum : jacobiMetricSecondRate G B C =
      jacobiMetricRate G C + jacobiMetricRate (jacobiMetricRate G B) B := by
    unfold jacobiMetricSecondRate jacobiMetricRate
    abel
  rw [hsum, jacobiMetricPair_matrix_add, jacobiMetricRate_pair,
    jacobiMetricRate_pair, jacobiMetricPair_symm hG (C *ᵥ v) v,
    jacobiMetricPair_symm (jacobiMetricRate_symm hG B) (B *ᵥ v) v,
    jacobiMetricRate_pair]
  ring

def coordinateEnergySecondDensity (G H K : Mat4) (v w : JacobiCoordinateVector) : ℝ :=
  jacobiMetricPair G w w + 2 * jacobiMetricPair H w v +
    (1 / 2 : ℝ) * jacobiMetricPair K v v

theorem coordinateEnergySecondDensity_expansion {G : Mat4} (hG : G.IsSymm)
    (B C : Mat4) (v w : JacobiCoordinateVector) :
    coordinateEnergySecondDensity G (jacobiMetricRate G B) (jacobiMetricSecondRate G B C) v w =
      jacobiMetricPair G w w + 2 * jacobiMetricPair G w (B *ᵥ v) +
        2 * jacobiMetricPair G v (B *ᵥ w) + jacobiMetricPair G v (C *ᵥ v) +
        jacobiMetricPair G (B *ᵥ v) (B *ᵥ v) +
        jacobiMetricPair G v (B *ᵥ (B *ᵥ v)) := by
  rw [coordinateEnergySecondDensity, jacobiMetricSecondRate_pair_self hG,
    jacobiMetricRate_pair, jacobiMetricPair_symm hG (B *ᵥ w) v]
  ring

theorem jacobiMetricPair_skew {G K : Mat4}
    (hK : Kᵀ * G + G * K = 0) (v y : JacobiCoordinateVector) :
    jacobiMetricPair G (K *ᵥ v) y = -jacobiMetricPair G v (K *ᵥ y) := by
  have h := congrArg (fun A : Mat4 => jacobiMetricPair A v y) hK
  rw [jacobiMetricPair_matrix_add, jacobiMetricPair_left_product,
    jacobiMetricPair_right_product] at h
  have hz : jacobiMetricPair (0 : Mat4) v y = 0 := by
    simp [jacobiMetricPair]
  rw [hz] at h
  linarith

/-- The vector terms left after adding the boundary derivative to the
curvature term collapse by torsion freedom and its derivative. -/
theorem jacobiSecondVariation_vector_identity (Γ : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4)
    (hΓ : ∀ a i j, Γ i a j = Γ j a i)
    (hD : ∀ r a i j, D r i a j = D r j a i)
    (v y : JacobiCoordinateVector) :
    jacobiCurvature Γ D y v *ᵥ y +
        jacobiConnection Γ v *ᵥ (jacobiConnection Γ y *ᵥ y) +
        jacobiConnectionDerivative D v y *ᵥ y =
      jacobiConnectionDerivative D y y *ᵥ v +
        jacobiConnection Γ y *ᵥ (jacobiConnection Γ y *ᵥ v) := by
  rw [jacobiCurvature_eq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    jacobiConnection_mulVec_comm Γ hΓ v y,
    jacobiConnectionDerivative_mulVec_comm D hD y v y]
  module

def coordinateIndexDensity (G : Mat4) (Γ : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4) (v y w : JacobiCoordinateVector) : ℝ :=
  jacobiMetricPair G (w + jacobiConnection Γ v *ᵥ y)
      (w + jacobiConnection Γ v *ᵥ y) -
    jacobiMetricPair G (jacobiCurvature Γ D y v *ᵥ v) y

def coordinateEnergyBoundaryRate (G : Mat4) (Γ : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4) (v y w : JacobiCoordinateVector) : ℝ :=
  jacobiMetricPair G v
    (jacobiConnection Γ v *ᵥ (jacobiConnection Γ y *ᵥ y) +
      jacobiConnectionDerivative D v y *ᵥ y +
      (2 : ℝ) • (jacobiConnection Γ y *ᵥ w))

/-- The full pointwise second-variation identity. -/
theorem coordinateEnergySecondDensity_eq_index_add_boundary
    (G : Mat4) (Γ : Fin 4 → Mat4) (D : Fin 4 → Fin 4 → Mat4)
    (hG : G.IsSymm) (hΓ : ∀ a i j, Γ i a j = Γ j a i)
    (hD : ∀ r a i j, D r i a j = D r j a i)
    (v y w : JacobiCoordinateVector)
    (hK : (jacobiCurvature Γ D y v)ᵀ * G + G * jacobiCurvature Γ D y v = 0) :
    coordinateEnergySecondDensity G (jacobiMetricRate G (jacobiConnection Γ y))
        (jacobiMetricSecondRate G (jacobiConnection Γ y) (jacobiConnectionDerivative D y y)) v w =
      coordinateIndexDensity G Γ D v y w + coordinateEnergyBoundaryRate G Γ D v y w := by
  have hAy := jacobiConnection_mulVec_comm Γ hΓ v y
  have hvec := jacobiSecondVariation_vector_identity Γ D hΓ hD v y
  have hpair := congrArg (fun u => jacobiMetricPair G v u) hvec
  simp only [jacobiMetricPair_add_right] at hpair
  rw [coordinateEnergySecondDensity_expansion hG]
  unfold coordinateIndexDensity coordinateEnergyBoundaryRate
  rw [jacobiMetricPair_skew hK, hAy]
  simp only [jacobiMetricPair_add_left, jacobiMetricPair_add_right,
    jacobiMetricPair_smul_right]
  rw [jacobiMetricPair_symm hG (jacobiConnection Γ y *ᵥ v) w]
  linarith

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

/-! Vanishing of the nonnegative exterior/codifferential quadratic form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators

theorem twoFormDeRhamQuadratic_eq_zero (A : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    twoFormDeRhamQuadratic A = 0 ↔
      (∀ i j k, twoFormExteriorComponent A i j k = 0) ∧
      ∀ k, twoFormCodiffComponent A k = 0 := by
  constructor
  · intro h
    have hE : 0 ≤ ∑ i, ∑ j, ∑ k, twoFormExteriorComponent A i j k ^ 2 := by positivity
    have hC : 0 ≤ ∑ k, twoFormCodiffComponent A k ^ 2 := by positivity
    have he : (∑ i, ∑ j, ∑ k, twoFormExteriorComponent A i j k ^ 2) = 0 := by
      unfold twoFormDeRhamQuadratic at h
      linarith
    have hc : (∑ k, twoFormCodiffComponent A k ^ 2) = 0 := by
      unfold twoFormDeRhamQuadratic at h
      linarith
    constructor
    · intro i j k
      apply sq_eq_zero_iff.mp
      have hi := sum_four_nonneg_zero _ (fun _ => by positivity) he i
      have hj := sum_four_nonneg_zero _ (fun _ => by positivity) hi j
      exact sum_four_nonneg_zero _ (fun _ => sq_nonneg _) hj k
    · intro k
      exact sq_eq_zero_iff.mp (sum_four_nonneg_zero _ (fun _ => sq_nonneg _) hc k)
  · rintro ⟨he, hc⟩
    simp only [twoFormDeRhamQuadratic, he, hc, zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero, add_zero]

end PositiveEinsteinFour.Geometry
end


section

/-! The second-variation density and boundary term in an actual metric chart.
All metric, connection and curvature coefficients come from the existing
Levi-Civita definitions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem weightedMetricSecond_identity (G : Mat4) (Γ P : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4) (y : JacobiCoordinateVector) :
    (∑ i, ∑ j, (y i * y j) •
      ((D i j)ᵀ * G + (Γ j)ᵀ * P i + P i * Γ j + G * D i j)) =
      (jacobiConnectionDerivative D y y)ᵀ * G +
        (jacobiConnection Γ y)ᵀ * (∑ i, y i • P i) +
        (∑ i, y i • P i) * jacobiConnection Γ y +
        G * jacobiConnectionDerivative D y y := by
  have h₁ : (∑ i, ∑ j, (y i * y j) • ((D i j)ᵀ * G)) =
      (jacobiConnectionDerivative D y y)ᵀ * G := by
    simp only [jacobiConnectionDerivative, Matrix.transpose_sum, Matrix.transpose_smul,
      Finset.sum_mul, smul_mul_assoc]
  have h₂ : (∑ i, ∑ j, (y i * y j) • ((Γ j)ᵀ * P i)) =
      (jacobiConnection Γ y)ᵀ * (∑ i, y i • P i) := by
    simp only [jacobiConnection, Matrix.transpose_sum, Matrix.transpose_smul,
      Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul]
  have h₃ : (∑ i, ∑ j, (y i * y j) • (P i * Γ j)) =
      (∑ i, y i • P i) * jacobiConnection Γ y := by
    simp only [jacobiConnection, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  have h₄ : (∑ i, ∑ j, (y i * y j) • (G * D i j)) =
      G * jacobiConnectionDerivative D y y := by
    simp only [jacobiConnectionDerivative, Finset.mul_sum, mul_smul_comm]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [h₁, h₂, h₃, h₄]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem hasDerivAt_metricPair (G : ℝ → Mat4) (G' : Mat4)
    (v u : ℝ → JacobiCoordinateVector) (v' u' : JacobiCoordinateVector) (s : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) s)
    (hv : HasDerivAt v v' s) (hu : HasDerivAt u u' s) :
    HasDerivAt (fun t => jacobiMetricPair (G t) (v t) (u t))
      (jacobiMetricPair G' (v s) (u s) + jacobiMetricPair (G s) v' (u s) +
        jacobiMetricPair (G s) (v s) u') s := by
  have hGu (i : Fin 4) : HasDerivAt (fun t => (G t *ᵥ u t) i)
      ((G' *ᵥ u s + G s *ᵥ u') i) s := by
    have hh := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      (hG i j).mul (hasDerivAt_pi.mp hu j))
    simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply, Pi.add_apply,
      Finset.sum_add_distrib] using hh
  have hh := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_pi.mp hv i).mul (hGu i))
  have heq : (∑ i, (v' i * (G s *ᵥ u s) i +
      v s i * (G' *ᵥ u s + G s *ᵥ u') i)) =
      jacobiMetricPair G' (v s) (u s) + jacobiMetricPair (G s) v' (u s) +
        jacobiMetricPair (G s) (v s) u' := by
    simp only [jacobiMetricPair, dotProduct, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
    ring
  rw [heq] at hh
  simpa only [jacobiMetricPair, dotProduct, Pi.mul_apply] using hh

theorem hasDerivAt_matrix_vector (A : ℝ → Mat4) (A' : Mat4)
    (y : ℝ → JacobiCoordinateVector) (y' : JacobiCoordinateVector) (t : ℝ)
    (hA : HasDerivAt A A' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => A s *ᵥ y s) (A' *ᵥ y t + A t *ᵥ y') t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hh := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j).mul (hasDerivAt_pi.mp hy j))
  simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply, Pi.add_apply,
    Finset.sum_add_distrib] using hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual second derivatives of the energy of a straight chart variation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem energyPair_hasDerivAt (G : ℝ → Mat4) (G' : Mat4)
    (v u : ℝ → JacobiCoordinateVector) (v' u' : JacobiCoordinateVector) (s : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) s)
    (hv : HasDerivAt v v' s) (hu : HasDerivAt u u' s) :
    HasDerivAt (fun t => jacobiMetricPair (G t) (v t) (u t))
      (jacobiMetricPair G' (v s) (u s) + jacobiMetricPair (G s) v' (u s) +
        jacobiMetricPair (G s) (v s) u') s := by
  have hGu (i : Fin 4) : HasDerivAt (fun t => (G t *ᵥ u t) i)
      ((G' *ᵥ u s + G s *ᵥ u') i) s := by
    have hh := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      (hG i j).mul (hasDerivAt_pi.mp hu j))
    simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply, Pi.add_apply,
      Finset.sum_add_distrib] using hh
  have hh := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_pi.mp hv i).mul (hGu i))
  have heq : (∑ i, (v' i * (G s *ᵥ u s) i +
      v s i * (G' *ᵥ u s + G s *ᵥ u') i)) =
      jacobiMetricPair G' (v s) (u s) + jacobiMetricPair (G s) v' (u s) +
        jacobiMetricPair (G s) (v s) u' := by
    simp only [jacobiMetricPair, dotProduct, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
    ring
  rw [heq] at hh
  simpa only [jacobiMetricPair, dotProduct, Pi.mul_apply] using hh

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem matrixEnergy_secondJet (G H : ℝ → Mat4) (K : Mat4)
    (p p' : ℝ → JacobiCoordinateVector) (q : JacobiCoordinateVector)
    (hG : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i j, HasDerivAt (fun r => G r i j) (H s i j) s)
    (hH : ∀ i j, HasDerivAt (fun r => H r i j) (K i j) 0)
    (hp : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt p (p' s) s)
    (hp' : HasDerivAt p' q 0) (hGsym : (G 0).IsSymm) (hHsym : (H 0).IsSymm) :
    HasDerivAt (deriv (fun s : ℝ => (1 / 2 : ℝ) * jacobiMetricPair (G s) (p s) (p s)))
      (coordinateEnergySecondDensity (G 0) (H 0) K (p 0) (p' 0) +
        jacobiMetricPair (G 0) (p 0) q) 0 := by
  let Q : ℝ → ℝ := fun s => (1 / 2 : ℝ) *
    (jacobiMetricPair (H s) (p s) (p s) + jacobiMetricPair (G s) (p' s) (p s) +
      jacobiMetricPair (G s) (p s) (p' s))
  have hG0 := hG.self_of_nhds
  have hp0 := hp.self_of_nhds
  have h₁ := energyPair_hasDerivAt H K p p (p' 0) (p' 0) 0 hH hp0 hp0
  have h₂ := energyPair_hasDerivAt G (H 0) p' p q (p' 0) 0 hG0 hp' hp0
  have h₃ := energyPair_hasDerivAt G (H 0) p p' (p' 0) q 0 hG0 hp0 hp'
  have hQ := ((h₁.add h₂).add h₃).const_mul (1 / 2 : ℝ)
  have hQ' : HasDerivAt Q
      (coordinateEnergySecondDensity (G 0) (H 0) K (p 0) (p' 0) +
        jacobiMetricPair (G 0) (p 0) q) 0 := by
    convert hQ using 1
    all_goals try with_reducible_and_instances rfl
    rw [jacobiMetricPair_symm hHsym (p 0) (p' 0),
      jacobiMetricPair_symm hGsym q (p 0)]
    unfold coordinateEnergySecondDensity
    ring
  have heq : deriv (fun s : ℝ => (1 / 2 : ℝ) * jacobiMetricPair (G s) (p s) (p s)) =ᶠ[𝓝 0] Q := by
    filter_upwards [hG, hp] with s hs hps
    exact ((energyPair_hasDerivAt G (H s) p p (p' s) (p' s) s hs hps hps).const_mul
      (1 / 2 : ℝ)).deriv
  exact hQ'.congr_of_eventuallyEq heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial-frame flow keeps its direction and preserves the actual
metric Gram matrix of the transported frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatMatrixProduct_hasDerivAt (A B : ℝ → Mat4) (A' B' : Mat4) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : Fin 4) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  have h := HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) => (hA i k).mul (hB k j))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Pi.mul_apply]
    using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer the derived full Weyl derivative bound through the published
frame disintegration. No integrated Weyl equation is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance frameEnergyTransferInstance1 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup

end
end PositiveEinsteinFour.Geometry
end


section

/-! The total second-variation boundary term is independent of the chart.
The second coordinate jet includes the Hessian of the actual chart change;
the Christoffel transformation cancels exactly that extra term. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem jacobiConnection_weighted (J : Mat4) (Γ : Fin 4 → Mat4)
    (y : JacobiCoordinateVector) :
    jacobiConnection (weightedConnection J Γ) y =
      jacobiConnection Γ (J *ᵥ y) := by
  simp only [jacobiConnection, weightedConnection, Matrix.mulVec, dotProduct,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem jacobiConnection_pullback (J : Mat4) (Γ Δ P : Fin 4 → Mat4)
    (h : ∀ i, J * Γ i = P i + weightedConnection J Δ i * J)
    (y : JacobiCoordinateVector) :
    J * jacobiConnection Γ y =
      jacobiConnection P y + jacobiConnection Δ (J *ᵥ y) * J := by
  calc
    _ = ∑ i, y i • (J * Γ i) := by
      simp only [jacobiConnection, Finset.mul_sum, mul_smul_comm]
    _ = (∑ i, y i • P i) + (∑ i, y i • weightedConnection J Δ i) * J := by
      simp only [h, smul_add, Finset.sum_add_distrib, Finset.sum_mul,
        smul_mul_assoc]
    _ = _ := by
      change jacobiConnection P y + jacobiConnection (weightedConnection J Δ) y * J = _
      rw [jacobiConnection_weighted]

def jacobiCovariantSecondJet (Γ : Fin 4 → Mat4)
    (y u : JacobiCoordinateVector) : JacobiCoordinateVector :=
  u + jacobiConnection Γ y *ᵥ y

theorem jacobiCovariantSecondJet_pullback (J : Mat4) (Γ Δ P : Fin 4 → Mat4)
    (h : ∀ i, J * Γ i = P i + weightedConnection J Δ i * J)
    (y u : JacobiCoordinateVector) :
    J *ᵥ jacobiCovariantSecondJet Γ y u =
      jacobiCovariantSecondJet Δ (J *ᵥ y)
        (J *ᵥ u + jacobiConnection P y *ᵥ y) := by
  rw [jacobiCovariantSecondJet, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    jacobiConnection_pullback J Γ Δ P h y, Matrix.add_mulVec]
  simp only [jacobiCovariantSecondJet, Matrix.mulVec_mulVec]
  abel

theorem jacobiMetricPair_pullback (G H J : Mat4)
    (h : G = Jᵀ * (H * J)) (v w : JacobiCoordinateVector) :
    jacobiMetricPair G v w = jacobiMetricPair H (J *ᵥ v) (J *ᵥ w) := by
  rw [h, jacobiMetricPair_left_product, jacobiMetricPair_right_product]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial volume bound for the metric fields. The Weyl identities
are Gursky--LeBrun (1999), equations (3), (12) and Lemma 1; spherical
disintegration and parallel flow are Brin--Karcher (1984), Section 1.
The Jacobi/polar construction retains the ordinary ODE and polar density
formula (Sakai, Chapter II, Section 5), together with the diameter truncation.
No curvature-energy bound or radial-volume deficit is an input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

local instance geometricVolumeNormedAddCommGroup : NormedAddCommGroup Mat3 :=
  Matrix.frobeniusNormedAddCommGroup

end

end PositiveEinsteinFour.Geometry
end


section

/-! The explicit energy densities inherit continuity from the raw coordinate
jets.  In particular the endpoint-corrected variation satisfies all three
continuity hypotheses of the interval differentiation theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem continuousOn_metricPair {P : Type*} [TopologicalSpace P]
    {S : Set P} {G : P → Mat4} {v w : P → JacobiCoordinateVector}
    (hG : ContinuousOn G S) (hv : ContinuousOn v S) (hw : ContinuousOn w S) :
    ContinuousOn (fun p => jacobiMetricPair (G p) (v p) (w p)) S := by
  unfold jacobiMetricPair Matrix.mulVec dotProduct
  apply continuousOn_finsetSum
  intro i _
  apply (continuousOn_pi.mp hv i).mul
  apply continuousOn_finsetSum
  intro j _
  exact (continuousOn_pi.mp (continuousOn_pi.mp hG i) j).mul (continuousOn_pi.mp hw j)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The connection-curvature contributions to the Euler and signature
local trace polynomials, with the actual covariant-slot convention. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem sum_four_components_connection (f : (Fin 4 → Fin 4) → ℝ) :
    (∑ a, f a) = ∑ i, ∑ j, ∑ k, ∑ l, f ![i,j,k,l] := by
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Joining two chart partitions at the corner of a piecewise C1 normal
field, and reconstructing the two index integrals from their finite sums. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

theorem joinedPartitionTime_left (a c b : ℝ) (n m i : ℕ) (hi : i ≤ n) :
    joinedPartitionTime a c b n m i = affinePartitionTime a c n i := by
  simp only [joinedPartitionTime, ite_eq_left hi]

theorem joinedPartitionTime_right (a c b : ℝ) (n m j : ℕ) (hn : 0 < n) :
    joinedPartitionTime a c b n m (n + j) = affinePartitionTime c b m j := by
  by_cases hj : j = 0
  · subst j
    rw [Nat.add_zero, joinedPartitionTime_left _ _ _ _ _ _ le_rfl,
      affinePartitionTime_last _ _ _ hn, affinePartitionTime_zero]
  · have hnot : ¬ n + j ≤ n := by omega
    simp only [joinedPartitionTime, ite_eq_right hnot, Nat.add_sub_cancel_left]

theorem joinedPartitionTime_zero (a c b : ℝ) (n m : ℕ) :
    joinedPartitionTime a c b n m 0 = a := by
  rw [joinedPartitionTime_left _ _ _ _ _ _ (Nat.zero_le _), affinePartitionTime_zero]

theorem joinedPartitionTime_last (a c b : ℝ) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    joinedPartitionTime a c b n m (n + m) = b := by
  rw [joinedPartitionTime_right _ _ _ _ _ _ hn, affinePartitionTime_last _ _ _ hm]

theorem joinedPartitionTime_step_lt (a c b : ℝ) (n m i : ℕ)
    (hac : a < c) (hcb : c < b) (hn : 0 < n) (hm : 0 < m) :
    joinedPartitionTime a c b n m i < joinedPartitionTime a c b n m (i + 1) := by
  by_cases hi : i < n
  · rw [joinedPartitionTime_left _ _ _ _ _ _ hi.le,
      joinedPartitionTime_left _ _ _ _ _ _ hi]
    exact affinePartitionTime_step_lt a c n i hac hn
  · have heq : i = n + (i - n) := by omega
    rw [heq, show n + (i - n) + 1 = n + (i - n + 1) by omega,
      joinedPartitionTime_right _ _ _ _ _ _ hn, joinedPartitionTime_right _ _ _ _ _ _ hn]
    exact affinePartitionTime_step_lt c b m (i - n) hcb hm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem joinedPartition_sum_integral (a c b : ℝ) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (F G : ℝ → ℝ) (hF : Continuous F) (hG : Continuous G) :
    (∑ i ∈ Finset.range (n + m),
      ∫ r in joinedPartitionTime a c b n m i..joinedPartitionTime a c b n m (i + 1),
        (if i < n then F r else G r)) =
      (∫ r in a..c, F r) + ∫ r in c..b, G r := by
  rw [Finset.sum_range_add]
  have hl : (∑ i ∈ Finset.range n,
      ∫ r in joinedPartitionTime a c b n m i..joinedPartitionTime a c b n m (i + 1),
        (if i < n then F r else G r)) = ∫ r in a..c, F r := by
    calc
      _ = ∑ i ∈ Finset.range n, ∫ r in affinePartitionTime a c n i..
          affinePartitionTime a c n (i + 1), F r := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simp only [ite_eq_left hi', joinedPartitionTime_left _ _ _ _ _ _ hi'.le,
          joinedPartitionTime_left _ _ _ _ _ _ hi']
      _ = _ := by
        rw [sum_intervalIntegral_partition F hF, affinePartitionTime_zero,
          affinePartitionTime_last _ _ _ hn]
  have hr : (∑ j ∈ Finset.range m,
      ∫ r in joinedPartitionTime a c b n m (n + j)..joinedPartitionTime a c b n m (n + j + 1),
        (if n + j < n then F r else G r)) = ∫ r in c..b, G r := by
    calc
      _ = ∑ j ∈ Finset.range m, ∫ r in affinePartitionTime c b m j..
          affinePartitionTime c b m (j + 1), G r := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : ¬ n + j < n := by omega
        simp only [ite_eq_right hj, show n + j + 1 = n + (j + 1) by omega,
          joinedPartitionTime_right _ _ _ _ _ _ hn]
      _ = _ := by
        rw [sum_intervalIntegral_partition G hG, affinePartitionTime_zero,
          affinePartitionTime_last _ _ _ hm]
  rw [hl, hr]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the actual normal Jacobi equation.
The quadratic term uses the Euclidean coordinate pairing. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

def normalIndexDensity (R : NormalMatrix) (y z : Fin 3 → ℝ) : ℝ :=
  z ⬝ᵥ z - (R *ᵥ y) ⬝ᵥ y

def mulVecRightLinear (w : Fin 3 → ℝ) :
    NormalMatrix →ₗ[ℝ] (Fin 3 → ℝ) :=
  (Matrix.mulVecBilin ℝ ℝ).flip w

theorem hasDerivAt_mulVec_right (A : ℝ → NormalMatrix) (A' : NormalMatrix)
    (w : Fin 3 → ℝ) (s : ℝ) (hA : HasDerivAt A A' s) :
    HasDerivAt (fun r => A r *ᵥ w) (A' *ᵥ w) s :=
  (mulVecRightLinear w).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s hA

theorem MatrixJacobiSolution.field_position_hasDerivAt {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (fun r => d.J r *ᵥ w) (d.V s *ᵥ w) s :=
  hasDerivAt_mulVec_right d.J (d.V s) w s (d.position_derivative s)

theorem MatrixJacobiSolution.field_velocity_hasDerivAt {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (fun r => d.V r *ᵥ w) (-(R s *ᵥ (d.J s *ᵥ w))) s := by
  simpa only [Matrix.neg_mulVec, Matrix.mulVec_mulVec] using
    hasDerivAt_mulVec_right d.V (-(R s * d.J s)) w s (d.velocity_derivative s)

theorem normalJacobi_pairing_hasDerivAt (R : NormalMatrix)
    (y z : ℝ → Fin 3 → ℝ) (s : ℝ)
    (hy : HasDerivAt y (z s) s) (hz : HasDerivAt z (-(R *ᵥ y s)) s) :
    HasDerivAt (fun r => y r ⬝ᵥ z r) (normalIndexDensity R (y s) (z s)) s := by
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_pi.mp hy i).mul (hasDerivAt_pi.mp hz i))
  have heq : (∑ i, (z s i * z s i + y s i * (-(R *ᵥ y s)) i)) =
      normalIndexDensity R (y s) (z s) := by
    rw [Finset.sum_add_distrib]
    change z s ⬝ᵥ z s + y s ⬝ᵥ (-(R *ᵥ y s)) =
      z s ⬝ᵥ z s - (R *ᵥ y s) ⬝ᵥ y s
    rw [dotProduct_neg, dotProduct_comm (y s) (R *ᵥ y s)]
    simp only [sub_eq_add_neg]
  rw [heq] at hd
  simpa only [dotProduct, Pi.mul_apply] using hd

theorem MatrixJacobiSolution.index_integral_eq_boundary {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (w : Fin 3 → ℝ) (a b : ℝ) :
    (∫ s in a..b, normalIndexDensity (R s) (d.J s *ᵥ w) (d.V s *ᵥ w)) =
      (d.J b *ᵥ w) ⬝ᵥ (d.V b *ᵥ w) - (d.J a *ᵥ w) ⬝ᵥ (d.V a *ᵥ w) := by
  have hy : Continuous (fun s => d.J s *ᵥ w) :=
    (mulVecRightLinear w).toContinuousLinearMap.continuous.comp d.continuous_J
  have hz : Continuous (fun s => d.V s *ᵥ w) :=
    (mulVecRightLinear w).toContinuousLinearMap.continuous.comp d.continuous_V
  have hr : Continuous (fun s => R s *ᵥ (d.J s *ᵥ w)) := by
    have hh := (mulVecRightLinear w).toContinuousLinearMap.continuous.comp
      (hR.mul d.continuous_J)
    change Continuous (fun s => (R s * d.J s) *ᵥ w) at hh
    simpa only [Matrix.mulVec_mulVec] using hh
  have hcont : Continuous (fun s => normalIndexDensity (R s) (d.J s *ᵥ w) (d.V s *ᵥ w)) := by
    unfold normalIndexDensity dotProduct
    fun_prop
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hcont.intervalIntegrable a b)
  intro s _
  exact normalJacobi_pairing_hasDerivAt (R s) _ _ s
    (d.field_position_hasDerivAt w s) (d.field_velocity_hasDerivAt w s)

end
end PositiveEinsteinFour.Jacobi

end


section

/-! A zero-ended, piecewise smooth negative-index variation after a conjugate
point.  The action is written as the sum on the two smooth pieces. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

def normalIndexPairing (R : NormalMatrix) (y z h k : Fin 3 → ℝ) : ℝ :=
  z ⬝ᵥ k - (R *ᵥ y) ⬝ᵥ h

theorem normalIndexDensity_sub_smul (R : NormalMatrix) (hR : R.IsSymm)
    (y z h k : Fin 3 → ℝ) (ε : ℝ) :
    normalIndexDensity R (y - ε • h) (z - ε • k) =
      normalIndexDensity R y z - 2 * ε * normalIndexPairing R y z h k +
        ε ^ 2 * normalIndexDensity R h k := by
  have hsym (u v : Fin 3 → ℝ) : u ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ (R *ᵥ u) := by
    have hv := Matrix.vecMul_transpose R u
    rw [hR] at hv
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, hv]
  have hmix : (R *ᵥ h) ⬝ᵥ y = (R *ᵥ y) ⬝ᵥ h := by
    rw [dotProduct_comm (R *ᵥ h) y, hsym y h,
      dotProduct_comm h (R *ᵥ y)]
  simp only [normalIndexDensity, normalIndexPairing, Matrix.mulVec_sub,
    Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [hmix, dotProduct_comm k z]
  ring

theorem normalIndexDensity_smul (R : NormalMatrix) (y z : Fin 3 → ℝ) (ε : ℝ) :
    normalIndexDensity R (ε • y) (ε • z) = ε ^ 2 * normalIndexDensity R y z := by
  simp only [normalIndexDensity, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

theorem continuous_normalIndexDensity {R : ℝ → NormalMatrix}
    {y z : ℝ → Fin 3 → ℝ} (hR : Continuous R) (hy : Continuous y) (hz : Continuous z) :
    Continuous (fun s => normalIndexDensity (R s) (y s) (z s)) :=
  (hz.dotProduct hz).sub ((hR.matrix_mulVec hy).dotProduct hy)

theorem continuous_normalIndexPairing {R : ℝ → NormalMatrix}
    {y z h k : ℝ → Fin 3 → ℝ} (hR : Continuous R) (hy : Continuous y)
    (hz : Continuous z) (hh : Continuous h) (hk : Continuous k) :
    Continuous (fun s => normalIndexPairing (R s) (y s) (z s) (h s) (k s)) :=
  (hz.dotProduct hk).sub ((hR.matrix_mulVec hy).dotProduct hh)

theorem normalJacobi_mixed_pairing_hasDerivAt (R : NormalMatrix)
    (y z h k : ℝ → Fin 3 → ℝ) (s : ℝ)
    (hz : HasDerivAt z (-(R *ᵥ y s)) s) (hh : HasDerivAt h (k s) s) :
    HasDerivAt (fun r => z r ⬝ᵥ h r)
      (normalIndexPairing R (y s) (z s) (h s) (k s)) s := by
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_pi.mp hz i).mul (hasDerivAt_pi.mp hh i))
  have heq : (∑ i, ((-(R *ᵥ y s)) i * h s i + z s i * k s i)) =
      normalIndexPairing R (y s) (z s) (h s) (k s) := by
    rw [Finset.sum_add_distrib]
    change (-(R *ᵥ y s)) ⬝ᵥ h s + z s ⬝ᵥ k s =
      z s ⬝ᵥ k s - (R *ᵥ y s) ⬝ᵥ h s
    rw [neg_dotProduct]
    ring
  rw [heq] at hd
  simpa only [dotProduct, Pi.mul_apply] using hd

theorem MatrixJacobiSolution.index_pairing_integral {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (w : Fin 3 → ℝ)
    (h k : ℝ → Fin 3 → ℝ) (hh : ∀ s, HasDerivAt h (k s) s)
    (hk : Continuous k) (a b : ℝ) :
    (∫ s in a..b, normalIndexPairing (R s) (d.J s *ᵥ w) (d.V s *ᵥ w) (h s) (k s)) =
      (d.V b *ᵥ w) ⬝ᵥ h b - (d.V a *ᵥ w) ⬝ᵥ h a := by
  have hy : Continuous (fun s => d.J s *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun s => (d.field_position_hasDerivAt w s).continuousAt
  have hz : Continuous (fun s => d.V s *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun s => (d.field_velocity_hasDerivAt w s).continuousAt
  have hhcont : Continuous h :=
    continuous_iff_continuousAt.mpr fun s => (hh s).continuousAt
  have hint : IntervalIntegrable (fun s => normalIndexPairing (R s)
      (d.J s *ᵥ w) (d.V s *ᵥ w) (h s) (k s)) volume a b :=
    (continuous_normalIndexPairing hR hy hz hhcont hk).intervalIntegrable a b
  have hderiv (s : ℝ) : HasDerivAt (fun r => (d.V r *ᵥ w) ⬝ᵥ h r)
      (normalIndexPairing (R s) (d.J s *ᵥ w) (d.V s *ᵥ w) (h s) (k s)) s :=
    normalJacobi_mixed_pairing_hasDerivAt (R s)
      (fun r => d.J r *ᵥ w) (fun r => d.V r *ᵥ w) h k s
      (d.field_velocity_hasDerivAt w s) (hh s)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hint

theorem index_integral_sub_smul {R : ℝ → NormalMatrix}
    {y z h k : ℝ → Fin 3 → ℝ} (hR : Continuous R)
    (hsym : ∀ s, (R s).IsSymm) (hy : Continuous y) (hz : Continuous z)
    (hh : Continuous h) (hk : Continuous k) (ε a b : ℝ) :
    (∫ s in a..b, normalIndexDensity (R s) (y s - ε • h s) (z s - ε • k s)) =
      (∫ s in a..b, normalIndexDensity (R s) (y s) (z s)) -
        2 * ε * (∫ s in a..b, normalIndexPairing (R s) (y s) (z s) (h s) (k s)) +
        ε ^ 2 * (∫ s in a..b, normalIndexDensity (R s) (h s) (k s)) := by
  have hi : IntervalIntegrable (fun s => normalIndexDensity (R s) (y s) (z s)) volume a b :=
    (continuous_normalIndexDensity hR hy hz).intervalIntegrable a b
  have hm : IntervalIntegrable (fun s => normalIndexPairing (R s) (y s) (z s) (h s) (k s))
      volume a b := (continuous_normalIndexPairing hR hy hz hh hk).intervalIntegrable a b
  have hh' : IntervalIntegrable (fun s => normalIndexDensity (R s) (h s) (k s)) volume a b :=
    (continuous_normalIndexDensity hR hh hk).intervalIntegrable a b
  simp_rw [normalIndexDensity_sub_smul _ (hsym _) ]
  rw [intervalIntegral.integral_add (hi.sub (hm.const_mul _)) (hh'.const_mul _),
    intervalIntegral.integral_sub hi (hm.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The action on the two smooth pieces of the zero-extended conjugate field
minus the explicit endpoint bump. -/
def conjugateIndexAction {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε : ℝ) : ℝ :=
  let h := indexEndpointBump c b (d.V c *ᵥ w)
  let k := indexEndpointBumpDerivative c b (d.V c *ᵥ w)
  (∫ s in (0 : ℝ)..c, normalIndexDensity (R s) (d.J s *ᵥ w - ε • h s)
    (d.V s *ᵥ w - ε • k s)) +
  (∫ s in c..b, normalIndexDensity (R s) (-(ε • h s)) (-(ε • k s)))

end
end PositiveEinsteinFour.Jacobi

end


section

/-! Globally C1 extensions of the two smooth pieces of the conjugate-point
test field.  The extensions agree at the conjugate point, so a chart partition
can treat each side separately without differentiating at the corner. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

def conjugateLeftField {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε t : ℝ) : Fin 3 → ℝ :=
  d.J t *ᵥ w - ε • indexEndpointBump c b (d.V c *ᵥ w) t

def conjugateLeftRate {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε t : ℝ) : Fin 3 → ℝ :=
  d.V t *ᵥ w - ε • indexEndpointBumpDerivative c b (d.V c *ᵥ w) t

def conjugateRightField {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε t : ℝ) : Fin 3 → ℝ :=
  -(ε • indexEndpointBump c b (d.V c *ᵥ w) t)

def conjugateRightRate {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε t : ℝ) : Fin 3 → ℝ :=
  -(ε • indexEndpointBumpDerivative c b (d.V c *ᵥ w) t)

theorem conjugateLeftField_hasDerivAt {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε t : ℝ) :
    HasDerivAt (conjugateLeftField d w c b ε) (conjugateLeftRate d w c b ε t) t := by
  exact (d.field_position_hasDerivAt w t).sub
    ((indexEndpointBump_hasDerivAt c b (d.V c *ᵥ w) t).const_smul ε)

theorem conjugateRightField_hasDerivAt {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε t : ℝ) :
    HasDerivAt (conjugateRightField d w c b ε) (conjugateRightRate d w c b ε t) t := by
  exact ((indexEndpointBump_hasDerivAt c b (d.V c *ᵥ w) t).const_smul ε).neg

theorem conjugateLeftRate_continuous {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    Continuous (conjugateLeftRate d w c b ε) := by
  have hV : Continuous (fun t => d.V t *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun t => (d.field_velocity_hasDerivAt w t).continuousAt
  exact hV.sub ((indexEndpointBumpDerivative_continuous c b (d.V c *ᵥ w)).const_smul ε)

theorem conjugateRightRate_continuous {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    Continuous (conjugateRightRate d w c b ε) :=
  ((indexEndpointBumpDerivative_continuous c b (d.V c *ᵥ w)).const_smul ε).neg

theorem conjugateBranches_agree {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ)
    (hJ : d.J c *ᵥ w = 0) :
    conjugateLeftField d w c b ε c = conjugateRightField d w c b ε c := by
  simp only [conjugateLeftField, conjugateRightField, hJ, zero_sub]

end
end PositiveEinsteinFour.Jacobi
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The L⁴ Sobolev representative is the same actual base function as its L² representative of the intrinsic first-jet completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

local instance instFactLeENNRealOfNat_solutions_7 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong subcritical convergence for bounded intrinsic H¹ sequences,
using the actual manifold L² compactness and the L²/L⁴ interpolation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

local instance instFactLeENNRealOfNat_solutions_15 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual rational-test energy and the resulting L⁸ gain for the
subcritical minimizing scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal BigOperators

noncomputable section

local instance katoEnergy_four : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The closed nonnegative Hodge form on the actual H1 completion. Its
zero-energy space is the finite weak harmonic kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem linear_term_zero {a b : ℝ}
    (hb : 0 ≤ b) (h : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b) : a = 0 := by
  by_cases hzero : b = 0
  · have ht := h (-a)
    rw [hzero] at ht
    nlinarith [sq_nonneg a]
  · have hp : 0 < b := lt_of_le_of_ne hb (Ne.symm hzero)
    have he : 2 * (-a / b) * a + (-a / b) ^ 2 * b = -(a ^ 2 / b) := by
      field_simp
      ring
    have ht := h (-a / b)
    rw [he] at ht
    have hs : a ^ 2 ≤ 0 := by
      simpa using (div_le_iff₀ hp).mp (show a ^ 2 / b ≤ 0 by linarith)
    nlinarith [sq_nonneg a]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Vanishing lower-order signed traces for the actual normal-frame
connection and first heat amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heat_hodgeMatrix_symmetric : twoFormHodgeMatrixᵀ = twoFormHodgeMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [twoFormHodgeMatrix]

theorem heat_signed_skew_trace (A : HeatMat6) (hA : Aᵀ = -A) :
    (twoFormHodgeMatrix * A).trace = 0 := by
  have h : (twoFormHodgeMatrix * A).trace = -(twoFormHodgeMatrix * A).trace := by
    calc
      _ = (twoFormHodgeMatrix * A)ᵀ.trace := (Matrix.trace_transpose _).symm
      _ = _ := by
        rw [Matrix.transpose_mul, hA, heat_hodgeMatrix_symmetric, Matrix.neg_mul,
          Matrix.trace_neg, Matrix.trace_mul_comm]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior derivative of an actual smooth one-form is closed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem exterior_second_zero (X : CovariantCoordinates 3)
    (A : CovariantCoordinates 1) (R : Angular.CurvatureArray)
    (hX : ∀ i j k, X ![i,j,k] - X ![j,i,k] = -(∑ p, R i j k p * A ![p]))
    (hR : AlgebraicCurvature.FirstBianchi R) (i j k : Fin 4) :
    (X ![i,j,k] - X ![i,k,j]) - (X ![j,i,k] - X ![j,k,i]) +
      (X ![k,i,j] - X ![k,j,i]) = 0 := by
  have hB : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0 := hR
  have hc : (∑ p, R i j k p * A ![p]) + (∑ p, R j k i p * A ![p]) +
      (∑ p, R k i j p * A ![p]) = 0 := by
    calc
      _ = ∑ p, (R i j k p + R j k i p + R k i j p) * A ![p] := by
        simp only [add_mul, Finset.sum_add_distrib]
      _ = 0 := by simp only [hB, zero_mul, Finset.sum_const_zero]
  linarith only [hX i j k, hX j k i, hX k i j, hc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiation and radial integration commute with the fixed
Hodge-signed trace on the six-dimensional two-form fiber. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise Interval

noncomputable section

instance heatSignedTraceENorm : ENormedAddMonoid HeatMat6 :=
  @NormedAddGroup.toENormedAddMonoid HeatMat6
    (inferInstanceAs (NormedAddGroup HeatMat6))

def heatSignedTraceLinear : HeatMat6 →ₗ[ℝ] ℝ where
  toFun A := (twoFormHodgeMatrix * A).trace
  map_add' A B := by rw [Matrix.mul_add, Matrix.trace_add]
  map_smul' r A := by
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic codifferential density and the four-dimensional Hodge
splitting of the actual de Rham energy density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoFormCodiffTensor_squareNorm (A : CovariantCoordinates 3) :
    frameTensorSquareNorm (twoFormCodiffTensor A) =
      ∑ k, twoFormCodiffComponent (fun p q r => A ![p,q,r]) k ^ 2 := by
  unfold frameTensorSquareNorm frameTensorPairing
  rw [sum_tensor_indices_cons]
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro k _
  change (-∑ i, A ![i,i,k]) * (-∑ i, A ![i,i,k]) = (-∑ i, A ![i,i,k]) ^ 2
  ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! At the radial center, derivatives of the scalar metric weights do
not contribute to the quadratic connection trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_trace_product_expansion (H A B : HeatMat6) :
    (H * A * B).trace = ∑ k, ∑ l, ∑ q, H k l * (A l q * B q k) := by
  calc
    _ = (H * (A * B)).trace := congrArg Matrix.trace (Matrix.mul_assoc H A B)
    _ = _ := by simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Unit-norm Weyl curvature yields the parallel rank-one orthogonal
projector (W+ + I)/3. The polynomial relation comes from the actual
second derivative and Weyl equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
local instance projectorNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance projectorNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


