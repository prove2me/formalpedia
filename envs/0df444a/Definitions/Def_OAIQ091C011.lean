-- Prove2me | Definitions.Def_OAIQ091C011
-- name    : OAIQ091C011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:57:43.476583+00:00
-- url     : https://prove2.me/theorems/40e42840-0748-4803-a8a1-c0c33a4af4a4
-- title:
--   Definitions bundle OAIQ091C011 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 346 declarations of OpenAI's Lean: 92 definitions, 1 inductive type or structure, 2 instances and 251 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.blockTensorCoordinates`, `OAI.PositiveEinsteinFour.Geometry.complexAffineLift`, `OAI.PositiveEinsteinFour.Geometry.complexAffinePoint`, `OAI.PositiveEinsteinFour.Geometry.complexCutLift`, `OAI.PositiveEinsteinFour.Geometry.complexCutPoint`, `OAI.PositiveEinsteinFour.Geometry.complexGreatCircle`, `OAI.PositiveEinsteinFour.Geometry.complexGreatCircleUnit`, `OAI.PositiveEinsteinFour.Geometry.complexGreatCircleVelocity`, `OAI.PositiveEinsteinFour.Geometry.complexHeadTail`, `OAI.PositiveEinsteinFour.Geometry.complexHorizontalPart`, `OAI.PositiveEinsteinFour.Geometry.complexNormalize`, `OAI.PositiveEinsteinFour.Geometry.complexSphereProjection`, `OAI.PositiveEinsteinFour.Geometry.complexTailCLM`, `OAI.PositiveEinsteinFour.Geometry.complexTailLinear`, `OAI.PositiveEinsteinFour.Geometry.complexVectorAffine`, `OAI.PositiveEinsteinFour.Geometry.curvatureForm`, `OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedRing`, `OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedSpace`, `OAI.PositiveEinsteinFour.Geometry.curvatureInvariantFrobenius`, `OAI.PositiveEinsteinFour.Geometry.derivativeBasis`, `OAI.PositiveEinsteinFour.Geometry.directionalCurvatureMatrix`, `OAI.PositiveEinsteinFour.Geometry.directionalDerivativeTensor`, `OAI.PositiveEinsteinFour.Geometry.frameNormalFrobenius`, `OAI.PositiveEinsteinFour.Geometry.greenDataNormedRing`, `OAI.PositiveEinsteinFour.Geometry.greenDataNormedSpace`, `OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat`, `OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3`, `OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3_1`, `OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3_2`, `OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3_3`, `OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3_5`, `OAI.PositiveEinsteinFour.Geometry.instNormedSpaceRealMat`, `OAI.PositiveEinsteinFour.Geometry.instNormedSpaceRealMat3`, `OAI.PositiveEinsteinFour.Geometry.instNormedSpaceRealMat3_1`, `OAI.PositiveEinsteinFour.Geometry.matrixSlotAt`, `OAI.PositiveEinsteinFour.Geometry.minusIntegralNormedRing`, `OAI.PositiveEinsteinFour.Geometry.minusIntegralNormedSpace`, `OAI.PositiveEinsteinFour.Geometry.normEquationNormedAlgebra`, `OAI.PositiveEinsteinFour.Geometry.normEquationNormedRing`, `OAI.PositiveEinsteinFour.Geometry.normalChange` and 53 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_ActualJacobiODEDependence`, `EinsteinFour_AveragedRadial`, `EinsteinFour_AveragedVolume`, `EinsteinFour_CP2Overlap`, `EinsteinFour_CP2UnitGeometry`, `EinsteinFour_ComplexPairAlignment`, `EinsteinFour_ComplexProjectiveTriangle`, `EinsteinFour_ConditionalUnoriented`, `EinsteinFour_ContinuousRadialComparison`, `EinsteinFour_CurvatureForm`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_DirichletMatrix`, `EinsteinFour_FlatDirichletNormalizer`, `EinsteinFour_FrameAverages`, `EinsteinFour_FrameFlow`, `EinsteinFour_FrameRegularity`, `EinsteinFour_GeodesicGeometry04`, `EinsteinFour_GeodesicGeometry11`, `EinsteinFour_GeodesicGeometry12`, `EinsteinFour_GeodesicGeometry13`, `EinsteinFour_HessianCompression`, `EinsteinFour_HighestCoordinates`, `EinsteinFour_HighestMinusCoordinates`, `EinsteinFour_JacobiAverage`, `EinsteinFour_JacobiDensityMeasurability`, `EinsteinFour_JacobiMatrixLoss`, `EinsteinFour_JacobiRadialDeficit`, `EinsteinFour_JacobiRadialODE`, `EinsteinFour_JacobiRiemann`, `EinsteinFour_JacobiSineReference`, `EinsteinFour_MatrixGeodesicAverage`, `EinsteinFour_MatrixSlotOperator`, `EinsteinFour_ModeAverageLimit`, `EinsteinFour_RadialCoefficient`, `EinsteinFour_ScalarCompositionHessian`, `EinsteinFour_ScalarDirichlet`, `EinsteinFour_ScalarH2Closure`, `EinsteinFour_ScalarNormalizer`, `EinsteinFour_ScalarPoissonKernelContinuousEmbedding`, `EinsteinFour_ScalarRegularity06`, `EinsteinFour_ScalarRegularity07`, `EinsteinFour_SineModeLimit`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylGeometry`, `EinsteinFour_WeylNormal`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C000`, `OAIQ091C001`, `OAIQ091C002` and `OAIQ091C003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C015`, `OAIQ091C016` and `OAIQ091C051`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C000
import Definitions.Def_OAIQ091C001
import Definitions.Def_OAIQ091C002
import Definitions.Def_OAIQ091C003

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

/-- The ordered Schur pivots telescope at the determinant level even when
successive Jacobi matrices do not commute. -/
theorem determinant_pivot_product (Y : ℕ → NormalMatrix) (n : ℕ)
    (hY : ∀ i ≤ n, (Y i).det ≠ 0) :
    (∏ i ∈ Finset.range n, (Y (i + 1) * (Y i)⁻¹).det) =
      (Y n).det / (Y 0).det := by
  induction n with
  | zero => simp [hY 0 le_rfl]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih (fun i hi => hY i (Nat.le_succ_of_le hi)),
        Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      field_simp [hY n (Nat.le_succ n), hY 0 (Nat.zero_le _)]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarDirichlet
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive first mode of the scalar Dirichlet comparison matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem scalarDirichlet_isHermitian (N : ℕ) (d : ℝ) : (scalarDirichlet N d).IsHermitian := by
  ext i j
  change scalarDirichlet N d j i = scalarDirichlet N d i j
  simp only [scalarDirichlet, eq_comm]
  ring

/-- Positivity of the scalar reference follows from its first sine mode;
no diagonalization of the other sine modes is needed. -/
theorem scalarDirichlet_posDef (N : ℕ) (d : ℝ)
    (hfirst : 0 < d - 2 * Real.cos (firstSineAngle N)) :
    (scalarDirichlet N d).PosDef := by
  apply scalar_posDef_of_positive_mode _ (firstSineVector N)
    (d - 2 * Real.cos (firstSineAngle N)) (scalarDirichlet_isHermitian N d)
    ?_ (firstSineVector_pos N) hfirst (firstSineVector_eigenvector N d)
  intro i j hij
  simp only [scalarDirichlet, ite_eq_right hij, zero_sub]
  split_ifs <;> norm_num

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarNormalizer
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive scalar normalizer used in finite radial compression. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix
open scoped MatrixOrder

noncomputable section

/-- The normalizer acts by the reciprocal square root on the prescribed
positive scalar eigenmode. -/
theorem scalarNormalizer_eigenvector {N : ℕ}
    {L : Matrix (Fin N) (Fin N) ℝ} (hL : L.PosDef)
    {w : Fin N → ℝ} {lam : ℝ} (hlam : 0 < lam) (heigen : L *ᵥ w = lam • w) :
    scalarNormalizer L *ᵥ w = (1 / Real.sqrt lam) • w := by
  have hi : L⁻¹ *ᵥ w = (1 / lam) • w := by
    have h := congrArg (fun x => L⁻¹ *ᵥ x) heigen
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hL.isUnit),
      Matrix.one_mulVec, Matrix.mulVec_smul] at h
    calc
      _ = (1 / lam) • (lam • (L⁻¹ *ᵥ w)) := by
        rw [smul_smul, one_div_mul_cancel hlam.ne', one_smul]
      _ = _ := by rw [← h]
  apply positive_square_root_eigenvector (scalarNormalizer_posSemidef L)
    (one_div_pos.mpr (Real.sqrt_pos.mpr hlam))
  rw [scalarNormalizer_square hL, hi]
  congr 1
  rw [div_pow, one_pow, Real.sq_sqrt hlam.le]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SineModeLimit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first scalar Dirichlet eigenvalue and its radial comparison limit. -/

namespace PositiveEinsteinFour.Jacobi

open Filter _root_.Topology

noncomputable section

theorem firstEigenvalue_eventually_pos {t : ℝ} (ht : 0 ≤ t) (htπ : t < Real.pi) :
    ∀ᶠ N : ℕ in atTop, 0 < firstEigenvalue t N := by
  have hlim : 0 < Real.pi ^ 2 - t ^ 2 := by nlinarith [Real.pi_pos]
  filter_upwards [(scaledFirstEigenvalue_tendsto t).eventually (eventually_gt_nhds hlim)] with N hN
  have hsq : 0 < ((N : ℝ) + 1) ^ 2 := by positivity
  exact (mul_pos_iff_of_pos_left hsq).mp hN

theorem first_mode_coefficient_tendsto {t : ℝ} (ht : 0 ≤ t) (htπ : t < Real.pi) :
    Tendsto (fun N : ℕ => (t / (N + 1)) ^ 2 / firstEigenvalue t N)
      atTop (𝓝 (t ^ 2 / (Real.pi ^ 2 - t ^ 2))) := by
  have hne : Real.pi ^ 2 - t ^ 2 ≠ 0 := by nlinarith [Real.pi_pos]
  have h := (tendsto_const_nhds (x := t ^ 2)).div (scaledFirstEigenvalue_tendsto t) hne
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  unfold scaledFirstEigenvalue
  simp only [div_pow, div_div]
  rfl

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualJacobiODEDependence
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness and continuous parameter dependence for the bounded linear
equation used by the actual Jacobi fields. -/

namespace PositiveEinsteinFour.Jacobi

open Set Filter Metric
open scoped _root_.Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem global_linear_solution_unique (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) {γ η : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (A t (γ t)) t)
    (hη : ∀ t, HasDerivAt η (A t (η t)) t) (h0 : γ 0 = η 0) : γ = η := by
  funext t
  let r := |t| + 1
  have hr : 0 < r := by dsimp [r]; positivity
  exact linear_curve_eqOn_interval A K hK (fun s _ => hγ s) (fun s _ => hη s)
    (t := 0) ⟨by linarith, hr⟩ h0 (abs_lt.mp (lt_add_one |t|))

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiAverage
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace and curvature bounds for the concrete sine-weighted average. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

local instance instNormedAddCommGroupNormalMatrix : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup

instance matrixContinuousENorm_p1 : ContinuousENorm NormalMatrix :=
  @SeminormedAddGroup.toContinuousENorm NormalMatrix
    (inferInstanceAs (SeminormedAddGroup NormalMatrix))

def quadraticCLM (x : Fin 3 → ℝ) : NormalMatrix →L[ℝ] ℝ :=
  ∑ i, ∑ j, (x i * x j) • entryCLM i j

theorem quadraticCLM_apply (x : Fin 3 → ℝ) (A : NormalMatrix) :
    quadraticCLM x A = star x ⬝ᵥ (A *ᵥ x) := by
  simp only [quadraticCLM, _root_.sum_apply, _root_.smul_apply,
    entryCLM_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def traceCLM : NormalMatrix →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap

theorem integral_sine_posSemidef {A : ℝ → NormalMatrix}
    (hi : Integrable A Averages.sineMeasure) (hpos : ∀ s, (A s).PosSemidef) :
    (∫ s, A s ∂Averages.sineMeasure).PosSemidef := by
  have he (i j : Fin 3) :
      (∫ s, A s ∂Averages.sineMeasure) i j = ∫ s, A s i j ∂Averages.sineMeasure := by
    have h := (entryCLM i j).integral_comp_comm hi
    exact h.symm
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    change (∫ s, A s ∂Averages.sineMeasure) j i =
      (∫ s, A s ∂Averages.sineMeasure) i j
    rw [he, he]
    apply integral_congr_ae
    filter_upwards [] with s
    exact congrFun (congrFun (hpos s).isHermitian.eq i) j
  · intro x
    rw [← quadraticCLM_apply]
    calc
      0 ≤ ∫ s, quadraticCLM x (A s) ∂Averages.sineMeasure := by
        apply integral_nonneg
        intro s
        change 0 ≤ quadraticCLM x (A s)
        rw [quadraticCLM_apply]
        exact (hpos s).dotProduct_mulVec_nonneg x
      _ = quadraticCLM x (∫ s, A s ∂Averages.sineMeasure) :=
        (quadraticCLM x).integral_comp_comm hi

theorem sine_average_trace {A : ℝ → NormalMatrix} (hA : Continuous A)
    (htrace : ∀ s, (A s).trace = 0) :
    (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s).trace = 0 := by
  rw [← Averages.integral_sineMeasure A]
  have h := traceCLM.integral_comp_comm (Averages.integrable_sineMeasure hA)
  change (∫ s, (A s).trace ∂Averages.sineMeasure) =
    (∫ s, A s ∂Averages.sineMeasure).trace at h
  simpa only [htrace, integral_zero] using h.symm

/-- Averaging preserves the lower normal-curvature bound. -/
theorem sine_average_add_one_posSemidef {A : ℝ → NormalMatrix} (hA : Continuous A)
    (hpos : ∀ s, (A s + 1).PosSemidef) :
    ((∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s) + 1).PosSemidef := by
  have hp := integral_sine_posSemidef
    ((Averages.integrable_sineMeasure hA).add (integrable_const 1)) hpos
  change (∫ s, (A s + 1) ∂Averages.sineMeasure).PosSemidef at hp
  rw [integral_add (Averages.integrable_sineMeasure hA) (integrable_const 1),
    integral_const] at hp
  simpa only [probReal_univ, one_smul, Averages.integral_sineMeasure] using hp

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiMatrixLoss
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar determinant deficit applied to the actual symmetric matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

theorem trace_unitary_conj (U : Matrix.unitaryGroup (Fin 3) ℝ) (A : NormalMatrix) :
    (Unitary.conjStarAlgAut ℝ NormalMatrix U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem det_unitary_conj (U : Matrix.unitaryGroup (Fin 3) ℝ) (A : NormalMatrix) :
    (Unitary.conjStarAlgAut ℝ NormalMatrix U A).det = A.det := by
  have hU := congrArg Matrix.det (Unitary.coe_star_mul_self U)
  simp only [Matrix.det_mul, Matrix.det_one] at hU
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = ((star U : NormalMatrix).det * (U : NormalMatrix).det) * A.det := by ring
    _ = A.det := by rw [hU, one_mul]

theorem posSemidef_unitary_conj (U : Matrix.unitaryGroup (Fin 3) ℝ)
    {A : NormalMatrix} (hA : A.PosSemidef) :
    (Unitary.conjStarAlgAut ℝ NormalMatrix U A).PosSemidef := by
  have h := hA.conjTranspose_mul_mul_same (star (U : NormalMatrix))
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using h

theorem frobenius_sq_eq_trace_square {A : NormalMatrix} (hA : A.IsHermitian) :
    ‖A‖ ^ 2 = (A * A).trace := by
  have hs (i j : Fin 3) : A j i = A i j := by
    have h := congrFun (congrFun hA.eq i) j
    exact h
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs, pow_two]

/-- The concrete Frobenius norm is the sum of the three eigenvalue squares. -/
theorem frobenius_sq_eq_sum_eigenvalues {A : NormalMatrix} (hA : A.IsHermitian) :
    ‖A‖ ^ 2 = ∑ i, (hA.eigenvalues i) ^ 2 := by
  let φ := Unitary.conjStarAlgAut ℝ NormalMatrix (star hA.eigenvectorUnitary)
  have hd : φ A = diagonal hA.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [frobenius_sq_eq_trace_square hA]
  calc
    (A * A).trace = (φ (A * A)).trace :=
      (trace_unitary_conj (star hA.eigenvectorUnitary) (A * A)).symm
    _ = (diagonal hA.eigenvalues * diagonal hA.eigenvalues).trace := by rw [map_mul, hd]
    _ = ∑ i, hA.eigenvalues i ^ 2 := by simp [Matrix.diagonal_mul_diagonal, pow_two]

/-- Matrix form of the preconjugate determinant loss. The two semidefinite
hypotheses are exactly the lower curvature bound and the first-mode compression. -/
theorem matrix_preconjugate_loss {A : NormalMatrix} {β : ℝ} (hA : A.IsHermitian)
    (hβ : 0 ≤ β) (htrace : A.trace = 0)
    (hlower : (A + 1).PosSemidef) (hupper : (1 - β • A).PosSemidef) :
    (1 - β • A).det ≤ 1 - lossFactor β / 6 * ‖A‖ ^ 2 := by
  let φ := Unitary.conjStarAlgAut ℝ NormalMatrix (star hA.eigenvectorUnitary)
  let e := hA.eigenvalues
  have hd : φ A = diagonal e := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hlo := posSemidef_unitary_conj (star hA.eigenvectorUnitary) hlower
  have hup := posSemidef_unitary_conj (star hA.eigenvectorUnitary) hupper
  change (φ (A + 1)).PosSemidef at hlo
  change (φ (1 - β • A)).PosSemidef at hup
  have hdiaglo : φ (A + 1) = diagonal (fun i => e i + 1) := by
    rw [map_add, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hdiagup : φ (1 - β • A) = diagonal (fun i => 1 - β * e i) := by
    rw [map_sub, map_one, map_smul, hd]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.smul_apply, smul_eq_mul, hij]
  rw [hdiaglo, Matrix.posSemidef_diagonal_iff] at hlo
  rw [hdiagup, Matrix.posSemidef_diagonal_iff] at hup
  have htr : e 0 + e 1 + e 2 = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    simpa [Fin.sum_univ_succ, htrace, e, add_assoc] using h.symm
  have hn : ‖A‖ ^ 2 = e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 := by
    simpa [Fin.sum_univ_succ, e, add_assoc] using frobenius_sq_eq_sum_eigenvalues hA
  have hdet : (1 - β • A).det = (1 - β * e 0) * (1 - β * e 1) * (1 - β * e 2) := by
    rw [← det_unitary_conj (star hA.eigenvectorUnitary) (1 - β • A)]
    change (φ (1 - β • A)).det = _
    rw [hdiagup, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ, mul_assoc]
  have hloss := preconjugate_loss hβ htr (by linarith [hlo 0])
    (by linarith [hlo 1]) (by linarith [hlo 2]) (by linarith [hup 0])
    (by linarith [hup 1]) (by linarith [hup 2])
  rw [hn, hdet]
  unfold loss at hloss
  linarith

/-- The positive curvature lower bound and trace normalization also control
the postconjugate branch, where radial density is set to zero. -/
theorem matrix_postconjugate_loss {A : NormalMatrix} (hA : A.IsHermitian)
    (β : ℝ) (htrace : A.trace = 0) (hlower : (A + 1).PosSemidef) :
    lossFactor β / 6 * ‖A‖ ^ 2 ≤ 1 := by
  let φ := Unitary.conjStarAlgAut ℝ NormalMatrix (star hA.eigenvectorUnitary)
  let e := hA.eigenvalues
  have hd : φ A = diagonal e := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hlo := posSemidef_unitary_conj (star hA.eigenvectorUnitary) hlower
  change (φ (A + 1)).PosSemidef at hlo
  have hdiaglo : φ (A + 1) = diagonal (fun i => e i + 1) := by
    rw [map_add, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hdiaglo, Matrix.posSemidef_diagonal_iff] at hlo
  have htr : e 0 + e 1 + e 2 = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    simpa [Fin.sum_univ_succ, htrace, e, add_assoc] using h.symm
  have hn : ‖A‖ ^ 2 = e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 := by
    simpa [Fin.sum_univ_succ, e, add_assoc] using frobenius_sq_eq_sum_eigenvalues hA
  rw [hn]
  exact postconjugate_loss htr
    ⟨by linarith [hlo 0], by linarith [hlo 1, hlo 2]⟩
    ⟨by linarith [hlo 1], by linarith [hlo 0, hlo 2]⟩
    ⟨by linarith [hlo 2], by linarith [hlo 0, hlo 1]⟩

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiRiemann
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative Riemann sums for the smooth matrix curves in the radial comparison. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniform_mesh_remainder {F f : ℝ → E} {h L : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hF : ∀ s, HasDerivAt F (f s) s)
    (hf : ∀ s t, ‖f s - f t‖ ≤ L * |s - t|) (N : ℕ) :
    ‖F (N * h) - F 0 - h • (∑ i ∈ Finset.range N, f (i * h))‖ ≤ N * L * h ^ 2 := by
  have htel : ∑ i ∈ Finset.range N, (F ((i + 1) * h) - F (i * h)) = F (N * h) - F 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        abel
  have hid : F (N * h) - F 0 - h • (∑ i ∈ Finset.range N, f (i * h)) =
      ∑ i ∈ Finset.range N, (F ((i + 1) * h) - F (i * h) - h • f (i * h)) := by
    rw [Finset.sum_sub_distrib, htel, Finset.smul_sum]
  rw [hid]
  calc
    _ ≤ ∑ i ∈ Finset.range N, ‖F ((i + 1) * h) - F (i * h) - h • f (i * h)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range N, L * h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hb := first_order_remainder hh hL (a := i * h) (f := F) (d := f)
        (fun s _ => hF s) (fun s hs => by
          simpa only [abs_of_nonneg (sub_nonneg.mpr hs.1)] using hf s (i * h))
      simpa only [add_mul, one_mul] using hb
    _ = _ := by simp [mul_assoc]

theorem uniform_mesh_tendsto_antiderivative {F f : ℝ → E} {t L : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hF : ∀ s, HasDerivAt F (f s) s)
    (hf : ∀ s r, ‖f s - f r‖ ≤ L * |s - r|) :
    Tendsto (fun N : ℕ => (t / N) • (∑ i ∈ Finset.range N, f (i * (t / N)) ))
      atTop (nhds (F t - F 0)) := by
  apply (converges_of_inverse_mesh_error (v := fun _ => (0 : E)) (V := 0)
    (C := L * t ^ 2) ?_).1
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hb := uniform_mesh_remainder (div_nonneg ht (Nat.cast_nonneg N)) hL hF hf N
  have hid : (N : ℝ) * (t / N) = t := by field_simp
  rw [hid, norm_sub_rev] at hb
  simpa only [sub_zero, norm_zero, add_zero, show (N : ℝ) * L * (t / N) ^ 2 =
    L * t ^ 2 / N by field_simp] using hb

variable [CompleteSpace E]

/-- The left mesh sums converge to the actual interval integral. -/
theorem uniform_mesh_tendsto_integral {f : ℝ → E} {t L : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L) (hc : Continuous f)
    (hf : ∀ s r, ‖f s - f r‖ ≤ L * |s - r|) :
    Tendsto (fun N : ℕ => (t / N) • (∑ i ∈ Finset.range N, f (i * (t / N))))
      atTop (nhds (∫ s in (0 : ℝ)..t, f s)) := by
  have hF : ∀ s, HasDerivAt (fun r => ∫ u in (0 : ℝ)..r, f u) (f s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [intervalIntegral.integral_same, sub_zero] using
    uniform_mesh_tendsto_antiderivative ht hL hF hf

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ModeAverageLimit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of the normalized scalar-mode curvature average. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem interiorMean_tendsto {f : ℝ → E} {L : ℝ}
    (hL : 0 ≤ L) (hc : Continuous f) (hf0 : f 0 = 0)
    (hf : ∀ s r, ‖f s - f r‖ ≤ L * |s - r|) :
    Tendsto (interiorMean f) atTop (nhds (∫ s in (0 : ℝ)..1, f s)) := by
  have hs (N : ℕ) : (∑ i : Fin N, f ((i.val + 1) / ((N : ℝ) + 1))) =
      ∑ i ∈ Finset.range (N + 1), f ((i : ℝ) / ((N : ℝ) + 1)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, hf0, add_zero]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => f (((i : ℝ) + 1) / ((N : ℝ) + 1))) N)
  have h := (uniform_mesh_tendsto_integral (by norm_num : (0 : ℝ) ≤ 1) hL hc hf).comp
    (show Tendsto (fun N : ℕ => N + 1) atTop atTop from tendsto_add_atTop_nat 1)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  rw [interiorMean, hs]
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul]

theorem sineWeight_at_node (N : ℕ) (i : Fin N) :
    Averages.sineWeight ((i.val + 1) / ((N : ℝ) + 1)) = 2 * firstSineVector N i ^ 2 := by
  rw [Averages.sineWeight_eq]
  change 2 * Real.sin (Real.pi * ((i.val + 1) / ((N : ℝ) + 1))) ^ 2 =
    2 * Real.sin (((i.val : ℝ) + 1) * (Real.pi / ((N : ℝ) + 1))) ^ 2
  congr 1
  apply congrArg (fun z : ℝ => Real.sin z ^ 2)
  ring

def modeAverage (A : ℝ → E) (N : ℕ) : E :=
  ∑ i : Fin N, unitFirstSineVector N i ^ 2 • A ((i.val + 1) / ((N : ℝ) + 1))

omit [CompleteSpace E] in
theorem modeAverage_eq_ratio (A : ℝ → E) {N : ℕ} (hN : 0 < N) :
    modeAverage A N =
      (interiorMean Averages.sineWeight N)⁻¹ •
        interiorMean (fun s => Averages.sineWeight s • A s) N := by
  have hs : 0 < firstSineNormSq N := firstSineNormSq_pos hN
  have hM : (N : ℝ) + 1 ≠ 0 := by positivity
  have hd : interiorMean Averages.sineWeight N =
      (2 / ((N : ℝ) + 1)) * firstSineNormSq N := by
    simp only [interiorMean, sineWeight_at_node, smul_eq_mul, ← Finset.mul_sum]
    change (1 / ((N : ℝ) + 1)) * (2 * firstSineNormSq N) = _
    ring
  have hu : interiorMean (fun s => Averages.sineWeight s • A s) N =
      (2 / ((N : ℝ) + 1)) •
        (∑ i : Fin N, firstSineVector N i ^ 2 • A ((i.val + 1) / ((N : ℝ) + 1))) := by
    simp only [interiorMean, sineWeight_at_node, mul_smul]
    rw [← Finset.smul_sum, smul_smul]
    congr 1
    ring
  have hm : modeAverage A N = (1 / firstSineNormSq N) •
      (∑ i : Fin N, firstSineVector N i ^ 2 • A ((i.val + 1) / ((N : ℝ) + 1))) := by
    unfold modeAverage unitFirstSineVector
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mul_smul,
      div_pow, one_pow, Real.sq_sqrt hs.le]
    rw [← Finset.smul_sum]
  rw [hm, hd, hu, smul_smul]
  congr 1
  field_simp [hM, hs.ne']

/-- The normalized discrete sine mode converges to the actual sine-weighted
integral. Only regularity of the weighted curvature curve is used. -/
theorem modeAverage_tendsto {A : ℝ → E} {L : ℝ}
    (hL : 0 ≤ L) (hc : Continuous (fun s => Averages.sineWeight s • A s))
    (hLip : ∀ s r, ‖Averages.sineWeight s • A s - Averages.sineWeight r • A r‖ ≤
      L * |s - r|) :
    Tendsto (modeAverage A) atTop
      (nhds (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s)) := by
  have hwc : Continuous Averages.sineWeight := by
    unfold Averages.sineWeight
    fun_prop
  have hw0 : Averages.sineWeight 0 = 0 := by simp [Averages.sineWeight]
  have hd : Tendsto (interiorMean Averages.sineWeight) atTop (nhds 1) := by
    simpa only [Averages.integral_sineWeight] using
      interiorMean_tendsto (by positivity : 0 ≤ 2 * Real.pi) hwc hw0 sineWeight_lipschitz
  have hn := interiorMean_tendsto hL hc (by simp only [hw0, zero_smul]) hLip
  have hquot := (hd.inv₀ one_ne_zero).smul hn
  simp only [inv_one, one_smul] at hquot
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (modeAverage_eq_ratio A hN).symm

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ContinuousRadialComparison
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the actual first-mode Dirichlet comparison to the radial limit. -/

namespace PositiveEinsteinFour.Jacobi

open Filter
open scoped Matrix.Norms.Frobenius

noncomputable section

def sampledCurvature (A : ℝ → NormalMatrix) (N : ℕ) : Fin N → NormalMatrix :=
  fun i => A ((i.val + 1) / ((N : ℝ) + 1))

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSineReference
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference determinant limit is instantiated by the sine Jacobi curve. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

def sineJacobi (t : ℝ) : RegularJacobi t where
  R := fun _ => 1
  J := fun s => Real.sin s • 1
  V := fun s => Real.cos s • 1
  K := 1
  Lx := 1
  Lv := 1
  F := 1
  K_nonneg := zero_le_one
  Lx_nonneg := zero_le_one
  Lv_nonneg := zero_le_one
  F_nonneg := zero_le_one
  initial_position := by simp
  initial_velocity := by simp
  symmetric := by intro s; simp
  curvature_bound := by intro s hs; simp
  position_derivative := by
    intro s hs
    exact (Real.hasDerivAt_sin s).smul_const (1 : NormalMatrix)
  velocity_derivative := by
    intro s hs
    simpa only [one_mul, neg_smul] using
      (Real.hasDerivAt_cos s).smul_const (1 : NormalMatrix)
  velocity_lipschitz := by
    intro s hs r hr
    simpa only [← sub_smul, norm_smul, norm_one, mul_one, one_mul, Real.norm_eq_abs]
      using Real.abs_cos_sub_cos_le s r
  acceleration_lipschitz := by
    intro s hs r hr
    calc
      ‖-((1 : NormalMatrix) * (Real.sin s • 1)) - -(1 * (Real.sin r • 1))‖ =
          ‖(Real.sin s - Real.sin r) • (1 : NormalMatrix)‖ := by
            rw [one_mul, one_mul, neg_sub_neg, norm_sub_rev, sub_smul]
      _ ≤ 1 * |s - r| := by
        simpa only [norm_smul, norm_one, mul_one, one_mul, Real.norm_eq_abs] using
          Real.abs_sin_sub_sin_le s r
  force_bound := by
    intro s hs
    simpa only [one_mul, norm_smul, norm_one, mul_one, Real.norm_eq_abs] using
      Real.abs_sin_le_one s

theorem sineJacobi_preconjugate {t : ℝ} (htπ : t < Real.pi) :
    ∀ s, 0 < s → s ≤ t → IsUnit ((sineJacobi t).J s) := by
  intro s hs hst
  have hu : IsUnit (Real.sin s) :=
    isUnit_iff_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hs (hst.trans_lt htπ)).ne'
  simpa only [sineJacobi, Algebra.algebraMap_eq_smul_one] using
    hu.map (algebraMap ℝ NormalMatrix)

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiRadialODE
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial determinant comparison from the Jacobi ODE. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

def radialCurvature (R : ℝ → NormalMatrix) (t s : ℝ) : NormalMatrix := R (s * t) - 1

theorem sampled_radialCurvature (R : ℝ → NormalMatrix) (t : ℝ) (N : ℕ) :
    sampledCurvature (radialCurvature R t) N = fun i : Fin N =>
      R (((i.val + 1 : ℕ) : ℝ) * meshStep t N) - 1 := by
  funext i
  dsimp [sampledCurvature, radialCurvature, meshStep]
  rw [Nat.cast_add, Nat.cast_one]
  congr 2
  ring

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiRadialDeficit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative radial deficit before the first conjugate point. -/

namespace PositiveEinsteinFour.Jacobi.RegularJacobi

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

variable {t : ℝ} (d : RegularJacobi t)

/-- After conjugacy the truncated radial density is zero. The same upper
bound stays nonnegative from the curvature range alone. -/
theorem radial_deficit_nonneg (ht : 0 ≤ t) (htπ : t < Real.pi)
    (hR : Continuous d.R) (hRpos : ∀ s, (d.R s).PosSemidef)
    (htrace : ∀ s, (d.R s).trace = 3) :
    0 ≤ Real.sin t ^ 3 *
      (1 - lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6 *
        ‖∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s‖ ^ 2) := by
  let A := radialCurvature d.R t
  let B : NormalMatrix := ∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s
  have hA : Continuous A := (hR.comp (continuous_id.mul_const t)).sub continuous_const
  have hAt : ∀ s, (A s).trace = 0 := fun s => by
    simp [A, radialCurvature, Matrix.trace_sub, htrace]
  have hAp : ∀ s, (A s + 1).PosSemidef := fun s => by
    simpa only [A, radialCurvature, sub_add_cancel] using hRpos (s * t)
  have hBt : B.trace = 0 := sine_average_trace hA hAt
  have hBp : (B + 1).PosSemidef := sine_average_add_one_posSemidef hA hAp
  have hBh : B.IsHermitian := by
    simpa only [add_sub_cancel_right] using hBp.isHermitian.sub (isHermitian_one :
      (1 : NormalMatrix).IsHermitian)
  have hl := matrix_postconjugate_loss hBh
    (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) hBt hBp
  exact mul_nonneg (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht htπ.le) 3)
    (sub_nonneg.mpr hl)

end

end PositiveEinsteinFour.Jacobi.RegularJacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixGeodesicAverage
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Specialization of mean-square geodesic averaging to actual normal
curvature matrices, using their Frobenius norm. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

local instance instNormedAddCommGroupNormalMatrix_1 : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup

local instance instNormedSpaceRealNormalMatrix : NormedSpace ℝ NormalMatrix := Matrix.frobeniusNormedSpace

instance matrixContinuousENorm_p3 : ContinuousENorm NormalMatrix :=
  @SeminormedAddGroup.toContinuousENorm NormalMatrix
    (inferInstanceAs (SeminormedAddGroup NormalMatrix))

/-- Entry coordinates preserve the Frobenius norm exactly. -/
def matrixVector : NormalMatrix →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3 × Fin 3) where
  toLinearMap :=
    { toFun := fun A => WithLp.toLp 2 (fun ij => A ij.1 ij.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' A := by
    change ‖(WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 => A ij.1 ij.2) :
      EuclideanSpace ℝ (Fin 3 × Fin 3))‖ = ‖A‖
    simp only [EuclideanSpace.norm_eq, Fintype.sum_prod_type,
      Matrix.frobenius_norm_def, Real.rpow_two, Real.sqrt_eq_rpow]

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

local instance instNormedAddCommGroupContinuousMapNormalMatrix : NormedAddCommGroup C(Ω, NormalMatrix) :=
  ContinuousMap.instNormedAddCommGroup

local instance instNormedSpaceRealContinuousMapNormalMatrix : NormedSpace ℝ C(Ω, NormalMatrix) := ContinuousMap.normedSpace

/-- The matrix form of the averaging theorem used by the radial comparison.
The derivative is a derivative of the continuous curvature field, so its
energy is measured over all initial geodesics. -/
theorem matrix_geodesic_mean_square_lower {F G : ℝ → C(Ω, NormalMatrix)} {q t : ℝ}
    (hq : 0 ≤ q)
    (hderiv : ∀ r, HasDerivAt F (G r) r)
    (hstationary : ∀ r, (∫ x, ‖F r x‖ ^ 2 ∂μ) = q)
    (henergy : ∀ r, (∫ x, ‖G r x‖ ^ 2 ∂μ) ≤ (3 / 2) * q) :
    q * (1 - (t / Real.pi) ^ 2 / 2) ≤
      ∫ x, ‖∫ u, F (t * u) x ∂Averages.sineMeasure‖ ^ 2 ∂μ := by
  let T := matrixVector.toContinuousLinearMap.compLeftContinuous ℝ Ω
  have hd (r : ℝ) : HasDerivAt (fun r => T (F r)) (T (G r)) r :=
    T.hasFDerivAt.comp_hasDerivAt r (hderiv r)
  have hs (r : ℝ) : (∫ x, ‖T (F r) x‖ ^ 2 ∂μ) = q := by
    change (∫ x, ‖matrixVector (F r x)‖ ^ 2 ∂μ) = q
    simpa only [matrixVector.norm_map] using hstationary r
  have he (r : ℝ) : (∫ x, ‖T (G r) x‖ ^ 2 ∂μ) ≤ (3 / 2) * q := by
    change (∫ x, ‖matrixVector (G r x)‖ ^ 2 ∂μ) ≤ (3 / 2) * q
    simpa only [matrixVector.norm_map] using henergy r
  have h := Averages.geodesic_mean_square_lower hq hd hs he (t := t)
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun r =>
    HasDerivAt.continuousAt (F := C(Ω, NormalMatrix)) (hderiv r)
  have hc : Continuous (fun u => F (t * u)) :=
    hF.comp (continuous_const.mul continuous_id)
  have hi (x : Ω) : Integrable (fun u => F (t * u) x) Averages.sineMeasure :=
    Averages.integrable_sineMeasure ((ContinuousMap.evalCLM ℝ x).continuous.comp hc)
  have hn (x : Ω) :
      ‖∫ u, T (F (t * u)) x ∂Averages.sineMeasure‖ =
      ‖∫ u, F (t * u) x ∂Averages.sineMeasure‖ := by
    change ‖∫ u, matrixVector.toContinuousLinearMap (F (t * u) x)
      ∂Averages.sineMeasure‖ = _
    rw [matrixVector.toContinuousLinearMap.integral_comp_comm (hi x)]
    exact matrixVector.norm_map _
  simpa only [hn] using h

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AveragedRadial
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the proved Jacobi determinant deficit over initial geodesics.
The density is explicitly truncated at the first conjugate point. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

local instance instNormedAddCommGroupNormalMatrix_2 : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup

local instance instNormedSpaceRealNormalMatrix_1 : NormedSpace ℝ NormalMatrix := Matrix.frobeniusNormedSpace

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

local instance instNormedAddCommGroupContinuousMapNormalMatrix_1 : NormedAddCommGroup C(Ω, NormalMatrix) :=
  ContinuousMap.instNormedAddCommGroup

local instance instNormedSpaceRealContinuousMapNormalMatrix_1 : NormedSpace ℝ C(Ω, NormalMatrix) := ContinuousMap.normedSpace

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RadialCoefficient
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the piecewise polynomial integration weight with the exact
Jacobi determinant-loss coefficient. The variable is `u = t / pi`. -/

namespace PositiveEinsteinFour.Jacobi

open VolumeConstants

noncomputable section

/-- The full piecewise lower weight is valid on the preconjugate radial
interval. Its jump at `5/8` is intentional and included in the proof. -/
theorem radialLower_le_lossFactor {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    radialLower u ≤ lossFactor (u ^ 2 / (1 - u ^ 2)) := by
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  by_cases hh : u ≤ 5 / 8
  · rw [radialLower, ite_eq_left hh]
    have h := small_parameter_bound (sq_nonneg u) (by nlinarith [sq_nonneg (u - 5 / 8)])
    have hid : initialFactor u = (u ^ 2) ^ 2 * (3 + 5 * u ^ 2 + 6 * (u ^ 2) ^ 2) := by
      unfold initialFactor
      ring
    rwa [hid]
  · rw [radialLower, ite_eq_right hh]
    apply large_parameter_bound
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg (u - 5 / 8)]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AveragedVolume
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The volume deficit follows from the averaged Jacobi bound and the polar
volume formula. All numerical constants and integration weights are proved. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory VolumeConstants

noncomputable section

/-- Replace the exact determinant coefficient by the explicit integrable
piecewise lower bound used in the volume estimate. -/
theorem averaged_radial_piecewise_bound {D s u : ℝ}
    (hu : 0 ≤ u) (hu1 : u < 1) (hs : 0 ≤ s)
    (hD : D ≤ Real.sin (Real.pi * u) ^ 3 *
      (1 - lossFactor ((Real.pi * u) ^ 2 /
        (Real.pi ^ 2 - (Real.pi * u) ^ 2)) / 6 *
        ((3 / 2) * s) * (1 - ((Real.pi * u) / Real.pi) ^ 2 / 2))) :
    D ≤ Real.sin (Real.pi * u) ^ 3 *
      (1 - radialLower u * s * (1 - u ^ 2 / 2) / 4) := by
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have hid : (Real.pi * u) ^ 2 / (Real.pi ^ 2 - (Real.pi * u) ^ 2) =
      u ^ 2 / (1 - u ^ 2) := by
    field_simp [Real.pi_ne_zero, ne_of_gt hden]
  have htime : (Real.pi * u) / Real.pi = u := by
    field_simp [Real.pi_ne_zero]
  rw [hid, htime] at hD
  have hc := radialLower_le_lossFactor hu hu1
  have hw : 0 ≤ s * (1 - u ^ 2 / 2) := by
    apply mul_nonneg hs
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hc hw
  have hsin : 0 ≤ Real.sin (Real.pi * u) ^ 3 := by
    apply pow_nonneg
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hscaled := mul_le_mul_of_nonneg_left hmul hsin
  nlinarith only [hD, hscaled]

/-- The upper-volume estimate with the averaged radial determinant bound.
The only volume premise is the classical polar integration upper bound;
the sharp deficit coefficient is derived here. -/
theorem volume_ratio_upper_of_averaged_radial {D : ℝ → ℝ} {V s : ℝ}
    (hs : 0 ≤ s)
    (hD0 : IntervalIntegrable D volume 0 (5 / 8))
    (hD1 : IntervalIntegrable D volume (5 / 8) 1)
    (hpolar : V ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), D u) + ∫ u in (5 / 8 : ℝ)..1, D u))
    (hD : ∀ u, 0 < u → u < 1 → D u ≤ Real.sin (Real.pi * u) ^ 3 *
      (1 - lossFactor ((Real.pi * u) ^ 2 /
        (Real.pi ^ 2 - (Real.pi * u) ^ 2)) / 6 *
        ((3 / 2) * s) * (1 - ((Real.pi * u) / Real.pi) ^ 2 / 2))) :
    V ≤ 1 - (3 / 40) * s := by
  apply volume_ratio_upper_of_radial_comparison_open hs hD0 hD1 hpolar
  · intro u hu
    have h := averaged_radial_piecewise_bound hu.1.le (by linarith [hu.2]) hs
      (hD u hu.1 (by linarith [hu.2]))
    rw [radialLower, ite_eq_left hu.2.le] at h
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (unfold upperKernel ; field_simp [Real.pi_ne_zero] ; ring)
  · intro u hu
    have h := averaged_radial_piecewise_bound (by linarith [hu.1]) hu.2 hs
      (hD u (by linarith [hu.1]) hu.2)
    rw [radialLower, ite_eq_right (not_le.mpr hu.1)] at h
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (unfold upperKernelEnd ; field_simp [Real.pi_ne_zero] ; ring)

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CP2Overlap
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit representatives and transition probabilities for the actual
Fubini--Study distance on CP2. -/

namespace PositiveEinsteinFour

open EinsteinFour

noncomputable section

theorem cp2Overlap_nonneg (p q : ComplexProjective2) : 0 ≤ cp2Overlap p q := norm_nonneg _

theorem cp2Overlap_le_one (p q : ComplexProjective2) : cp2Overlap p q ≤ 1 := by
  simpa only [cp2Overlap, cp2UnitRep_norm, one_mul] using norm_inner_le_norm (cp2UnitRep p) (cp2UnitRep q)

theorem cp2Overlap_eq_ratio (p q : ComplexProjective2) :
    cp2Overlap p q = ‖inner ℂ p.rep q.rep‖ / (‖p.rep‖ * ‖q.rep‖) := by
  have hp : (((‖p.rep‖⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr p.rep_nonzero)
  have hq : (((‖q.rep‖⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr q.rep_nonzero)
  have h := normalized_inner_smul p.rep q.rep
    (((‖p.rep‖⁻¹ : ℝ) : ℂ)) (((‖q.rep‖⁻¹ : ℝ) : ℂ)) hp hq
  change ‖inner ℂ (cp2UnitRep p) (cp2UnitRep q)‖ /
    (‖cp2UnitRep p‖ * ‖cp2UnitRep q‖) = _ at h
  simpa only [cp2Overlap, cp2UnitRep_norm, one_mul, div_one] using h


theorem fubiniStudyDistance_eq_arccos (p q : ComplexProjective2) :
    fubiniStudyDistance p q = Real.arccos (cp2Overlap p q) := by
  rw [cp2Overlap_eq_ratio]
  rfl

theorem cp2Overlap_mk (x y : CP2Vector) (hx : x ≠ 0) (hy : y ≠ 0) :
    cp2Overlap (Projectivization.mk ℂ x hx) (Projectivization.mk ℂ y hy) =
      ‖inner ℂ x y‖ / (‖x‖ * ‖y‖) := by
  rw [cp2Overlap_eq_ratio, normalized_inner_mk_rep]

theorem cp2Overlap_comm (p q : ComplexProjective2) : cp2Overlap p q = cp2Overlap q p :=
  norm_inner_symm _ _

end
end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CP2UnitGeometry
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unit representatives needed for the projective fixed-point argument. -/

namespace PositiveEinsteinFour

open EinsteinFour

noncomputable section

theorem cp2Overlap_of_unit_representatives (p q : ComplexProjective2)
    (x y : CP2Vector) (hx : x ≠ 0) (hy : y ≠ 0)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1)
    (hpx : Projectivization.mk ℂ x hx = p) (hqy : Projectivization.mk ℂ y hy = q) :
    cp2Overlap p q = ‖inner ℂ x y‖ := by
  rw [← hpx, ← hqy, cp2Overlap_mk, hnx, hny, one_mul, div_one]

theorem cp2_unit_aligned (p q : ComplexProjective2) (h : 0 < cp2Overlap p q) :
    ∃ v : CP2Vector, ∃ hv : v ≠ 0,
      ‖v‖ = 1 ∧ Projectivization.mk ℂ v hv = q ∧
      inner ℂ (cp2UnitRep p) v = (cp2Overlap p q : ℂ) := by
  let z := inner ℂ (cp2UnitRep p) (cp2UnitRep q)
  have hz : z ≠ 0 := by
    intro hz
    change 0 < ‖z‖ at h
    rw [hz, norm_zero] at h
    exact (lt_irrefl 0) h
  let a : ℂ := (‖z‖ : ℂ) / z
  have ha : a ≠ 0 := div_ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr hz)) hz
  have han : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, norm_ne_zero_iff.mpr hz]
  let v : CP2Vector := a • cp2UnitRep q
  have hv : v ≠ 0 := smul_ne_zero ha (cp2UnitRep_ne_zero q)
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · simp only [v, norm_smul, han, cp2UnitRep_norm, mul_one]
  · rw [← cp2UnitRep_mk q]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a, rfl⟩
  · change inner ℂ (cp2UnitRep p) (a • cp2UnitRep q) = (‖z‖ : ℂ)
    rw [inner_smul_right]
    change ((‖z‖ : ℂ) / z) * z = _
    exact div_mul_cancel₀ _ hz

end
end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ComplexPairAlignment
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit representatives with nonnegative real overlap, including orthogonal pairs. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem cp2_aligned_unit_representative (p q : ComplexProjective2) :
    ∃ v : CP2Vector, ∃ hv : v ≠ 0, ‖v‖ = 1 ∧ Projectivization.mk ℂ v hv = q ∧
      inner ℂ (cp2UnitRep p) v = (cp2Overlap p q : ℂ) := by
  by_cases hpos : 0 < cp2Overlap p q
  · exact cp2_unit_aligned p q hpos
  have hz : cp2Overlap p q = 0 := le_antisymm (le_of_not_gt hpos) (cp2Overlap_nonneg p q)
  refine ⟨cp2UnitRep q,cp2UnitRep_ne_zero q,cp2UnitRep_norm q,cp2UnitRep_mk q,?_⟩
  have hi : inner ℂ (cp2UnitRep p) (cp2UnitRep q) = 0 := norm_eq_zero.mp hz
  rw [hi,hz,Complex.ofReal_zero]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ComplexProjectiveTriangle
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The triangle inequality for the actual Fubini--Study distance on CP2. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complex_unit_angle (u v : CP2Vector) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    InnerProductGeometry.angle u v = Real.arccos (inner ℝ u v) := by
  simp only [InnerProductGeometry.angle,hu,hv,one_mul,div_one]

theorem fubiniStudyDistance_triangle (P Q R : ComplexProjective2) :
    fubiniStudyDistance P R ≤ fubiniStudyDistance P Q + fubiniStudyDistance Q R := by
  obtain ⟨p,hp,hpn,hpP,hqp⟩ := cp2_aligned_unit_representative Q P
  obtain ⟨r,hr,hrn,hrR,hqr⟩ := cp2_aligned_unit_representative Q R
  let q := cp2UnitRep Q
  have hpqR : inner ℝ q p = cp2Overlap Q P := by
    simpa only [Complex.ofReal_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hqp
  have hqrR : inner ℝ q r = cp2Overlap Q R := by
    simpa only [Complex.ofReal_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hqr
  have hreal : inner ℝ p r ≤ ‖inner ℂ p r‖ := by
    simpa only [← real_inner_eq_re_inner ℂ] using! Complex.re_le_norm (inner ℂ p r)
  calc
    fubiniStudyDistance P R = Real.arccos ‖inner ℂ p r‖ := by
      rw [fubiniStudyDistance_eq_arccos,cp2Overlap_of_unit_representatives P R p r hp hr hpn hrn hpP hrR]
    _ ≤ InnerProductGeometry.angle p r := by
      rw [complex_unit_angle p r hpn hrn]
      exact Real.antitone_arccos hreal
    _ ≤ InnerProductGeometry.angle p q + InnerProductGeometry.angle q r :=
      InnerProductGeometry.angle_le_angle_add_angle p q r
    _ = fubiniStudyDistance P Q + fubiniStudyDistance Q R := by
      rw [complex_unit_angle p q hpn (cp2UnitRep_norm Q),
        complex_unit_angle q r (cp2UnitRep_norm Q) hrn,
        real_inner_comm q p,hpqR,hqrR,cp2Overlap_comm Q P,
        fubiniStudyDistance_eq_arccos,fubiniStudyDistance_eq_arccos]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylGeometry
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

namespace OrthonormalFrame

variable {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c)

/-- Positivity in chart coordinates is preserved by the actual invertible
frame change. This uses the sectional-curvature predicate in the target. -/
theorem sectional_pos (hsec : HasPositiveSectionalCurvature g)
    (u v : FourSpace) (huv : LinearIndependent ℝ ![u, v]) :
    0 < sectionalNumerator g c (chartAt FourSpace c c) (e.map u) (e.map v) := by
  apply hsec
  have h := huv.map' e.map (LinearMap.ker_eq_bot.mpr e.map_injective)
  have heq : e.map ∘ ![u, v] = ![e.map u, e.map v] := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at h

end OrthonormalFrame

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ConditionalUnoriented
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section Lean433MfldCatCompatibility
open scoped Manifold ContDiff
universe u v

namespace ModelWithCorners

attribute [instance] MfldCat.topologicalSpace MfldCat.chartedSpace MfldCat.isManifold

initialize_simps_projections MfldCat (-topologicalSpace, -chartedSpace, -isManifold)

namespace MfldCat

attribute [coe] MfldCat.carrier

end MfldCat
end ModelWithCorners
end Lean433MfldCatCompatibility

namespace OAI

/-! The topological reduction from the oriented two-model theorem to the
unoriented three-model theorem uses the orientation cover, its pullback metric
and the Euler/Betti identities from Hatcher. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

universe u

attribute [instance] ClosedOrientedMetricFour.regular
  ClosedOrientedMetricFour.secondCountable ClosedOrientedMetricFour.compact
  ClosedOrientedMetricFour.connected

variable {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Hatcher's connected orientation cover, equipped with the pullback
metric. Preservation of Einstein and positive sectional curvature is the
local-isometry specialization in Petersen §1.3.3. -/
structure OrientationMetricDoubleCover (g : SmoothMetric M) where
  oriented : ClosedOrientedMetricFour.{u}
  cover : MetricDoubleCover g oriented.metric
  einstein : IsEinstein g → IsEinstein oriented.metric
  positive : HasPositiveSectionalCurvature g → HasPositiveSectionalCurvature oriented.metric

/-- Hatcher, Proposition 3.25 and Theorem 3.26(c), together with smooth
metric pullback: either an orientation exists, or its connected two-sheeted
cover has the displayed actual geometric data. -/
def HatcherOrientationCoverInput (g : SmoothMetric M) : Prop :=
  Nonempty (Geometry.FrameOrientation g) ∨ Nonempty (OrientationMetricDoubleCover g)

end
end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Link the normal-tensor calculation to the concrete metric. The classical
curvature decomposition is displayed as an explicit local hypothesis here;
the angular mean identities themselves are proved, not postulated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

local instance instNormedAddCommGroupMat3 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureForm
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coordinate curvature is a four-linear form. This supplies
the multilinearity used to change normal frames without an independent
curvature-transformation assumption. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem multilinear_combinations
    (f : MultilinearMap ℝ (fun _ : Fin 4 => FourSpace) ℝ)
    (A : Mat4) (e : Fin 4 → FourSpace) (v : Fin 4 → Fin 4) :
    f (fun s => ∑ a, A a (v s) • e a) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        (A a (v 0) * A b (v 1) * A c (v 2) * A d (v 3)) *
          f ![e a, e b, e c, e d] := by
  rw [f.map_sum]
  simp_rw [f.map_smul_univ, smul_eq_mul]
  rw [sum_four_indices_p0]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  congr 1
  funext a
  congr 1
  funext b
  congr 1
  funext c
  congr 1
  funext d
  congr 1
  · change A a (v 0) * (A b (v 1) * (A c (v 2) * A d (v 3))) = _
    ring
  · congr 1
    funext i
    fin_cases i <;> rfl

def curvatureForm (g : SmoothMetric M) (c : M) :
    MultilinearMap ℝ (fun _ : Fin 4 => FourSpace) ℝ :=
  MultilinearMap.mk'
    (fun v => ∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
      chartMetric g c a b * curvatureComponent g c (chartAt FourSpace c c) a p q r *
        v 0 p * v 1 q * v 2 r * v 3 b)
    (by
      intro v i x y
      fin_cases i <;>
        simp [Function.update, add_mul, mul_add, Finset.sum_add_distrib])
    (by
      intro v i k x
      fin_cases i <;> simp [Function.update, Finset.mul_sum]
      all_goals
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro r _
        ring)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameAverages
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spherical disintegration of the actual frame-curvature energies.

The explicit published input `BrinKarcherAveraging` is the specialization of
the Riemannian-base times Stiefel probability measure in Brin--Karcher (1984),
Section 1, p.275, to functions depending only on the first frame direction.
It is a generic integration statement and contains no curvature estimate.
The angular curvature identities used below are proved separately. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

local instance instNormedAddCommGroupMat3_1 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The undetermined Hessian in concrete quaternion coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian


@[simp] theorem freeCoordinates_0 (c : Fin 50 → ℝ) :
    freeCoordinates c 0 = c 21 := rfl

@[simp] theorem freeCoordinates_1 (c : Fin 50 → ℝ) :
    freeCoordinates c 1 = c 24 := rfl

@[simp] theorem freeCoordinates_2 (c : Fin 50 → ℝ) :
    freeCoordinates c 2 = c 26 := rfl

@[simp] theorem freeCoordinates_3 (c : Fin 50 → ℝ) :
    freeCoordinates c 3 = c 29 := rfl

@[simp] theorem freeCoordinates_4 (c : Fin 50 → ℝ) :
    freeCoordinates c 4 = c 31 := rfl

@[simp] theorem freeCoordinates_5 (c : Fin 50 → ℝ) :
    freeCoordinates c 5 = c 34 := rfl

@[simp] theorem freeCoordinates_6 (c : Fin 50 → ℝ) :
    freeCoordinates c 6 = c 35 := rfl

@[simp] theorem freeCoordinates_7 (c : Fin 50 → ℝ) :
    freeCoordinates c 7 = c 36 := rfl

@[simp] theorem freeCoordinates_8 (c : Fin 50 → ℝ) :
    freeCoordinates c 8 = c 37 := rfl

@[simp] theorem freeCoordinates_9 (c : Fin 50 → ℝ) :
    freeCoordinates c 9 = c 38 := rfl

@[simp] theorem freeCoordinates_10 (c : Fin 50 → ℝ) :
    freeCoordinates c 10 = c 39 := rfl

@[simp] theorem freeCoordinates_11 (c : Fin 50 → ℝ) :
    freeCoordinates c 11 = c 40 := rfl

@[simp] theorem freeCoordinates_12 (c : Fin 50 → ℝ) :
    freeCoordinates c 12 = c 41 := rfl

@[simp] theorem freeCoordinates_13 (c : Fin 50 → ℝ) :
    freeCoordinates c 13 = c 42 := rfl

@[simp] theorem freeCoordinates_14 (c : Fin 50 → ℝ) :
    freeCoordinates c 14 = c 43 := rfl

@[simp] theorem freeCoordinates_15 (c : Fin 50 → ℝ) :
    freeCoordinates c 15 = c 44 := rfl

@[simp] theorem freeCoordinates_16 (c : Fin 50 → ℝ) :
    freeCoordinates c 16 = c 45 := rfl

@[simp] theorem freeCoordinates_17 (c : Fin 50 → ℝ) :
    freeCoordinates c 17 = c 46 := rfl

@[simp] theorem freeCoordinates_18 (c : Fin 50 → ℝ) :
    freeCoordinates c 18 = c 47 := rfl

@[simp] theorem freeCoordinates_19 (c : Fin 50 → ℝ) :
    freeCoordinates c 19 = c 48 := rfl

@[simp] theorem freeCoordinates_20 (c : Fin 50 → ℝ) :
    freeCoordinates c 20 = c 49 := rfl


end
end PositiveEinsteinFour.HighestHessian

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

local instance instNormedAddCommGroupMat3_2 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealMat3 : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace

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

local instance instNormedAddCommGroupMat : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealMat : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinusCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate action of the three total minus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

@[simp] theorem minusCoordinates_0_10 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 10 = 2 * c 15 := rfl

@[simp] theorem minusCoordinates_0_11 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 11 = -c 6 + c 16 := rfl

@[simp] theorem minusCoordinates_0_12 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 12 = -c 7 + c 17 := rfl

@[simp] theorem minusCoordinates_0_13 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 13 = -c 8 + c 18 := rfl

@[simp] theorem minusCoordinates_0_14 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 14 = -c 9 + c 19 := rfl

@[simp] theorem minusCoordinates_0_15 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 15 = -c 10 + c 20 := rfl

@[simp] theorem minusCoordinates_0_16 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 16 = -2 * c 11 := rfl

@[simp] theorem minusCoordinates_0_17 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 17 = -2 * c 12 := rfl

@[simp] theorem minusCoordinates_0_18 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 18 = -2 * c 13 := rfl

@[simp] theorem minusCoordinates_0_19 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 19 = -2 * c 14 := rfl

@[simp] theorem minusCoordinates_0_20 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 20 = -2 * c 15 := rfl

@[simp] theorem minusCoordinates_1_0 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 0 = -2 * c 4 := rfl

@[simp] theorem minusCoordinates_1_1 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 1 = -2 * c 5 := rfl

@[simp] theorem minusCoordinates_1_2 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 2 = -c 1 - 2 * c 12 - c 20 := rfl

@[simp] theorem minusCoordinates_1_3 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 3 = c 0 + c 7 := rfl

@[simp] theorem minusCoordinates_1_4 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 4 = c 0 - c 17 := rfl

@[simp] theorem minusCoordinates_1_5 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 5 = c 1 - c 20 := rfl

@[simp] theorem minusCoordinates_1_6 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 6 = 2 * c 9 - 2 * c 13 := rfl

@[simp] theorem minusCoordinates_1_7 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 7 = -2 * c 3 + 2 * c 13 := rfl

@[simp] theorem minusCoordinates_1_8 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 8 = 2 * c 10 - 2 * c 12 := rfl

@[simp] theorem minusCoordinates_1_9 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 9 = -2 * c 6 - 2 * c 7 - 2 * c 15 := rfl

@[simp] theorem minusCoordinates_1_10 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 10 = 2 * c 2 - 2 * c 8 := rfl

@[simp] theorem minusCoordinates_1_11 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 11 = -c 8 - c 18 := rfl

@[simp] theorem minusCoordinates_1_12 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 12 = c 2 - c 5 + c 18 := rfl

@[simp] theorem minusCoordinates_1_13 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 13 = -c 7 - c 17 := rfl

@[simp] theorem minusCoordinates_1_14 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 14 = -c 10 - c 20 := rfl

@[simp] theorem minusCoordinates_1_15 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 15 = c 3 + c 4 - c 13 := rfl

@[simp] theorem minusCoordinates_1_16 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 16 = -2 * c 13 - 2 * c 19 := rfl

@[simp] theorem minusCoordinates_1_17 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 17 = 2 * c 4 := rfl

@[simp] theorem minusCoordinates_1_18 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 18 = -2 * c 12 - 2 * c 20 := rfl

@[simp] theorem minusCoordinates_1_19 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 19 = -2 * c 15 + 2 * c 16 + 2 * c 17 := rfl

@[simp] theorem minusCoordinates_1_20 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 20 = 2 * c 5 := rfl

@[simp] theorem minusCoordinates_2_0 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 0 = 2 * c 2 := rfl

@[simp] theorem minusCoordinates_2_1 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 1 = 2 * c 3 := rfl

@[simp] theorem minusCoordinates_2_2 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 2 = -c 0 + c 7 := rfl

@[simp] theorem minusCoordinates_2_3 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 3 = -c 1 + c 10 := rfl


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HessianCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Curvature compression on all actual inner-Bianchi Hessian tensors. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

def rawQuaternion (s : Fin 3) (Z : RawGradient) : RawGradient := fun a b =>
  quaternion s (Z a b)

def rawMatrixAt (Z : RawGradient) (j : Fin 4) : Mat := fun a b => Z a b j

end
end PositiveEinsteinFour.HighestHessian

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

/-! Evaluate both terms of the varying matrix-slot Green formula. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

def matrixSlotAt (Z : GradientVector) : Mat →ₗ[ℝ] GradientVector where
  toFun A := matrixSlotOperator A Z
  map_add' A B := congrArg (fun F : GradientVector →L[ℝ] GradientVector => F Z)
    (matrixSlotOperatorLinear.map_add A B)
  map_smul' r A := congrArg (fun F : GradientVector →L[ℝ] GradientVector => F Z)
    (matrixSlotOperatorLinear.map_smul r A)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The prescribed-trace coefficient and its ordinary derivative in an
arbitrary frame. No derivative of a matrix eigenframe is used. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian HighestHessian Bianchi
open scoped BigOperators

noncomputable section

local instance traceCoefficientNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance traceCoefficientNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance traceCoefficientNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth norm regularization for the actual squared Weyl weight.
The positive regularization parameter allows the Green identities to be
used at Weyl zeros as well as on the positive-norm set. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian Filter
open scoped _root_.Topology

noncomputable section

local instance smoothWeylNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance smoothWeylNormedSpace_rbc8abb_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance smoothWeylNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

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

/-- The harmless sign in the lifted three-dimensional basis cancels from
both matrix slots, exactly as needed for diagonalization. -/
theorem signed_conjugation (c : ℝ) (hc : c ^ 2 = 1) (R A : Mat) :
    (c • R)ᵀ * A * (c • R) = Rᵀ * A * R := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  simp only [← pow_two, hc, one_smul]


theorem matrix_spectral_square (A : Mat) (hA : A.IsHermitian) :
    (∑ i, hA.eigenvalues i ^ 2) = Matrix.trace (A * A) := by
  let V := hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ Mat (star V)
  have hd : φ A = Matrix.diagonal hA.eigenvalues := by
    simpa only [φ, V, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have htrace (B : Mat) : Matrix.trace (φ B) = Matrix.trace B := by
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  calc
    _ = Matrix.trace (Matrix.diagonal hA.eigenvalues *
        Matrix.diagonal hA.eigenvalues) := by
      simp [Matrix.diagonal_mul_diagonal, pow_two]
    _ = Matrix.trace (φ (A * A)) := by rw [map_mul, hd]
    _ = Matrix.trace (A * A) := htrace _

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The raw classical parallel-frame calculus used by the weighted Green
argument. Every field refers to the actual metric tensors. No compressed
Ricci equation or integral estimate is a field of this structure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance greenDataNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance greenDataNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! Evaluate the derivative-slot Green integral on actual metric tensors,
using the published raw curvature decomposition and Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance curvatureIntegralNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance curvatureIntegralNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! Matrix conjugation and the derivative-index change used at a single
spectral frame. All maps act on the actual matrix arrays; no smooth choice
of eigenvectors is involved. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def conjugateMatrix (R A : Mat) : Mat := Rᵀ * A * R

theorem conjugateMatrix_add (R A B : Mat) :
    conjugateMatrix R (A + B) = conjugateMatrix R A + conjugateMatrix R B := by
  simp only [conjugateMatrix, Matrix.mul_add, Matrix.add_mul]

theorem conjugateMatrix_sub (R A B : Mat) :
    conjugateMatrix R (A - B) = conjugateMatrix R A - conjugateMatrix R B := by
  simp only [conjugateMatrix, Matrix.mul_sub, Matrix.sub_mul]

theorem conjugateMatrix_smul (R A : Mat) (c : ℝ) :
    conjugateMatrix R (c • A) = c • conjugateMatrix R A := by
  simp only [conjugateMatrix, Matrix.mul_smul, Matrix.smul_mul]

theorem conjugateMatrix_one (R : Mat) (hR : Rᵀ * R = 1) :
    conjugateMatrix R 1 = 1 := by
  simpa only [conjugateMatrix, Matrix.mul_one] using hR

theorem conjugateMatrix_mul (R : Mat) (hR : R * Rᵀ = 1) (A B : Mat) :
    conjugateMatrix R A * conjugateMatrix R B = conjugateMatrix R (A * B) := by
  simp only [conjugateMatrix]
  calc
    Rᵀ * A * R * (Rᵀ * B * R) = Rᵀ * A * (R * Rᵀ) * B * R := by
      simp only [Matrix.mul_assoc]
    _ = Rᵀ * (A * B) * R := by
      rw [hR, Matrix.mul_one]
      simp only [Matrix.mul_assoc]

theorem conjugateMatrix_trace (R : Mat) (hR : R * Rᵀ = 1) (A : Mat) :
    Matrix.trace (conjugateMatrix R A) = Matrix.trace A := by
  rw [conjugateMatrix, Matrix.trace_mul_cycle, hR, Matrix.one_mul]

theorem conjugateMatrix_transpose (R A : Mat) :
    (conjugateMatrix R A)ᵀ = conjugateMatrix R Aᵀ := by
  simp only [conjugateMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

theorem conjugateMatrix_symmetric (R A : Mat) (hA : symmetric A) :
    symmetric (conjugateMatrix R A) := by
  have ht : Aᵀ = A := by ext i j; exact hA j i
  have h := conjugateMatrix_transpose R A
  rw [ht] at h
  intro i j
  exact (congrArg (fun N : Mat => N i j) h).symm

/-- Passive rotation of all three slots of a matrix-valued covector. -/
def turnGradient (R : Mat) (P : Mat4) (Z : Angular.Gradient) : Angular.Gradient :=
  fun i => ∑ j, P j i • conjugateMatrix R (Z j)

theorem turnGradient_symmetric (R : Mat) (P : Mat4) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) (i : Fin 4) :
    symmetric (turnGradient R P Z i) := by
  intro a b
  simp only [turnGradient, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [conjugateMatrix_symmetric R (Z j) (hZ j) a b]

theorem turnGradient_traceFree (R : Mat) (hR : R * Rᵀ = 1) (P : Mat4)
    (Z : Angular.Gradient) (hZ : ∀ i, traceFree (Z i)) (i : Fin 4) :
    traceFree (turnGradient R P Z i) := by
  change Matrix.trace (∑ j, P j i • conjugateMatrix R (Z j)) = 0
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, conjugateMatrix_trace R hR,
    show ∀ j, Matrix.trace (Z j) = 0 from hZ, smul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The opposite Weyl block acts on the derivative slots of the plus
Hessian. All derivatives of the opposite coefficient are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance minusIntegralNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance minusIntegralNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! The minimum of the constructed normalized spectrum gives exactly
the scalar parameter r in the closed spectral domain. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem conjugateMatrix_posSemidef (R A : Mat) (hA : A.PosSemidef) :
    (conjugateMatrix R A).PosSemidef := by
  simpa only [conjugateMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hA.conjTranspose_mul_mul_same R

theorem shape_shift_bounds (A R : Mat) (hR : Rᵀ * R = 1)
    (S : Shape) (v x : ℝ)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun a => v * S.s a))
    (hAx : (A + x • (1 : Mat)).PosSemidef) :
    ∀ a, -x ≤ v * S.s a := by
  have h := conjugateMatrix_posSemidef R _ hAx
  rw [conjugateMatrix_add, conjugateMatrix_smul, conjugateMatrix_one R hR, hdiag] at h
  intro a
  have hd := h.diag_nonneg (i := a)
  simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at hd
  linarith only [hd]

theorem shape_minimum_parameter_bound (A R : Mat) (hR : Rᵀ * R = 1)
    (S : Shape) (v x r : ℝ)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun a => v * S.s a))
    (hAx : (A + x • (1 : Mat)).PosSemidef) (hr : ∃ i, S.s i = -r) :
    v * r ≤ x := by
  obtain ⟨i, hi⟩ := hr
  have h := shape_shift_bounds A R hR S v x hdiag hAx i
  rw [hi] at h
  linarith only [h]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The quadratic and radial scalar contractions are unchanged by the
pointwise spectral frame. These are identities on finite arrays. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The radial trace is a covector under the same actual four-frame change. -/
theorem trace_turnGradient (R : Mat) (hR : R * Rᵀ = 1) (P : Mat4)
    (A : Mat) (Z : Angular.Gradient) (i : Fin 4) :
    Matrix.trace (conjugateMatrix R A * turnGradient R P Z i) =
      ∑ j, P j i * Matrix.trace (A * Z j) := by
  simp only [turnGradient, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, conjugateMatrix_mul R hR, conjugateMatrix_trace R hR,
    smul_eq_mul]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Covariance of the quaternionic Bianchi constraint under a genuine
oriented four-frame lift. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def turnVector (P : Mat4) (v : Vec) : Vec := WithLp.toLp 2 (Pᵀ *ᵥ (v : Fin 4 → ℝ))

theorem turnVector_smul (P : Mat4) (c : ℝ) (v : Vec) :
    turnVector P (c • v) = c • turnVector P v := by
  ext i
  simp only [turnVector, Matrix.mulVec, dotProduct, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem turnVector_sum {ι : Type*} [Fintype ι] (P : Mat4) (v : ι → Vec) :
    turnVector P (∑ i, v i) = ∑ i, turnVector P (v i) := by
  ext j
  simp only [turnVector, Matrix.mulVec, dotProduct, WithLp.ofLp_sum,
    Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem turnVector_zero (P : Mat4) : turnVector P 0 = 0 := by
  ext i
  simp [turnVector]

theorem turnVector_norm (P : Mat4) (hP : P * Pᵀ = 1) (v : Vec) :
    ‖turnVector P v‖ = ‖v‖ := by
  have hs : ‖turnVector P v‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, turnVector, Matrix.mulVec,
      Matrix.transpose_apply, dotProduct] using orthogonal_square_sum P hP v
  nlinarith [norm_nonneg (turnVector P v), norm_nonneg v]

def turnRawGradient (R : Mat) (P : Mat4) (Z : RawGradient) : RawGradient :=
  fun a b => turnVector P (∑ r, ∑ s, (R r a * R s b) • Z r s)

theorem turnRawGradient_field (R : Mat) (P : Mat4) (Z : Angular.Gradient) (a b : Fin 3) :
    turnRawGradient R P (fun c d => WithLp.toLp 2 (fun i => Z i c d)) a b =
      WithLp.toLp 2 (fun i => turnGradient R P Z i a b) := by
  ext i
  simp only [turnRawGradient, turnVector, turnGradient, conjugateMatrix,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mulVec, dotProduct, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The exact prescribed trace in arbitrary matrix coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The operator on a matrix obtained by contracting two infinitesimal
matrix rotations with the full Weyl coefficient. -/
def generalMatrixActionSquare (A M : Mat) : Mat :=
  ∑ r, ∑ s, A r s • matrixAction r (matrixAction s M)

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The elementary Grassmannian calculation needed for the sectional
criterion. Two arbitrary unit coefficient vectors in the positive and
negative quaternion triples are realized by a genuine two-plane. -/

namespace PositiveEinsteinFour.SectionalPlane

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame Angular
open scoped BigOperators

noncomputable section

theorem act_add (A B : Geometry.Mat4) (v : Vec4) :
    act (A + B) v = act A v + act B v := by
  ext i
  simp [act, Matrix.add_mulVec]

theorem act_smul (r : ℝ) (A : Geometry.Mat4) (v : Vec4) :
    act (r • A) v = r • act A v := by
  ext i
  simp [act, Matrix.smul_mulVec]

theorem act_sum {ι : Type*} [Fintype ι] (A : ι → Geometry.Mat4) (v : Vec4) :
    act (∑ i, A i) v = ∑ i, act (A i) v := by
  ext i
  simp [act, Matrix.sum_mulVec]

theorem act_mul (A B : Geometry.Mat4) (v : Vec4) :
    act (A * B) v = act A (act B v) := by
  ext i
  simp [act, Matrix.mulVec_mulVec]

theorem act_smul_vector (A : Geometry.Mat4) (r : ℝ) (v : Vec4) :
    act A (r • v) = r • act A v := by
  ext i
  simp [act, Matrix.mulVec_smul]

theorem act_norm (A : Geometry.Mat4) (hA : Aᵀ * A = 1) (v : Vec4) :
    ‖act A v‖ = ‖v‖ := by
  have hs : ‖act A v‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa only [act, EuclideanSpace.real_norm_sq_eq, Matrix.transpose_transpose,
      Matrix.transpose_apply, Matrix.mulVec, dotProduct] using
      orthogonal_square_sum Aᵀ (by simpa using hA) v
  nlinarith [norm_nonneg (act A v), norm_nonneg v]

theorem act_inner_adjoint (A : Geometry.Mat4) (v w : Vec4) :
    inner ℝ (act A v) w = inner ℝ v (act Aᵀ w) := by
  simp only [act, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem act_skew_self (A : Geometry.Mat4) (hA : Aᵀ = -A) (v : Vec4) :
    inner ℝ (act A v) v = 0 := by
  have hh := act_inner_adjoint A v v
  rw [hA, show -A = (-1 : ℝ) • A by simp, act_smul] at hh
  simp only [inner_smul_right, neg_one_mul] at hh
  rw [real_inner_comm v (act A v)] at hh
  linarith [real_inner_comm (act A v) v]

def coefficient (Q : Geometry.Mat4) (u v : Vec4) : ℝ := inner ℝ (act Q v) u

theorem coefficient_eq_sum (Q : Geometry.Mat4) (u v : Vec4) :
    coefficient Q u v = ∑ a, ∑ b, Q a b * u a * v b := by
  simp only [coefficient, act, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem coefficient_combination (Q : Fin 3 → Geometry.Mat4)
    (hQ : ∀ v i j, inner ℝ (act (Q i) v) (act (Q j) v) =
      if i = j then ‖v‖ ^ 2 else 0) (s : Fin 3 → ℝ) (v : Vec4) (i : Fin 3) :
    coefficient (Q i) (act (imaginaryCombination Q s) v) v = s i * ‖v‖ ^ 2 := by
  rw [coefficient, imaginaryCombination, act_sum]
  simp only [act_smul, inner_sum, inner_smul_right, hQ, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

end
end PositiveEinsteinFour.SectionalPlane
end


section

/-! The sharp opposite-block cost for an arbitrary symmetric coefficient
matrix.  A concrete orthogonal quaternion expansion of the two derivative
slots replaces a second choice of eigenframe. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- A shifted positive matrix with zero trace has a nonnegative shift. -/
theorem shift_nonneg_of_traceFree (U : Mat) (hU : traceFree U) (y : ℝ)
    (hUy : (U + y • (1 : Mat)).PosSemidef) : 0 ≤ y := by
  have h := hUy.trace_nonneg
  have ht : Matrix.trace U = 0 := hU
  rw [Matrix.trace_add, Matrix.trace_smul, ht] at h
  norm_num at h
  linarith

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The nine commuting-quaternion products are an actual orthogonal
basis for symmetric trace-free scalar Hessians in four dimensions. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian

noncomputable section

abbrev Matrix4 := Geometry.Mat4

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The actual projection cost is a four-by-four quadratic form in the
weight derivative. This finite expansion is used for its integral limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def derivativeBasis (i : Fin 4) : Vec := WithLp.toLp 2 (fun j => if j = i then 1 else 0)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sectional criterion from actual two-planes. The quaternionic
Grassmann calculation and the minimum-eigenvalue argument connect sectional
positivity with the Riemann curvature decomposition and symmetry identities. -/

namespace PositiveEinsteinFour.SectionalPlane

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

def quadratic (A : Geometry.Mat3) (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i, ∑ j, A i j * v i * v j

theorem quadratic_smul (A : Geometry.Mat3) (r : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    quadratic A (r • v) = r ^ 2 * quadratic A v := by
  simp only [quadratic, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_add_scalar (A : Geometry.Mat3) (r : ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) :
    quadratic (A + r • (1 : Geometry.Mat3)) v = quadratic A v + r * ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [quadratic, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite,
    one_mul, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true,
    pow_two, Finset.mul_sum, mul_assoc]

/-- An attained minimum on the unit sphere supplies the exact PSD shift. -/
theorem exists_minimum_shift (A : Geometry.Mat3) (hA : symmetric A) :
    ∃ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 ∧
      (A + (-quadratic A s) • (1 : Geometry.Mat3)).PosSemidef := by
  have hcont : Continuous (quadratic A) := by unfold quadratic; fun_prop
  obtain ⟨s, hs, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)) hcont.continuousOn
  have hsnorm : ‖s‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hs
  refine ⟨s, hsnorm, ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have ha : A.IsHermitian := by ext i j; exact hA j i
    exact ha.add (Matrix.isHermitian_one.smul (show IsSelfAdjoint (-quadratic A s) by rfl))
  · intro z
    let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 z
    have hv : 0 ≤ quadratic (A + (-quadratic A s) • (1 : Geometry.Mat3)) v := by
      by_cases hz : v = 0
      · simp [hz, quadratic]
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
      have hunit : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_smul_inv_norm hz
      have hl := hmin (show (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere 0 1 by
        simpa only [Metric.mem_sphere, dist_zero_right] using hunit)
      change quadratic A s ≤ quadratic A ((‖v‖⁻¹ : ℝ) • v) at hl
      rw [quadratic_smul] at hl
      have hscale : ‖v‖ ^ 2 * (‖v‖⁻¹) ^ 2 = 1 := by field_simp [ne_of_gt hn]
      have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg ‖v‖)
      rw [← mul_assoc, hscale, one_mul] at hm
      rw [quadratic_add_scalar]
      nlinarith only [hm]
    simpa only [quadratic, v, Matrix.mulVec, dotProduct, Pi.star_apply,
      star_trivial, PiLp.toLp_apply, Finset.mul_sum, mul_assoc, mul_comm,
      mul_left_comm] using hv

def sectionalValue (R : CurvatureArray) (u v : Vec4) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * u a * v b * v c * u d

theorem sectionalValue_add (R S : CurvatureArray) (u v : Vec4) :
    sectionalValue (R + S) u v = sectionalValue R u v + sectionalValue S u v := by
  simp [sectionalValue, add_mul, Finset.sum_add_distrib]

theorem sectionalValue_smul (r : ℝ) (R : CurvatureArray) (u v : Vec4) :
    sectionalValue (r • R) u v = r * sectionalValue R u v := by
  simp [sectionalValue, Finset.mul_sum, mul_assoc]

theorem sectionalValue_sum {ι : Type*} [Fintype ι] (R : ι → CurvatureArray)
    (u v : Vec4) : sectionalValue (∑ i, R i) u v = ∑ i, sectionalValue (R i) u v := by
  let F : CurvatureArray →ₗ[ℝ] ℝ :=
    { toFun := fun S => sectionalValue S u v
      map_add' := fun S T => sectionalValue_add S T u v
      map_smul' := fun r S => by
        simpa only [smul_eq_mul, RingHom.id_apply] using sectionalValue_smul r S u v }
  change F (∑ i, R i) = ∑ i, F (R i)
  exact map_sum F R Finset.univ

theorem sectionalValue_twoFormProduct (P Q : Geometry.Mat4) (u v : Vec4) :
    sectionalValue (twoFormProduct P Q) u v = coefficient P u v * coefficient Q u v := by
  simp only [sectionalValue, twoFormProduct, coefficient_eq_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem sectionalValue_blockTensor (A : Geometry.Mat3) (Q : Fin 3 → Geometry.Mat4)
    (u v : Vec4) : sectionalValue (blockTensor A Q) u v =
      (1 / 2 : ℝ) * ∑ i, ∑ j, A i j * coefficient (Q i) u v * coefficient (Q j) u v := by
  simp only [blockTensor, sectionalValue_smul, sectionalValue_sum,
    sectionalValue_twoFormProduct, mul_assoc]

theorem plane_independent {u v : Vec4} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (horth : inner ℝ u v = 0) : LinearIndependent ℝ ![u, v] := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro i
    fin_cases i
    · change u ≠ 0
      exact norm_ne_zero_iff.mp (by rw [hu]; norm_num)
    · change v ≠ 0
      exact norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · change inner ℝ u v = 0
      exact horth
    · change inner ℝ v u = 0
      simpa only [real_inner_comm] using horth
    · exact False.elim (hij rfl)

end
end PositiveEinsteinFour.SectionalPlane
namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix SectionalPlane
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem OrthonormalFrame.map_eq_combination {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (u : FourSpace) :
    e.map u = ∑ i, u i • e.vector i := by
  ext j
  simp only [OrthonormalFrame.map_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    OrthonormalFrame.vector_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regularized scalar Weyl equation follows from ordinary derivatives
of the actual block and its proved matrix Laplacian. Test functions are
arbitrary smooth flow weights, ready for the polynomial coupling test. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance normEquationNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance normEquationNormedSpace_rbc8abb_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance normEquationNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integrated scalar-Hessian curvature identity. The only
differential inputs are the raw scalar and Weyl parallel-frame derivatives
and Ricci commutator. Coefficient divergence and the exact contraction are
proved from the Bianchi equation and the finite-dimensional calculations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Bianchi ScalarHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance scalarIdentityRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance scalarIdentitySpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

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

/-! Positive sectional curvature makes the actual normal Jacobi curvature
matrix positive semidefinite. No separate matrix-positivity input is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix SectionalPlane
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def normalCoordinates (v : Fin 3 → ℝ) : FourSpace :=
  WithLp.toLp 2 (Fin.cons 0 v)

theorem normalCoordinates_ne_zero {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    normalCoordinates v ≠ 0 := by
  intro he
  apply hv
  funext i
  exact congrArg (fun w : FourSpace => w i.succ) he

theorem normalCoordinates_orthogonal (v : Fin 3 → ℝ) :
    inner ℝ (normalCoordinates v) (coordinateVector 0) = 0 := by
  simp [normalCoordinates, coordinateVector, PiLp.inner_apply, RCLike.inner_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar shape in the integrated Weyl equation is determined by
the actual determinant and norm, including at a zero Weyl block. Its
upper bound follows from the three-dimensional spectral identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem orthogonal_conjugate_det (A R : Mat3) (hR : Rᵀ * R = 1) :
    (Rᵀ * A * R).det = A.det := by
  calc
    _ = A.det * (Rᵀ * R).det := by simp only [Matrix.det_mul]; ring
    _ = _ := by rw [hR, Matrix.det_one, mul_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal-frame changes and their exact Frobenius invariants. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped Manifold ContDiff BigOperators

noncomputable section

local instance frameNormalFrobenius : NormedAddCommGroup Mat3 :=
  Matrix.frobeniusNormedAddCommGroup

/-- The normal restriction of a bilinear form written in coordinate components. -/
def normalRestriction (E K : Mat4) : Mat3 :=
  (Eᵀ * K * E).submatrix Fin.succ Fin.succ

/-- Restrict a full frame change to the three normal vectors. -/
def normalChange (P : Mat4) : Mat3 := P.submatrix Fin.succ Fin.succ

theorem normalChange_orthogonal (P : Mat4) (hP : Pᵀ * P = 1)
    (h0 : ∀ i, P i 0 = if i = 0 then 1 else 0) :
    (normalChange P)ᵀ * normalChange P = 1 := by
  have hrow (j : Fin 4) : P 0 j = if (0 : Fin 4) = j then 1 else 0 := by
    have h := congrArg (fun A : Mat4 => A 0 j) hP
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, h0, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true,
      Matrix.one_apply] using h
  ext i j
  have hz (k : Fin 3) : ¬(0 : Fin 4) = k.succ := Ne.symm (Fin.succ_ne_zero k)
  have h := congrArg (fun A : Mat4 => A i.succ j.succ) hP
  simpa only [normalChange, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, Fin.sum_univ_succ, hrow, hz, ite_false, if_false,
    zero_mul, zero_add, Matrix.one_apply, Fin.succ_inj] using h

theorem normalRestriction_conjugate (E K P : Mat4)
    (hrow : ∀ j, P 0 j = if (0 : Fin 4) = j then 1 else 0) :
    normalRestriction (E * P) K =
      (normalChange P)ᵀ * normalRestriction E K * normalChange P := by
  have hfull : (E * P)ᵀ * K * (E * P) = Pᵀ * (Eᵀ * K * E) * P := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  ext i j
  have hz (k : Fin 3) : ¬(0 : Fin 4) = k.succ := Ne.symm (Fin.succ_ne_zero k)
  change ((E * P)ᵀ * K * (E * P)) i.succ j.succ = _
  rw [hfull]
  simp only [normalRestriction, normalChange, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.submatrix_apply, Fin.sum_univ_succ,
    hrow, hz, ite_false, if_false, zero_mul, mul_zero, zero_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature and its covariant derivative depend on the first
frame direction through their Frobenius norms, not on the normal basis. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

local instance curvatureInvariantFrobenius : NormedAddCommGroup Mat3 :=
  Matrix.frobeniusNormedAddCommGroup

/-- Contract the two Jacobi directions before choosing the normal basis. -/
def directionalCurvatureMatrix (T : CovariantCoordinates 4) (w : Fin 4 → ℝ) : Mat4 :=
  fun a b => ∑ p, ∑ q, w p * w q * T ![a, p, q, b]

def directionalDerivativeTensor (T : CovariantCoordinates 5) (w : Fin 4 → ℝ) :
    CovariantCoordinates 4 := fun a => ∑ d, w d * T (Fin.cons d a)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem blockTensor_add (A B : Mat3) (Q : Fin 3 → Mat4) :
    blockTensor (A + B) Q = blockTensor A Q + blockTensor B Q := by
  simp only [blockTensor, Matrix.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rotation of the actual first curvature derivative, including its
covector direction, before either Weyl block is contracted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem turn_blockTensor_add (A B : Mat3) (Q : Fin 3 → Mat4) :
    blockTensor (A + B) Q = blockTensor A Q + blockTensor B Q := by
  simp only [blockTensor, Matrix.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify the actual metric integral with the finite-array integrand.
Only fixed frame reflection is used for the second Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def reflectedVector (p : Vec) : Vec :=
  WithLp.toLp 2 (fun i => orientationSign i * p i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normalization of the two quaternionic blocks in the full tensor norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped BigOperators

noncomputable section

def blockTensorCoordinates (A : Mat3) (Q : Fin 3 → Mat4) : CovariantCoordinates 4 :=
  fun a => blockTensor A Q (a 0) (a 1) (a 2) (a 3)

theorem frameTensorPairing_add_right {n : ℕ} (R S T : CovariantCoordinates n) :
    frameTensorPairing R (S + T) = frameTensorPairing R S + frameTensorPairing R T := by
  simp only [frameTensorPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem frameTensorPairing_const_mul_right {n : ℕ} (R T : CovariantCoordinates n) (c : ℝ) :
    frameTensorPairing R (fun a => c * T a) = c * frameTensorPairing R T := by
  simp only [frameTensorPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem frameTensorPairing_sum_right {n : ℕ} {ι : Type*} [Fintype ι]
    (R : CovariantCoordinates n) (T : ι → CovariantCoordinates n) :
    frameTensorPairing R (fun a => ∑ i, T i a) = ∑ i, frameTensorPairing R (T i) := by
  simp only [frameTensorPairing, Finset.mul_sum]
  exact Finset.sum_comm

theorem sum_four_coordinates (f : (Fin 4 → Fin 4) → ℝ) :
    (∑ a, f a) = ∑ i, ∑ j, ∑ k, ∑ l, f ![i, j, k, l] := by
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite curvature contractions occurring in the four-dimensional
Euler and first Pontryagin densities.  These are pointwise identities for
the actual metric curvature; no characteristic-number or Hodge theorem is
assumed or asserted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

def twoFormProductCoordinates (P Q : Mat4) : CovariantCoordinates 4 :=
  fun a => twoFormProduct P Q (a 0) (a 1) (a 2) (a 3)

theorem twoFormProductCoordinates_smul_left (c : ℝ) (P Q : Mat4) :
    twoFormProductCoordinates (c • P) Q = c • twoFormProductCoordinates P Q := by
  funext a
  simp only [twoFormProductCoordinates, twoFormProduct, Matrix.smul_apply,
    smul_eq_mul, Pi.smul_apply]
  ring

theorem blockTensorCoordinates_sum (A : Mat3) (Q : Fin 3 → Mat4) :
    blockTensorCoordinates A Q = (1 / 2 : ℝ) •
      ∑ s, ∑ t, A s t • twoFormProductCoordinates (Q s) (Q t) := by
  funext a
  simp only [blockTensorCoordinates, blockTensor, twoFormProductCoordinates,
    Pi.smul_apply, Finset.sum_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthogonal coefficient matrices of orientation-preserving four-frame changes. -/

namespace PositiveEinsteinFour.QuaternionFrame

open Matrix TraceHessian PositiveEinsteinFour.Geometry
open Angular (oppositeMatrix)
open scoped BigOperators

noncomputable section

def fourMatrixPairing (A B : Mat4) : ℝ := ∑ i, ∑ j, A i j * B i j

theorem fourMatrixPairing_eq_trace (A B : Mat4) :
    fourMatrixPairing A B = Matrix.trace (Aᵀ * B) := by
  simp only [fourMatrixPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

theorem fourMatrixPairing_add_left (A B C : Mat4) :
    fourMatrixPairing (A + B) C = fourMatrixPairing A C + fourMatrixPairing B C := by
  simp only [fourMatrixPairing, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem fourMatrixPairing_add_right (A B C : Mat4) :
    fourMatrixPairing A (B + C) = fourMatrixPairing A B + fourMatrixPairing A C := by
  simp only [fourMatrixPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem fourMatrixPairing_smul_left (A B : Mat4) (c : ℝ) :
    fourMatrixPairing (c • A) B = c * fourMatrixPairing A B := by
  simp only [fourMatrixPairing, Matrix.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

theorem fourMatrixPairing_smul_right (A B : Mat4) (c : ℝ) :
    fourMatrixPairing A (c • B) = c * fourMatrixPairing A B := by
  simp only [fourMatrixPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem fourMatrixPairing_conjugate (P A B : Mat4) (hP : Pᵀ * P = 1) :
    fourMatrixPairing (P * A * Pᵀ) (P * B * Pᵀ) = fourMatrixPairing A B := by
  rw [fourMatrixPairing_eq_trace, fourMatrixPairing_eq_trace]
  have hm : (P * A * Pᵀ)ᵀ * (P * B * Pᵀ) = P * (Aᵀ * B) * Pᵀ := by
    calc
      _ = P * Aᵀ * (Pᵀ * P) * B * Pᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = _ := by rw [hP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hm, Matrix.trace_mul_cycle, hP, Matrix.one_mul]

/-- Coefficients of the positive two-form action. -/
def positiveOrientationMatrix (P : Mat4) : Mat3 := fun r s =>
  (P * quaternionMatrix s * Pᵀ) r.succ 0

/-- Coefficients of the negative two-form action. -/
def negativeOrientationMatrix (P : Mat4) : Mat3 := fun r s =>
  -(P * oppositeMatrix s * Pᵀ) r.succ 0

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The individual Weyl norms descend to each oriented frame component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular QuaternionFrame
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem bilinearPullback_apply (P A : Mat4) (i j : Fin 4) :
    (Pᵀ * A * P) i j = ∑ a, ∑ b, P a i * A a b * P b j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

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

theorem frameTensor_contDiffAt {E : FourSpace → Mat4}
    {T : FourSpace → CovariantCoordinates 4} {z : FourSpace}
    (hE : ∀ i j, ContDiffAt ℝ ∞ (fun w => E w i j) z)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z) (a : Fin 4 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => frameTensor (E w) (T w) a) z := by
  unfold frameTensor
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_prod fun k _ => hE (b k) (a k)).mul (hT b)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletNormalizer
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual square-root normalizer for the flat Green kernel. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

def flatGreenRoot (t : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (t / (N + 1)) • scalarNormalizer (scalarDirichlet N 2)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameRegularity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundedness on the compact frame space supplies the weighted Lipschitz
condition required by the proved discrete-to-continuous radial comparison. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance instNormedAddCommGroupMat3_3 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealMat3_1 : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiDensityMeasurability
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the first-conjugate-point truncation. The apparently
uncountable condition is a countable intersection of open conditions on
compact time intervals. No stability theorem for conjugate points is used. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

theorem isOpen_forall_isUnit {K X : Type*} [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace X] (f : K × X → NormalMatrix)
    (hf : Continuous f) : IsOpen {x | ∀ k, IsUnit (f (k, x))} := by
  have hz : IsClosed {p : K × X | (f p).det = 0} :=
    isClosed_eq hf.matrix_det continuous_const
  have hc := isClosedMap_snd_of_compactSpace _ hz
  have heq : {x | ∀ k, IsUnit (f (k, x))} =
      (Prod.snd '' {p : K × X | (f p).det = 0})ᶜ := by
    ext x
    simp only [mem_ofPred_eq, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      mem_compl_iff, mem_image, Prod.exists]
    aesop
  rw [heq]
  exact hc.isOpen_compl

def preconjugateSet {X : Type*} (J : ℝ × X → NormalMatrix) : Set (ℝ × X) :=
  {p | ∀ s, 0 < s → s ≤ p.1 → IsUnit (J (s, p.2))}

def compactPreconjugateSet {X : Type*} (J : ℝ × X → NormalMatrix)
    (n : ℕ) : Set (ℝ × X) :=
  {p | ∀ r : Icc (1 / ((n : ℝ) + 1)) 1, IsUnit (J (p.1 * r.val, p.2))}

theorem measurableSet_preconjugate {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (J : ℝ × X → NormalMatrix)
    (hJ : Continuous J) : MeasurableSet (preconjugateSet J) := by
  have hopen (n : ℕ) : IsOpen (compactPreconjugateSet J n) := by
    apply isOpen_forall_isUnit
      (fun p : Icc (1 / ((n : ℝ) + 1)) 1 × (ℝ × X) =>
        J (p.2.1 * p.1.val, p.2.2))
    exact hJ.comp (((continuous_fst.comp continuous_snd).mul
      (continuous_subtype_val.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_snd))
  have heq : preconjugateSet J = {p : ℝ × X | p.1 ≤ 0} ∪
      ({p : ℝ × X | 0 < p.1} ∩ ⋂ n, compactPreconjugateSet J n) := by
    ext p
    constructor
    · intro hp
      by_cases ht : p.1 ≤ 0
      · exact Or.inl ht
      · refine Or.inr ⟨lt_of_not_ge ht, mem_iInter.mpr (fun n r => ?_)⟩
        have hr : 0 < r.val := lt_of_lt_of_le (by positivity) r.property.1
        exact hp _ (mul_pos (lt_of_not_ge ht) hr)
          (by nlinarith [r.property.2])
    · rintro (ht | ⟨ht, hp⟩) s hs hst
      · exact False.elim (not_lt_of_ge (hst.trans ht) hs)
      · change 0 < p.1 at ht
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hs ht)
        let r : Icc (1 / ((n : ℝ) + 1)) 1 :=
          ⟨s / p.1, hn.le, (div_le_one ht).mpr hst⟩
        have h := mem_iInter.mp hp n r
        have he : p.1 * r.val = s := by dsimp [r]; field_simp [ne_of_gt ht]
        simpa only [he] using h
  rw [heq]
  exact (isClosed_le continuous_fst continuous_const).measurableSet.union
    ((isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (MeasurableSet.iInter (fun n => (hopen n).measurableSet)))

def truncatedJacobiDensity {X : Type*} (J : ℝ × X → NormalMatrix) (p : ℝ × X) : ℝ :=
  open Classical in if p ∈ preconjugateSet J then (J p).det else 0

theorem truncatedJacobiDensity_rescale {X : Type*} (J : ℝ × X → NormalMatrix)
    (c : ℝ) (hc : 0 < c) (t : ℝ) (x : X) :
    truncatedJacobiDensity (fun p => J (c * p.1, p.2)) (t, x) =
      truncatedJacobiDensity J (c * t, x) := by
  classical
  have hp : (t, x) ∈ preconjugateSet (fun p => J (c * p.1, p.2)) ↔
      (c * t, x) ∈ preconjugateSet J := by
    constructor
    · intro h s hs hst
      have h' := h (s / c) (div_pos hs hc) ((div_le_iff₀ hc).mpr (by nlinarith))
      simpa only [mul_div_cancel₀ _ hc.ne'] using h'
    · intro h s hs hst
      exact h (c * s) (mul_pos hc hs) (mul_le_mul_of_nonneg_left hst hc.le)
  simp only [truncatedJacobiDensity, hp]

theorem measurable_truncatedJacobiDensity {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (J : ℝ × X → NormalMatrix)
    (hJ : Continuous J) : Measurable (truncatedJacobiDensity J) := by
  classical
  exact Measurable.ite (measurableSet_preconjugate J hJ) hJ.matrix_det.measurable
    measurable_const

theorem norm_truncatedJacobiDensity_le {X : Type*} (J : ℝ × X → NormalMatrix)
    (p : ℝ × X) : ‖truncatedJacobiDensity J p‖ ≤ |(J p).det| := by
  classical
  unfold truncatedJacobiDensity
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using abs_nonneg (J p).det

/-- Each fixed-radius density is integrable on a compact parameter space.
Only joint continuity of the actual Jacobi matrix is needed. -/
theorem integrable_truncatedJacobiDensity_slice {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (J : ℝ × X → NormalMatrix) (hJ : Continuous J) (t : ℝ) :
    Integrable (fun x => truncatedJacobiDensity J (t, x)) μ := by
  have hd : Continuous (fun x => |(J (t, x)).det|) :=
    (hJ.comp (continuous_const.prodMk continuous_id)).matrix_det.abs
  have hi : Integrable (fun x => |(J (t, x)).det|) μ :=
    hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply hi.mono'
    ((measurable_truncatedJacobiDensity J hJ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => norm_truncatedJacobiDensity_le J (t, x))

theorem integrable_truncatedJacobiDensity_product {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (J : ℝ × X → NormalMatrix) (hJ : Continuous J) (a b : ℝ) :
    Integrable (truncatedJacobiDensity J) ((volume.restrict (Icc a b)).prod μ) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set X))).exists_bound_of_continuousOn
      hJ.matrix_det.continuousOn
  have hs : ∀ᵐ p : ℝ × X ∂(volume.restrict (Icc a b)).prod μ, p.1 ∈ Icc a b := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Icc)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Filter.Eventually.of_forall (fun _ => ht)
  apply (integrable_const (max 0 C : ℝ)).mono'
    (measurable_truncatedJacobiDensity J hJ).aestronglyMeasurable
  filter_upwards [hs] with p hp
  exact (norm_truncatedJacobiDensity_le J p).trans
    ((hC p ⟨hp, mem_univ _⟩).trans (le_max_right _ _))

/-- The averaged radial density is integrable on every bounded time interval. -/
theorem intervalIntegrable_truncatedJacobiDensity_average {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (J : ℝ × X → NormalMatrix) (hJ : Continuous J) (a b : ℝ)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t => ∫ x, truncatedJacobiDensity J (t, x) ∂μ) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact (integrable_truncatedJacobiDensity_product μ J hJ a b).integral_prod_left

end
end PositiveEinsteinFour.Jacobi

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

/-! The unique actual Jacobi fields depend continuously on time and frame.
All interval-wise comparison data use these same global fields. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

namespace MatrixJacobiSolution

theorem unique {R : ℝ → NormalMatrix} (d e : MatrixJacobiSolution R)
    (K : ℝ≥0) (hK : ∀ s, ‖R s‖ ≤ K) : d.J = e.J ∧ d.V = e.V := by
  let γ : ℝ → JacobiState := fun s => (d.J s, d.V s)
  let η : ℝ → JacobiState := fun s => (e.J s, e.V s)
  have hγ (s : ℝ) : HasDerivAt γ (jacobiStateOperator (R s) (γ s)) s :=
    (d.position_derivative s).prodMk (d.velocity_derivative s)
  have hη (s : ℝ) : HasDerivAt η (jacobiStateOperator (R s) (η s)) s :=
    (e.position_derivative s).prodMk (e.velocity_derivative s)
  have hbound (s : ℝ) : ‖jacobiStateOperator (R s)‖ ≤ ((1 + K : ℝ≥0) : ℝ) := by
    apply (norm_jacobiStateOperator_le _).trans
    simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using add_le_add_left (hK s) 1
  have h0 : γ 0 = η 0 := by
    simp only [γ, η, d.initial_position, e.initial_position, d.initial_velocity, e.initial_velocity]
  have heq := global_linear_solution_unique (fun s => jacobiStateOperator (R s))
    (1 + K) hbound hγ hη h0
  exact ⟨funext (fun s => congrArg Prod.fst (congrFun heq s)),
    funext (fun s => congrArg Prod.snd (congrFun heq s))⟩

end MatrixJacobiSolution
end
end PositiveEinsteinFour.Jacobi

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

/-! Rational Brezis--Kato tests with bounded derivatives.  Their exact
algebra relates the tested Dirichlet form to the square test, uniformly as
the truncation parameter tends to zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

theorem scalarKatoSquare_smooth {lam : ℝ} (hlam : 0 < lam) : ContDiff ℝ ∞ (scalarKatoSquare lam) := by
  exact (contDiff_id.pow 2).div
    ((contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).sqrt
      (fun s => (scalarKato_den_pos hlam s).ne'))
    (fun s => (Real.sqrt_pos.mpr (scalarKato_den_pos hlam s)).ne')

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The critical L4 estimate for the first derivatives of an H2 distribution.
The compactly supported Gagliardo--Nirenberg estimate is extended by cutoffs;
Schwartz approximation is then taken through the actual L2 Bessel inverse. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter Set FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem h2SchwartzInverse_L2 (f : 𝓢(V, ℂ)) :
    (h2SchwartzInverse f).toLp 2 volume = scalarBesselInverseL2 (f.toLp 2 volume) := by
  apply h2_L2_injective
  change ((h2SchwartzInverse f).toLp 2 volume : 𝓢'(V, ℂ)) =
    (scalarBesselInverseL2 (f.toLp 2 volume) : 𝓢'(V, ℂ))
  rw [scalarBesselInverseL2_distribution, Lp.toTemperedDistribution_toLp_eq,
    Lp.toTemperedDistribution_toLp_eq]
  unfold besselPotential
  norm_num only [show (-2 : ℝ) / 2 = -1 by norm_num]
  exact (fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (g := fun x : V => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ)))
    (by fun_prop) f).symm

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarCompositionHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonlinear Hessian candidate and its strong L2 continuity. This is
the two-term chain rule, with L4 first derivatives and L2 second derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped ENNReal ContDiff _root_.Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_1
theorem scalarCompositionHessian_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C₁ C₂ : ℝ} (h₁ : ∀ s, |deriv φ s| ≤ C₁) (h₂ : ∀ s, |deriv (deriv φ) s| ≤ C₂)
    (u : ℕ → X → ℝ) (v : X → ℝ)
    (hu : ∀ n, AEStronglyMeasurable (u n) μ) (hv : AEStronglyMeasurable v μ)
    (huv : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    (g₁ g₂ : ℕ → Lp ℝ 4 μ) (h : ℕ → Lp ℝ 2 μ)
    (G₁ G₂ : Lp ℝ 4 μ) (H : Lp ℝ 2 μ)
    (hg₁ : Tendsto g₁ atTop (𝓝 G₁)) (hg₂ : Tendsto g₂ atTop (𝓝 G₂))
    (hh : Tendsto h atTop (𝓝 H)) :
    Tendsto (fun n => scalarCompositionHessian φ hφ h₁ h₂ (u n) (hu n)
      (g₁ n) (g₂ n) (h n)) atTop
      (𝓝 (scalarCompositionHessian φ hφ h₁ h₂ v hv G₁ G₂ H)) := by
  have hC₁ : 0 ≤ C₁ := (abs_nonneg (deriv φ 0)).trans (h₁ 0)
  have hC₂ : 0 ≤ C₂ := (abs_nonneg (deriv (deriv φ) 0)).trans (h₂ 0)
  have hlim₁ : ∀ᵐ x ∂μ, Tendsto (fun n => deriv φ (u n x)) atTop (𝓝 (deriv φ (v x))) := by
    filter_upwards [huv] with x hx
    exact (hφ.continuous_deriv (by simp)).continuousAt.tendsto.comp hx
  have hlim₂ : ∀ᵐ x ∂μ, Tendsto (fun n => deriv (deriv φ) (u n x)) atTop
      (𝓝 (deriv (deriv φ) (v x))) := by
    filter_upwards [huv] with x hx
    exact (secondDerivative_continuous φ hφ).continuousAt.tendsto.comp hx
  have hfirst := scalarL4Product_coefficient_tendsto
    (fun n => (secondDerivative_continuous φ hφ).comp_aestronglyMeasurable (hu n))
    ((secondDerivative_continuous φ hφ).comp_aestronglyMeasurable hv)
    hC₂ (fun n x => h₂ (u n x)) (fun x => h₂ (v x)) hlim₂ hg₁ hg₂
  have hsecond := scalarCompositionL2Multiply_tendsto
    (fun n => (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable (hu n))
    ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable hv)
    hC₁ (fun n x => h₁ (u n x)) (fun x => h₁ (v x)) hlim₁ hh
  exact hfirst.add hsecond

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarH2Closure
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the first and second weak derivatives through strong L2 limits.
This closes the nonlinear H2 calculation after its explicit product limits. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter LineDeriv
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_L2_weak_derivative_limit (f g : ℕ → L2) (u v : L2)
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v)) (i : Fin 4)
    (heq : ∀ n, scalarCoordinateDerivative i (f n : T) = (g n : T)) :
    scalarCoordinateDerivative i (u : T) = (v : T) := by
  have hU := (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp hf
  have hV := (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp hg
  have hD := (lineDerivOpCLM ℂ T (EuclideanSpace.basisFun (Fin 4) ℝ i)).continuous.continuousAt.tendsto.comp hU
  apply tendsto_nhds_unique hD
  convert hV using 1
  · funext n
    exact heq n
  · rfl

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelContinuousEmbedding
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite H3 embedding needed for weak positivity.  Fourier inversion
provides a bounded continuous representative before any positivity or smooth
nonlinear chain rule is available. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BoundedContinuousFunction

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem scalar_L2_H3_continuous_representative
    (u : Lp ℂ 2 (volume : Measure V)) (hu : MemSobolev 3 2 (u : 𝓢'(V, ℂ))) :
    ∃ f : V → ℂ, Continuous f ∧ (u : V → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, hf⟩ := scalar_L2_H3_boundedContinuous_representative u hu
  exact ⟨f, f.continuous, hf⟩

theorem scalar_L2_H3_continuous_real_representative
    (u : Lp ℂ 2 (volume : Measure V)) (hu : MemSobolev 3 2 (u : 𝓢'(V, ℂ))) :
    ∃ f : V → ℝ, Continuous f ∧ (fun x : V => (u x).re) =ᵐ[volume] f := by
  obtain ⟨f, hf, heq⟩ := scalar_L2_H3_continuous_representative u hu
  refine ⟨Complex.reCLM ∘ f, Complex.reCLM.continuous.comp hf, ?_⟩
  filter_upwards [heq] with x hx
  exact congrArg Complex.re hx

end
end PositiveEinsteinFour.Geometry

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

/-! Finite distributional jets characterize integer Sobolev regularity.
This closes the higher nonlinear chain rules after their L2 product limits. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "T" => 𝓢'(V, ℂ)

theorem scalarCoordinateJet_append (is js : List (Fin 4)) (u : T) :
    scalarCoordinateJet (is ++ js) u = scalarCoordinateJet is (scalarCoordinateJet js u) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, scalarCoordinateJet_cons, ih]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The interpolation estimate between scalar L² and L⁴, in the exact
subcritical range used for the Sobolev minimizer. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped ENNReal _root_.Topology

noncomputable section

theorem scalar_subcritical_moment_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : X → ℝ) (hf : AEStronglyMeasurable f μ)
    {p : ℝ} (hp : 2 ≤ p) (hp4 : p ≤ 4) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ≤
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ ((4 - p) / 2) *
        (∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂μ) ^ ((p - 2) / 2) := by
  have ha : 0 ≤ (4 - p) / 2 := by linarith
  have hb : 0 ≤ (p - 2) / 2 := by linarith
  have hsum : (4 - p) / 2 + (p - 2) / 2 = 1 := by ring
  have h := ENNReal.lintegral_mul_norm_pow_le
    (hf.enorm.pow_const (2 : ℝ))
    (hf.enorm.pow_const (4 : ℝ)) ha hb hsum
  have he (x : X) : (‖f x‖ₑ ^ (2 : ℝ)) ^ ((4 - p) / 2) *
      (‖f x‖ₑ ^ (4 : ℝ)) ^ ((p - 2) / 2) = ‖f x‖ₑ ^ p := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg (by norm_num) ha)
        (mul_nonneg (by norm_num) hb)]
    congr 1
    ring
  simpa only [he] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Lp representatives and convergence in the subcritical range.
The inclusion uses the same almost-everywhere function; the convergence
statement combines small L² norm with a bounded L⁴ norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

theorem scalar_subcritical_moment_filter_tendsto_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {ι : Type*} {l : Filter ι}
    (f : ι → X → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {p : ℝ} (hp : 2 < p) (hp4 : p < 4) {B : ℝ≥0∞} (hB : B ≠ (∞ : ℝ≥0∞))
    (hfour : ∀ n, (∫⁻ x, ‖f n x‖ₑ ^ (4 : ℝ) ∂μ) ≤ B)
    (htwo : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ p ∂μ) l (𝓝 0) := by
  have ha : 0 < (4 - p) / 2 := by linarith
  have hb : 0 ≤ (p - 2) / 2 := by linarith
  have hlimit : Tendsto
      (fun n => (∫⁻ x, ‖f n x‖ₑ ^ (2 : ℝ) ∂μ) ^ ((4 - p) / 2)) l (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (4 - p) / 2)).tendsto (0 : ℝ≥0∞)
    rw [ENNReal.zero_rpow_of_pos ha] at h
    exact h.comp htwo
  have hbound : B ^ ((p - 2) / 2) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg hb hB
  have hproduct := ENNReal.Tendsto.mul_const hlimit (Or.inr hbound)
  rw [zero_mul] at hproduct
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hproduct
    (fun n => (show (0 : ℝ≥0∞) ≤ (∫⁻ x, ‖f n x‖ₑ ^ p ∂μ) from bot_le))
  intro n
  exact (scalar_subcritical_moment_le (f n) (hf n) hp.le hp4.le).trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hfour n) hb))

theorem scalar_subcritical_eLpNorm_tendsto_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {ι : Type*} {l : Filter ι}
    (f : ι → X → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {p : ℝ} (hp : 2 < p) (hp4 : p < 4) {B : ℝ≥0∞} (hB : B ≠ (∞ : ℝ≥0∞))
    (hfour : ∀ n, eLpNorm (f n) 4 μ ≤ B)
    (htwo : Tendsto (fun n => eLpNorm (f n) 2 μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) (ENNReal.ofReal p) μ) l (𝓝 0) := by
  have hm2 (n : ι) : (∫⁻ x, ‖f n x‖ₑ ^ (2 : ℝ) ∂μ) =
      eLpNorm (f n) 2 μ ^ (2 : ℝ) :=
    (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)).symm
  have hm4 (n : ι) : (∫⁻ x, ‖f n x‖ₑ ^ (4 : ℝ) ∂μ) =
      eLpNorm (f n) 4 μ ^ (4 : ℝ) :=
    (eLpNorm_nnreal_pow_eq_lintegral (p := (4 : ℝ≥0)) (by norm_num)).symm
  have ht : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) := by
    simpa only [Function.comp_def, hm2,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp htwo
  have hb4 : B ^ (4 : ℝ) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB
  have hmoment := scalar_subcritical_moment_filter_tendsto_zero f hf hp hp4 hb4
    (fun n => by rw [hm4]; exact ENNReal.rpow_le_rpow (hfour n) (by norm_num)) ht
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hpow := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hmoment
  rw [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] at hpow
  convert hpow using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Absolute values in actual Lp and the convergence of positive smooth
regularizations of an approximating scalar sequence. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

theorem scalarLpAbs_nonneg (f : Lp ℝ p μ) : ∀ᵐ x ∂μ, 0 ≤ scalarLpAbs f x := by
  filter_upwards [scalarLpAbs_coe f] with x hx
  rw [hx]
  exact abs_nonneg _

theorem scalarLpAbs_continuous [Fact (1 ≤ p)] :
    Continuous (scalarLpAbs : Lp ℝ p μ → Lp ℝ p μ) :=
  lipschitzWith_one_norm.continuous_compLp norm_zero

end
end PositiveEinsteinFour.Geometry
end


section

/-! The L8 gain puts the actual subcritical nonlinearity in L2, allowing
the weak equation to use every H1 test and the proved elliptic estimates. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

theorem scalar_nonlinear_memLp_two_of_eight {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ} (hf : MemLp f 8 μ)
    {p : ℝ} (hp : 2 < p) (hp4 : p < 4) :
    MemLp (fun x => |f x| ^ (p - 2) * f x) 2 μ := by
  have hexp : (6 : ℝ≥0∞) / 3 = 2 := by
    rw [show (6 : ℝ≥0∞) = 2 * 3 by norm_num]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  have hcube : MemLp (fun x => |f x| ^ 3) 2 μ := by
    have h := (hf.mono_exponent (by norm_num : (6 : ℝ≥0∞) ≤ 8)).norm_rpow_div 3
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs, hexp] using h
  have hc : Continuous (fun s : ℝ => |s| ^ (p - 2) * s) :=
    (continuous_abs.rpow_const (fun _ => Or.inr (by linarith : 0 ≤ p - 2))).mul continuous_id
  have hdom : MemLp (fun x => 1 + |f x| ^ 3) 2 μ := (memLp_const (1 : ℝ)).add hcube
  apply hdom.mono' (hc.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  filter_upwards [] with x
  have hnorm : ‖|f x| ^ (p - 2) * f x‖ = |f x| ^ (p - 1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      ← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 2 + 1 ≠ 0)]
    congr 1
    ring
  rw [hnorm]
  by_cases hsmall : |f x| ≤ 1
  · exact (Real.rpow_le_one (abs_nonneg _) hsmall (by linarith : 0 ≤ p - 1)).trans
      (le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) 3))
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hsmall)
      (by linarith : p - 1 ≤ 3)
    have h3 : |f x| ^ (p - 1) ≤ |f x| ^ (3 : ℕ) := by
      simpa only [Real.rpow_ofNat] using h
    exact h3.trans (le_add_of_nonneg_left zero_le_one)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first derivative of the subcritical nonlinearity is square
integrable once the actual H2 estimate supplies L4 weak derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

theorem scalar_subcritical_derivative_memLp_four
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : MemLp f 8 μ) {p : ℝ} (hp : 2 < p) (hp4 : p < 4) :
    MemLp (fun x => (p - 1) * |f x| ^ (p - 2)) 4 μ := by
  have hs : MemLp (fun x => |f x| ^ (2 : ℕ)) 4 μ := by
    have hexp : (8 : ℝ≥0∞) / 2 = 4 := by
      rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num]
      exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    simpa only [hexp, ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs] using
      hf.norm_rpow_div 2
  have hd : MemLp (fun x => 1 + |f x| ^ (2 : ℕ)) 4 μ := (memLp_const (1 : ℝ)).add hs
  have hm : MemLp (fun x => |f x| ^ (p - 2)) 4 μ := by
    apply hd.mono'
      ((continuous_abs.rpow_const (fun _ => Or.inr (by linarith : 0 ≤ p - 2))).comp_aestronglyMeasurable hf.aestronglyMeasurable)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    by_cases hx : |f x| ≤ 1
    · exact (Real.rpow_le_one (abs_nonneg _) hx (by linarith)).trans
        (le_add_of_nonneg_right (sq_nonneg _))
    · have hr := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx)
        (show p - 2 ≤ 2 by linarith)
      have hr2 : |f x| ^ (p - 2) ≤ |f x| ^ (2 : ℕ) := by
        simpa only [Real.rpow_ofNat] using hr
      exact hr2.trans (le_add_of_nonneg_left zero_le_one)
  exact hm.const_mul _

theorem scalar_subcritical_nonlinear_gradient_memLp_two
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f v : X → ℝ} (hf : MemLp f 8 μ) (hv : MemLp v 4 μ)
    {p : ℝ} (hp : 2 < p) (hp4 : p < 4) :
    MemLp (fun x => (p - 1) * |f x| ^ (p - 2) * v x) 2 μ :=
  by
    have : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
      constructor
      change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0) : ℝ≥0∞)⁻¹
      rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
        ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
      norm_num
    exact MeasureTheory.MemLp.mul (hφ := (scalar_subcritical_derivative_memLp_four hf hp hp4)) (hf := hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The subcritical nonlinear chain rule on the actual H1 closure. Smooth
bounded-derivative truncations converge strongly in the value and all four
weak derivatives, using L8 values and L4 gradients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

theorem nonlinear_power_tendsto {q : ℝ} (hq : 0 < q) (s : ℝ) :
    Tendsto (fun n => (s ^ 2 + nonlinearEpsilon n) ^ (q / 2)) atTop (𝓝 (|s| ^ q)) := by
  have hbase : Tendsto (fun n => s ^ 2 + nonlinearEpsilon n) atTop (𝓝 (s ^ 2)) :=
    by simpa only [add_zero] using
      (show Tendsto (fun _ : ℕ => s ^ 2) atTop (𝓝 (s ^ 2)) from tendsto_const_nhds).add
        nonlinearEpsilon_tendsto
  have ht := hbase.rpow_const (Or.inr (show 0 ≤ q / 2 by positivity))
  simpa only [add_zero, nonlinear_square_rpow] using ht

theorem nonlinear_value_tendsto {q : ℝ} (hq : 0 < q) (s : ℝ) :
    Tendsto (fun n => scalarNonlinearTruncation q (nonlinearEpsilon n) s)
      atTop (𝓝 (|s| ^ q * s)) := by
  have hd : Tendsto (fun n => 1 + nonlinearEpsilon n * s ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add (nonlinearEpsilon_tendsto.mul_const (s ^ 2))
  have h := ((nonlinear_power_tendsto hq s).const_mul s).div hd one_ne_zero
  simpa only [scalarNonlinearTruncation, Pi.div_apply, div_one, mul_comm] using! h

section Measure

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem nonlinear_L2_tendsto (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ)
    (B : X → ℝ) (hB : MemLp B 2 μ)
    (hfB : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ B x)
    (hgB : ∀ᵐ x ∂μ, |g x| ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto f atTop (𝓝 g) := by
  let d : ℕ → Lp ℝ 2 μ := fun n => f n - g
  have hd (n : ℕ) : d n =ᵐ[μ] fun x => f n x - g x := Lp.coeFn_sub _ _
  have hint := tendsto_integral_of_dominated_convergence (fun x => (2 * B x) ^ 2)
    (fun n => ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable g)).pow 2)
    (by simpa only [mul_pow] using hB.integrable_sq.const_mul (2 ^ 2 : ℝ))
    (fun n => by
      filter_upwards [hfB n, hgB] with x hfx hgx
      simp only [Pi.pow_apply, Pi.sub_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ha : |f n x - g x| ≤ 2 * B x := (abs_sub _ _).trans (by linarith)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by linarith [abs_nonneg (g x)])).2 ha)
    (f := fun _ => (0 : ℝ)) (by
      filter_upwards [hlim] with x hx
      simpa only [Pi.pow_apply, Pi.sub_apply, sub_self, zero_pow (by decide : 2 ≠ 0)] using!
        (hx.sub_const (g x)).pow 2)
  have hs : Tendsto (fun n => ‖d n‖ ^ 2) atTop (𝓝 0) := by
    convert hint using 1
    · funext n
      rw [scalarL2_norm_sq]
      exact integral_congr_ae ((hd n).fun_comp fun t : ℝ => t ^ 2)
    · simp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero, d] using h

variable [IsFiniteMeasure μ]

theorem nonlinear_value_dominator {f : X → ℝ} (hf : MemLp f 8 μ) :
    MemLp (fun x => |f x| * (1 + f x ^ 2)) 2 μ := by
  have hexp : (6 : ℝ≥0∞) / 3 = 2 := by
    rw [show (6 : ℝ≥0∞) = 2 * 3 by norm_num]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  have hcube : MemLp (fun x => |f x| ^ (3 : ℕ)) 2 μ := by
    have h := (hf.mono_exponent (by norm_num : (6 : ℝ≥0∞) ≤ 8)).norm_rpow_div 3
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs,
      hexp] using h
  convert (hf.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 8)).norm.add hcube using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  change |f x| * (1 + f x ^ 2) = ‖f x‖ + |f x| ^ 3
  rw [Real.norm_eq_abs, ← sq_abs]
  ring

theorem nonlinear_gradient_dominator {f v : X → ℝ}
    (hf : MemLp f 8 μ) (hv : MemLp v 4 μ) :
    MemLp (fun x => 5 * (1 + f x ^ 2) * |v x|) 2 μ := by
  have hexp : (8 : ℝ≥0∞) / 2 = 4 := by
    rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  have hs : MemLp (fun x => f x ^ 2) 4 μ := by
    have h := hf.norm_rpow_div 2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      hexp] using h
  have : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
    constructor
    change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
    norm_num
  exact MemLp.mul' (r := 2) hv.norm ((memLp_const (1 : ℝ)).add hs |>.const_mul 5)

end Measure

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The radial determinant estimate with the actual volume factor retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

local instance instNormedAddCommGroupMat3_5 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup

end

end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature-energy volume deficit in the normalization used
by the proved Euler and signature integrals. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
local instance normalizedGeometricVolumeNorm : NormedAddCommGroup Mat3 :=
  Matrix.frobeniusNormedAddCommGroup

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

/-! Constant-curvature Jacobi fields for the round branch of model
identification. All coefficients are the actual metric curvature. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Set
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator
noncomputable section

theorem MatrixJacobiSolution.eq_sine_of_curvature_one {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : ∀ t, R t = 1) (t : ℝ) :
    d.J t = Real.sin t • (1 : NormalMatrix) ∧
      d.V t = Real.cos t • (1 : NormalMatrix) := by
  let γ : ℝ → JacobiState := fun s => (d.J s, d.V s)
  let η : ℝ → JacobiState := fun s =>
    (Real.sin s • (1 : NormalMatrix), Real.cos s • (1 : NormalMatrix))
  let a := -(|t| + 1)
  let b := |t| + 1
  have hγ : LinearCurveOn (fun _ => jacobiStateOperator (1 : NormalMatrix)) γ (Ioo a b) := by
    intro s _
    simpa only [γ, hR s, one_mul, jacobiStateOperator_apply] using
      (d.position_derivative s).prodMk (d.velocity_derivative s)
  have hη : LinearCurveOn (fun _ => jacobiStateOperator (1 : NormalMatrix)) η (Ioo a b) := by
    intro s _
    simpa only [η, jacobiStateOperator_apply, one_mul, neg_smul] using
      ((Real.hasDerivAt_sin s).smul_const (1 : NormalMatrix)).prodMk
        ((Real.hasDerivAt_cos s).smul_const (1 : NormalMatrix))
  have hbound (s : ℝ) : ‖jacobiStateOperator (1 : NormalMatrix)‖ ≤
      (‖jacobiStateOperator (1 : NormalMatrix)‖₊ : ℝ) := le_rfl
  have hzero : (0 : ℝ) ∈ Ioo a b :=
    ⟨by dsimp [a]; linarith [abs_nonneg t], by dsimp [b]; positivity⟩
  have hinit : γ 0 = η 0 := by simp [γ, η, d.initial_position, d.initial_velocity]
  have heq := linear_curve_eqOn_interval (fun _ => jacobiStateOperator (1 : NormalMatrix))
    ‖jacobiStateOperator (1 : NormalMatrix)‖₊ hbound hγ hη hzero hinit
  have ht : t ∈ Ioo a b := by
    dsimp [a, b]
    exact abs_lt.mp (lt_add_one |t|)
  exact ⟨congrArg Prod.fst (heq ht), congrArg Prod.snd (heq ht)⟩

end
end PositiveEinsteinFour.Jacobi

end


section

/-! The two eigenvalues of unit parallel Weyl curvature are expressed by
an actual orthogonal projection, without choosing eigenvectors. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix
open scoped BigOperators
noncomputable section

def unitWeylProjection (A : Mat) : Mat := (1 / 3 : ℝ) • (A + 1)

theorem unitWeylProjection_idempotent (A : Mat)
    (hA : A * A = A + (2 : ℝ) • (1 : Mat)) :
    IsIdempotentElem (unitWeylProjection A) := by
  change ((1 / 3 : ℝ) • (A + 1)) * ((1 / 3 : ℝ) • (A + 1)) = (1 / 3 : ℝ) • (A + 1)
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hA]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem unitWeylProjection_symmetric (A : Mat) (hA : symmetric A) :
    (unitWeylProjection A).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  have hAs : Aᵀ = A := by ext i j; exact hA j i
  change (unitWeylProjection A)ᵀ = unitWeylProjection A
  simp only [unitWeylProjection, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_one, hAs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact matrix Jacobi solution for the two eigenspaces of the
Ricci-normalized complex-space-form curvature. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

def complexJacobiCurvature (P : NormalMatrix) : NormalMatrix :=
  (1 / 2 : ℝ) • (1 : NormalMatrix) + (3 / 2 : ℝ) • P

def complexJacobiPosition (P : NormalMatrix) (t : ℝ) : NormalMatrix :=
  complexJacobiSlow t • (1 - P) + complexJacobiFast t • P

def complexJacobiVelocity (P : NormalMatrix) (t : ℝ) : NormalMatrix :=
  Real.cos (t / Real.sqrt 2) • (1 - P) + Real.cos (Real.sqrt 2 * t) • P

theorem complexJacobiCurvature_mul_projection (P : NormalMatrix) (hP : P * P = P) :
    complexJacobiCurvature P * P = (2 : ℝ) • P := by
  rw [complexJacobiCurvature, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.one_mul, hP]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem complexJacobiCurvature_mul_complement (P : NormalMatrix) (hP : P * P = P) :
    complexJacobiCurvature P * (1 - P) = (1 / 2 : ℝ) • (1 - P) := by
  rw [Matrix.mul_sub, Matrix.mul_one, complexJacobiCurvature_mul_projection P hP]
  ext i j
  simp only [complexJacobiCurvature, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Jacobi
end


section

/-! The determinant and first zero of the complex-space-form Jacobi matrix. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

theorem complexJacobiRadius_pos : 0 < complexJacobiRadius := by
  exact div_pos Real.pi_pos (by positivity)

end
end PositiveEinsteinFour.Jacobi
end


section

/-! Squaring the actual complex Jacobi solution retains its two orthogonal
eigenspaces. This is the pullback metric, rather than merely its determinant. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix PositiveEinsteinFour.Geometry
noncomputable section

def complexJacobiGram (P : NormalMatrix) (t : ℝ) : NormalMatrix :=
  complexJacobiSlow t ^ 2 • (1 - P) + complexJacobiFast t ^ 2 • P

theorem complexJacobiPosition_transpose_mul (P : NormalMatrix)
    (hs : Pᵀ = P) (hp : P * P = P) (t : ℝ) :
    (complexJacobiPosition P t)ᵀ * complexJacobiPosition P t = complexJacobiGram P t := by
  have hPQ : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hp, sub_self]
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPQ, sub_zero]
  have hQP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hp, sub_self]
  rw [complexJacobiPosition, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one, hs,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hQ, hPQ, hQP, hp, smul_zero,
    add_zero, zero_add, smul_smul, complexJacobiGram, pow_two]

end
end PositiveEinsteinFour.Jacobi
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Real complex circles are exactly multiplication by unit complex scalars. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
noncomputable section

theorem complexPhase_arg (a : ℂ) (ha : ‖a‖ = 1) : complexPhase a.arg = a := by
  have hz : a ≠ 0 := by
    intro h
    rw [h,norm_zero] at ha
    exact zero_ne_one ha
  apply Complex.ext
  · change Real.cos a.arg = a.re
    rw [Complex.cos_arg hz,ha,div_one]
  · change Real.sin a.arg = a.im
    rw [Complex.sin_arg,ha,div_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unit representatives with nonnegative real first coordinate, for the
closed-ball polar description of the actual projective plane. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem cp2_exists_first_aligned (p : ComplexProjective2) :
    ∃ z : CP2Vector, ∃ hz : z ≠ 0,
      ‖z‖ = 1 ∧ Projectivization.mk ℂ z hz = p ∧
      (z 0).im = 0 ∧ 0 ≤ (z 0).re := by
  let x := cp2UnitRep p
  have hx : x ≠ 0 := cp2UnitRep_ne_zero p
  by_cases hz : x 0 = 0
  · exact ⟨x,hx,cp2UnitRep_norm p,cp2UnitRep_mk p,by rw [hz]; rfl,
      by rw [hz]; exact le_rfl⟩
  let a : ℂ := (‖x 0‖ : ℂ) / x 0
  have ha : a ≠ 0 := div_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr hz) hz
  have han : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, norm_ne_zero_iff.mpr hz]
  let z := a • x
  have hzn : z ≠ 0 := smul_ne_zero ha hx
  have hz0 : z 0 = (‖x 0‖ : ℂ) := by
    change a * x 0 = _
    exact div_mul_cancel₀ _ hz
  refine ⟨z,hzn,?_,?_,?_,?_⟩
  · change ‖a • x‖ = 1
    rw [norm_smul, han, cp2UnitRep_norm, mul_one]
  · rw [← cp2UnitRep_mk p]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a,rfl⟩
  · rw [hz0]
    rfl
  · rw [hz0]
    exact norm_nonneg _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Norm and inner product of the actual homogeneous projective coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexHeadTail (a : ℂ) (u : EuclideanSpace ℂ (Fin 2)) : CP2Vector :=
  WithLp.toLp 2 ![a,u 0,u 1]

theorem complexHeadTail_norm_sq (a : ℂ) (u : EuclideanSpace ℂ (Fin 2)) :
    ‖complexHeadTail a u‖ ^ 2 = ‖a‖ ^ 2 + ‖u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,Fin.sum_univ_three,Fin.sum_univ_two]
  change ‖a‖ ^ 2 + ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = ‖a‖ ^ 2 + (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2)
  ring

theorem complexHeadTail_inner (a b : ℂ) (u v : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (complexHeadTail a u) (complexHeadTail b v) =
      b * star a + inner ℂ u v := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two,
    Pi.star_apply]
  change b * star a + v 0 * star (u 0) + v 1 * star (u 1) =
    b * star a + (v 0 * star (u 0) + v 1 * star (u 1))
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The projective quotient preserves the polar radius and is injective
at every strictly positive radius before the boundary. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

theorem complexPolar_angle_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius) :
    t / Real.sqrt 2 ∈ Icc (0 : ℝ) (Real.pi / 2) := by
  refine ⟨div_nonneg ht.1 (Real.sqrt_nonneg _), ?_⟩
  have h := div_le_div_of_nonneg_right ht.2 (Real.sqrt_nonneg 2)
  unfold complexJacobiRadius at h
  rw [div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary affine chart of CP2 and its exact polar coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

def complexAffineLift (z : EuclideanSpace ℂ (Fin 2)) : CP2Vector :=
  WithLp.toLp 2 ![1,z 0,z 1]

theorem complexAffineLift_ne_zero (z : EuclideanSpace ℂ (Fin 2)) : complexAffineLift z ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : CP2Vector => v 0) h
  exact one_ne_zero h0

def complexAffinePoint (z : EuclideanSpace ℂ (Fin 2)) : ComplexProjective2 :=
  Projectivization.mk ℂ (complexAffineLift z) (complexAffineLift_ne_zero z)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact boundary equivalence relation of the projective polar ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
noncomputable section

theorem complexPolar_radius_angle : complexJacobiRadius / Real.sqrt 2 = Real.pi / 2 := by
  rw [complexJacobiRadius,div_div,← pow_two,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact logarithm of the standard projective affine chart, in the
Ricci-three normal coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

theorem complexAffineRadius_mem (z : EuclideanSpace ℂ (Fin 2)) :
    complexAffineRadius z ∈ Ico (0 : ℝ) complexJacobiRadius := by
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (Real.arctan_nonneg.mpr (norm_nonneg _)),?_⟩
  have h := mul_lt_mul_of_pos_left (Real.arctan_lt_pi_div_two ‖z‖)
    (by positivity : 0 < Real.sqrt 2)
  have heq : Real.sqrt 2 * (Real.pi / 2) = complexJacobiRadius := by
    unfold complexJacobiRadius
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact h.trans_eq heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity of the Fubini--Study distance in the projective overlap topology. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section
attribute [local instance] complexProjectiveTopology

theorem fubiniStudyDistance_left_continuous (P : ComplexProjective2) :
    Continuous (fubiniStudyDistance P) := by
  have h : Continuous (fun Q : ComplexProjective2 => cp2Overlap P Q) :=
    (continuous_apply P).comp complexProjectiveEvaluation_isEmbedding.continuous
  change Continuous (fun Q => fubiniStudyDistance P Q)
  simp_rw [fubiniStudyDistance_eq_arccos]
  exact Real.continuous_arccos.comp h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The homogeneous lift of the actual normal-coordinate projective map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
noncomputable section

theorem complexHeadTail_hasDerivAt {a : ℝ → ℂ} {b : ℝ → EuclideanSpace ℂ (Fin 2)}
    {a' : ℂ} {b' : EuclideanSpace ℂ (Fin 2)} {s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) :
    HasDerivAt (fun r => complexHeadTail (a r) (b r)) (complexHeadTail a' b') s := by
  have hb' := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt s hb
  have hp : HasDerivAt (fun r => (![a r,b r 0,b r 1] : Fin 3 → ℂ))
      (![a',b' 0,b' 1] : Fin 3 → ℂ) s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ha
    · exact hasDerivAt_pi.mp hb' 0
    · exact hasDerivAt_pi.mp hb' 1
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt s hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Horizontal projection and the phase-invariant projective speed. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexHorizontalPart (u v : CP2Vector) : CP2Vector := v - (inner ℂ u v) • u

theorem complexHorizontalPart_orthogonal (u v : CP2Vector) (hu : ‖u‖ = 1) :
    inner ℂ u (complexHorizontalPart u v) = 0 := by
  simp [complexHorizontalPart,inner_self_eq_norm_sq_to_K,hu]

theorem complexHorizontalPart_norm_sq (u v : CP2Vector) (hu : ‖u‖ = 1) :
    ‖complexHorizontalPart u v‖^2 = ‖v‖^2 - ‖inner ℂ u v‖^2 := by
  have hsum : (inner ℂ u v) • u + complexHorizontalPart u v = v := by
    dsimp [complexHorizontalPart]
    abel
  have hn := norm_add_sq (𝕜 := ℂ) ((inner ℂ u v) • u) (complexHorizontalPart u v)
  rw [hsum,inner_smul_left,complexHorizontalPart_orthogonal u v hu,mul_zero] at hn
  simp only [map_zero,mul_zero,add_zero,norm_smul,hu,mul_one] at hn
  linarith

theorem complexHorizontalPart_phase (u v : CP2Vector) (hu : ‖u‖ = 1)
    (a b : ℂ) (ha : ‖a‖ = 1) :
    complexHorizontalPart (a • u) (b • u + a • v) = a • complexHorizontalPart u v := by
  have haa : star a * a = 1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',ha]
    norm_num
  have hi : inner ℂ (a • u) (b • u + a • v) = star a * b + inner ℂ u v := by
    simp only [inner_smul_left,inner_add_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hu]
    norm_num only [RCLike.ofReal_one,one_pow,mul_one]
    simp only [starRingEnd_apply]
    calc
      _ = star a * b + (star a * a) * inner ℂ u v := by ring
      _ = _ := by rw [haa,one_mul]
  have hs : (star a * b + inner ℂ u v) * a = b + a * inner ℂ u v := by
    calc
      _ = (star a * a) * b + a * inner ℂ u v := by ring
      _ = _ := by rw [haa,one_mul]
  rw [complexHorizontalPart,hi,smul_smul,hs]
  dsimp [complexHorizontalPart]
  module

theorem complexHorizontalPart_phase_norm (u v : CP2Vector) (hu : ‖u‖ = 1)
    (a b : ℂ) (ha : ‖a‖ = 1) :
    ‖complexHorizontalPart (a • u) (b • u + a • v)‖ = ‖complexHorizontalPart u v‖ := by
  rw [complexHorizontalPart_phase u v hu a b ha,norm_smul,ha,one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Horizontal great circles of unit homogeneous representatives. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexGreatCircle (p q : CP2Vector) (t : ℝ) : CP2Vector :=
  Real.cos t • p + Real.sin t • q

def complexGreatCircleVelocity (p q : CP2Vector) (t : ℝ) : CP2Vector :=
  -Real.sin t • p + Real.cos t • q

theorem complexGreatCircle_hasDerivAt (p q : CP2Vector) (t : ℝ) :
    HasDerivAt (complexGreatCircle p q) (complexGreatCircleVelocity p q t) t := by
  exact ((Real.hasDerivAt_cos t).smul_const p).add ((Real.hasDerivAt_sin t).smul_const q)

theorem complexGreatCircle_norm (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) : ‖complexGreatCircle p q t‖ = 1 := by
  have hr : inner ℝ p q = 0 := by
    simpa only [Complex.zero_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hpq
  have hs : ‖complexGreatCircle p q t‖^2 = 1 := by
    rw [complexGreatCircle,norm_add_sq_real,norm_smul,norm_smul,
      real_inner_smul_left,real_inner_smul_right,hr,hp,hq]
    simp only [Real.norm_eq_abs,mul_one,mul_zero,add_zero,sq_abs]
    exact Real.cos_sq_add_sin_sq t
  nlinarith [norm_nonneg (complexGreatCircle p q t)]

theorem complexGreatCircleVelocity_norm (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) : ‖complexGreatCircleVelocity p q t‖ = 1 := by
  have hr : inner ℝ p q = 0 := by
    simpa only [Complex.zero_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hpq
  have hs : ‖complexGreatCircleVelocity p q t‖^2 = 1 := by
    rw [complexGreatCircleVelocity,norm_add_sq_real,norm_smul,norm_smul,
      real_inner_smul_left,real_inner_smul_right,hr,hp,hq]
    simp only [Real.norm_eq_abs,mul_one,mul_zero,add_zero,abs_neg,sq_abs]
    exact Real.sin_sq_add_cos_sq t
  nlinarith [norm_nonneg (complexGreatCircleVelocity p q t)]

theorem complexGreatCircle_horizontal (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) :
    inner ℂ (complexGreatCircle p q t) (complexGreatCircleVelocity p q t) = 0 := by
  have hqp : inner ℂ q p = 0 := by rw [← inner_conj_symm,hpq]; simp
  simp only [complexGreatCircle,complexGreatCircleVelocity,inner_add_left,inner_add_right,
    inner_smul_left_eq_smul,inner_smul_right_eq_smul,inner_self_eq_norm_sq_to_K,hp,hq,hpq,hqp]
  norm_num
  ring

theorem complexGreatCircle_horizontal_speed (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) :
    ‖complexHorizontalPart (complexGreatCircle p q t) (complexGreatCircleVelocity p q t)‖ = 1 := by
  rw [complexHorizontalPart,complexGreatCircle_horizontal p q hp hq hpq,zero_smul,sub_zero,
    complexGreatCircleVelocity_norm p q hp hq hpq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Horizontal speed is independent of a differentiable unit lift. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped _root_.Topology
noncomputable section

theorem complex_unit_aligned_coefficient (u w : CP2Vector) (hu : ‖u‖ = 1)
    (heq : ∃ a : ℂ, w = a • u) :
    w = (inner ℂ u w) • u := by
  obtain ⟨a,rfl⟩ := heq
  simp [inner_self_eq_norm_sq_to_K,hu]

theorem complexHorizontalPart_curve_invariant {u w : ℝ → CP2Vector}
    {u' w' : CP2Vector} {s : ℝ}
    (hu : ∀ r, ‖u r‖ = 1) (hw : ∀ r, ‖w r‖ = 1)
    (heq : ∀ᶠ r in 𝓝 s, ∃ a : ℂ, w r = a • u r)
    (hdu : HasDerivAt u u' s) (hdw : HasDerivAt w w' s) :
    ‖complexHorizontalPart (w s) w'‖ = ‖complexHorizontalPart (u s) u'‖ := by
  let a : ℝ → ℂ := fun r => inner ℂ (u r) (w r)
  have halign : ∀ᶠ r in 𝓝 s, w r = a r • u r := by
    filter_upwards [heq] with r hr
    exact complex_unit_aligned_coefficient (u r) (w r) (hu r) hr
  have ha : ‖a s‖ = 1 := by
    have h := hw s
    rw [halign.self_of_nhds,norm_smul,hu s,mul_one] at h
    exact h
  let b : ℂ := inner ℂ (u s) w' + inner ℂ u' (w s)
  have hda : HasDerivAt a b s := hdu.inner ℂ hdw
  have hd : HasDerivAt (fun r => a r • u r) (a s • u' + b • u s) s := hda.smul hdu
  have hv : w' = b • u s + a s • u' :=
    (hdw.unique (hd.congr_of_eventuallyEq halign)).trans (add_comm _ _)
  calc
    _ = ‖complexHorizontalPart (a s • u s) (b • u s + a s • u')‖ := by
      congr 2
      · exact halign.self_of_nhds
    _ = _ := complexHorizontalPart_phase_norm (u s) u' (hu s) (a s) b ha

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cauchy--Schwarz for the horizontal part of a projective velocity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complexHorizontalPairing (p u w : CP2Vector)
    (hw : (inner ℂ u w).re = 0) :
    inner ℝ (inner ℂ p u) (inner ℂ p w) =
      inner ℝ (inner ℂ p u) (inner ℂ p (complexHorizontalPart u w)) := by
  have hdec : inner ℂ p w = (inner ℂ u w) * inner ℂ p u +
      inner ℂ p (complexHorizontalPart u w) := by
    simp only [complexHorizontalPart,inner_sub_right,inner_smul_right]
    ring
  rw [hdec,inner_add_right,complex_real_inner_mul_self,hw,mul_zero,zero_add]

theorem complex_horizontal_inner_bound (p u w : CP2Vector) (hu : ‖u‖ = 1) :
    ‖inner ℂ p (complexHorizontalPart u w)‖ ≤
      ‖complexHorizontalPart u p‖ * ‖complexHorizontalPart u w‖ := by
  have heq : inner ℂ (complexHorizontalPart u p) (complexHorizontalPart u w) =
      inner ℂ p (complexHorizontalPart u w) := by
    rw [complexHorizontalPart,inner_sub_left,inner_smul_left,
      complexHorizontalPart_orthogonal u w hu,mul_zero,sub_zero]
  rw [← heq]
  exact norm_inner_le_norm _ _

theorem complex_unit_curve_tangent {u : ℝ → UnitSphere CP2Vector} {t : ℝ}
    {w : CP2Vector} (hd : HasDerivAt (fun s => (u s).val) w t) :
    (inner ℂ (u t).val w).re = 0 := by
  have h := hd.norm_sq
  have heq : (fun s => ‖(u s).val‖^2) = fun _ : ℝ => (1 : ℝ) := by
    funext s
    rw [(u s).property,one_pow]
  rw [heq] at h
  have hz := h.unique (hasDerivAt_const t (1 : ℝ))
  have hr : inner ℝ (u t).val w = 0 := by linarith
  simpa only [← real_inner_eq_re_inner ℂ] using! hr

end
end PositiveEinsteinFour.Geometry
end


section

/-! Affine coordinates of an actual homogeneous vector and their regularity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexTailLinear : CP2Vector →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun v := WithLp.toLp 2 ![v 1,v 2]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

def complexTailCLM : CP2Vector →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  complexTailLinear.toContinuousLinearMap

def complexVectorAffine (v : CP2Vector) : EuclideanSpace ℂ (Fin 2) :=
  (v 0)⁻¹ • complexTailCLM v

theorem complexVectorAffine_differentiableAt {v : CP2Vector} (hv : v 0 ≠ 0) :
    DifferentiableAt ℝ complexVectorAffine v := by
  have hh : DifferentiableAt ℝ (fun u : CP2Vector => u 0) v :=
    ((PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 3 => ℂ) 0).restrictScalars ℝ).differentiableAt
  exact (hh.inv hv).smul (complexTailCLM.restrictScalars ℝ).differentiableAt

theorem complexAffinePoint_vector (v : CP2Vector) (hv : v 0 ≠ 0) (hv0 : v ≠ 0) :
    complexAffinePoint (complexVectorAffine v) = Projectivization.mk ℂ v hv0 := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(v 0)⁻¹,?_⟩
  ext i
  fin_cases i
  · change (v 0)⁻¹ * v 0 = 1
    exact inv_mul_cancel₀ hv
  · rfl
  · rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! C1 regularity of the affine logarithm used for projective paths. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complexVectorAffine_contDiffAt {v : CP2Vector} (hv : v 0 ≠ 0) :
    ContDiffAt ℝ 1 complexVectorAffine v := by
  have hh : ContDiffAt ℝ 1 (fun u : CP2Vector => u 0) v :=
    ((PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 3 => ℂ) 0).restrictScalars ℝ).contDiff.contDiffAt
  have ht : ContDiffAt ℝ 1 (fun u => complexTailCLM u) v :=
    (complexTailCLM.restrictScalars ℝ).contDiff.contDiffAt
  exact (hh.inv hv).smul ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unit-sphere representatives of the horizontal projective great circles. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexGreatCircleUnit (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) : UnitSphere CP2Vector :=
  ⟨complexGreatCircle p q t,complexGreatCircle_norm p q hp hq hpq t⟩

theorem complexGreatCircle_contDiff (p q : CP2Vector) : ContDiff ℝ 1 (complexGreatCircle p q) := by
  unfold complexGreatCircle
  fun_prop

theorem complexGreatCircleUnit_continuous (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) : Continuous (complexGreatCircleUnit p q hp hq hpq) :=
  (complexGreatCircle_contDiff p q).continuous.subtype_mk _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual unit-sphere projection to the projective overlap topology. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section
attribute [local instance] complexProjectiveTopology

def complexSphereProjection (p : UnitSphere CP2Vector) : ComplexProjective2 :=
  Projectivization.mk ℂ p.val (unitSphere_ne_zero p)

theorem complexSphereProjection_continuous : Continuous complexSphereProjection := by
  apply complexProjectiveEvaluation_isEmbedding.continuous_iff.mpr
  apply continuous_pi
  intro p
  change Continuous (fun q : UnitSphere CP2Vector => cp2Overlap p (complexSphereProjection q))
  have heq (q : UnitSphere CP2Vector) : cp2Overlap p (complexSphereProjection q) =
      ‖inner ℂ (cp2UnitRep p) q.val‖ :=
    cp2Overlap_of_unit_representatives _ _ _ _ (cp2UnitRep_ne_zero p)
      (unitSphere_ne_zero q) (cp2UnitRep_norm p) q.property (cp2UnitRep_mk p) rfl
  simp_rw [heq]
  exact (continuous_const.inner continuous_subtype_val).norm

theorem complexSphereProjection_affine (p : UnitSphere CP2Vector) (hp : p.val 0 ≠ 0) :
    complexSphereProjection p = complexAffinePoint (complexVectorAffine p.val) := by
  exact (complexAffinePoint_vector p.val hp (unitSphere_ne_zero p)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nontrivial complex sine/cosine combination has at most one zero in a quadrant. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
noncomputable section

theorem complexGreatCircle_coordinate_zeros_finite (p q : CP2Vector) (i : Fin 3)
    (hi : p i ≠ 0 ∨ q i ≠ 0) :
    {t : ℝ | t ∈ Ioo 0 (Real.pi/2) ∧ complexGreatCircle p q t i = 0}.Finite := by
  have h := (complex_trigonometric_zeros_subsingleton (p i) (q i) hi).finite
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  simp only [complexGreatCircle,PiLp.add_apply,PiLp.smul_apply,Complex.real_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A pair of aligned projective representatives lies on an explicit horizontal circle. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
noncomputable section

theorem complex_aligned_circle (p v : CP2Vector) (hp : ‖p‖ = 1) (hv : ‖v‖ = 1)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hc : inner ℂ p v = (c : ℂ)) :
    ∃ q : CP2Vector, ‖q‖ = 1 ∧ inner ℂ p q = 0 ∧
      complexGreatCircle p q (Real.arccos c) = v := by
  let θ := Real.arccos c
  have hcos : Real.cos θ = c := Real.cos_arccos (by linarith) hc1.le
  have hθ : θ ∈ Icc 0 (Real.pi/2) :=
    ⟨Real.arccos_nonneg c,Real.arccos_le_pi_div_two.mpr hc0⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi
    (Real.arccos_pos.mpr hc1) (by linarith [hθ.2,Real.pi_pos])
  let D : CP2Vector := v-c • p
  have hr : inner ℝ p v = c := by
    simpa only [Complex.ofReal_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hc
  have hrv : inner ℝ v p = c := (real_inner_comm p v).trans hr
  have hD : ‖D‖^2 = 1-c^2 := by
    rw [norm_sub_sq_real,norm_smul,hp,hv,real_inner_smul_right,hrv]
    simp only [Real.norm_eq_abs,mul_one,sq_abs]
    ring
  have hDn : ‖D‖ = Real.sin θ := by
    have ht := Real.sin_sq_add_cos_sq θ
    rw [hcos] at ht
    nlinarith [norm_nonneg D]
  let q : CP2Vector := (Real.sin θ)⁻¹ • D
  have hq : ‖q‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hsin.le),hDn,inv_mul_cancel₀ hsin.ne']
  have horth : inner ℂ p q = 0 := by
    change inner ℂ p ((Real.sin θ)⁻¹ • (v-c • p)) = 0
    rw [inner_smul_right_eq_smul,inner_sub_right,inner_smul_right_eq_smul,
      inner_self_eq_norm_sq_to_K,hp,hc]
    norm_num
  refine ⟨q,hq,horth,?_⟩
  change Real.cos θ • p + Real.sin θ • ((Real.sin θ)⁻¹ • (v-c • p)) = v
  rw [hcos,smul_smul,mul_inv_cancel₀ hsin.ne',one_smul]
  module

end
end PositiveEinsteinFour.Geometry
end


section

/-! A projective great circle not contained in the cut hyperplane has only
finitely many exceptional affine parameters. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
noncomputable section

theorem complex_orthonormal_pair_tail (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) : ∃ i : Fin 3, i ≠ 0 ∧ (p i ≠ 0 ∨ q i ≠ 0) := by
  by_cases h1 : p 1 ≠ 0 ∨ q 1 ≠ 0
  · exact ⟨1,by decide,h1⟩
  by_cases h2 : p 2 ≠ 0 ∨ q 2 ≠ 0
  · exact ⟨2,by decide,h2⟩
  have hp1 : p 1 = 0 := not_ne_iff.mp (not_or.mp h1).1
  have hq1 : q 1 = 0 := not_ne_iff.mp (not_or.mp h1).2
  have hp2 : p 2 = 0 := not_ne_iff.mp (not_or.mp h2).1
  have hq2 : q 2 = 0 := not_ne_iff.mp (not_or.mp h2).2
  have hp0 : p 0 ≠ 0 := by
    intro hz
    have h : p = 0 := by ext i; fin_cases i <;> assumption
    rw [h,norm_zero] at hp
    exact zero_ne_one hp
  have hq0 : q 0 ≠ 0 := by
    intro hz
    have h : q = 0 := by ext i; fin_cases i <;> assumption
    rw [h,norm_zero] at hq
    exact zero_ne_one hq
  have hh : q 0 * star (p 0) = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_three,
      Pi.star_apply,hp1,hp2,hq1,hq2] using hpq
  exact ((mul_ne_zero hq0 (star_ne_zero.mpr hp0)) hh).elim

theorem complexVectorAffine_ne_zero_of_coordinate (v : CP2Vector) (hhead : v 0 ≠ 0)
    (i : Fin 3) (hi : i ≠ 0) (hv : v i ≠ 0) : complexVectorAffine v ≠ 0 := by
  intro hz
  fin_cases i
  · exact hi rfl
  · have h := congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z 0) hz
    change (v 0)⁻¹ * v 1 = 0 at h
    exact (mul_ne_zero (inv_ne_zero hhead) hv) h
  · have h := congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z 1) hz
    change (v 0)⁻¹ * v 2 = 0 at h
    exact (mul_ne_zero (inv_ne_zero hhead) hv) h

theorem complexGreatCircle_regular_off_finite (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (hhead : p 0 ≠ 0 ∨ q 0 ≠ 0) :
    ∃ E : Finset ℝ, ∀ t ∈ Ioo 0 (Real.pi/2), t ∉ E →
      complexGreatCircle p q t 0 ≠ 0 ∧ complexVectorAffine (complexGreatCircle p q t) ≠ 0 := by
  classical
  obtain ⟨i,hi,hcoord⟩ := complex_orthonormal_pair_tail p q hp hq hpq
  have h0 := complexGreatCircle_coordinate_zeros_finite p q 0 hhead
  have h1 := complexGreatCircle_coordinate_zeros_finite p q i hcoord
  refine ⟨(h0.union h1).toFinset,?_⟩
  intro t ht he
  have hn : t ∉ {s : ℝ | s ∈ Ioo 0 (Real.pi/2) ∧ complexGreatCircle p q s 0 = 0} ∪
      {s : ℝ | s ∈ Ioo 0 (Real.pi/2) ∧ complexGreatCircle p q s i = 0} := by
    simpa only [Set.Finite.mem_toFinset] using he
  have hn0 : complexGreatCircle p q t 0 ≠ 0 := fun h => hn (Or.inl ⟨ht,h⟩)
  have hni : complexGreatCircle p q t i ≠ 0 := fun h => hn (Or.inr ⟨ht,h⟩)
  exact ⟨hn0,complexVectorAffine_ne_zero_of_coordinate _ hn0 i hi hni⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate nonvanishing and distance continuity for actual unit representatives. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem cp2UnitRep_coordinate_ne_zero_of_unit (u : UnitSphere CP2Vector) (i : Fin 3)
    (hi : u.val i ≠ 0) : cp2UnitRep (complexSphereProjection u) i ≠ 0 := by
  have heq : Projectivization.mk ℂ (cp2UnitRep (complexSphereProjection u))
      (cp2UnitRep_ne_zero _) = Projectivization.mk ℂ u.val (unitSphere_ne_zero u) :=
    cp2UnitRep_mk _
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz,zero_smul] at ha
    exact cp2UnitRep_ne_zero _ ha.symm
  have hai := congrArg (fun v : CP2Vector => v i) ha
  change a * u.val i = cp2UnitRep (complexSphereProjection u) i at hai
  rw [← hai]
  exact mul_ne_zero ha0 hi

theorem fubiniStudyDistance_sphere_continuous (Q : ComplexProjective2) :
    Continuous (fun u : UnitSphere CP2Vector => fubiniStudyDistance (complexSphereProjection u) Q) := by
  have heq (u : UnitSphere CP2Vector) :
      fubiniStudyDistance (complexSphereProjection u) Q =
        Real.arccos ‖inner ℂ u.val (cp2UnitRep Q)‖ := by
    rw [fubiniStudyDistance_eq_arccos]
    exact congrArg Real.arccos (cp2Overlap_of_unit_representatives
      (complexSphereProjection u) Q u.val (cp2UnitRep Q)
      (unitSphere_ne_zero u) (cp2UnitRep_ne_zero Q) u.property (cp2UnitRep_norm Q)
      rfl (cp2UnitRep_mk Q))
  simp_rw [heq]
  exact Real.continuous_arccos.comp (continuous_subtype_val.inner continuous_const).norm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projective angular differential is bounded by horizontal speed. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complex_overlap_derivative_bound (p : UnitSphere CP2Vector)
    {u : ℝ → UnitSphere CP2Vector} {t : ℝ} {w : CP2Vector}
    (hu : HasDerivAt (fun s => (u s).val) w t)
    (hc0 : 0 < ‖inner ℂ p.val (u t).val‖) :
    DifferentiableAt ℝ (fun s => ‖inner ℂ p.val (u s).val‖) t ∧
      |deriv (fun s => ‖inner ℂ p.val (u s).val‖) t| ≤
        Real.sqrt (1-‖inner ℂ p.val (u t).val‖^2) *
          ‖complexHorizontalPart (u t).val w‖ := by
  let f : ℝ → ℂ := fun s => inner ℂ p.val (u s).val
  let c : ℝ := ‖f t‖
  have hf : HasDerivAt f (inner ℂ p.val w) t := by
    simpa only [inner_zero_left,add_zero] using (hasDerivAt_const t p.val).inner ℂ hu
  have hn : DifferentiableAt ℝ (fun s => ‖f s‖) t :=
    hf.differentiableAt.norm ℂ (norm_pos_iff.mp hc0)
  have hs := (hn.hasDerivAt.pow 2).unique hf.norm_sq
  have hs' : c * deriv (fun s => ‖f s‖) t = inner ℝ (f t) (inner ℂ p.val w) := by
    dsimp only [c]
    norm_num only [Nat.cast_ofNat,pow_one] at hs
    linarith
  have hproj : ‖complexHorizontalPart (u t).val p.val‖ = Real.sqrt (1-c^2) := by
    have hsq := complexHorizontalPart_norm_sq (u t).val p.val (u t).property
    rw [p.property,norm_inner_symm] at hsq
    change ‖complexHorizontalPart (u t).val p.val‖^2 = 1^2-c^2 at hsq
    norm_num only [one_pow] at hsq
    rw [← hsq]
    exact (Real.sqrt_sq (norm_nonneg (complexHorizontalPart (u t).val p.val))).symm
  have hb : |inner ℝ (f t) (inner ℂ p.val w)| ≤
      c * (Real.sqrt (1-c^2) * ‖complexHorizontalPart (u t).val w‖) := by
    change |inner ℝ (inner ℂ p.val (u t).val) (inner ℂ p.val w)| ≤ _
    rw [complexHorizontalPairing p.val (u t).val w (complex_unit_curve_tangent hu)]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [hproj] using complex_horizontal_inner_bound p.val (u t).val w (u t).property)
      (norm_nonneg _))
  rw [← hs',abs_mul,abs_of_pos hc0] at hb
  exact ⟨hn,le_of_mul_le_mul_left hb hc0⟩

theorem complex_angle_derivative_bound (p : UnitSphere CP2Vector)
    {u : ℝ → UnitSphere CP2Vector} {t : ℝ} {w : CP2Vector}
    (hu : HasDerivAt (fun s => (u s).val) w t)
    (hc0 : 0 < ‖inner ℂ p.val (u t).val‖)
    (hc1 : ‖inner ℂ p.val (u t).val‖ < 1) :
    DifferentiableAt ℝ (fun s => Real.arccos ‖inner ℂ p.val (u s).val‖) t ∧
      |deriv (fun s => Real.arccos ‖inner ℂ p.val (u s).val‖) t| ≤
        ‖complexHorizontalPart (u t).val w‖ := by
  let f : ℝ → ℝ := fun s => ‖inner ℂ p.val (u s).val‖
  obtain ⟨hf,hb⟩ := complex_overlap_derivative_bound p hu hc0
  have hroot : 0 < Real.sqrt (1-f t^2) := Real.sqrt_pos.mpr (by dsimp [f]; nlinarith)
  have hd := (Real.hasDerivAt_arccos (by dsimp [f]; linarith) hc1.ne).comp t hf.hasDerivAt
  refine ⟨hd.differentiableAt,?_⟩
  change |deriv (Real.arccos ∘ f) t| ≤ _
  rw [hd.deriv]
  simp only [one_div]
  change |-(Real.sqrt (1-f t^2))⁻¹ * deriv f t| ≤ _
  rw [abs_mul,abs_neg,abs_inv,abs_of_pos hroot]
  have hb' : |deriv f t| ≤ Real.sqrt (1-f t^2) * ‖complexHorizontalPart (u t).val w‖ := hb
  calc
    _ ≤ (Real.sqrt (1-f t^2))⁻¹ *
        (Real.sqrt (1-f t^2) * ‖complexHorizontalPart (u t).val w‖) :=
      mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr hroot.le)
    _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hroot.ne',one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform projective distance estimate in homogeneous unit coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem fubiniStudyDistance_unit_le_chord (p q : UnitSphere CP2Vector) :
    fubiniStudyDistance (complexSphereProjection p) (complexSphereProjection q) ≤
      (Real.pi/2) * ‖p.val-q.val‖ := by
  let c := ‖inner ℂ p.val q.val‖
  let d := Real.arccos c
  have hc0 : 0 ≤ c := norm_nonneg _
  have hc1 : c ≤ 1 := by
    simpa only [p.property,q.property,one_mul] using norm_inner_le_norm p.val q.val
  have hd0 : 0 ≤ d := Real.arccos_nonneg c
  have hdpi : d ≤ Real.pi := Real.arccos_le_pi c
  have hcos : Real.cos d = c := Real.cos_arccos (by linarith) hc1
  have ht := Real.cos_le_one_sub_mul_cos_sq (x := d) (by rwa [abs_of_nonneg hd0])
  rw [hcos] at ht
  have hpi2 : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_left ht hpi2.le
  have hcancel : Real.pi^2 * (1-2/Real.pi^2*d^2) = Real.pi^2-2*d^2 := by
    field_simp
  rw [hcancel] at hmul
  have hinner : inner ℝ p.val q.val ≤ c := by
    simpa only [← real_inner_eq_re_inner ℂ] using! Complex.re_le_norm (inner ℂ p.val q.val)
  have hnorm : ‖p.val-q.val‖^2 = 2-2*inner ℝ p.val q.val := by
    rw [norm_sub_sq_real,p.property,q.property]
    ring
  have hchord : 2-2*c ≤ ‖p.val-q.val‖^2 := by linarith
  have hbound := mul_le_mul_of_nonneg_left hchord hpi2.le
  have hfinal : d ≤ (Real.pi/2)*‖p.val-q.val‖ := by
    have hn : 0 ≤ (Real.pi/2)*‖p.val-q.val‖ := mul_nonneg (by positivity) (norm_nonneg _)
    nlinarith
  have heq : fubiniStudyDistance (complexSphereProjection p) (complexSphereProjection q) = d := by
    rw [fubiniStudyDistance_eq_arccos]
    exact congrArg Real.arccos (cp2Overlap_of_unit_representatives _ _ p.val q.val
      (unitSphere_ne_zero p) (unitSphere_ne_zero q) p.property q.property rfl rfl)
  rwa [heq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform Lipschitz control for normalizing homogeneous vectors bounded away from zero. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexNormalize (x : CP2Vector) (hx : x ≠ 0) : UnitSphere CP2Vector :=
  ⟨‖x‖⁻¹ • x,by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem complexNormalize_projection (x : CP2Vector) (hx : x ≠ 0) :
    complexSphereProjection (complexNormalize x hx) = Projectivization.mk ℂ x hx := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨(‖x‖⁻¹ : ℝ),rfl⟩

theorem complex_normalization_distance_le (x y : CP2Vector) (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2*‖x-y‖ := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy
  have hsplit : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x-y) + (‖x‖⁻¹-‖y‖⁻¹) • y := by module
  have hcoef : |‖x‖⁻¹-‖y‖⁻¹| * ‖y‖ = ‖x‖⁻¹ * |‖y‖-‖x‖| := by
    have heq : ‖x‖⁻¹-‖y‖⁻¹ = (‖y‖-‖x‖)/(‖x‖*‖y‖) := by field_simp
    rw [heq,abs_div,abs_of_pos (mul_pos hx0 hy0)]
    field_simp
  calc
    _ ≤ ‖‖x‖⁻¹ • (x-y)‖ + ‖(‖x‖⁻¹-‖y‖⁻¹) • y‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x-y‖ + ‖x‖⁻¹ * |‖y‖-‖x‖| := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hx0),hcoef]
    _ ≤ ‖x‖⁻¹ * ‖x-y‖ + ‖x‖⁻¹ * ‖x-y‖ := by
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = ‖x‖⁻¹ * (2*‖x-y‖) := by ring
    _ ≤ 2*‖x-y‖ := mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Two bounded complex coordinate charts cover the projective cut hyperplane. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexCutLift (i : Fin 2) (z : ℂ) : CP2Vector :=
  if i = 0 then WithLp.toLp 2 ![0,1,z] else WithLp.toLp 2 ![0,z,1]

theorem complexCutLift_norm_ge_one (i : Fin 2) (z : ℂ) : 1 ≤ ‖complexCutLift i z‖ := by
  fin_cases i
  · simpa [complexCutLift] using PiLp.norm_apply_le (complexCutLift 0 z) 1
  · simpa [complexCutLift] using PiLp.norm_apply_le (complexCutLift 1 z) 2

theorem complexCutLift_ne_zero (i : Fin 2) (z : ℂ) : complexCutLift i z ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one (complexCutLift_norm_ge_one i z)))

def complexCutPoint (i : Fin 2) (z : ℂ) : ComplexProjective2 :=
  Projectivization.mk ℂ (complexCutLift i z) (complexCutLift_ne_zero i z)

theorem complexCutPoint_covers (P : ComplexProjective2) (hP : cp2UnitRep P 0 = 0) :
    ∃ (i : Fin 2) (z : ℂ), ‖z‖ ≤ 1 ∧ complexCutPoint i z = P := by
  let p := cp2UnitRep P
  have hp0 : p 0 = 0 := hP
  have hnon : p 1 ≠ 0 ∨ p 2 ≠ 0 := by
    by_contra h
    push Not at h
    have hz : p = 0 := by ext i; fin_cases i <;> simp [hp0,h.1,h.2]
    exact cp2UnitRep_ne_zero P hz
  by_cases hnorm : ‖p 2‖ ≤ ‖p 1‖
  · have hp1 : p 1 ≠ 0 := by
      intro hz
      have hz2 : p 2 = 0 := norm_eq_zero.mp (le_antisymm
        (by simpa only [hz,norm_zero] using hnorm) (norm_nonneg _))
      exact hnon.elim (fun h => h hz) (fun h => h hz2)
    refine ⟨0,p 2 / p 1,?_,?_⟩
    · rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hp1)).mpr hnorm
    · rw [← cp2UnitRep_mk P]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      refine ⟨(p 1)⁻¹,?_⟩
      change (p 1)⁻¹ • p = complexCutLift 0 (p 2 / p 1)
      ext i
      fin_cases i <;> simp [complexCutLift,hp0,hp1,div_eq_mul_inv,mul_comm]
  · have hp2 : p 2 ≠ 0 := by
      intro hz
      have hh := lt_of_not_ge hnorm
      rw [hz,norm_zero] at hh
      exact (not_lt_of_ge (norm_nonneg _)) hh
    refine ⟨1,p 1 / p 2,?_,?_⟩
    · rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hp2)).mpr (le_of_not_ge hnorm)
    · rw [← cp2UnitRep_mk P]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      refine ⟨(p 2)⁻¹,?_⟩
      change (p 2)⁻¹ • p = complexCutLift 1 (p 1 / p 2)
      ext i
      fin_cases i <;> simp [complexCutLift,hp0,hp2,div_eq_mul_inv,mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit Fubini--Study distance induces the existing compact projective topology. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space

theorem fubiniStudyDistance_self (P : ComplexProjective2) : fubiniStudyDistance P P = 0 := by
  rw [fubiniStudyDistance_eq_arccos,cp2Overlap_self,Real.arccos_one]

theorem fubiniStudyDistance_comm (P Q : ComplexProjective2) :
    fubiniStudyDistance P Q = fubiniStudyDistance Q P := by
  simp only [fubiniStudyDistance_eq_arccos,cp2Overlap_comm P Q]

theorem fubiniStudyDistance_eq_zero_iff (P Q : ComplexProjective2) :
    fubiniStudyDistance P Q = 0 ↔ P = Q := by
  rw [fubiniStudyDistance_eq_arccos,Real.arccos_eq_zero]
  exact ⟨fun h => (cp2Overlap_eq_one_iff P Q).mp (le_antisymm (cp2Overlap_le_one P Q) h),
    fun h => by subst Q; rw [cp2Overlap_self]⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual cut locus is covered by two Lipschitz images of closed complex disks. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section

theorem cp2UnitRep_cut_head (i : Fin 2) (z : ℂ) : cp2UnitRep (complexCutPoint i z) 0 = 0 := by
  have h : Projectivization.mk ℂ (cp2UnitRep (complexCutPoint i z))
      (cp2UnitRep_ne_zero _) = Projectivization.mk ℂ (complexCutLift i z) (complexCutLift_ne_zero i z) :=
    cp2UnitRep_mk _
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have hh := congrArg (fun p : CP2Vector => p 0) ha
  have hzero : complexCutLift i z 0 = 0 := by fin_cases i <;> simp [complexCutLift]
  change a * complexCutLift i z 0 = cp2UnitRep (complexCutPoint i z) 0 at hh
  simpa only [hzero,mul_zero] using hh.symm

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


