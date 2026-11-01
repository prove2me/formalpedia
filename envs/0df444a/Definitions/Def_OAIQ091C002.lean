-- Prove2me | Definitions.Def_OAIQ091C002
-- name    : OAIQ091C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:49:25.289849+00:00
-- url     : https://prove2.me/theorems/55f5c7a3-daf5-443a-b60e-8c4badf981de
-- title:
--   Definitions bundle OAIQ091C002 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 306 declarations of OpenAI's Lean: 72 definitions and 234 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.MatrixVector`, `OAI.PositiveEinsteinFour.Geometry.ScalarCutoffNested`, `OAI.PositiveEinsteinFour.Geometry.affinePartitionTime`, `OAI.PositiveEinsteinFour.Geometry.besselFirstSymbol`, `OAI.PositiveEinsteinFour.Geometry.besselInverseSymbol`, `OAI.PositiveEinsteinFour.Geometry.besselSecondSymbol`, `OAI.PositiveEinsteinFour.Geometry.complexPhase`, `OAI.PositiveEinsteinFour.Geometry.endpointCorrectedMixed`, `OAI.PositiveEinsteinFour.Geometry.endpointCorrectedMixedSecond`, `OAI.PositiveEinsteinFour.Geometry.endpointCorrectedParameter`, `OAI.PositiveEinsteinFour.Geometry.endpointCorrectedPosition`, `OAI.PositiveEinsteinFour.Geometry.endpointCorrectedSecond`, `OAI.PositiveEinsteinFour.Geometry.endpointCorrectedVelocity`, `OAI.PositiveEinsteinFour.Geometry.endpointResidual`, `OAI.PositiveEinsteinFour.Geometry.endpointWeightLeft`, `OAI.PositiveEinsteinFour.Geometry.endpointWeightRight`, `OAI.PositiveEinsteinFour.Geometry.fourGradientDirichlet`, `OAI.PositiveEinsteinFour.Geometry.fourGradientSolution`, `OAI.PositiveEinsteinFour.Geometry.h2Bump`, `OAI.PositiveEinsteinFour.Geometry.h2BumpDerivativeBound`, `OAI.PositiveEinsteinFour.Geometry.h2Cutoff`, `OAI.PositiveEinsteinFour.Geometry.h3InverseBounded`, `OAI.PositiveEinsteinFour.Geometry.heatResidualAtZero`, `OAI.PositiveEinsteinFour.Geometry.jacobiMetricRate`, `OAI.PositiveEinsteinFour.Geometry.jacobiMetricSecondRate`, `OAI.PositiveEinsteinFour.Geometry.joinedPartitionTime`, `OAI.PositiveEinsteinFour.Geometry.modeSynthesis`, `OAI.PositiveEinsteinFour.Geometry.nonlinearEpsilon`, `OAI.PositiveEinsteinFour.Geometry.normalizedScalarHelmholtz`, `OAI.PositiveEinsteinFour.Geometry.scalarBesselCoordinate`, `OAI.PositiveEinsteinFour.Geometry.scalarBesselFirstL2`, `OAI.PositiveEinsteinFour.Geometry.scalarBesselInverseL2`, `OAI.PositiveEinsteinFour.Geometry.scalarBesselReciprocal`, `OAI.PositiveEinsteinFour.Geometry.scalarBesselSecondL2`, `OAI.PositiveEinsteinFour.Geometry.scalarBoundedTestPairing`, `OAI.PositiveEinsteinFour.Geometry.scalarCutoffL2`, `OAI.PositiveEinsteinFour.Geometry.scalarH3ContinuousLift`, `OAI.PositiveEinsteinFour.Geometry.scalarH3Representative`, `OAI.PositiveEinsteinFour.Geometry.scalarH3RepresentativeLinear`, `OAI.PositiveEinsteinFour.Geometry.scalarHalfBumpGap` and 32 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_ActualJacobiODEDependence`, `EinsteinFour_DirichletMatrix`, `EinsteinFour_FourHeatCompactTimeIntegral`, `EinsteinFour_FourHeatGaussian`, `EinsteinFour_FourHeatGaussianConvolution`, `EinsteinFour_FourHeatGaussianMoments`, `EinsteinFour_GeodesicGeometry04`, `EinsteinFour_GeodesicGeometry05`, `EinsteinFour_GeodesicGeometry06`, `EinsteinFour_GeodesicGeometry13`, `EinsteinFour_GeodesicJacobiIntegralCalculus`, `EinsteinFour_GeodesicJacobiSecondVariationAlgebra`, `EinsteinFour_HeatForcedScalar`, `EinsteinFour_HeatKernels10`, `EinsteinFour_HilbertImageTotal`, `EinsteinFour_HodgeTheory08`, `EinsteinFour_HodgeTheory11`, `EinsteinFour_JacobiApproximation`, `EinsteinFour_JacobiInverse`, `EinsteinFour_JacobiMeshCoefficient`, `EinsteinFour_JacobiMeshInverse`, `EinsteinFour_JacobiNearZero`, `EinsteinFour_JacobiNormalized`, `EinsteinFour_JacobiODEPositivity`, `EinsteinFour_JacobiPositivity`, `EinsteinFour_JacobiRatioLimit`, `EinsteinFour_MatrixRatioPositivity`, `EinsteinFour_MetricCurvatureGreen`, `EinsteinFour_ModeCompression`, `EinsteinFour_ReferenceCompression`, `EinsteinFour_ScalarAdjointCoordinates`, `EinsteinFour_ScalarBoundedBessel`, `EinsteinFour_ScalarBoundedPairing`, `EinsteinFour_ScalarCompositionHessian`, `EinsteinFour_ScalarContinuousLift`, `EinsteinFour_ScalarDirichlet`, `EinsteinFour_ScalarEigenMultiplier`, `EinsteinFour_ScalarH1EllipticGain`, `EinsteinFour_ScalarHalfBallCutoffs`, `EinsteinFour_ScalarPoissonKernelAdjoint`, `EinsteinFour_ScalarPoissonKernelAdjointEstimate`, `EinsteinFour_ScalarPoissonKernelBesselEstimate`, `EinsteinFour_ScalarPoissonKernelBootstrap`, `EinsteinFour_ScalarPoissonKernelCommutator`, `EinsteinFour_ScalarPoissonKernelContinuousEmbedding`, `EinsteinFour_ScalarPoissonKernelDerivative`, `EinsteinFour_ScalarPoissonKernelHelmholtz`, `EinsteinFour_ScalarPoissonKernelLocalRegularity`, `EinsteinFour_ScalarPoissonKernelLocalRepresentative`, `EinsteinFour_ScalarPoissonKernelLocalTests`, `EinsteinFour_ScalarPoissonKernelLocalization`, `EinsteinFour_ScalarPoissonKernelMultiplier`, `EinsteinFour_ScalarPoissonKernelPerturbation`, `EinsteinFour_ScalarPoissonKernelPotential`, `EinsteinFour_ScalarPoissonKernelSobolev`, `EinsteinFour_ScalarPoissonKernelSourceChain`, `EinsteinFour_ScalarPoissonKernelUniqueness`, `EinsteinFour_ScalarRegularity06`, `EinsteinFour_ScalarRegularity07`, `EinsteinFour_ScalarSpectralOrthogonal`, `EinsteinFour_SineModeLimit`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C009`, `OAIQ091C010` and `OAIQ091C011`; the statement `OAI_PositiveEinsteinFour_QuarticClosed_quartic_energy_bound_closed`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stability and consistency for the kick-drift approximation of the
matrix Jacobi equation. The estimates use operator bounds, so no two
curvature matrices are required to commute. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def kick (R : E →L[ℝ] E) (h : ℝ) (x v : E) : E := v - h • R x

def drift (R : E →L[ℝ] E) (h : ℝ) (x v : E) : E := x + h • kick R h x v

/-- A first-order Taylor remainder with the uniform quadratic bound needed
for convergence. The slightly larger constant avoids unnecessary sharpness. -/
theorem first_order_remainder {f d : ℝ → E} {a h L : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hd : ∀ s ∈ Set.Icc a (a + h), HasDerivAt f (d s) s)
    (hlip : ∀ s ∈ Set.Icc a (a + h), ‖d s - d a‖ ≤ L * (s - a)) :
    ‖f (a + h) - f a - h • d a‖ ≤ L * h ^ 2 := by
  let g : ℝ → E := fun s => f s - f a - (s - a) • d a
  have hg (s : ℝ) (hs : s ∈ Set.Icc a (a + h)) :
      HasDerivAt g (d s - d a) s := by
    convert ((hd s hs).sub_const (f a)).sub
      (((hasDerivAt_id s).sub_const a).smul_const (d a)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | simp
  have hb (s : ℝ) (hs : s ∈ Set.Ico a (a + h)) : ‖d s - d a‖ ≤ L * h :=
    (hlip s ⟨hs.1, hs.2.le⟩).trans (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hL)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hg s hs).hasDerivWithinAt) hb (a + h) ⟨by linarith, le_rfl⟩
  simpa [g, pow_two, mul_assoc] using h

theorem kick_stability {R : E →L[ℝ] E} {h K : ℝ}
    (hh : 0 ≤ h) (hR : ‖R‖ ≤ K) (x v y w : E) :
    ‖kick R h x v - kick R h y w‖ ≤ ‖v - w‖ + h * K * ‖x - y‖ := by
  have hid : kick R h x v - kick R h y w = (v - w) - h • R (x - y) := by
    simp only [kick, map_sub, smul_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖v - w‖ + ‖h • R (x - y)‖ := norm_sub_le _ _
    _ = ‖v - w‖ + h * ‖R (x - y)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    _ ≤ ‖v - w‖ + h * (K * ‖x - y‖) := by
      gcongr
      exact (R.le_opNorm (x - y)).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
    _ = _ := by ring

theorem kick_drift_stability {R : E →L[ℝ] E} {h K : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hK : 0 ≤ K) (hR : ‖R‖ ≤ K)
    (x v y w : E) :
    ‖drift R h x v - drift R h y w‖ + ‖kick R h x v - kick R h y w‖ ≤
      (1 + (1 + 2 * K) * h) * (‖x - y‖ + ‖v - w‖) := by
  have hv := kick_stability hh hR x v y w
  have hx : ‖drift R h x v - drift R h y w‖ ≤
      ‖x - y‖ + h * ‖kick R h x v - kick R h y w‖ := by
    have hid : drift R h x v - drift R h y w =
        (x - y) + h • (kick R h x v - kick R h y w) := by
      simp only [drift, smul_sub]
      abel
    rw [hid]
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh] using norm_add_le
      (x - y) (h • (kick R h x v - kick R h y w))
  have hbound : h * K * ‖x - y‖ * (1 - h) +
      h * ‖x - y‖ + 2 * K * h * ‖v - w‖ ≥ 0 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hv hh]

/-- Local error of the actual update, from the two Taylor remainders. -/
theorem kick_drift_local_error {R : E →L[ℝ] E} {h Cx Cv F : ℝ}
    {x v x' v' : E} (hh : 0 ≤ h)
    (hx : ‖x' - x - h • v‖ ≤ Cx * h ^ 2)
    (hv : ‖v' - v + h • R x‖ ≤ Cv * h ^ 2)
    (hforce : ‖R x‖ ≤ F) :
    ‖x' - drift R h x v‖ + ‖v' - kick R h x v‖ ≤
      (Cx + Cv + F) * h ^ 2 := by
  have hvid : v' - kick R h x v = v' - v + h • R x := by unfold kick; abel
  have hxid : x' - drift R h x v = (x' - x - h • v) + (h * h) • R x := by
    simp only [drift, kick, smul_sub, smul_smul]
    abel
  have hxbound : ‖x' - drift R h x v‖ ≤ (Cx + F) * h ^ 2 := by
    rw [hxid]
    calc
      _ ≤ ‖x' - x - h • v‖ + ‖(h * h) • R x‖ := norm_add_le _ _
      _ = ‖x' - x - h • v‖ + h ^ 2 * ‖R x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh hh), pow_two]
      _ ≤ Cx * h ^ 2 + h ^ 2 * F := add_le_add hx (mul_le_mul_of_nonneg_left hforce (sq_nonneg h))
      _ = _ := by ring
  rw [hvid]
  linarith

/-- The local error hypotheses follow from the differential equation and
Lipschitz bounds for its velocity and acceleration on the current interval. -/
theorem kick_drift_consistency {R : ℝ → E →L[ℝ] E} {X V : ℝ → E}
    {a h Lx Lv F : ℝ} (hh : 0 ≤ h) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hX : ∀ s ∈ Set.Icc a (a + h), HasDerivAt X (V s) s)
    (hV : ∀ s ∈ Set.Icc a (a + h), HasDerivAt V (-(R s) (X s)) s)
    (hvelocity : ∀ s ∈ Set.Icc a (a + h), ‖V s - V a‖ ≤ Lx * (s - a))
    (hacceleration : ∀ s ∈ Set.Icc a (a + h),
      ‖-(R s) (X s) - -(R a) (X a)‖ ≤ Lv * (s - a))
    (hforce : ‖(R a) (X a)‖ ≤ F) :
    ‖X (a + h) - drift (R a) h (X a) (V a)‖ +
      ‖V (a + h) - kick (R a) h (X a) (V a)‖ ≤ (Lx + Lv + F) * h ^ 2 := by
  have hx := first_order_remainder hh hLx hX hvelocity
  have hv := first_order_remainder hh hLv hV hacceleration
  apply kick_drift_local_error hh hx ?_ hforce
  simpa only [smul_neg, sub_neg_eq_add] using hv

/-- Discrete Grönwall on precisely the finite interval used by the Jacobi
approximation. It also handles zero step size and zero local error. -/
theorem finite_error_bound {u : ℕ → ℝ} {N : ℕ} {h K C : ℝ}
    (hh : 0 ≤ h) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hu0 : u 0 = 0) (hu : ∀ i ≤ N, 0 ≤ u i)
    (hstep : ∀ i < N, u (i + 1) ≤ (1 + K * h) * u i + C * h ^ 2) :
    u N ≤ C * N * h ^ 2 * Real.exp (K * N * h) := by
  let U : ℕ → ℝ := fun i => u (min i N)
  have hU (i : ℕ) (_ : 0 ≤ i) : U (i + 1) ≤ (1 + K * h) * U i + C * h ^ 2 := by
    by_cases hi : i < N
    · simpa [U, min_eq_left hi.le, min_eq_left (Nat.succ_le_of_lt hi)] using hstep i hi
    · have hN : N ≤ i := Nat.le_of_not_gt hi
      simp only [U, min_eq_right hN, min_eq_right (hN.trans (Nat.le_succ i))]
      have hhprod : 0 ≤ K * h * u N := mul_nonneg (mul_nonneg hK hh) (hu N le_rfl)
      have hlocal : 0 ≤ C * h ^ 2 := mul_nonneg hC (sq_nonneg h)
      nlinarith
  have hb := discrete_gronwall (show 0 ≤ U 0 by simp [U, hu0]) hU
    (fun _ _ => mul_nonneg hK hh) (fun _ _ => mul_nonneg hC (sq_nonneg h))
    (show 0 ≤ N by omega)
  simp [U, hu0, Finset.sum_const] at hb
  have he : (N : ℝ) * (K * h) = K * N * h := by ring
  rw [he] at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- Propagation of local Jacobi errors, with the curvature operator allowed
to vary arbitrarily from one mesh point to the next. -/
theorem kick_drift_global_error
    {R : ℕ → E →L[ℝ] E} {x v X V : ℕ → E} {N : ℕ} {h K C : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hR : ∀ i < N, ‖R i‖ ≤ K)
    (hx0 : x 0 = X 0) (hv0 : v 0 = V 0)
    (hxstep : ∀ i < N, x (i + 1) = drift (R i) h (x i) (v i))
    (hvstep : ∀ i < N, v (i + 1) = kick (R i) h (x i) (v i))
    (hlocal : ∀ i < N,
      ‖X (i + 1) - drift (R i) h (X i) (V i)‖ +
      ‖V (i + 1) - kick (R i) h (X i) (V i)‖ ≤ C * h ^ 2) :
    ‖x N - X N‖ + ‖v N - V N‖ ≤
      C * N * h ^ 2 * Real.exp ((1 + 2 * K) * N * h) := by
  let u : ℕ → ℝ := fun i => ‖x i - X i‖ + ‖v i - V i‖
  apply finite_error_bound hh (by positivity) hC (u := u)
  · simp [u, hx0, hv0]
  · intro i _
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro i hi
    have hstab := kick_drift_stability hh hh1 hK (hR i hi) (x i) (v i) (X i) (V i)
    have hpos := norm_sub_le_norm_sub_add_norm_sub
      (drift (R i) h (x i) (v i)) (drift (R i) h (X i) (V i)) (X (i + 1))
    have hvel := norm_sub_le_norm_sub_add_norm_sub
      (kick (R i) h (x i) (v i)) (kick (R i) h (X i) (V i)) (V (i + 1))
    rw [norm_sub_rev (drift (R i) h (X i) (V i)) (X (i + 1))] at hpos
    rw [norm_sub_rev (kick (R i) h (X i) (V i)) (V (i + 1))] at hvel
    dsimp only [u]
    rw [hxstep i hi, hvstep i hi]
    linarith [hlocal i hi]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiNearZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform relative errors at the initial endpoint. These estimates let the
Jacobi approximation be used on intervals reaching zero, where the inverse
of the exact Jacobi matrix itself is unbounded. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Dividing the position error by time leaves an error of order one mesh
step, uniformly over every positive mesh index. -/
theorem relative_position_error {x X : E} {i : ℕ} {h C K : ℝ}
    (hi : 0 < i) (hh : 0 < h)
    (herr : ‖x - X‖ ≤ C * i * h ^ 2 * Real.exp (K * i * h)) :
    ‖((1 : ℝ) / (i * h)) • x - ((1 : ℝ) / (i * h)) • X‖ ≤
      C * h * Real.exp (K * i * h) := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have ht : (0 : ℝ) < i * h := mul_pos hi' hh
  calc
    _ = (1 / (i * h)) * ‖x - X‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr ht)]
    _ ≤ (1 / (i * h)) * (C * i * h ^ 2 * Real.exp (K * i * h)) :=
      mul_le_mul_of_nonneg_left herr (one_div_nonneg.mpr ht.le)
    _ = _ := by field_simp

/-- The operator-norm neighborhood used to keep the symmetric Schur pivots
positive. This lower bound also records the size of the positive margin. -/
theorem quadratic_lower_of_norm_error
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : F →L[ℝ] F) (c : ℝ) (x : F) :
    (c - ‖A - c • ContinuousLinearMap.id ℝ F‖) * ‖x‖ ^ 2 ≤ inner ℝ (A x) x := by
  let B := A - c • ContinuousLinearMap.id ℝ F
  have herr : |inner ℝ (B x) x| ≤ ‖B‖ * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖B x‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg x)
      _ = _ := by ring
  have hid : inner ℝ (A x) x = c * ‖x‖ ^ 2 + inner ℝ (B x) x := by
    change inner ℝ (A x) x = c * ‖x‖ ^ 2 + inner ℝ (A x - c • x) x
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  change (c - ‖B‖) * ‖x‖ ^ 2 ≤ inner ℝ (A x) x
  linarith [neg_abs_le (inner ℝ (B x) x)]

/-- Strict positivity follows without taking an inverse of a limiting
matrix. Symmetry can then be supplied separately by the Schur recurrence. -/
theorem quadratic_pos_of_norm_error
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : F →L[ℝ] F} {c : ℝ}
    (hA : ‖A - c • ContinuousLinearMap.id ℝ F‖ < c) {x : F} (hx : x ≠ 0) :
    0 < inner ℝ (A x) x := by
  exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hA) (sq_pos_of_pos (norm_pos_iff.mpr hx)))
    (quadratic_lower_of_norm_error A c x)

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of Jacobi ratios close to the initial endpoint. -/

namespace PositiveEinsteinFour.Jacobi

open Filter _root_.Topology

noncomputable section

/-- A positive multiple of a map within distance one of the identity can
be added to the identity without losing strict positivity. -/
theorem identity_add_ratio_quadratic_pos
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {P : F →L[ℝ] F} {r : ℝ} (hr : 0 ≤ r)
    (hP : ‖P - ContinuousLinearMap.id ℝ F‖ < 1)
    {x : F} (hx : x ≠ 0) :
    0 < inner ℝ ((ContinuousLinearMap.id ℝ F + r • P) x) x := by
  have hp : 0 < inner ℝ (P x) x := by
    apply quadratic_pos_of_norm_error (c := 1) ?_ hx
    simpa only [one_smul] using hP
  change 0 < inner ℝ (x + r • P x) x
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (mul_nonneg hr hp.le)

/-- Split the mesh into a neighborhood of zero and its complement. A
uniform coefficient bound suffices on the complement, while closeness to
the initial coefficient handles all of the first mesh nodes at once. -/
theorem mesh_ratio_quadratic_pos
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {P : F →L[ℝ] F} {h η K : ℝ} {i : ℕ}
    (hi : 0 < i) (hh : 0 < h) (hmesh : h * K < η)
    (hbound : ‖P‖ ≤ K)
    (hnear : (i : ℝ) * h ≤ η → ‖P - ContinuousLinearMap.id ℝ F‖ < 1)
    {x : F} (hx : x ≠ 0) :
    0 < inner ℝ ((ContinuousLinearMap.id ℝ F + ((1 : ℝ) / i) • P) x) x := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  by_cases ht : (i : ℝ) * h ≤ η
  · exact identity_add_ratio_quadratic_pos (by positivity) (hnear ht) hx
  · have hKi : K < (i : ℝ) := by nlinarith [lt_of_not_ge ht]
    apply quadratic_pos_of_norm_error (c := 1) ?_ hx
    simp only [one_smul, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hi')]
    calc
      (1 / (i : ℝ)) * ‖P‖ ≤ (1 / i) * K :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ < 1 := by rw [one_div_mul_eq_div]; exact (div_lt_one hi').mpr hKi

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative inverse control for the normalized Jacobi matrices. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

theorem inverse_perturbation_bound
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    (u : Rˣ) (A : R) {K : ℝ} (hK : 0 < K) (hu : ‖((u⁻¹ : Rˣ) : R)‖ ≤ K)
    (herror : ‖A - (u : R)‖ ≤ 1 / (2 * K)) :
    IsUnit A ∧ ‖Ring.inverse A‖ ≤ 2 * K ∧
      ‖Ring.inverse A - ((u⁻¹ : Rˣ) : R)‖ ≤ 2 * K ^ 2 * ‖A - (u : R)‖ := by
  have heK : ‖A - (u : R)‖ * K ≤ 1 / 2 := by
    calc
      _ ≤ (1 / (2 * K)) * K := mul_le_mul_of_nonneg_right herror hK.le
      _ = _ := by field_simp
  have heI : ‖A - (u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hu (norm_nonneg _)).trans heK
  have hnear : ‖A - (u : R)‖ < ‖((u⁻¹ : Rˣ) : R)‖⁻¹ :=
    by
      rw [← one_div]
      exact (lt_div_iff₀ (Units.norm_pos u⁻¹)).mpr (by linarith)
  let v := u.ofNearby A hnear
  have hv : (v : R) = A := rfl
  have huu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by simp
  have hvv : ((v⁻¹ : Rˣ) : R) * (v : R) = 1 := by simp
  have hid : ((v⁻¹ : Rˣ) : R) = ((u⁻¹ : Rˣ) : R) +
      ((v⁻¹ : Rˣ) : R) * ((u : R) - (v : R)) * ((u⁻¹ : Rˣ) : R) := by
    calc
      _ = ((u⁻¹ : Rˣ) : R) +
          (((v⁻¹ : Rˣ) : R) - ((u⁻¹ : Rˣ) : R)) := by abel
      _ = _ := by
        rw [mul_sub, sub_mul, mul_assoc ((v⁻¹ : Rˣ) : R) (u : R),
          huu, mul_one, hvv, one_mul]
  have hprod : ‖((v⁻¹ : Rˣ) : R) * ((u : R) - (v : R)) * ((u⁻¹ : Rˣ) : R)‖ ≤
      ‖((v⁻¹ : Rˣ) : R)‖ * ‖A - (u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ := by
    calc
      _ ≤ (‖((v⁻¹ : Rˣ) : R)‖ * ‖(u : R) - (v : R)‖) * ‖((u⁻¹ : Rˣ) : R)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = _ := by rw [hv, norm_sub_rev]
  have hbound : ‖((v⁻¹ : Rˣ) : R)‖ ≤ 2 * K := by
    have hn : ‖((v⁻¹ : Rˣ) : R)‖ ≤ ‖((u⁻¹ : Rˣ) : R)‖ +
        ‖((v⁻¹ : Rˣ) : R)‖ * ‖A - (u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ := by
      calc
        _ = ‖((u⁻¹ : Rˣ) : R) +
            ((v⁻¹ : Rˣ) : R) * ((u : R) - (v : R)) * ((u⁻¹ : Rˣ) : R)‖ := congrArg norm hid
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right hprod _)
    have hm := mul_le_mul_of_nonneg_left heI (norm_nonneg (((v⁻¹ : Rˣ) : R)))
    nlinarith [norm_nonneg (((v⁻¹ : Rˣ) : R))]
  have hdiff : ‖((v⁻¹ : Rˣ) : R) - ((u⁻¹ : Rˣ) : R)‖ ≤
      2 * K ^ 2 * ‖A - (u : R)‖ := by
    have hd : ((v⁻¹ : Rˣ) : R) - ((u⁻¹ : Rˣ) : R) =
        ((v⁻¹ : Rˣ) : R) * ((u : R) - (v : R)) * ((u⁻¹ : Rˣ) : R) := by
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hid)
    rw [hd]
    calc
      _ ≤ ‖((v⁻¹ : Rˣ) : R)‖ * ‖A - (u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ := hprod
      _ ≤ (2 * K) * ‖A - (u : R)‖ * K := by gcongr
      _ = _ := by ring
  have hinv : Ring.inverse A = ((v⁻¹ : Rˣ) : R) := by
    rw [← hv, Ring.inverse_unit]
  refine ⟨hv ▸ v.isUnit, ?_, ?_⟩
  · simpa only [hinv] using hbound
  · simpa only [hinv] using hdiff

/-- The inverse bounds can be chosen once on a compact preconjugate
interval, including the continuously normalized initial endpoint. -/
theorem uniform_inverse_neighborhood
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    {B : ℝ → R} {t : ℝ}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Set.Icc 0 t, ∀ A : R,
      ‖A - B s‖ ≤ 1 / (2 * K) →
      IsUnit A ∧ ‖Ring.inverse A‖ ≤ 2 * K ∧
        ‖Ring.inverse A - Ring.inverse (B s)‖ ≤ 2 * K ^ 2 * ‖A - B s‖ := by
  have hi : ContinuousOn (fun s => Ring.inverse (B s)) (Set.Icc 0 t) := by
    intro s hs
    have hinv : ContinuousAt (Ring.inverse : R → R) (B s) := by
      simpa using (NormedRing.inverse_continuousAt (hunit s hs).unit)
    exact hinv.comp_continuousWithinAt (hB s hs)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hi
  let K := max C 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  refine ⟨K, hK, ?_⟩
  intro s hs A hA
  have hb : ‖(((hunit s hs).unit⁻¹ : Rˣ) : R)‖ ≤ K := by
    have huinv : (((hunit s hs).unit⁻¹ : Rˣ) : R) = Ring.inverse (B s) := by
      exact (Ring.inverse_of_isUnit (hunit s hs)).symm
    rw [huinv]
    exact (hC s hs).trans (le_max_left C 1)
  simpa only [IsUnit.unit_spec, ← Ring.inverse_unit] using
    inverse_perturbation_bound (hunit s hs).unit A hK hb
      (by simpa only [IsUnit.unit_spec] using hA)

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiNormalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the zero of the Jacobi matrix at its initial endpoint. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

def normalizedJacobi (J : ℝ → R) : ℝ → R := dslope J 0

theorem normalizedJacobi_zero {J : ℝ → R} (hJ : HasDerivAt J 1 0) :
    normalizedJacobi J 0 = 1 := by
  rw [normalizedJacobi, dslope_same, hJ.deriv]

theorem normalizedJacobi_pos {J : ℝ → R} (hJ0 : J 0 = 0) {s : ℝ} (hs : s ≠ 0) :
    normalizedJacobi J s = s⁻¹ • J s := by
  rw [normalizedJacobi, dslope_of_ne J hs, slope_def_module, hJ0, sub_zero, sub_zero]

theorem normalizedJacobi_continuousOn {J : ℝ → R} {t : ℝ}
    (hc : ContinuousOn J (Set.Icc 0 t)) (hJ : HasDerivAt J 1 0) :
    ContinuousOn (normalizedJacobi J) (Set.Icc 0 t) := by
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    exact (continuousAt_dslope_same.mpr hJ.differentiableAt).continuousWithinAt
  · exact (continuousWithinAt_dslope_of_ne hs0).mpr (hc s hs)

/-- Preconjugacy gives invertibility of the normalized curve on the
closed interval, including its value one at the initial endpoint. -/
theorem normalizedJacobi_isUnit {J : ℝ → R} {t : ℝ}
    (hJ0 : J 0 = 0) (hJ : HasDerivAt J 1 0)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (J s)) :
    ∀ s ∈ Set.Icc 0 t, IsUnit (normalizedJacobi J s) := by
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    rw [normalizedJacobi_zero hJ]
    exact isUnit_one
  · rw [normalizedJacobi_pos hJ0 hs0, Algebra.smul_def]
    have hscalar : IsUnit (algebraMap ℝ R s⁻¹) :=
      (isUnit_iff_ne_zero.mpr (inv_ne_zero hs0)).map (algebraMap ℝ R)
    exact hscalar.mul (hpre s (lt_of_le_of_ne hs.1 (Ne.symm hs0)) hs.2)

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite block matrices for the Jacobi determinant approximation. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix OrderDual

noncomputable section

def nodeBlockEquiv {N : ℕ} (i : (Fin N)ᵒᵈ) :
    {j : Fin 3 × Fin N // toDual j.2 = i} ≃ Fin 3 where
  toFun j := j.val.1
  invFun k := ⟨(k, ofDual i), rfl⟩
  left_inv j := by
    apply Subtype.ext
    exact Prod.ext rfl j.property.symm
  right_inv _ := rfl

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ModeCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression onto a common scalar time mode in the three normal directions. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def modeEmbedding {N : ℕ} (w : Fin N → ℝ) : Matrix (Fin 3 × Fin N) (Fin 3) ℝ :=
  fun i a => if i.1 = a then w i.2 else 0

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarDirichlet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive first mode of the scalar Dirichlet comparison matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def scalarDirichlet (N : ℕ) (d : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  (if i = j then d else 0) - (if j.val + 1 = i.val then 1 else 0) -
    (if i.val + 1 = j.val then 1 else 0)

theorem predecessor_sum {N : ℕ} (f : ℕ → ℝ) (hf : f 0 = 0) (i : Fin N) :
    (∑ j : Fin N, if j.val + 1 = i.val then f (j.val + 1) else 0) = f i.val := by
  by_cases hi : i.val = 0
  · simp [hi, hf]
  · let k : Fin N := ⟨i.val - 1, by omega⟩
    have hk : k.val + 1 = i.val := by dsimp [k]; omega
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hj
      have hji : j.val + 1 ≠ i.val := by
        intro h
        apply hj
        apply Fin.ext
        dsimp [k]
        omega
      simp [hji]
    · simp

theorem successor_sum {N : ℕ} (f : ℕ → ℝ) (hf : f (N + 1) = 0) (i : Fin N) :
    (∑ j : Fin N, if i.val + 1 = j.val then f (j.val + 1) else 0) = f (i.val + 2) := by
  by_cases hi : i.val + 1 < N
  · let k : Fin N := ⟨i.val + 1, hi⟩
    rw [Finset.sum_eq_single k]
    · simp [k, Nat.add_assoc]
    · intro j _ hj
      have hji : i.val + 1 ≠ j.val := by
        intro h
        apply hj
        exact Fin.ext h.symm
      simp [hji]
    · simp
  · have hiN : i.val + 2 = N + 1 := by omega
    have hall : ∀ j : Fin N, i.val + 1 ≠ j.val := by intro j; omega
    simp [hall, hiN, hf]

theorem scalarDirichlet_apply_sequence {N : ℕ} (d : ℝ) (f : ℕ → ℝ)
    (h0 : f 0 = 0) (hN : f (N + 1) = 0) (i : Fin N) :
    (scalarDirichlet N d *ᵥ fun j => f (j.val + 1)) i =
      d * f (i.val + 1) - f i.val - f (i.val + 2) := by
  simp only [Matrix.mulVec, dotProduct, scalarDirichlet, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_sub_distrib]
  rw [predecessor_sum f h0, successor_sum f hN]
  simp

theorem scalarDirichlet_sine_eigenvector {N : ℕ} (d θ : ℝ)
    (hθ : Real.sin ((N + 1) * θ) = 0) :
    scalarDirichlet N d *ᵥ (fun i => Real.sin ((i.val + 1) * θ)) =
      (d - 2 * Real.cos θ) • (fun i : Fin N => Real.sin ((i.val + 1) * θ)) := by
  funext i
  have happly := scalarDirichlet_apply_sequence d (fun k => Real.sin (k * θ))
    (by simp) (by simpa only [Nat.cast_add, Nat.cast_one] using hθ) i
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at happly
  rw [happly]
  change d * Real.sin ((i.val + 1) * θ) - Real.sin (i.val * θ) -
    Real.sin ((i.val + 2) * θ) = (d - 2 * Real.cos θ) * Real.sin ((i.val + 1) * θ)
  have hplus : ((i.val : ℝ) + 2) * θ = ((i.val : ℝ) + 1) * θ + θ := by ring
  have hminus : (i.val : ℝ) * θ = ((i.val : ℝ) + 1) * θ - θ := by ring
  rw [hplus, hminus, Real.sin_add, Real.sin_sub]
  ring

def firstSineAngle (N : ℕ) : ℝ := Real.pi / (N + 1)

def firstSineVector (N : ℕ) (i : Fin N) : ℝ := Real.sin ((i.val + 1) * firstSineAngle N)

theorem firstSineVector_pos (N : ℕ) (i : Fin N) : 0 < firstSineVector N i := by
  have hden : (0 : ℝ) < N + 1 := by positivity
  have hπ : 0 < Real.pi / (N + 1) := div_pos Real.pi_pos hden
  have hi : (i.val : ℝ) + 1 < N + 1 := by exact_mod_cast Nat.succ_lt_succ i.isLt
  have hb := mul_lt_mul_of_pos_right hi hπ
  have he : ((N : ℝ) + 1) * (Real.pi / (N + 1)) = Real.pi := by field_simp
  rw [he] at hb
  exact Real.sin_pos_of_pos_of_lt_pi (by dsimp [firstSineAngle]; positivity) hb

theorem firstSineVector_eigenvector (N : ℕ) (d : ℝ) :
    scalarDirichlet N d *ᵥ firstSineVector N =
      (d - 2 * Real.cos (firstSineAngle N)) • firstSineVector N := by
  apply scalarDirichlet_sine_eigenvector
  have hden : (N : ℝ) + 1 ≠ 0 := by positivity
  have he : ((N : ℝ) + 1) * firstSineAngle N = Real.pi := by
    dsimp [firstSineAngle]
    field_simp
  rw [he, Real.sin_pi]

def firstSineNormSq (N : ℕ) : ℝ := ∑ i, firstSineVector N i ^ 2

theorem firstSineNormSq_pos {N : ℕ} (hN : 0 < N) : 0 < firstSineNormSq N := by
  apply Finset.sum_pos' (fun i _ => sq_nonneg (firstSineVector N i))
  exact ⟨⟨0, hN⟩, Finset.mem_univ _, sq_pos_of_pos (firstSineVector_pos N ⟨0, hN⟩)⟩

def unitFirstSineVector (N : ℕ) : Fin N → ℝ :=
  (1 / Real.sqrt (firstSineNormSq N)) • firstSineVector N

theorem unitFirstSineVector_norm {N : ℕ} (hN : 0 < N) :
    ∑ i, unitFirstSineVector N i ^ 2 = 1 := by
  have hs := firstSineNormSq_pos hN
  simp only [unitFirstSineVector, Pi.smul_apply, smul_eq_mul, mul_pow,
    ← Finset.mul_sum]
  change (1 / Real.sqrt (firstSineNormSq N)) ^ 2 * firstSineNormSq N = 1
  rw [div_pow, one_pow, Real.sq_sqrt hs.le]
  exact one_div_mul_cancel hs.ne'

theorem unitFirstSineVector_eigenvector (N : ℕ) (d : ℝ) :
    scalarDirichlet N d *ᵥ unitFirstSineVector N =
      (d - 2 * Real.cos (firstSineAngle N)) • unitFirstSineVector N := by
  rw [unitFirstSineVector, Matrix.mulVec_smul, firstSineVector_eigenvector]
  exact smul_comm _ _ _

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SineModeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first scalar Dirichlet eigenvalue and its radial comparison limit. -/

namespace PositiveEinsteinFour.Jacobi

open Filter _root_.Topology

noncomputable section

theorem two_sub_two_cos (x : ℝ) : 2 - 2 * Real.cos x = 4 * Real.sin (x / 2) ^ 2 := by
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc
  nlinarith

def firstEigenvalue (t : ℝ) (N : ℕ) : ℝ :=
  2 - (t / (N + 1)) ^ 2 - 2 * Real.cos (firstSineAngle N)

def scaledFirstEigenvalue (t : ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) + 1) ^ 2 * firstEigenvalue t N

theorem scaledFirstEigenvalue_eq_sinc (t : ℝ) (N : ℕ) :
    scaledFirstEigenvalue t N =
      Real.pi ^ 2 * Real.sinc (Real.pi / (2 * (N + 1))) ^ 2 - t ^ 2 := by
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  have hx : Real.pi / (2 * ((N : ℝ) + 1)) ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hx]
  unfold scaledFirstEigenvalue firstEigenvalue firstSineAngle
  rw [show 2 - (t / ((N : ℝ) + 1)) ^ 2 -
      2 * Real.cos (Real.pi / (N + 1)) =
      (2 - 2 * Real.cos (Real.pi / (N + 1))) - (t / (N + 1)) ^ 2 by ring,
    two_sub_two_cos]
  have hh : Real.pi / ((N : ℝ) + 1) / 2 = Real.pi / (2 * (N + 1)) := by field_simp
  rw [hh]
  field_simp
  ring

theorem scaledFirstEigenvalue_tendsto (t : ℝ) :
    Tendsto (scaledFirstEigenvalue t) atTop (𝓝 (Real.pi ^ 2 - t ^ 2)) := by
  have hzero : Tendsto (fun N : ℕ => Real.pi / (2 * ((N : ℝ) + 1)))
      atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.pi / 2)
    convert h using 1
    · funext N
      field_simp
    · simp
  have hs : Tendsto (fun N : ℕ => Real.sinc (Real.pi / (2 * ((N : ℝ) + 1))))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp hzero
  convert ((hs.pow 2).const_mul (Real.pi ^ 2)).sub_const (t ^ 2) using 1
  · funext N
    exact scaledFirstEigenvalue_eq_sinc t N
  · simp

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ReferenceCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the finite comparison to the actual scalar Dirichlet reference. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def referenceMatrix (t : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  scalarDirichlet N (2 - (t / (N + 1)) ^ 2)

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiRatioLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform convergence of the normalized velocity gives positivity of all
discrete Jacobi ratios, including the first nodes next to zero. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

theorem inverse_product_error
    {R : Type*} [NormedRing R] {B b V v : R} {K M : ℝ}
    (hb : ‖Ring.inverse b‖ ≤ K) (hV : ‖V‖ ≤ M) :
    ‖v * Ring.inverse b - V * Ring.inverse B‖ ≤
      K * ‖v - V‖ + M * ‖Ring.inverse b - Ring.inverse B‖ := by
  have hid : v * Ring.inverse b - V * Ring.inverse B =
      (v - V) * Ring.inverse b + V * (Ring.inverse b - Ring.inverse B) := by
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖(v - V) * Ring.inverse b‖ + ‖V * (Ring.inverse b - Ring.inverse B)‖ :=
      norm_add_le _ _
    _ ≤ ‖v - V‖ * ‖Ring.inverse b‖ + ‖V‖ * ‖Ring.inverse b - Ring.inverse B‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ K * ‖v - V‖ + M * ‖Ring.inverse b - Ring.inverse B‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (v - V)),
        mul_le_mul_of_nonneg_right hV (norm_nonneg (Ring.inverse b - Ring.inverse B))]

/-- Uniform convergence to a continuous coefficient whose initial value
is the identity gives a single mesh threshold for every positive node. -/
theorem eventually_mesh_ratio_positive
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {t : ℝ} (ht : 0 < t) {C : ℝ → F →L[ℝ] F}
    (hC : ContinuousOn C (Set.Icc 0 t)) (hC0 : C 0 = ContinuousLinearMap.id ℝ F)
    {P : ℕ → ℕ → F →L[ℝ] F} {e : ℕ → ℝ}
    (he : Tendsto e atTop (nhds 0))
    (happrox : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ‖P N i - C ((i : ℝ) * (t / (N + 1)))‖ ≤ e N) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N → ∀ x : F, x ≠ 0 →
      0 < inner ℝ ((ContinuousLinearMap.id ℝ F + ((1 : ℝ) / i) • P N i) x) x := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hC
  let K : ℝ := max (M + 1) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousWithinAt_iff.mp
    (hC 0 ⟨le_rfl, ht.le⟩)) (1 / 2) (by norm_num)
  let η : ℝ := δ / 2
  have hη : 0 < η := half_pos hδ
  have hmesh : Tendsto (fun N : ℕ => (t / (N + 1)) * K) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat t).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, zero_mul] using
      h.mul_const K
  filter_upwards [happrox, he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hmesh.eventually (gt_mem_nhds hη)] with N hN heN hmN
  intro i hi hiN x hx
  have hh : 0 < t / (N + 1 : ℝ) := div_pos ht (by positivity)
  have his : (i : ℝ) * (t / (N + 1)) ∈ Set.Icc 0 t := by
    constructor
    · positivity
    · have hi' : (i : ℝ) ≤ N + 1 := by exact_mod_cast hiN.trans (Nat.le_succ N)
      calc
        _ ≤ (N + 1 : ℝ) * (t / (N + 1)) := mul_le_mul_of_nonneg_right hi' hh.le
        _ = t := by field_simp
  have hb : ‖P N i‖ ≤ K := by
    calc
      _ ≤ ‖P N i - C ((i : ℝ) * (t / (N + 1)))‖ +
          ‖C ((i : ℝ) * (t / (N + 1)))‖ := norm_le_norm_sub_add _ _
      _ ≤ e N + M := add_le_add (hN i hi hiN) (hM _ his)
      _ ≤ M + 1 := by linarith
      _ ≤ K := le_max_left _ _
  apply mesh_ratio_quadratic_pos hi hh hmN hb ?_ hx
  intro hs
  have hd : dist ((i : ℝ) * (t / (N + 1))) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg his.1]
    exact lt_of_le_of_lt hs (by dsimp [η]; linarith)
  have hc := hnear his hd
  rw [hC0, dist_eq_norm] at hc
  calc
    _ ≤ ‖P N i - C ((i : ℝ) * (t / (N + 1)))‖ +
        ‖C ((i : ℝ) * (t / (N + 1))) - ContinuousLinearMap.id ℝ F‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ e N + ‖C ((i : ℝ) * (t / (N + 1))) - ContinuousLinearMap.id ℝ F‖ :=
      add_le_add_left (hN i hi hiN) _
    _ < 1 := by linarith

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixRatioPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translating the operator-norm mesh criterion into positive matrices. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

theorem matrix_posDef_of_quadratic {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hsym : Aᵀ = A)
    (hpos : ∀ x : EuclideanSpace ℝ n, x ≠ 0 →
      0 < inner ℝ ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) A x) x) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hsym
  · intro y hy
    have hx : WithLp.toLp 2 y ≠ (0 : EuclideanSpace ℝ n) := by
      intro he
      apply hy
      exact congrArg WithLp.ofLp he
    have hp := hpos (WithLp.toLp 2 y) hx
    rw [real_inner_comm, Matrix.inner_toEuclideanCLM] at hp
    simpa using hp

/-- A symmetric matrix ratio is eventually positive at every mesh node
once its coefficient converges uniformly to the normalized Jacobi curve. -/
theorem eventually_matrix_ratio_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {t : ℝ} (ht : 0 < t) {C : ℝ → Matrix n n ℝ}
    (hC : ContinuousOn C (Set.Icc 0 t)) (hC0 : C 0 = 1)
    {P : ℕ → ℕ → Matrix n n ℝ} {e : ℕ → ℝ}
    (he : Tendsto e atTop (nhds 0))
    (happrox : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ‖P N i - C ((i : ℝ) * (t / (N + 1)))‖ ≤ e N)
    (hsym : ∀ N i : ℕ, ((1 : Matrix n n ℝ) + ((1 : ℝ) / i) • P N i)ᵀ =
      1 + ((1 : ℝ) / i) • P N i) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ((1 : Matrix n n ℝ) + ((1 : ℝ) / i) • P N i).PosDef := by
  have hc : ContinuousOn (fun s => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (C s)) (Set.Icc 0 t) := by
    have hi : Isometry (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) :=
      AddMonoidHomClass.isometry_of_norm
        (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).toAlgEquiv.toAddEquiv (fun _ => rfl)
    exact hi.continuous.comp_continuousOn hC
  have hc0 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (C 0) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ n) := by
    rw [hC0, map_one]
    rfl
  have ha : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (P N i) -
        (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (C ((i : ℝ) * (t / (N + 1))))‖ ≤ e N := by
    filter_upwards [happrox] with N hN i hi hiN
    simpa only [← map_sub, Matrix.l2_opNorm_toEuclideanCLM] using hN i hi hiN
  have hp := eventually_mesh_ratio_positive ht hc hc0 he ha
  filter_upwards [hp] with N hN i hi hiN
  apply matrix_posDef_of_quadratic (hsym N i)
  intro x hx
  simpa only [map_add, map_one, map_smul, ContinuousLinearMap.one_def] using hN i hi hiN x hx

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiMeshInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform inverse control at every node of a preconjugate mesh. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

theorem isUnit_of_divided_time {R : Type*} [Ring R] [Algebra ℝ R]
    {X : R} {s : ℝ} (hs : s ≠ 0) (hX : IsUnit (s⁻¹ • X)) : IsUnit X := by
  have hu : IsUnit (algebraMap ℝ R s) :=
    (isUnit_iff_ne_zero.mpr hs).map (algebraMap ℝ R)
  have h := hu.mul hX
  simpa only [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hs, one_smul] using h

/-- Invertibility is uniform on the whole closed preconjugate interval;
the error threshold is independent of the mesh node. -/
theorem eventually_mesh_inverse_bounds
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    {t : ℝ} (ht : 0 ≤ t) {B : ℝ → R}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s))
    {b : ℕ → ℕ → R} {e : ℕ → ℝ} (he : Tendsto e atTop (nhds 0))
    (herror : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N + 1 →
      ‖b N i - B ((i : ℝ) * (t / (N + 1)))‖ ≤ e N) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N + 1 →
      IsUnit (b N i) ∧ ‖Ring.inverse (b N i)‖ ≤ 2 * K ∧
        ‖Ring.inverse (b N i) - Ring.inverse (B ((i : ℝ) * (t / (N + 1))))‖ ≤
          2 * K ^ 2 * e N := by
  obtain ⟨K, hK, hb⟩ := uniform_inverse_neighborhood hB hunit
  refine ⟨K, hK, ?_⟩
  filter_upwards [herror, he.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * K)))] with N hN heN
  intro i hi
  have hh : 0 ≤ t / (N + 1 : ℝ) := div_nonneg ht (by positivity)
  have hs : (i : ℝ) * (t / (N + 1)) ∈ Set.Icc 0 t := by
    constructor
    · positivity
    · calc
        _ ≤ (N + 1 : ℝ) * (t / (N + 1)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh
        _ = t := by field_simp
  obtain ⟨hu, hn, hd⟩ := hb _ hs (b N i) ((hN i hi).trans heN.le)
  exact ⟨hu, hn, hd.trans (mul_le_mul_of_nonneg_left (hN i hi) (by positivity))⟩

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiMeshCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform approximation of the velocity times normalized-position inverse. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

theorem inverse_product_continuousOn
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    {B V : ℝ → R} {t : ℝ}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hV : ContinuousOn V (Set.Icc 0 t))
    (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s)) :
    ContinuousOn (fun s => V s * Ring.inverse (B s)) (Set.Icc 0 t) := by
  apply hV.mul
  intro s hs
  have hi : ContinuousAt (Ring.inverse : R → R) (B s) := by
    simpa using NormedRing.inverse_continuousAt (hunit s hs).unit
  exact hi.comp_continuousWithinAt (hB s hs)

theorem mesh_inverse_product_converges
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    {t : ℝ} (ht : 0 ≤ t) {B V : ℝ → R}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hV : ContinuousOn V (Set.Icc 0 t))
    (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s))
    {b v : ℕ → ℕ → R} {eB eV : ℕ → ℝ}
    (heB : Tendsto eB atTop (nhds 0)) (heV : Tendsto eV atTop (nhds 0))
    (hb : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N + 1 →
      ‖b N i - B ((i : ℝ) * (t / (N + 1)))‖ ≤ eB N)
    (hv : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N →
      ‖v N i - V ((i : ℝ) * (t / (N + 1)))‖ ≤ eV N) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N → IsUnit (b N i) ∧
        ‖v N i * Ring.inverse (b N i) -
          V ((i : ℝ) * (t / (N + 1))) *
            Ring.inverse (B ((i : ℝ) * (t / (N + 1))))‖ ≤ e N := by
  obtain ⟨K, hK, hinv⟩ := eventually_mesh_inverse_bounds ht hB hunit heB hb
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hV
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  let e : ℕ → ℝ := fun N => 2 * K * eV N + M * (2 * K ^ 2 * eB N)
  have he : Tendsto e atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (heV.const_mul (2 * K)).add ((heB.const_mul (2 * K ^ 2)).const_mul M)
  refine ⟨e, he, ?_⟩
  filter_upwards [hinv, hv] with N hN hvN
  intro i hi
  obtain ⟨hu, hn, hd⟩ := hN i (hi.trans (Nat.le_succ N))
  have hs : (i : ℝ) * (t / (N + 1)) ∈ Set.Icc 0 t := by
    constructor
    · positivity
    · calc
        _ ≤ (N + 1 : ℝ) * (t / (N + 1)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi.trans (Nat.le_succ N))
            (div_nonneg ht (by positivity))
        _ = t := by field_simp
  refine ⟨hu, ?_⟩
  calc
    _ ≤ (2 * K) * ‖v N i - V ((i : ℝ) * (t / (N + 1)))‖ +
        M * ‖Ring.inverse (b N i) - Ring.inverse (B ((i : ℝ) * (t / (N + 1))))‖ :=
      inverse_product_error hn ((hM₀ _ hs).trans (le_max_left _ _))
    _ ≤ e N := by
      dsimp [e]
      gcongr
      · exact hvN i hi

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiODEPositivity
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

def meshStep (t : ℝ) (N : ℕ) : ℝ := t / (N + 1)

theorem meshStep_tendsto (t : ℝ) : Tendsto (meshStep t) atTop (nhds 0) := by
  change Tendsto (fun N : ℕ => t / ((N : ℝ) + 1)) atTop (nhds 0)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualJacobiODEDependence
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

/-- A perturbation estimate uses a bound only on the reference solution. -/
theorem linear_solution_difference_bound (A B : ℝ → E →L[ℝ] E)
    (γ η : ℝ → E) (K : ℝ≥0) (δ C T : ℝ) (hδ : 0 ≤ δ)
    (hK : ∀ t, ‖A t‖ ≤ K)
    (hγ : ∀ t, HasDerivAt γ (A t (γ t)) t)
    (hη : ∀ t, HasDerivAt η (B t (η t)) t) (h0 : γ 0 = η 0)
    (hAB : ∀ s ∈ Icc 0 T, ‖A s - B s‖ ≤ δ)
    (hC : ∀ s ∈ Icc 0 T, ‖η s‖ ≤ C) :
    ∀ t ∈ Icc 0 T, ‖γ t - η t‖ ≤ gronwallBound 0 K (δ * C) t := by
  have hd (s : ℝ) : HasDerivAt (fun t => γ t - η t)
      (A s (γ s) - B s (η s)) s := (hγ s).sub (hη s)
  have hc : ContinuousOn (fun t => γ t - η t) (Icc 0 T) :=
    fun s _ => (hd s).continuousAt.continuousWithinAt
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      ‖A s (γ s) - B s (η s)‖ ≤ (K : ℝ) * ‖γ s - η s‖ + δ * C := by
    have heq : A s (γ s) - B s (η s) =
        A s (γ s - η s) + (A s - B s) (η s) := by
      simp only [map_sub, sub_apply]
      abel
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add ((A s).le_of_opNorm_le (hK s) _)
    calc
      ‖(A s - B s) (η s)‖ ≤ δ * ‖η s‖ :=
        (A s - B s).le_of_opNorm_le (hAB s (Ico_subset_Icc_self hs)) _
      _ ≤ δ * C := mul_le_mul_of_nonneg_left (hC s (Ico_subset_Icc_self hs)) hδ
  intro t ht
  simpa only [sub_zero] using norm_le_gronwallBound_of_norm_deriv_right_le hc
    (fun s _ => (hd s).hasDerivWithinAt) (by rw [h0, sub_self, norm_zero]) hb t ht

theorem linear_solution_difference_bound_abs (A B : ℝ → E →L[ℝ] E)
    (γ η : ℝ → E) (K : ℝ≥0) (δ C T : ℝ) (hδ : 0 ≤ δ) (hC0 : 0 ≤ C)
    (hK : ∀ t, ‖A t‖ ≤ K)
    (hγ : ∀ t, HasDerivAt γ (A t (γ t)) t)
    (hη : ∀ t, HasDerivAt η (B t (η t)) t) (h0 : γ 0 = η 0)
    (hAB : ∀ s ∈ Icc (-T) T, ‖A s - B s‖ ≤ δ)
    (hC : ∀ s ∈ Icc (-T) T, ‖η s‖ ≤ C) (t : ℝ) (ht : |t| ≤ T) :
    ‖γ t - η t‖ ≤ gronwallBound 0 K (δ * C) T := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hmono := gronwallBound_mono (δ := 0) (K := (K : ℝ)) (ε := δ * C)
    le_rfl (mul_nonneg hδ hC0) K.coe_nonneg
  by_cases ht0 : 0 ≤ t
  · apply (linear_solution_difference_bound A B γ η K δ C T hδ hK hγ hη h0
      (fun s hs => hAB s ⟨by linarith [hs.1], hs.2⟩)
      (fun s hs => hC s ⟨by linarith [hs.1], hs.2⟩) t
      ⟨ht0, (le_abs_self t).trans ht⟩).trans
    exact hmono ((le_abs_self t).trans ht)
  · have hrevγ (s : ℝ) : HasDerivAt (fun u => γ (-u))
        ((-A (-s)) (γ (-s))) s := by
      simpa only [Function.comp_def, neg_one_smul, neg_apply] using
        (hγ (-s)).scomp s (hasDerivAt_id s).neg
    have hrevη (s : ℝ) : HasDerivAt (fun u => η (-u))
        ((-B (-s)) (η (-s))) s := by
      simpa only [Function.comp_def, neg_one_smul, neg_apply] using
        (hη (-s)).scomp s (hasDerivAt_id s).neg
    have habrev (s : ℝ) (hs : s ∈ Icc 0 T) : ‖-A (-s) - -B (-s)‖ ≤ δ := by
      simpa only [neg_sub_neg, norm_sub_rev] using hAB (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h := linear_solution_difference_bound (fun s => -A (-s)) (fun s => -B (-s))
      (fun s => γ (-s)) (fun s => η (-s)) K δ C T hδ
      (fun s => by simpa only [norm_neg] using hK (-s)) hrevγ hrevη
      (by simpa only [neg_zero] using h0) habrev
      (fun s hs => hC (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (-t) ⟨by linarith, (neg_le_abs t).trans ht⟩
    simp only [neg_neg] at h
    exact h.trans (hmono ((neg_le_abs t).trans ht))

variable {P : Type*} [TopologicalSpace P]

theorem coefficient_eventually_close (A : ℝ × P → E →L[ℝ] E)
    (hA : Continuous A) (p : P) (T δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ q in 𝓝 p, ∀ s ∈ Icc (-T) T, ‖A (s, q) - A (s, p)‖ < δ := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro s _
  have hc : Continuous (fun q : P × ℝ => ‖A (q.2, q.1) - A (q.2, p)‖) :=
    (hA.comp (continuous_snd.prodMk continuous_fst)).sub
      (hA.comp (continuous_snd.prodMk continuous_const)) |>.norm
  exact hc.continuousAt.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hδ))

/-- Continuity holds for any choice of the global solutions, since their
initial values are fixed and the bounded linear equation is unique. -/
theorem continuous_linear_solution_family (A : ℝ × P → E →L[ℝ] E)
    (γ : P → ℝ → E) (x : E) (hA : Continuous A) (K : ℝ≥0)
    (hK : ∀ s p, ‖A (s, p)‖ ≤ K) (h0 : ∀ p, γ p 0 = x)
    (hd : ∀ p s, HasDerivAt (γ p) (A (s, p) (γ p s)) s) :
    Continuous (fun p : ℝ × P => γ p.2 p.1) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, p⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let T := |t| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hγc : Continuous (γ p) :=
    continuous_iff_continuousAt.mpr (fun s => (hd p s).continuousAt)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hγc.continuousOn
  let C₀ := max 0 C
  have hC0 : 0 ≤ C₀ := le_max_left _ _
  have hbound (s : ℝ) (hs : s ∈ Icc (-T) T) : ‖γ p s‖ ≤ C₀ :=
    (hC s hs).trans (le_max_right _ _)
  have hg : Tendsto (fun δ : ℝ => gronwallBound 0 K (δ * C₀) T) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, zero_mul, gronwallBound_ε0_δ0] using
      ((gronwallBound_continuous_ε 0 K T).comp (continuous_id.mul_const C₀)).tendsto 0
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hg (ε / 2) (half_pos hε))
  have hδsmall : gronwallBound 0 K ((δ / 2) * C₀) T < ε / 2 := by
    have hz := hsmall (show dist (δ / 2) 0 < δ by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
    exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hz)
  have hcoeff := coefficient_eventually_close A hA p T (δ / 2) (half_pos hδ)
  have htime : ∀ᶠ u in 𝓝 t, |u| ≤ T := by
    exact (continuous_abs.tendsto t).eventually
      (eventually_le_nhds (show |t| < T by dsimp [T]; linarith))
  have hbase : ∀ᶠ u in 𝓝 t, dist (γ p u) (γ p t) < ε / 2 :=
    (hγc.tendsto t).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hcoeff,
    continuous_fst.continuousAt.preimage_mem_nhds htime,
    continuous_fst.continuousAt.preimage_mem_nhds hbase] with q hq hqt hqb
  have hdiff : ‖γ q.2 q.1 - γ p q.1‖ ≤ gronwallBound 0 K ((δ / 2) * C₀) T :=
    linear_solution_difference_bound_abs (fun s => A (s, q.2)) (fun s => A (s, p))
      (γ q.2) (γ p) K (δ / 2) C₀ T (half_pos hδ).le hC0
      (fun s => hK s q.2) (hd q.2) (hd p) ((h0 q.2).trans (h0 p).symm)
      (fun s hs => (hq s hs).le) hbound q.1 hqt
  apply (dist_triangle _ (γ p q.1) _).trans_lt
  calc
    dist (γ q.2 q.1) (γ p q.1) + dist (γ p q.1) (γ p t) < ε / 2 + ε / 2 :=
      add_lt_add (by simpa only [dist_eq_norm] using hdiff.trans_lt hδsmall) hqb
    _ = ε := add_halves ε

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized Euclidean four-dimensional Gaussian used in the local
heat construction. All integrals use the actual Euclidean volume measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory GaussianFourier

noncomputable section

theorem fourGaussian_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : FourSpace => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (integrable_cexp_neg_mul_sq_norm_add (V := FourSpace) (b := (b : ℂ))
    (by simpa using hb) 0 0).re
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [zero_mul, add_zero]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatCompactTimeIntegral
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating a four-dimensional compactly supported pairing at
positive time. The domination is proved from compactness, not assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric MeasureTheory
open scoped _root_.Topology

noncomputable section

theorem fourHeat_compact_time_integral
    (F F' : ℝ → FourSpace → ℝ) (K : Set FourSpace) (hK : IsCompact K)
    (hF : ∀ t > 0, Continuous (F t))
    (hF' : ContinuousOn (Function.uncurry F') (Ioi (0 : ℝ) ×ˢ univ))
    (hs : ∀ t > 0, ∀ x ∉ K, F t x = 0)
    (hs' : ∀ t > 0, ∀ x ∉ K, F' t x = 0)
    (hd : ∀ t > 0, ∀ x, HasDerivAt (fun s => F s x) (F' t x) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, F s x) (∫ x, F' t x) t := by
  have hI (s : ℝ) (hs : s ∈ closedBall t (t / 2)) : 0 < s := by
    have habs : |s - t| ≤ t / 2 := by simpa only [mem_closedBall, Real.dist_eq] using hs
    have := (abs_le.mp habs).1
    linarith
  have hprod : closedBall t (t / 2) ×ˢ K ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    fun z hz => ⟨hI z.1 hz.1, mem_univ _⟩
  have hcompact := (isCompact_closedBall t (t / 2)).prod hK
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image (hF'.mono hprod).norm
  let b : FourSpace → ℝ := K.indicator (fun _ => max C 0)
  have hb : Integrable b := by
    exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  have hbound : ∀ x, ∀ s ∈ ball t (t / 2), ‖F' s x‖ ≤ b x := by
    intro x s hsball
    by_cases hx : x ∈ K
    · change ‖F' s x‖ ≤ K.indicator (fun _ => max C 0) x
      rw [indicator_of_mem hx]
      exact (hC ⟨(s, x), ⟨ball_subset_closedBall hsball, hx⟩, rfl⟩).trans (le_max_left _ _)
    · change ‖F' s x‖ ≤ K.indicator (fun _ => max C 0) x
      rw [indicator_of_notMem hx, hs' s (hI s (ball_subset_closedBall hsball)) x hx,
        norm_zero]
  have hFc : HasCompactSupport (F t) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (hs t ht x hn)
  have hF't : Continuous (F' t) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hF'.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show (t, x) ∈ Ioi (0 : ℝ) ×ˢ univ from ⟨ht, mem_univ x⟩))).comp
      (continuousAt_const.prodMk continuousAt_id)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds t (by positivity))
    (by filter_upwards [Ioi_mem_nhds ht] with s hs; exact (hF s hs).aestronglyMeasurable)
    ((hF t ht).integrable_of_hasCompactSupport hFc) hF't.aestronglyMeasurable
    (Eventually.of_forall hbound) hb
    (Eventually.of_forall fun x s hsball => hd s (hI s (ball_subset_closedBall hsball)) x)).2

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianConvolution
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Completing the square gives the exact Euclidean heat semigroup. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

theorem fourHeatGaussian_complete_square (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (x y : FourSpace) :
    -(4 * t)⁻¹ * ‖x - y‖ ^ 2 + -(4 * s)⁻¹ * ‖y‖ ^ 2 =
      -(4 * (t + s))⁻¹ * ‖x‖ ^ 2 +
      -(4 * (t * s / (t + s)))⁻¹ * ‖y - (s / (t + s)) • x‖ ^ 2 := by
  have hts : t + s ≠ 0 := ne_of_gt (add_pos ht hs)
  rw [norm_sub_sq_real, norm_sub_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm y x]
  field_simp
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial absorption and actual Gaussian moment bounds for the local
heat remainder. These bounds use Euclidean volume and the proved unit mass. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

theorem fourHeatPolynomial_absorption (m : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    z ^ m * Real.exp (-z) ≤ (m.factorial : ℝ) := by
  have hf : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have h : z ^ m ≤ Real.exp z * (m.factorial : ℝ) :=
    (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp z hz m)
  calc
    _ ≤ (Real.exp z * (m.factorial : ℝ)) * Real.exp (-z) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (m.factorial : ℝ) := by
      rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricCurvatureGreen
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

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

abbrev MatrixVector := EuclideanSpace ℝ (Fin 3 × Fin 3)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Polarization of the actual derivative-slot Green integrands. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open PositiveEinsteinFour.Geometry

noncomputable section

abbrev DerivativeCoefficient := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

end
end PositiveEinsteinFour.HighestHessian
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicJacobiIntegralCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating an interval integral twice on a compact parameter strip.
Joint continuity supplies the uniform derivative bound, so no domination
estimate is added to the geometric hypotheses. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set Filter
open scoped _root_.Topology BigOperators

noncomputable section

theorem continuousOn_rectangle_slice (F : ℝ → ℝ → ℝ)
    {δ a b ε : ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b)) (hε : ε ∈ Icc (-δ) δ) :
    ContinuousOn (F ε) (Icc a b) :=
  hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ ht => ⟨hε, ht⟩)

theorem intervalIntegral_hasDerivAt_rectangle (F G : ℝ → ℝ → ℝ)
    {δ a b ε : ℝ} (hab : a ≤ b) (hε : ε ∈ Ioo (-δ) δ)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hd : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => F r t) (G s t) s) :
    HasDerivAt (fun s => ∫ t in a..b, F s t) (∫ t in a..b, G ε t) ε := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG
  have hs : Ioo (-δ) δ ∈ 𝓝 ε := isOpen_Ioo.mem_nhds hε
  have hmeas : ∀ᶠ s in 𝓝 ε, AEStronglyMeasurable (F s) (volume.restrict (Ioc a b)) := by
    filter_upwards [hs] with s hs
    exact ((continuousOn_rectangle_slice F hF ⟨hs.1.le, hs.2.le⟩).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hFint : Integrable (F ε) (volume.restrict (Ioc a b)) :=
    (continuousOn_rectangle_slice F hF ⟨hε.1.le, hε.2.le⟩).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hGmeas : AEStronglyMeasurable (G ε) (volume.restrict (Ioc a b)) :=
    ((continuousOn_rectangle_slice G hG ⟨hε.1.le, hε.2.le⟩).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ∀ s ∈ Ioo (-δ) δ, ‖G s t‖ ≤ C :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht s hs =>
      hC (s, t) ⟨⟨hs.1.le, hs.2.le⟩, ⟨ht.1.le, ht.2⟩⟩
  have hconst : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc a b)) :=
    (continuous_const : Continuous (fun _ : ℝ => C)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ∀ s ∈ Ioo (-δ) δ, HasDerivAt (fun r => F r t) (G s t) s :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht s hs => hd s hs t ⟨ht.1.le, ht.2⟩
  have hi := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hFint
    hGmeas hbound hconst hdiff).2
  simpa only [intervalIntegral.integral_of_le hab] using hi

theorem intervalIntegral_secondDeriv_rectangle (F G H : ℝ → ℝ → ℝ)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hd : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => F r t) (G s t) s)
    (hdd : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => G r t) (H s t) s) :
    HasDerivAt (deriv (fun s => ∫ t in a..b, F s t))
      (∫ t in a..b, H 0 t) 0 := by
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hi := intervalIntegral_hasDerivAt_rectangle G H hab hzero hG hH hdd
  have heq : deriv (fun s => ∫ t in a..b, F s t) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => ∫ t in a..b, G s t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    exact (intervalIntegral_hasDerivAt_rectangle F G hab hs hF hG hd).deriv
  exact hi.congr_of_eventuallyEq heq

/-- Matching chart boundary values cancel without requiring a global chart. -/
theorem finite_piece_boundary_cancellation (n : ℕ) (E I L R : ℕ → ℝ)
    (hE : ∀ i < n, E i = I i + R i - L i)
    (hjoin : ∀ i < n, R i = L (i + 1)) :
    (∑ i ∈ Finset.range n, E i) = (∑ i ∈ Finset.range n, I i) + L n - L 0 := by
  have hsum : (∑ i ∈ Finset.range n, E i) =
      (∑ i ∈ Finset.range n, I i) +
        ∑ i ∈ Finset.range n, (L (i + 1) - L i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hE i (Finset.mem_range.mp hi), hjoin i (Finset.mem_range.mp hi)]
    ring
  rw [hsum, Finset.sum_range_sub]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicJacobiSecondVariationAlgebra
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

def jacobiMetricRate (G A : Mat4) : Mat4 := Aᵀ * G + G * A

def jacobiMetricSecondRate (G B C : Mat4) : Mat4 :=
  Cᵀ * G + Bᵀ * jacobiMetricRate G B + jacobiMetricRate G B * B + G * C

theorem jacobiMetricRate_symm {G : Mat4} (hG : G.IsSymm) (A : Mat4) :
    (jacobiMetricRate G A).IsSymm := by
  change (Aᵀ * G + G * A)ᵀ = Aᵀ * G + G * A
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hG.eq]
  exact add_comm _ _

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

theorem sum_four_nonneg_zero (f : Fin 4 → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hz : ∑ i, f i = 0) (i : Fin 4) : f i = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hf j)).mp hz i (Finset.mem_univ i)

end PositiveEinsteinFour.Geometry
end


section

/-! Integrating the actual coordinate second variation.  Parameter derivatives
are raw derivatives of the position and velocity; time derivatives are the
geodesic equation and the two mixed derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem secondDeriv_at_of_shift (f : ℝ → ℝ) (s D : ℝ)
    (h : HasDerivAt (deriv (fun r => f (s + r))) D 0) :
    HasDerivAt (deriv f) D s := by
  have h' : HasDerivAt (fun r => deriv f (s + r)) D 0 := by
    have heq : deriv (fun r => f (s + r)) = (fun r => deriv f (s + r)) := by
      funext r
      exact deriv_comp_const_add f s r
    rw [heq] at h
    exact h
  have h'' : HasDerivAt (fun r => deriv f (s + r)) D (s - s) := by
    simpa only [sub_self] using h'
  have hc := h''.comp_sub_const s s
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A chart variation with exact prescribed endpoint curves.  The affine
correction preserves the desired position field and mixed derivative at zero,
while supplying the second jets required for chart boundary cancellation. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology

noncomputable section

def endpointWeightLeft (a b t : ℝ) : ℝ := (b - t) / (b - a)
def endpointWeightRight (a b t : ℝ) : ℝ := (t - a) / (b - a)

theorem endpointWeightLeft_hasDerivAt (a b t : ℝ) :
    HasDerivAt (endpointWeightLeft a b) (-(b - a)⁻¹) t := by
  simpa only [endpointWeightLeft, neg_div, one_div, Pi.sub_apply, id_eq, zero_sub] using!
    ((hasDerivAt_const t b).sub (hasDerivAt_id t)).div_const (b - a)

theorem endpointWeightRight_hasDerivAt (a b t : ℝ) :
    HasDerivAt (endpointWeightRight a b) ((b - a)⁻¹) t := by
  simpa only [endpointWeightRight, one_div, id_eq] using!
    ((hasDerivAt_id t).sub_const a).div_const (b - a)

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def endpointResidual (A : ℝ → E) (x y : E) (ε : ℝ) : E := A ε - x - ε • y

def endpointCorrectedPosition (x y A B : ℝ → E) (a b ε t : ℝ) : E :=
  x t + ε • y t + endpointWeightLeft a b t • endpointResidual A (x a) (y a) ε +
    endpointWeightRight a b t • endpointResidual B (x b) (y b) ε

def endpointCorrectedParameter (y A' B' : ℝ → E) (a b ε t : ℝ) : E :=
  y t + endpointWeightLeft a b t • (A' ε - y a) +
    endpointWeightRight a b t • (B' ε - y b)

def endpointCorrectedSecond (A'' B'' : ℝ → E) (a b ε t : ℝ) : E :=
  endpointWeightLeft a b t • A'' ε + endpointWeightRight a b t • B'' ε

def endpointCorrectedVelocity (x y v w A B : ℝ → E) (a b ε t : ℝ) : E :=
  v t + ε • w t - (b - a)⁻¹ • endpointResidual A (x a) (y a) ε +
    (b - a)⁻¹ • endpointResidual B (x b) (y b) ε

def endpointCorrectedMixed (y w A' B' : ℝ → E) (a b ε t : ℝ) : E :=
  w t - (b - a)⁻¹ • (A' ε - y a) + (b - a)⁻¹ • (B' ε - y b)

def endpointCorrectedMixedSecond (A'' B'' : ℝ → E) (a b ε : ℝ) : E :=
  -(b - a)⁻¹ • A'' ε + (b - a)⁻¹ • B'' ε

theorem endpointResidual_hasDerivAt (A : ℝ → E) (x y A' : E) (ε : ℝ)
    (hA : HasDerivAt A A' ε) :
    HasDerivAt (endpointResidual A x y) (A' - y) ε := by
  simpa only [endpointResidual, one_smul, Pi.sub_apply, id_eq] using!
    (hA.sub_const x).sub ((hasDerivAt_id ε).smul_const y)

theorem endpointCorrectedPosition_left (x y A B : ℝ → E) (a b ε : ℝ) (hab : a ≠ b) :
    endpointCorrectedPosition x y A B a b ε a = A ε := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [endpointCorrectedPosition, endpointWeightLeft, endpointWeightRight,
    sub_self, zero_div, zero_smul, div_self hba, one_smul, add_zero, endpointResidual]
  abel

theorem endpointCorrectedPosition_right (x y A B : ℝ → E) (a b ε : ℝ) (hab : a ≠ b) :
    endpointCorrectedPosition x y A B a b ε b = B ε := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [endpointCorrectedPosition, endpointWeightLeft, endpointWeightRight,
    sub_self, zero_div, zero_smul, div_self hba, one_smul, add_zero, endpointResidual]
  abel

theorem endpointCorrectedPosition_parameter (x y A B A' B' : ℝ → E)
    (a b ε t : ℝ) (hA : HasDerivAt A (A' ε) ε) (hB : HasDerivAt B (B' ε) ε) :
    HasDerivAt (fun r => endpointCorrectedPosition x y A B a b r t)
      (endpointCorrectedParameter y A' B' a b ε t) ε := by
  have h₁ := ((hasDerivAt_id ε).smul_const (y t)).const_add (x t)
  have h₂ := (endpointResidual_hasDerivAt A (x a) (y a) (A' ε) ε hA).const_smul
    (endpointWeightLeft a b t)
  have h₃ := (endpointResidual_hasDerivAt B (x b) (y b) (B' ε) ε hB).const_smul
    (endpointWeightRight a b t)
  simpa only [endpointCorrectedPosition, endpointCorrectedParameter, one_smul,
    Pi.add_apply, Pi.smul_apply, id_eq] using! (h₁.add h₂).add h₃

theorem endpointCorrectedParameter_parameter (y A' B' A'' B'' : ℝ → E)
    (a b ε t : ℝ) (hA : HasDerivAt A' (A'' ε) ε) (hB : HasDerivAt B' (B'' ε) ε) :
    HasDerivAt (fun r => endpointCorrectedParameter y A' B' a b r t)
      (endpointCorrectedSecond A'' B'' a b ε t) ε := by
  have h₁ := ((hA.sub_const (y a)).const_smul (endpointWeightLeft a b t)).const_add (y t)
  have h₂ := (hB.sub_const (y b)).const_smul (endpointWeightRight a b t)
  simpa only [endpointCorrectedParameter, endpointCorrectedSecond, Pi.add_apply,
    Pi.smul_apply] using! h₁.add h₂

theorem endpointCorrectedVelocity_parameter (x y v w A B A' B' : ℝ → E)
    (a b ε t : ℝ) (hA : HasDerivAt A (A' ε) ε) (hB : HasDerivAt B (B' ε) ε) :
    HasDerivAt (fun r => endpointCorrectedVelocity x y v w A B a b r t)
      (endpointCorrectedMixed y w A' B' a b ε t) ε := by
  have h₁ := ((hasDerivAt_id ε).smul_const (w t)).const_add (v t)
  have h₂ := (endpointResidual_hasDerivAt A (x a) (y a) (A' ε) ε hA).const_smul (b - a)⁻¹
  have h₃ := (endpointResidual_hasDerivAt B (x b) (y b) (B' ε) ε hB).const_smul (b - a)⁻¹
  simpa only [endpointCorrectedVelocity, endpointCorrectedMixed, one_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, id_eq] using! (h₁.sub h₂).add h₃

theorem endpointCorrectedMixed_parameter (y w A' B' A'' B'' : ℝ → E)
    (a b ε t : ℝ) (hA : HasDerivAt A' (A'' ε) ε) (hB : HasDerivAt B' (B'' ε) ε) :
    HasDerivAt (fun r => endpointCorrectedMixed y w A' B' a b r t)
      (endpointCorrectedMixedSecond A'' B'' a b ε) ε := by
  have h₁ := ((hA.sub_const (y a)).const_smul (b - a)⁻¹).neg.const_add (w t)
  have h₂ := (hB.sub_const (y b)).const_smul (b - a)⁻¹
  simpa only [endpointCorrectedMixed, endpointCorrectedMixedSecond, sub_eq_add_neg,
    neg_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply] using! h₁.add h₂

theorem endpointCorrectedPosition_time (x y v w A B : ℝ → E)
    (a b ε t : ℝ) (hx : HasDerivAt x (v t) t) (hy : HasDerivAt y (w t) t) :
    HasDerivAt (fun s => endpointCorrectedPosition x y A B a b ε s)
      (endpointCorrectedVelocity x y v w A B a b ε t) t := by
  have h₁ := hx.add (hy.const_smul ε)
  have h₂ := (endpointWeightLeft_hasDerivAt a b t).smul_const
    (endpointResidual A (x a) (y a) ε)
  have h₃ := (endpointWeightRight_hasDerivAt a b t).smul_const
    (endpointResidual B (x b) (y b) ε)
  simpa only [endpointCorrectedPosition, endpointCorrectedVelocity, sub_eq_add_neg,
    neg_smul, Pi.add_apply, Pi.smul_apply] using! (h₁.add h₂).add h₃

theorem endpointCorrectedSecond_time (A'' B'' : ℝ → E) (a b ε t : ℝ) :
    HasDerivAt (fun s => endpointCorrectedSecond A'' B'' a b ε s)
      (endpointCorrectedMixedSecond A'' B'' a b ε) t := by
  simpa only [endpointCorrectedSecond, endpointCorrectedMixedSecond, Pi.add_apply] using!
    ((endpointWeightLeft_hasDerivAt a b t).smul_const (A'' ε)).add
      ((endpointWeightRight_hasDerivAt a b t).smul_const (B'' ε))

theorem continuous_endpointCorrectedPosition (x y A B : ℝ → E) (a b : ℝ)
    (hx : Continuous x) (hy : Continuous y) (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun p : ℝ × ℝ => endpointCorrectedPosition x y A B a b p.1 p.2) := by
  unfold endpointCorrectedPosition endpointResidual endpointWeightLeft endpointWeightRight
  fun_prop

theorem continuous_endpointCorrectedSecond (A'' B'' : ℝ → E) (a b : ℝ)
    (hA : Continuous A'') (hB : Continuous B'') :
    Continuous (fun p : ℝ × ℝ => endpointCorrectedSecond A'' B'' a b p.1 p.2) := by
  unfold endpointCorrectedSecond endpointWeightLeft endpointWeightRight
  fun_prop

end Vector
end
end PositiveEinsteinFour.Geometry
end


section

/-! A local minimum of the actual energy forces the second derivative to
be nonnegative.  The finite-piece version cancels the chart boundary
terms before applying this elementary one-variable fact. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology BigOperators

noncomputable section

theorem localMin_secondDeriv_nonneg (f : ℝ → ℝ) (D : ℝ)
    (hmin : IsLocalMin f 0) (hfd : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f s)
    (hD : HasDerivAt (deriv f) D 0) : 0 ≤ D := by
  by_contra hnonneg
  have hnegative : D < 0 := lt_of_not_ge hnonneg
  have hzero : deriv f 0 = 0 := hmin.deriv_eq_zero
  have hratio : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      s⁻¹ * deriv f s < 0 := by
    have h := hD.tendsto_slope_zero_right.eventually (Iio_mem_nhds hnegative)
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul, mem_Iio] using h
  have hsign : ∀ᶠ s in 𝓝[>] (0 : ℝ), deriv f s < 0 := by
    filter_upwards [hratio, eventually_mem_nhdsWithin] with s hs hpos
    have hpos' : 0 < s := hpos
    have hinv : 0 < s⁻¹ := inv_pos.mpr hpos'
    nlinarith
  have hsign' : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ Ioi 0 → deriv f s < 0 :=
    eventually_nhdsWithin_iff.mp hsign
  have hvalue : ∀ᶠ s in 𝓝 (0 : ℝ), f 0 ≤ f s := hmin
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hfd.and (hvalue.and hsign'))
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hmem (s : ℝ) (hs : s ∈ Icc 0 (δ / 2)) : s ∈ Metric.ball (0 : ℝ) δ := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    linarith [hs.2]
  have hc : ContinuousOn f (Icc 0 (δ / 2)) := fun s hs =>
    ((hball (hmem s hs)).1).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ f (Ioo 0 (δ / 2)) := fun s hs =>
    ((hball (hmem s ⟨hs.1.le, hs.2.le⟩)).1).differentiableWithinAt
  obtain ⟨s, hs, heq⟩ := exists_deriv_eq_slope f hhalf hc hd
  have hsneg : deriv f s < 0 :=
    (hball (hmem s ⟨hs.1.le, hs.2.le⟩)).2.2 hs.1
  have hendpoint : f 0 ≤ f (δ / 2) :=
    (hball (hmem (δ / 2) ⟨hhalf.le, le_rfl⟩)).2.1
  have hquot : 0 ≤ (f (δ / 2) - f 0) / (δ / 2 - 0) :=
    div_nonneg (sub_nonneg.mpr hendpoint) (by linarith)
  rw [heq] at hsneg
  exact (not_lt_of_ge hquot) hsneg

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

theorem sum_pair_flip (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
  have h := (Equiv.prodComm (Fin 4 × Fin 4) (Fin 4 × Fin 4)).sum_comp
    (fun p => f p.1.1 p.1.2 p.2.1 p.2.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h.symm

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

/-! A finite subdivision of a compact curve segment whose individual
closed pieces lie in single coordinate charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

def affinePartitionTime (a b : ℝ) (n i : ℕ) : ℝ := a + (b - a) * (i : ℝ) / (n : ℝ)

theorem affinePartitionTime_zero (a b : ℝ) (n : ℕ) : affinePartitionTime a b n 0 = a := by
  simp [affinePartitionTime]

theorem affinePartitionTime_last (a b : ℝ) (n : ℕ) (hn : 0 < n) :
    affinePartitionTime a b n n = b := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [affinePartitionTime, hnr]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joining two chart partitions at the corner of a piecewise C1 normal
field, and reconstructing the two index integrals from their finite sums. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

def joinedPartitionTime (a c b : ℝ) (n m i : ℕ) : ℝ :=
  if i ≤ n then affinePartitionTime a c n i else affinePartitionTime c b m (i - n)

theorem affinePartitionTime_step_lt (a b : ℝ) (n i : ℕ) (hab : a < b) (hn : 0 < n) :
    affinePartitionTime a b n i < affinePartitionTime a b n (i + 1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : affinePartitionTime a b n (i + 1) - affinePartitionTime a b n i =
      (b - a) / (n : ℝ) := by
    simp only [affinePartitionTime, Nat.cast_add, Nat.cast_one]
    ring
  have hp : 0 < (b - a) / (n : ℝ) := div_pos (sub_pos.mpr hab) hnR
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem sum_intervalIntegral_partition (f : ℝ → ℝ) (hf : Continuous f) (T : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫ r in T i..T (i + 1), f r) = ∫ r in T 0..T n, f r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The trace-three Jacobi equation has no preconjugate interval longer
than π, by finite Dirichlet positivity and its first sine mode. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped _root_.Topology

noncomputable section

theorem firstEigenvalue_eventually_neg {t : ℝ} (ht : Real.pi < t) :
    ∀ᶠ N : ℕ in atTop, firstEigenvalue t N < 0 := by
  have hlim : Real.pi ^ 2 - t ^ 2 < 0 := by nlinarith [Real.pi_pos]
  filter_upwards [(scaledFirstEigenvalue_tendsto t).eventually
    (eventually_lt_nhds hlim)] with N hN
  have hsq : 0 < ((N : ℝ) + 1) ^ 2 := by positivity
  change ((N : ℝ) + 1) ^ 2 * firstEigenvalue t N < 0 at hN
  by_contra hnot
  exact (not_lt_of_ge (mul_nonneg hsq.le (le_of_not_gt hnot))) hN

end
end PositiveEinsteinFour.Jacobi

end


section

/-! Rational Brezis--Kato tests with bounded derivatives.  Their exact
algebra relates the tested Dirichlet form to the square test, uniformly as
the truncation parameter tends to zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

def scalarKatoSquare (lam s : ℝ) : ℝ := s ^ 2 / Real.sqrt (1 + lam * s ^ 2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth Poincaré estimate passes to the actual first-jet completion.
It makes the Dirichlet form coercive on the closed mean-zero subspace and
therefore supplies a unique mean-zero weak Poisson solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

def fourGradientDirichlet {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (G : Fin 4 → E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i : Fin 4, (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).bilinearComp (G i) (G i)

theorem fourGradientDirichlet_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (G : Fin 4 → E →L[ℝ] F) (u v : E) :
    fourGradientDirichlet G u v = ∑ i : Fin 4, inner ℝ (G i u) (G i v) := by
  simp only [fourGradientDirichlet, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]

section AbstractSolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def fourGradientSolution (G : Fin 4 → E →L[ℝ] F) (V : E →L[ℝ] F)
    (h : IsCoercive (fourGradientDirichlet G)) : F →L[ℝ] E :=
  h.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp V.adjoint

theorem fourGradientSolution_weak (G : Fin 4 → E →L[ℝ] F) (V : E →L[ℝ] F)
    (h : IsCoercive (fourGradientDirichlet G)) (f : F) (v : E) :
    (∑ i : Fin 4, inner ℝ (G i (fourGradientSolution G V h f)) (G i v)) =
      inner ℝ f (V v) := by
  rw [← fourGradientDirichlet_apply, ← h.continuousLinearEquivOfBilin_apply]
  change inner ℝ (h.continuousLinearEquivOfBilin
    (h.continuousLinearEquivOfBilin.symm (V.adjoint f))) v = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact V.adjoint_inner_left v f

end AbstractSolution

end
end PositiveEinsteinFour.Geometry
end


section

/-! A zero-ended, piecewise smooth negative-index variation after a conjugate
point.  The action is written as the sum on the two smooth pieces. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

def indexEndpointBump (c b : ℝ) (v : Fin 3 → ℝ) (s : ℝ) : Fin 3 → ℝ :=
  (s * (b - s) / (c * (b - c))) • v

def indexEndpointBumpDerivative (c b : ℝ) (v : Fin 3 → ℝ) (s : ℝ) : Fin 3 → ℝ :=
  ((b - 2 * s) / (c * (b - c))) • v

theorem indexEndpointBump_hasDerivAt (c b : ℝ) (v : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (indexEndpointBump c b v) (indexEndpointBumpDerivative c b v s) s := by
  have hd : HasDerivAt (fun r : ℝ => r * (b - r) / (c * (b - c)))
      ((b - 2 * s) / (c * (b - c))) s := by
    refine ((((hasDerivAt_id s).mul ((hasDerivAt_const s b).sub
      (hasDerivAt_id s))).div_const (c * (b - c))).congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv ?_
    · beta_reduce
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
    · simp only [Pi.sub_apply, id_eq]
      ring
  exact hd.smul_const v

theorem indexEndpointBump_continuous (c b : ℝ) (v : Fin 3 → ℝ) :
    Continuous (indexEndpointBump c b v) :=
  continuous_iff_continuousAt.mpr fun s => (indexEndpointBump_hasDerivAt c b v s).continuousAt

theorem indexEndpointBumpDerivative_continuous (c b : ℝ) (v : Fin 3 → ℝ) :
    Continuous (indexEndpointBumpDerivative c b v) := by
  unfold indexEndpointBumpDerivative
  fun_prop

end
end PositiveEinsteinFour.Jacobi

end


section

/-! The index density in an actual metric chart equals the normal Euclidean
Jacobi index density when evaluated in a parallel orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem normal_lift_dotProduct (u v : Fin 3 → ℝ) :
    (Fin.cons (0 : ℝ) u : Fin 4 → ℝ) ⬝ᵥ Fin.cons 0 v = u ⬝ᵥ v := by
  rw [dotProduct, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add, dotProduct]

theorem hasDerivAt_normal_lift (a : ℝ → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (t : ℝ) (ha : HasDerivAt a b t) :
    HasDerivAt (fun s => (Fin.cons (0 : ℝ) (a s) : Fin 4 → ℝ)) (Fin.cons 0 b) t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_pi.mp ha j

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal fields along the actual parallel-frame flow.  Their ordinary
coordinate derivatives and their index densities are derived from the
constructed horizontal ODE, rather than supplied as extra field identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem continuousOn_normal_lift (a : ℝ → Fin 3 → ℝ) (S : Set ℝ)
    (ha : ContinuousOn a S) :
    ContinuousOn (fun s => (Fin.cons (0 : ℝ) (a s) : Fin 4 → ℝ)) S := by
  apply continuousOn_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuousOn_const
  · exact continuousOn_pi.mp ha j

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual kinetic energy bounds for C1 curve segments.  The elementary
square inequality suffices at a unit-speed minimizing reference curve. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Pointwise completion of the square, integrated on a compact interval. -/
theorem integral_speed_le_energy_add (s : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs : ContinuousOn s (Icc a b)) :
    (∫ t in a..b, s t) ≤ (∫ t in a..b, (1 / 2 : ℝ) * (s t) ^ 2) + (b - a) / 2 := by
  have hsi : IntervalIntegrable s volume a b := hs.intervalIntegrable_of_Icc hab
  have hei : IntervalIntegrable (fun t => (1 / 2 : ℝ) * (s t) ^ 2) volume a b :=
    (continuousOn_const.mul (hs.pow 2)).intervalIntegrable_of_Icc hab
  have hbound := intervalIntegral.integral_mono_on hab hsi
    (hei.add intervalIntegrable_const) (fun t _ =>
      show s t ≤ (1 / 2 : ℝ) * (s t) ^ 2 + (1 / 2 : ℝ) by nlinarith [sq_nonneg (s t - 1)])
  rw [intervalIntegral.integral_add hei intervalIntegrable_const,
    intervalIntegral.integral_const] at hbound
  simpa only [smul_eq_mul, mul_one_div] using hbound

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Weighted exponential-area domination.  The weight is retained through
actual polar coordinates, for use with scalar oscillations and energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem radial_weight_cancel (a r : ℝ) (hr : 0 < r) (w : ℝ≥0∞) :
    ENNReal.ofReal (r ^ 3) * (ENNReal.ofReal |a / r ^ 3| * w) =
      ENNReal.ofReal |a| * w := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_pos hr 3).le]
  congr 1
  rw [abs_div, abs_of_pos (pow_pos hr 3)]
  field_simp

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelHelmholtz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized constant-coefficient Helmholtz operator gains two Sobolev
orders.  This is an identity of actual tempered-distribution operators,
deduced from the Fourier multiplier definition of the Bessel potential. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem scalar_fourierMultiplier_add_p1 {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (g + h) u =
      fourierMultiplierCLM ℂ g u + fourierMultiplierCLM ℂ h u := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_add hg hh,
    add_apply, fourierInv_add]

theorem scalar_bessel_two_add (u : 𝓢'(E, ℂ)) :
    besselPotential E ℂ 2 u =
      u + fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (‖x‖ ^ 2)) u := by
  rw [besselPotential]
  norm_num only [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  have hsymbol : (fun x : E => Complex.ofReal (1 + ‖x‖ ^ 2)) =
      (fun _ : E => (1 : ℂ)) + (fun x : E => Complex.ofReal (‖x‖ ^ 2)) := by
    ext x
    simp only [Pi.add_apply, Complex.ofReal_add, Complex.ofReal_one]
  rw [hsymbol, scalar_fourierMultiplier_add_p1 (by fun_prop) (by fun_prop),
    fourierMultiplierCLM_const]
  simp only [ContinuousLinearMap.id_apply, one_smul]

/-- The normalization follows the Fourier convention used by Mathlib:
`J² = 1 - (2π)⁻² Δ`. -/
def normalizedScalarHelmholtz (u : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ) :=
  u - ((2 * Real.pi) ^ 2)⁻¹ • Δ u

theorem normalizedScalarHelmholtz_eq_bessel (u : 𝓢'(E, ℂ)) :
    normalizedScalarHelmholtz u = besselPotential E ℂ 2 u := by
  have hπ : (2 * Real.pi) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hcoef : ((2 * Real.pi) ^ 2)⁻¹ * (-(2 * Real.pi) ^ 2) = -(1 : ℝ) := by
    rw [mul_neg, inv_mul_cancel₀ hπ]
  rw [normalizedScalarHelmholtz, laplacian_eq_fourierMultiplierCLM,
    smul_smul, hcoef, neg_one_smul, sub_neg_eq_add]
  exact (scalar_bessel_two_add u).symm

/-- No regularity is assumed for `u`: regularity of its normalized Helmholtz
image is equivalent to two additional Sobolev orders of `u`. -/
theorem normalizedScalarHelmholtz_memSobolev_iff {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : 𝓢'(E, ℂ)) :
    MemSobolev s p (normalizedScalarHelmholtz u) ↔ MemSobolev (s + 2) p u := by
  rw [normalizedScalarHelmholtz_eq_bessel, memSobolev_besselPotential_iff, add_comm (2 : ℝ)]

theorem normalizedScalarHelmholtz_gain_two {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {u f : 𝓢'(E, ℂ)} (heq : normalizedScalarHelmholtz u = f)
    (hf : MemSobolev s p f) : MemSobolev (s + 2) p u :=
  (normalizedScalarHelmholtz_memSobolev_iff u).mp (heq.symm ▸ hf)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Sobolev regularity in four dimensions is characterized by the
four actual distributional coordinate derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

def scalarBesselReciprocal (x : V) : ℂ :=
  Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))

def scalarBesselCoordinate (i : Fin 4) (x : V) : ℂ :=
  Complex.ofReal (x i * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))

theorem scalarBesselReciprocal_temperate :
    scalarBesselReciprocal.HasTemperateGrowth := by
  unfold scalarBesselReciprocal
  fun_prop

theorem scalarBesselCoordinate_temperate (i : Fin 4) :
    (scalarBesselCoordinate i).HasTemperateGrowth := by
  unfold scalarBesselCoordinate
  simp_rw [← EuclideanSpace.inner_basisFun_real]
  fun_prop

theorem scalarBesselReciprocal_bound (x : V) :
    ‖scalarBesselReciprocal x‖ ≤ 1 := by
  rw [scalarBesselReciprocal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (show 0 < 1 + ‖x‖ ^ 2 by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖]) (by norm_num)

theorem scalarBesselCoordinate_bound (i : Fin 4) (x : V) :
    ‖scalarBesselCoordinate i x‖ ≤ 1 := by
  have hρ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity), sq_abs, inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]
        simp
      _ = _ := by simp
  have hxi : |x i| ≤ ‖x‖ := by
    simpa only [EuclideanSpace.inner_basisFun_real,
      (EuclideanSpace.basisFun (Fin 4) ℝ).norm_eq_one, mul_one] using
      abs_real_inner_le_norm x (EuclideanSpace.basisFun (Fin 4) ℝ i)
  have hxi2 : |x i| ^ 2 ≤ 1 + ‖x‖ ^ 2 := by
    nlinarith [sq_le_sq₀ (abs_nonneg (x i)) (norm_nonneg x) |>.mpr hxi]
  apply le_of_sq_le_sq _ zero_le_one
  simp only [scalarBesselCoordinate, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, mul_pow, hρ, one_pow]
  calc
    |x i| ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ ≤
        (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2)⁻¹ := by
      gcongr
    _ = 1 := mul_inv_cancel₀ (by positivity)

theorem scalar_fourierMultiplier_add_p0 {g h : V → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(V, ℂ)) :
    fourierMultiplierCLM ℂ (fun x => g x + h x) u =
      fourierMultiplierCLM ℂ g u + fourierMultiplierCLM ℂ h u := by
  simp only [fourierMultiplierCLM_apply, show (fun x => g x + h x) = g + h from rfl,
    smulLeftCLM_add hg hh, add_apply, fourierInv_add]

theorem scalar_fourierMultiplier_sum (g : Fin 4 → V → ℂ)
    (hg : ∀ i, (g i).HasTemperateGrowth) (u : 𝓢'(V, ℂ)) :
    fourierMultiplierCLM ℂ (fun x => ∑ i, g i x) u =
      ∑ i, fourierMultiplierCLM ℂ (g i) u := by
  have h := congrArg (fun A : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) => A u)
    (fourierMultiplierCLM_sum ℂ (s := Finset.univ) (fun i _ => hg i))
  simpa only [sum_apply] using h

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelBesselEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative L2 realization of the normalized Helmholtz inverse and its
first two coordinate derivatives. The constants retain Mathlib's `2π`
Fourier normalization. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "Linf" => Lp ℂ ∞ (volume : Measure V)

theorem scalar_norm_fourierInv (f : L2) : ‖𝓕⁻ f‖ = ‖f‖ := by
  rw [← Lp.norm_fourier_eq (𝓕⁻ f), fourier_fourierInv_eq]

/-- A bounded Fourier symbol acts continuously on the actual L2 space. -/
def scalarL2FourierMultiplier (a : Linf) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun f => 𝓕⁻ (a • 𝓕 f : L2)
      map_add' := by
        intro f g
        rw [FourierTransform.fourier_add, Lp.add_smul, FourierTransform.fourierInv_add]
      map_smul' := by
        intro c f
        rw [FourierTransform.fourier_smul, ← Lp.smul_comm, FourierTransform.fourierInv_smul]
        rfl }
    ‖a‖ (fun f => by
      change ‖𝓕⁻ (a • 𝓕 f : L2)‖ ≤ _
      rw [scalar_norm_fourierInv]
      exact (Lp.norm_smul_le a (𝓕 f)).trans_eq (by rw [Lp.norm_fourier_eq]))

theorem scalarL2FourierMultiplier_norm (a : Linf) (f : L2) :
    ‖scalarL2FourierMultiplier a f‖ ≤ ‖a‖ * ‖f‖ := by
  change ‖𝓕⁻ (a • 𝓕 f : L2)‖ ≤ _
  rw [scalar_norm_fourierInv]
  exact (Lp.norm_smul_le a (𝓕 f)).trans_eq (by rw [Lp.norm_fourier_eq])

theorem scalarL2FourierMultiplier_distribution (a : V → ℂ)
    (ha : a.HasTemperateGrowth) (haLp : MemLp a ∞ (volume : Measure V)) (f : L2) :
    (scalarL2FourierMultiplier (haLp.toLp a) f : 𝓢'(V, ℂ)) =
      fourierMultiplierCLM ℂ a (f : 𝓢'(V, ℂ)) := by
  change ((𝓕⁻ (haLp.toLp a • 𝓕 f : L2) : L2) : 𝓢'(V, ℂ)) = _
  rw [← Lp.fourierInv_toTemperedDistribution_eq,
    Lp.toTemperedDistribution_smul_eq ha haLp,
    ← Lp.fourier_toTemperedDistribution_eq, fourierMultiplierCLM_apply]

def besselInverseSymbol (x : V) : ℂ :=
  Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ))

def besselFirstSymbol (i : Fin 4) (x : V) : ℂ :=
  Complex.ofReal (x i * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ))

def besselSecondSymbol (i j : Fin 4) (x : V) : ℂ :=
  Complex.ofReal (x i * x j * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ))

theorem besselInverseSymbol_temperate : besselInverseSymbol.HasTemperateGrowth := by
  unfold besselInverseSymbol
  fun_prop

theorem besselFirstSymbol_temperate (i : Fin 4) :
    (besselFirstSymbol i).HasTemperateGrowth := by
  unfold besselFirstSymbol
  simp_rw [← EuclideanSpace.inner_basisFun_real]
  fun_prop

theorem besselSecondSymbol_temperate (i j : Fin 4) :
    (besselSecondSymbol i j).HasTemperateGrowth := by
  unfold besselSecondSymbol
  simp_rw [← EuclideanSpace.inner_basisFun_real]
  fun_prop

theorem scalar_coordinate_abs_le (i : Fin 4) (x : V) : |x i| ≤ ‖x‖ := by
  simpa only [EuclideanSpace.inner_basisFun_real,
    (EuclideanSpace.basisFun (Fin 4) ℝ).norm_eq_one, mul_one] using
    abs_real_inner_le_norm x (EuclideanSpace.basisFun (Fin 4) ℝ i)

theorem besselInverseSymbol_bound (x : V) : ‖besselInverseSymbol x‖ ≤ 1 := by
  simp only [besselInverseSymbol, Real.rpow_neg_one, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_pos (show 0 < 1 + ‖x‖ ^ 2 by positivity)]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖x‖])

theorem besselFirstSymbol_bound (i : Fin 4) (x : V) :
    ‖besselFirstSymbol i x‖ ≤ 1 := by
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  simp only [besselFirstSymbol, Real.rpow_neg_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_inv, abs_of_pos hx]
  apply (mul_inv_le_iff₀ hx).mpr
  nlinarith [scalar_coordinate_abs_le i x, sq_nonneg (‖x‖ - 1)]

theorem besselSecondSymbol_bound (i j : Fin 4) (x : V) :
    ‖besselSecondSymbol i j x‖ ≤ 1 := by
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hij : |x i| * |x j| ≤ ‖x‖ ^ 2 := by
    calc
      |x i| * |x j| ≤ ‖x‖ * ‖x‖ :=
        mul_le_mul (scalar_coordinate_abs_le i x) (scalar_coordinate_abs_le j x)
          (abs_nonneg _) (norm_nonneg _)
      _ = _ := (pow_two _).symm
  simp only [besselSecondSymbol, Real.rpow_neg_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_inv, abs_of_pos hx]
  apply (mul_inv_le_iff₀ hx).mpr
  linarith

theorem scalar_symbol_memLp {a : V → ℂ} (ha : a.HasTemperateGrowth)
    (hb : ∀ x, ‖a x‖ ≤ 1) : MemLp a ∞ (volume : Measure V) :=
  memLp_top_of_bound ha.1.continuous.aestronglyMeasurable 1 (.of_forall hb)

theorem scalar_symbol_Linf_norm {a : V → ℂ} (ha : MemLp a ∞ (volume : Measure V))
    (hb : ∀ x, ‖a x‖ ≤ 1) : ‖ha.toLp a‖ ≤ 1 := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (eLpNormEssSup_le_of_ae_bound (.of_forall hb))

/-- The actual L2 inverse of `1 - (2π)⁻² Δ`. -/
def scalarBesselInverseL2 : L2 →L[ℂ] L2 :=
  scalarL2FourierMultiplier
    ((scalar_symbol_memLp besselInverseSymbol_temperate besselInverseSymbol_bound).toLp _)

/-- First distributional derivative of the normalized inverse, realized in L2. -/
def scalarBesselFirstL2 (i : Fin 4) : L2 →L[ℂ] L2 :=
  (2 * Real.pi * Complex.I) • scalarL2FourierMultiplier
    ((scalar_symbol_memLp (besselFirstSymbol_temperate i) (besselFirstSymbol_bound i)).toLp _)

/-- Second distributional derivative of the normalized inverse, realized in L2. -/
def scalarBesselSecondL2 (i j : Fin 4) : L2 →L[ℂ] L2 :=
  (2 * Real.pi * Complex.I) ^ 2 • scalarL2FourierMultiplier
    ((scalar_symbol_memLp (besselSecondSymbol_temperate i j)
      (besselSecondSymbol_bound i j)).toLp _)

theorem scalarBesselInverseL2_norm (f : L2) : ‖scalarBesselInverseL2 f‖ ≤ ‖f‖ := by
  exact (scalarL2FourierMultiplier_norm _ f).trans
    (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (scalar_symbol_Linf_norm _ besselInverseSymbol_bound) (norm_nonneg f)))

theorem scalar_fourier_constant_norm :
    ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  simp [abs_of_pos Real.pi_pos]

theorem scalar_L2_multiplier_contraction {a : V → ℂ}
    (ha : MemLp a ∞ (volume : Measure V)) (hb : ∀ x, ‖a x‖ ≤ 1) (f : L2) :
    ‖scalarL2FourierMultiplier (ha.toLp a) f‖ ≤ ‖f‖ := by
  exact (scalarL2FourierMultiplier_norm _ f).trans (by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (scalar_symbol_Linf_norm ha hb) (norm_nonneg f)))

theorem scalarBesselFirstL2_norm (i : Fin 4) (f : L2) :
    ‖scalarBesselFirstL2 i f‖ ≤ (2 * Real.pi) * ‖f‖ := by
  rw [scalarBesselFirstL2, _root_.smul_apply, norm_smul,
    scalar_fourier_constant_norm]
  exact mul_le_mul_of_nonneg_left
    (scalar_L2_multiplier_contraction _ (besselFirstSymbol_bound i) f) (by positivity)

theorem scalarBesselSecondL2_norm (i j : Fin 4) (f : L2) :
    ‖scalarBesselSecondL2 i j f‖ ≤ (2 * Real.pi) ^ 2 * ‖f‖ := by
  rw [scalarBesselSecondL2, _root_.smul_apply, norm_smul,
    norm_pow, scalar_fourier_constant_norm]
  exact mul_le_mul_of_nonneg_left
    (scalar_L2_multiplier_contraction _ (besselSecondSymbol_bound i j) f) (by positivity)

theorem scalarBesselInverseL2_distribution (f : L2) :
    (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) = besselPotential V ℂ (-2) f := by
  rw [scalarBesselInverseL2, scalarL2FourierMultiplier_distribution]
  unfold besselPotential besselInverseSymbol
  norm_num only [show (-2 : ℝ) / 2 = -1 by norm_num]
  exact besselInverseSymbol_temperate

theorem scalarBesselInverseL2_symbol (f : L2) :
    (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) =
      fourierMultiplierCLM ℂ besselInverseSymbol (f : 𝓢'(V, ℂ)) := by
  exact scalarL2FourierMultiplier_distribution _ besselInverseSymbol_temperate _ f

theorem scalar_L2_smul_distribution (c : ℂ) (f : L2) :
    ((c • f : L2) : 𝓢'(V, ℂ)) = c • (f : 𝓢'(V, ℂ)) :=
  (Lp.toTemperedDistributionCLM ℂ volume 2).map_smul c f

theorem scalarBesselFirstL2_symbol (i : Fin 4) (f : L2) :
    (scalarBesselFirstL2 i f : 𝓢'(V, ℂ)) =
      (2 * Real.pi * Complex.I) •
        fourierMultiplierCLM ℂ (besselFirstSymbol i) (f : 𝓢'(V, ℂ)) := by
  rw [scalarBesselFirstL2, _root_.smul_apply, scalar_L2_smul_distribution,
    scalarL2FourierMultiplier_distribution _ (besselFirstSymbol_temperate i)]

theorem scalarBesselSecondL2_symbol (i j : Fin 4) (f : L2) :
    (scalarBesselSecondL2 i j f : 𝓢'(V, ℂ)) =
      (2 * Real.pi * Complex.I) ^ 2 •
        fourierMultiplierCLM ℂ (besselSecondSymbol i j) (f : 𝓢'(V, ℂ)) := by
  rw [scalarBesselSecondL2, _root_.smul_apply, scalar_L2_smul_distribution,
    scalarL2FourierMultiplier_distribution _ (besselSecondSymbol_temperate i j)]

/-- The L2 construction solves the actual normalized distributional equation. -/
theorem scalarBesselInverseL2_helmholtz (f : L2) :
    normalizedScalarHelmholtz (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) = (f : 𝓢'(V, ℂ)) := by
  rw [scalarBesselInverseL2_distribution, normalizedScalarHelmholtz_eq_bessel,
    besselPotential_besselPotential_apply]
  norm_num

/-- The constructed inverse has two Sobolev derivatives. -/
theorem scalarBesselInverseL2_memSobolev (f : L2) :
    MemSobolev 2 2 (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) := by
  have hf : MemSobolev 0 2 (f : 𝓢'(V, ℂ)) :=
    memSobolev_zero_iff.mpr ⟨f, rfl⟩
  simpa only [zero_add] using
    normalizedScalarHelmholtz_gain_two (scalarBesselInverseL2_helmholtz f) hf

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compactly supported coefficients preserve every nonnegative
integer Sobolev order.  The proof uses the actual distributional product
rule and the coordinate-derivative characterization. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem scalar_schwartz_coordinate_product (a φ : 𝓢(V, ℂ)) (i : Fin 4) :
    ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (SchwartzMap.smulLeftCLM ℂ a φ) =
      SchwartzMap.smulLeftCLM ℂ (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)) φ +
        SchwartzMap.smulLeftCLM ℂ a (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply a.hasTemperateGrowth, smul_eq_mul]
  rw [fderiv_fun_mul a.differentiableAt φ.differentiableAt]
  simp only [add_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)).hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  ring

theorem scalar_memSobolev_zero_multiplier (a : 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM ℂ a u) := by
  obtain ⟨v, hv⟩ := memSobolev_zero_iff.mp hu
  have ha : MemLp (a : V → ℂ) ∞ (volume : Measure V) := a.memLp ∞ volume
  refine memSobolev_zero_iff.mpr ⟨ha.toLp • v, ?_⟩
  rw [hv]
  exact (Lp.toTemperedDistribution_smul_eq a.hasTemperateGrowth ha v).symm

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localization of the distributional Laplacian, and the loss of
only one Sobolev order in its smooth-cutoff commutator. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem scalar_schwartz_sum_multiplier (a : Fin 4 → 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) :
    smulLeftCLM ℂ (∑ i, a i : 𝓢(V, ℂ)) u = ∑ i, smulLeftCLM ℂ (a i) u := by
  have hf : ((∑ i, a i : 𝓢(V, ℂ)) : V → ℂ) = fun x => ∑ i, a i x := by
    funext x
    simp only [sum_apply]
  rw [hf]
  have h := congrArg (fun A : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) => A u)
    (smulLeftCLM_sum (F := ℂ) (s := Finset.univ) (fun i _ => (a i).hasTemperateGrowth))
  simpa only [sum_apply] using h

/-- The part created by commuting a smooth cutoff with the Laplacian. -/
def scalarLaplacianCommutator (a : 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) : 𝓢'(V, ℂ) :=
  Δ (smulLeftCLM ℂ a u) - smulLeftCLM ℂ a (Δ u)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative small-coefficient inverse on L2, with its actual
second-order distributional equation and H2 regularity. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "Linf" => Lp ℂ ∞ (volume : Measure V)

/-- Physical multiplication by an essentially bounded coefficient. -/
def scalarL2Multiply (a : Linf) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun f => a • f
      map_add' := fun f g => Lp.add_smul a f g
      map_smul' := fun c f => by
        rw [← Lp.smul_comm]
        rfl }
    ‖a‖ (fun f => Lp.norm_smul_le a f)

theorem scalarL2Multiply_norm (a : Linf) (f : L2) :
    ‖scalarL2Multiply a f‖ ≤ ‖a‖ * ‖f‖ := Lp.norm_smul_le a f

theorem scalarL2Multiply_distribution (a : V → ℂ) (ha : a.HasTemperateGrowth)
    (haLp : MemLp a ∞ (volume : Measure V)) (f : L2) :
    (scalarL2Multiply (haLp.toLp a) f : 𝓢'(V, ℂ)) =
      smulLeftCLM ℂ a (f : 𝓢'(V, ℂ)) :=
  Lp.toTemperedDistribution_smul_eq ha haLp f

/-- The lower-order perturbation after composing on the right with Bessel(-2). -/
def scalarL2Perturbation (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf) : L2 →L[ℂ] L2 :=
  (∑ i : Fin 4, ∑ j : Fin 4,
    (scalarL2Multiply (a i j)).comp (scalarBesselSecondL2 i j)) +
  ∑ i : Fin 4, (scalarL2Multiply (b i)).comp (scalarBesselFirstL2 i)

theorem scalarL2Perturbation_apply (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf)
    (f : L2) :
    scalarL2Perturbation a b f =
      (∑ i : Fin 4, ∑ j : Fin 4, scalarL2Multiply (a i j) (scalarBesselSecondL2 i j f)) +
      ∑ i : Fin 4, scalarL2Multiply (b i) (scalarBesselFirstL2 i f) := by
  simp only [scalarL2Perturbation, add_apply, sum_apply, ContinuousLinearMap.comp_apply]

/-- Sixteen second-order terms and four first-order terms, with exact Fourier factors. -/
theorem scalarL2Perturbation_bound (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf)
    (δ : ℝ) (ha : ∀ i j, ‖a i j‖ ≤ δ) (hb : ∀ i, ‖b i‖ ≤ δ) (f : L2) :
    ‖scalarL2Perturbation a b f‖ ≤
      (16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ) * ‖f‖ := by
  have hδ : 0 ≤ δ := (norm_nonneg (b 0)).trans (hb 0)
  have hsecond (i j : Fin 4) :
      ‖scalarL2Multiply (a i j) (scalarBesselSecondL2 i j f)‖ ≤
        δ * ((2 * Real.pi) ^ 2 * ‖f‖) := by
    exact (scalarL2Multiply_norm _ _).trans
      (mul_le_mul (ha i j) (scalarBesselSecondL2_norm i j f) (norm_nonneg _) hδ)
  have hfirst (i : Fin 4) :
      ‖scalarL2Multiply (b i) (scalarBesselFirstL2 i f)‖ ≤
        δ * ((2 * Real.pi) * ‖f‖) := by
    exact (scalarL2Multiply_norm _ _).trans
      (mul_le_mul (hb i) (scalarBesselFirstL2_norm i f) (norm_nonneg _) hδ)
  rw [scalarL2Perturbation_apply]
  calc
    _ ≤ (∑ i : Fin 4, ∑ j : Fin 4,
        ‖scalarL2Multiply (a i j) (scalarBesselSecondL2 i j f)‖) +
        ∑ i : Fin 4, ‖scalarL2Multiply (b i) (scalarBesselFirstL2 i f)‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      · exact norm_sum_le _ _
    _ ≤ (∑ _i : Fin 4, ∑ _j : Fin 4, δ * ((2 * Real.pi) ^ 2 * ‖f‖)) +
        ∑ _i : Fin 4, δ * ((2 * Real.pi) * ‖f‖) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hsecond i j))
      · exact Finset.sum_le_sum (fun i _ => hfirst i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem scalarL2Perturbation_opNorm (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf)
    (δ : ℝ) (ha : ∀ i j, ‖a i j‖ ≤ δ) (hb : ∀ i, ‖b i‖ ≤ δ) :
    ‖scalarL2Perturbation a b‖ ≤ 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · have hδ : 0 ≤ δ := (norm_nonneg (b 0)).trans (hb 0)
    positivity
  · exact scalarL2Perturbation_bound a b δ ha hb

/-- Neumann inversion of `Id + K` in the actual Banach space. -/
def scalarPerturbationEquiv (K : L2 →L[ℂ] L2) (hK : ‖K‖ < 1) : L2 ≃L[ℂ] L2 :=
  ContinuousLinearEquiv.unitsEquiv ℂ L2 (Units.oneSub (-K) (by simpa only [norm_neg] using hK))

theorem scalarPerturbationEquiv_apply (K : L2 →L[ℂ] L2) (hK : ‖K‖ < 1) (f : L2) :
    scalarPerturbationEquiv K hK f = f + K f := by
  change ((1 - -K : L2 →L[ℂ] L2) f) = _
  simp only [sub_neg_eq_add, add_apply, one_apply_eq_self]

/-- An L2 right-hand side has a unique transformed unknown for small coefficients. -/
theorem scalarL2Perturbation_existsUnique (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf)
    (δ : ℝ) (ha : ∀ i j, ‖a i j‖ ≤ δ) (hb : ∀ i, ‖b i‖ ≤ δ)
    (hsmall : 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ < 1) (f : L2) :
    ∃! v : L2, v + scalarL2Perturbation a b v = f := by
  let hK := (scalarL2Perturbation_opNorm a b δ ha hb).trans_lt hsmall
  let e := scalarPerturbationEquiv (scalarL2Perturbation a b) hK
  have he (v : L2) : e v = v + scalarL2Perturbation a b v :=
    scalarPerturbationEquiv_apply _ hK v
  refine ⟨e.symm f, ?_, ?_⟩
  · exact (he (e.symm f)).symm.trans (e.apply_symm_apply f)
  · intro v hv
    apply e.injective
    rw [e.apply_symm_apply, he]
    exact hv

theorem scalarCoefficient_memLp (a : V → ℂ) (ha : a.HasTemperateGrowth)
    (δ : ℝ) (hb : ∀ x, ‖a x‖ ≤ δ) : MemLp a ∞ (volume : Measure V) :=
  memLp_top_of_bound ha.1.continuous.aestronglyMeasurable δ (.of_forall hb)

theorem scalarCoefficient_Linf_bound (a : V → ℂ) (ha : MemLp a ∞ (volume : Measure V))
    (δ : ℝ) (hb : ∀ x, ‖a x‖ ≤ δ) : ‖ha.toLp a‖ ≤ δ := by
  have hδ : 0 ≤ δ := (norm_nonneg (a 0)).trans (hb 0)
  rw [Lp.norm_toLp, eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal hδ
    (eLpNormEssSup_le_of_ae_bound (.of_forall hb))

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transpose of the localized second-order scalar operator.
All coefficient and derivative operations here act on Schwartz functions;
there is no assumed integration-by-parts or regularity identity. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

/-- The normalized constant-coefficient operator on test functions. -/
def scalarSchwartzHelmholtz (φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  φ - (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) • Δ φ

theorem scalarSchwartzHelmholtz_transpose (u : 𝓢'(V, ℂ)) (φ : 𝓢(V, ℂ)) :
    normalizedScalarHelmholtz u φ = u (scalarSchwartzHelmholtz φ) := by
  simp [normalizedScalarHelmholtz, scalarSchwartzHelmholtz]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density step for distributional uniqueness. An invertible L2
extension of the transposed operator after Bessel regularization gives a
dense Schwartz range, and hence a trivial L2 distributional kernel. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

/-- The negative-two Bessel multiplier preserves the actual test space. -/
def scalarSchwartzBesselInverse (φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ
    (fun x : V => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ))) φ

theorem scalarSchwartzBesselInverse_distribution (φ : 𝓢(V, ℂ)) :
    (scalarSchwartzBesselInverse φ : 𝓢'(V, ℂ)) =
      besselPotential V ℂ (-2) (φ : 𝓢'(V, ℂ)) := by
  rw [besselPotential]
  norm_num only [show (-2 : ℝ) / 2 = -1 by norm_num]
  exact (fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) φ).symm

theorem scalarL2_distribution_injective :
    Function.Injective (fun f : L2 => (f : 𝓢'(V, ℂ))) :=
  LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
    (μ := (volume : Measure V)) (p := 2))

theorem scalarSchwartzBesselInverse_toLp (φ : 𝓢(V, ℂ)) :
    (scalarSchwartzBesselInverse φ).toLp 2 = scalarBesselInverseL2 (φ.toLp 2) := by
  apply scalarL2_distribution_injective
  change ((scalarSchwartzBesselInverse φ).toLp 2 : 𝓢'(V, ℂ)) =
    (scalarBesselInverseL2 (φ.toLp 2) : 𝓢'(V, ℂ))
  rw [Lp.toTemperedDistribution_toLp_eq, scalarSchwartzBesselInverse_distribution,
    scalarBesselInverseL2_distribution, Lp.toTemperedDistribution_toLp_eq]

/-- The bilinear, rather than Hermitian, L2 pairing used by distributions. -/
def scalarL2TestPairing (u : L2) : L2 →L[ℂ] ℂ :=
  (ContinuousLinearMap.lsmul ℂ ℂ).flip.lpPairing volume 2 2 u

theorem scalarL2TestPairing_schwartz (u : L2) (φ : 𝓢(V, ℂ)) :
    scalarL2TestPairing u (φ.toLp 2) = (u : 𝓢'(V, ℂ)) φ := by
  rw [scalarL2TestPairing, ContinuousLinearMap.lpPairing_eq_integral,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 (volume : Measure V)] with x hx
  simp only [ContinuousLinearMap.lsmul_flip_apply, ContinuousLinearMap.toSpanSingleton_apply,
    hx]

/-- Surjectivity on L2 after a Schwartz-preserving regularization implies
density of the unregularized test-function range. -/
theorem scalarSchwartz_denseRange_of_bessel_equiv
    (T : 𝓢(V, ℂ) → 𝓢(V, ℂ)) (e : L2 ≃L[ℂ] L2)
    (hT : ∀ φ : 𝓢(V, ℂ), (T (scalarSchwartzBesselInverse φ)).toLp 2 = e (φ.toLp 2)) :
    DenseRange (fun φ : 𝓢(V, ℂ) => (T φ).toLp 2) := by
  have hd : DenseRange (fun φ : 𝓢(V, ℂ) => e (φ.toLp 2)) :=
    e.surjective.denseRange.comp (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
      e.continuous
  apply hd.mono
  rintro y ⟨φ, rfl⟩
  exact ⟨scalarSchwartzBesselInverse φ, hT φ⟩

/-- Nondegeneracy of the distributional L2 pairing. -/
theorem scalarL2_eq_zero_of_pairing (u : L2)
    (hzero : ∀ v : L2, scalarL2TestPairing u v = 0) : u = 0 := by
  apply scalarL2_distribution_injective
  change (u : 𝓢'(V, ℂ)) = Lp.toTemperedDistributionCLM ℂ volume 2 0
  rw [map_zero]
  ext φ
  have hφ : scalarL2TestPairing u (φ.toLp 2 (volume : Measure V)) = 0 :=
    hzero (φ.toLp 2 (volume : Measure V))
  have hpair : scalarL2TestPairing u (φ.toLp 2 (volume : Measure V)) =
      (u : 𝓢'(V, ℂ)) φ := scalarL2TestPairing_schwartz u φ
  rw [hpair] at hφ
  exact hφ

/-- A distribution represented by L2 is zero if it annihilates a dense
L2 family of Schwartz test functions. -/
theorem scalarL2_eq_zero_of_dense_tests (u : L2) (T : 𝓢(V, ℂ) → 𝓢(V, ℂ))
    (hT : DenseRange (fun φ : 𝓢(V, ℂ) => (T φ).toLp 2))
    (hu : ∀ φ : 𝓢(V, ℂ), (u : 𝓢'(V, ℂ)) (T φ) = 0) : u = 0 := by
  apply scalarL2_eq_zero_of_pairing
  intro v
  refine hT.induction_on (p := fun w => scalarL2TestPairing u w = 0) v
    (isClosed_eq (scalarL2TestPairing u).continuous continuous_const) ?_
  intro φ
  rw [scalarL2TestPairing_schwartz]
  exact hu φ

end
end PositiveEinsteinFour.Geometry

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

/-! The actual metric coefficients put the chart Laplacian in divergence
form.  This supplies the coefficient identity for local energy estimates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_divergence_expansion (ρ : ℝ) (H D Q : Fin 4 → Fin 4 → ℝ)
    (P : Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hD : ∀ j, (∑ i, D i j) = -ρ * ∑ i, ∑ k, H i k * Γ j i k) :
    (∑ i, ∑ j, (D i j * P j + ρ * H i j * Q i j)) =
      ρ * ∑ i, ∑ j, H i j * (Q i j - ∑ k, Γ k i j * P k) := by
  have ht : (∑ j, (∑ i, ∑ k, H i k * Γ j i k) * P j) =
      ∑ i, ∑ k, H i k * (∑ j, Γ j i k * P j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have hd : (∑ i, ∑ j, D i j * P j) =
      -ρ * ∑ i, ∑ j, H i j * (∑ k, Γ k i j * P k) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hD]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ht]
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hd]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical L4 estimate for the first derivatives of an H2 distribution.
The compactly supported Gagliardo--Nirenberg estimate is extended by cutoffs;
Schwartz approximation is then taken through the actual L2 Bessel inverse. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter Set FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

def h2Bump : ContDiffBump (0 : V) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def h2Cutoff (n : ℕ) (x : V) : ℝ :=
  h2Bump (((n : ℝ) + 1)⁻¹ • x)

theorem h2Cutoff_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (h2Cutoff n) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : V => h2Bump (((n : ℝ) + 1)⁻¹ • x))
  exact h2Bump.contDiff.comp (show ContDiff ℝ (⊤ : ℕ∞)
    (fun x : V => ((n : ℝ) + 1)⁻¹ • x) by fun_prop)

theorem h2Cutoff_compact (n : ℕ) : HasCompactSupport (h2Cutoff n) :=
  h2Bump.hasCompactSupport.comp_smul (inv_ne_zero (by positivity))

def h2BumpDerivativeBound : ℝ :=
  SchwartzMap.seminorm ℝ 0 0
    (SchwartzMap.fderivCLM ℝ V ℝ (h2Bump.hasCompactSupport.toSchwartzMap h2Bump.contDiff))

theorem h2BumpDerivativeBound_nonneg : 0 ≤ h2BumpDerivativeBound := by
  exact apply_nonneg _ _

theorem h2Cutoff_derivative (n : ℕ) (x : V) :
    ‖fderiv ℝ (h2Cutoff n) x‖ ≤ h2BumpDerivativeBound := by
  have hd : DifferentiableAt ℝ h2Bump (((n : ℝ) + 1)⁻¹ • x) :=
    h2Bump.contDiff.differentiable_one |>.differentiableAt
  change ‖fderiv ℝ (fun y : V => h2Bump (((n : ℝ) + 1)⁻¹ • y)) x‖ ≤ _
  have hchain : fderiv ℝ (fun y : V => h2Bump (((n : ℝ) + 1)⁻¹ • y)) x =
      (fderiv ℝ h2Bump (((n : ℝ) + 1)⁻¹ • x)).comp
        (fderiv ℝ (fun y : V => ((n : ℝ) + 1)⁻¹ • y) x) := by
    simpa only [Function.comp_def] using fderiv_comp x hd
      ((differentiable_id.const_smul ((n : ℝ) + 1)⁻¹).differentiableAt)
  rw [hchain]
  calc
    _ ≤ ‖fderiv ℝ h2Bump (((n : ℝ) + 1)⁻¹ • x)‖ *
        ‖fderiv ℝ (fun y : V => ((n : ℝ) + 1)⁻¹ • y) x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ h2BumpDerivativeBound * 1 := by
      apply mul_le_mul
      · exact SchwartzMap.norm_le_seminorm ℝ
          (SchwartzMap.fderivCLM ℝ V ℝ
            (h2Bump.hasCompactSupport.toSchwartzMap h2Bump.contDiff)) _
      · have hi : HasFDerivAt (fun y : V => ((n : ℝ) + 1)⁻¹ • y)
            (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ V) x :=
          by
          simpa only [Pi.smul_apply, id_eq] using!
            ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul ((n : ℝ) + 1)⁻¹)
        rw [hi.fderiv, norm_smul, ContinuousLinearMap.norm_id, mul_one,
          Real.norm_eq_abs, abs_inv, abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]
        exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
      · positivity
      · exact h2BumpDerivativeBound_nonneg
    _ = _ := mul_one _

theorem h2Cutoff_tendsto (x : V) :
    Tendsto (fun n => h2Cutoff n x) atTop (𝓝 1) := by
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hx := h2Bump.continuous.continuousAt.tendsto.comp (hr.smul_const x)
  have hz : h2Bump (0 : V) = 1 := h2Bump.one_of_mem_closedBall (by simp [h2Bump])
  simpa only [h2Cutoff, Function.comp_def, zero_smul, hz] using hx

theorem h2_operator_norm (L : V →L[ℝ] ℂ) :
    ‖L‖ ≤ ∑ i : Fin 4, ‖L (EuclideanSpace.basisFun (Fin 4) ℝ i)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have hx := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x
  have hc (i : Fin 4) : |x i| ≤ ‖x‖ := by
    simpa only [EuclideanSpace.inner_basisFun_real,
      (EuclideanSpace.basisFun (Fin 4) ℝ).norm_eq_one, mul_one] using
      abs_real_inner_le_norm x (EuclideanSpace.basisFun (Fin 4) ℝ i)
  calc
    ‖L x‖ = ‖∑ i : Fin 4, (x i) • L (EuclideanSpace.basisFun (Fin 4) ℝ i)‖ := by
      congr 1
      conv_lhs => rw [← hx]
      simp
    _ ≤ ∑ i : Fin 4, ‖(x i) • L (EuclideanSpace.basisFun (Fin 4) ℝ i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 4, ‖x‖ * ‖L (EuclideanSpace.basisFun (Fin 4) ℝ i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

theorem h2_cutoff_fderiv_bound (f : 𝓢(V, ℂ)) (n : ℕ) (x : V) :
    ‖fderiv ℝ (fun y => h2Cutoff n y • f y) x‖ ≤
      h2BumpDerivativeBound * ‖f x‖ +
        ∑ i : Fin 4, ‖(∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f) x‖ := by
  rw [fderiv_fun_smul ((h2Cutoff_smooth n).of_le (by first | simp | exact_mod_cast le_top) |>.differentiable_one |>.differentiableAt)
    ((f.smooth 1).differentiable_one |>.differentiableAt)]
  rw [add_comm]
  calc
    _ ≤ ‖(fderiv ℝ (h2Cutoff n) x).smulRight (f x)‖ +
        ‖h2Cutoff n x • fderiv ℝ f x‖ := norm_add_le _ _
    _ ≤ h2BumpDerivativeBound * ‖f x‖ + 1 * ‖fderiv ℝ f x‖ := by
      simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (h2Cutoff_derivative n x) (norm_nonneg _)
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        change |h2Bump (((n : ℝ) + 1)⁻¹ • x)| ≤ 1
        rw [abs_of_nonneg h2Bump.nonneg]
        exact h2Bump.le_one
    _ ≤ _ := by
      rw [one_mul]
      apply add_le_add le_rfl
      simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
        h2_operator_norm (fderiv ℝ f x)

theorem h2_norm_sum_estimate (g : V → (V →L[ℝ] ℂ))
    (f : V → ℂ) (D : Fin 4 → V → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hg : AEStronglyMeasurable g volume) (hf : AEStronglyMeasurable f volume)
    (hD : ∀ i, AEStronglyMeasurable (D i) volume)
    (hb : ∀ x, ‖g x‖ ≤ B * ‖f x‖ + ∑ i, ‖D i x‖) :
    eLpNorm g 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume +
      ∑ i : Fin 4, eLpNorm (D i) 2 volume := by
  calc
    _ ≤ eLpNorm (fun x => B * ‖f x‖ + ∑ i : Fin 4, ‖D i x‖) 2 volume :=
      eLpNorm_mono_real hb
    _ ≤ eLpNorm (fun x => B * ‖f x‖) 2 volume +
        eLpNorm (fun x => ∑ i : Fin 4, ‖D i x‖) 2 volume :=
      eLpNorm_add_le (hf.norm.const_mul B)
        (by first | fun_prop | exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (hD i).norm))
        (by norm_num)
    _ ≤ _ := by
      apply add_le_add
      · have he : (fun x => B * ‖f x‖) = B • (fun x => ‖f x‖) := rfl
        rw [he, eLpNorm_const_smul, eLpNorm_norm _]
        simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hB, le_refl]
      · calc
          _ ≤ ∑ i : Fin 4, eLpNorm (fun x => ‖D i x‖) 2 volume := by
            have he : (fun x => ∑ i : Fin 4, ‖D i x‖) =
                ∑ i : Fin 4, (fun x => ‖D i x‖) := by
              funext x
              simp only [Finset.sum_apply]
            rw [he]
            exact eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (μ := (volume : Measure V)) (p := 2)
              (f := fun i : Fin 4 => fun x => ‖D i x‖)
              (s := Finset.univ) (by norm_num)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            exact eLpNorm_norm _

theorem h2_cutoff_L2_derivative (f : 𝓢(V, ℂ)) (n : ℕ) :
    eLpNorm (fderiv ℝ (fun x => h2Cutoff n x • f x)) 2 volume ≤
      ENNReal.ofReal h2BumpDerivativeBound * eLpNorm f 2 volume +
        ∑ i : Fin 4, eLpNorm
          ((∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f : 𝓢(V, ℂ)) : V → ℂ) 2 volume := by
  have hg : ContDiff ℝ 1 (fun x => h2Cutoff n x • f x) :=
    ((h2Cutoff_smooth n).of_le (by first | simp | exact_mod_cast le_top)).smul (f.smooth 1)
  exact h2_norm_sum_estimate _ f _ _ h2BumpDerivativeBound_nonneg
    (hg.continuous_fderiv one_ne_zero).aestronglyMeasurable
    f.continuous.aestronglyMeasurable
    (fun i => (SchwartzMap.continuous _).aestronglyMeasurable)
    (h2_cutoff_fderiv_bound f n)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HilbertImageTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two density facts used to transport the scalar and two-form spectral
families from L2 into their actual first-order energy spaces. -/

namespace PositiveEinsteinFour.Geometry

open Set

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

theorem adjoint_denseRange_of_injective (J : E →L[ℝ] F) (hJ : Function.Injective J) :
    DenseRange J.adjoint := by
  have h := J.orthogonal_ker
  rw [LinearMap.ker_eq_bot.mpr hJ, Submodule.bot_orthogonal_eq_top] at h
  apply denseRange_iff_closure_range.mpr
  exact congrArg (fun S : Submodule ℝ E => (S : Set E)) h.symm

omit [CompleteSpace E] [CompleteSpace F] in
theorem dense_span_continuousLinearMap_image {ι : Type*} (v : ι → E)
    (hv : (Submodule.span ℝ (range v)).topologicalClosure = ⊤)
    (A : E →L[ℝ] F) (hA : DenseRange A) :
    (Submodule.span ℝ (range (fun i => A (v i)))).topologicalClosure = ⊤ := by
  let S := (Submodule.span ℝ (range (fun i => A (v i)))).topologicalClosure
  have hs : IsClosed (S : Set F) := Submodule.isClosed_topologicalClosure _
  have hsub : Submodule.span ℝ (range v) ≤ S.comap A.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfull : (⊤ : Submodule ℝ E) ≤ S.comap A.toLinearMap := by
    rw [← hv]
    exact Submodule.topologicalClosure_minimal _ hsub (hs.preimage A.continuous)
  apply top_unique
  intro y _
  apply hs.closure_subset_iff.mpr (show range A ⊆ S from ?_) (hA y)
  rintro _ ⟨x, rfl⟩
  exact hfull (by trivial)

omit [CompleteSpace E] [CompleteSpace F] in
theorem continuousLinearMap_mem_closed_of_total {ι : Type*} (v : ι → E)
    (hv : (Submodule.span ℝ (range v)).topologicalClosure = ⊤)
    (A : E →L[ℝ] F) (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    (h : ∀ i, A (v i) ∈ S) (u : E) : A u ∈ S := by
  have hs : Submodule.span ℝ (range v) ≤ S.comap A.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  have ht := Submodule.topologicalClosure_minimal _ hs (hS.preimage A.continuous)
  rw [hv] at ht
  exact ht (by trivial)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelAdjointEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative bounded extension of the actual transposed operator after
Bessel regularization. Coefficient bounds imply the dense-range condition used for
distributional uniqueness. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal LineDeriv BigOperators Laplacian

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℂ)

/-- Multiplication by a Schwartz coefficient, as a physical L2 operator. -/
def scalarSchwartzMultiplyL2 (a : S) : L2 →L[ℂ] L2 :=
  scalarL2Multiply (a.toLp ∞)

theorem scalarSchwartz_product_distribution (a φ : S) :
    (SchwartzMap.smulLeftCLM ℂ a φ : 𝓢'(V, ℂ)) = smulLeftCLM ℂ a (φ : 𝓢'(V, ℂ)) := by
  ext ψ
  simp only [SchwartzMap.coe_apply, smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth, smul_eq_mul]
  ring

theorem scalarL2_eq_schwartz (u : L2) (φ : S)
    (hu : (u : 𝓢'(V, ℂ)) = (φ : 𝓢'(V, ℂ))) : u = φ.toLp 2 volume := by
  apply scalarL2_distribution_injective
  change (u : 𝓢'(V, ℂ)) = (φ.toLp 2 volume : 𝓢'(V, ℂ))
  rw [Lp.toTemperedDistribution_toLp_eq]
  exact hu

theorem scalarSchwartzMultiplyL2_distribution (a φ : S) :
    (scalarSchwartzMultiplyL2 a (φ.toLp 2 volume) : 𝓢'(V, ℂ)) =
      (SchwartzMap.smulLeftCLM ℂ a φ : 𝓢'(V, ℂ)) := by
  unfold scalarSchwartzMultiplyL2
  rw [SchwartzMap.toLp]
  rw [scalarL2Multiply_distribution _ a.hasTemperateGrowth (a.memLp ∞ volume),
    Lp.toTemperedDistribution_toLp_eq, scalarSchwartz_product_distribution]

theorem scalarSchwartzMultiplyL2_toLp (a φ : S) :
    scalarSchwartzMultiplyL2 a (φ.toLp 2 volume) =
      (SchwartzMap.smulLeftCLM ℂ a φ).toLp 2 volume :=
  scalarL2_eq_schwartz _ _ (scalarSchwartzMultiplyL2_distribution a φ)

theorem scalarSchwartzHelmholtz_distribution (φ : S) :
    (scalarSchwartzHelmholtz φ : 𝓢'(V, ℂ)) = normalizedScalarHelmholtz (φ : 𝓢'(V, ℂ)) := by
  unfold scalarSchwartzHelmholtz normalizedScalarHelmholtz
  change SchwartzMap.toTemperedDistributionCLM V ℂ volume _ = _
  rw [map_sub, map_smul]
  rw [laplacian_toTemperedDistributionCLM_eq]
  simp only [Complex.coe_smul]

theorem scalarSchwartzHelmholtz_bessel_toLp (φ : S) :
    (scalarSchwartzHelmholtz (scalarSchwartzBesselInverse φ)).toLp 2 volume = φ.toLp 2 volume := by
  apply scalarL2_distribution_injective
  change ((scalarSchwartzHelmholtz (scalarSchwartzBesselInverse φ)).toLp 2 volume : 𝓢'(V, ℂ)) =
    (φ.toLp 2 volume : 𝓢'(V, ℂ))
  rw [Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq,
    scalarSchwartzHelmholtz_distribution, scalarSchwartzBesselInverse_distribution,
    normalizedScalarHelmholtz_eq_bessel, besselPotential_besselPotential_apply]
  norm_num

theorem scalarSchwartzMultiplyL2_bound (a : S) (δ : ℝ)
    (ha : ‖a.toLp ∞ (volume : Measure V)‖ ≤ δ) (f : L2) :
    ‖scalarSchwartzMultiplyL2 a f‖ ≤ δ * ‖f‖ :=
  (scalarL2Multiply_norm _ _).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg f))

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelLocalRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-coefficient regularity applies to an existing L2 distributional
solution: construct an H2 solution, then identify the two using the actual
formal-transpose uniqueness theorem. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)

theorem scalarSchwartz_Linf_bound (a : S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ x, ‖a x‖ ≤ δ) : ‖a.toLp ∞ (volume : Measure V)‖ ≤ δ := by
  rw [SchwartzMap.toLp, Lp.norm_toLp,
    eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal hδ (eLpNormEssSup_le_of_ae_bound (.of_forall ha))

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelBootstrap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer-order elliptic bootstrap from the actual distributional
commutator and the proved small-coefficient H2 regularity theorem. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem scalar_sobolev_sum_p0 (n : ℕ) (u : Fin 4 → 𝓢'(V, ℂ))
    (hu : ∀ i, MemSobolev (n : ℝ) 2 (u i)) :
    MemSobolev (n : ℝ) 2 (∑ i : Fin 4, u i) := by
  have hs (s : Finset (Fin 4)) : MemSobolev (n : ℝ) 2 (∑ i ∈ s, u i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero V ℂ (n : ℝ) 2
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact (hu i).add ih
  exact hs Finset.univ

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarAdjointCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density-weighted chart equation gives the formal adjoint of the
nondivergence operator. Its expansion has the same principal coefficients,
a differentiated drift, and an explicit smooth zeroth-order potential. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

theorem scalar_adjoint_multiplier_sum (a : Fin 4 → S) (u : T) :
    M (∑ i, a i : S) u = ∑ i, M (a i) u := by
  have he : ((∑ i, a i : S) : V → ℂ) = fun x => ∑ i, a i x := by
    funext x
    simp only [sum_apply]
  rw [he]
  have hs := congrArg (fun A : T →L[ℂ] T => A u)
    (smulLeftCLM_sum (F := ℂ) (s := Finset.univ) (fun i _ => (a i).hasTemperateGrowth))
  simpa only [sum_apply] using hs

theorem scalar_adjoint_multiplier_add (a b : S) (u : T) :
    M (a + b : S) u = M a u + M b u := by
  change M ((a : V → ℂ) + (b : V → ℂ)) u = _
  rw [smulLeftCLM_add a.hasTemperateGrowth b.hasTemperateGrowth, add_apply]

theorem scalar_adjoint_multiplier_sub (a b : S) (u : T) :
    M (a - b : S) u = M a u - M b u := by
  change M ((a : V → ℂ) - (b : V → ℂ)) u = _
  rw [smulLeftCLM_sub a.hasTemperateGrowth b.hasTemperateGrowth, sub_apply]

theorem scalar_adjoint_nine_bound (p q : Fin 4 → ℂ) (b : ℂ) (δ : ℝ)
    (hp : ∀ i, ‖p i‖ ≤ δ) (hq : ∀ i, ‖q i‖ ≤ δ) (hb : ‖b‖ ≤ δ) :
    ‖(∑ i, p i) + (∑ i, q i) - b‖ ≤ 9 * δ := by
  have hp' : ‖∑ i, p i‖ ≤ 4 * δ := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ i : Fin 4, ‖p i‖) ≤ ∑ _i : Fin 4, δ := Finset.sum_le_sum (fun i _ => hp i)
      _ = 4 * δ := by simp
  have hq' : ‖∑ i, q i‖ ≤ 4 * δ := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ i : Fin 4, ‖q i‖) ≤ ∑ _i : Fin 4, δ := Finset.sum_le_sum (fun i _ => hq i)
      _ = 4 * δ := by simp
  calc
    _ ≤ ‖∑ i, p i‖ + ‖∑ i, q i‖ + ‖b‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 4 * δ + 4 * δ + δ := add_le_add (add_le_add hp' hq') hb
    _ = 9 * δ := by ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarCompositionHessian
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

local instance instFactLeENNRealOfNat_solutions_1 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A variable-coefficient cutoff commutator loses only one derivative.
Nested cutoffs let this estimate use regularity on a larger neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

theorem scalar_multiplier_commute (a b : S) (u : T) :
    M a (M b u) = M b (M a u) := by
  rw [smulLeftCLM_smulLeftCLM_apply b.hasTemperateGrowth a.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply a.hasTemperateGrowth b.hasTemperateGrowth]
  rw [mul_comm (b : V → ℂ) (a : V → ℂ)]

theorem scalar_multiplier_real_smul (a : S) (c : ℝ) (u : T) :
    M a (c • u) = c • M a u :=
  (M a).toLinearMap.map_smul_of_tower c u

theorem scalar_cutoff_helmholtz (ψ : S) (u : T) :
    normalizedScalarHelmholtz (M ψ u) = M ψ (normalizedScalarHelmholtz u) -
      (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) • scalarLaplacianCommutator ψ u := by
  simp only [normalizedScalarHelmholtz, scalarLaplacianCommutator,
    map_sub, scalar_multiplier_real_smul]
  module

theorem scalar_sobolev_sum_p1 (n : ℕ) (f : Fin 4 → T)
    (hf : ∀ i, MemSobolev (n : ℝ) 2 (f i)) : MemSobolev (n : ℝ) 2 (∑ i, f i) := by
  have hs (s : Finset (Fin 4)) : MemSobolev (n : ℝ) 2 (∑ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero V ℂ (n : ℝ) 2
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact (hf i).add ih
  exact hs Finset.univ

/-- The outer cutoff equals one near the support of the inner cutoff. -/
def ScalarCutoffNested (ψ χ : S) : Prop :=
  ∀ x ∈ tsupport (ψ : V → ℂ), (χ : V → ℂ) =ᶠ[𝓝 x] fun _ => 1

theorem scalar_cutoff_nested_value (ψ χ : S) (h : ScalarCutoffNested ψ χ) :
    (χ : V → ℂ) * ψ = ψ := by
  funext x
  by_cases hx : ψ x = 0
  · simp only [Pi.mul_apply, hx, mul_zero]
  · have hm : x ∈ tsupport (ψ : V → ℂ) := subset_closure hx
    simp only [Pi.mul_apply, (h x hm).eq_of_nhds, one_mul]

theorem scalar_cutoff_nested_mul (ψ χ : S) (h : ScalarCutoffNested ψ χ) (u : T) :
    M ψ (M χ u) = M ψ u := by
  rw [smulLeftCLM_smulLeftCLM_apply χ.hasTemperateGrowth ψ.hasTemperateGrowth,
    scalar_cutoff_nested_value ψ χ h]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily high scalar Sobolev regularity produces a smooth function.
The representative is constructed by inverse Fourier integration, rather than
assumed as an elliptic regularity input. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BoundedContinuousFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem inverse_fourier_pairing (v : Lp ℂ 1 (volume : Measure E))
    (φ : 𝓢(E, ℂ)) :
    (𝓕⁻ (v : 𝓢'(E, ℂ))) φ =
      ∫ x : E, φ x * (𝓕⁻ (v : E → ℂ)) x := by
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := -(innerₗ E))
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    Real.continuous_fourierChar (by
      change Continuous (fun p : E × E => - inner ℝ p.1 p.2)
      fun_prop)
    (memLp_one_iff_integrable.mp (Lp.memLp v)) φ.integrable
  simpa only [SchwartzMap.fourierInv_coe, VectorFourier.fourierIntegral, Real.fourierInv_eq,
    ContinuousLinearMap.mul_apply', LinearMap.neg_apply, LinearMap.flip_apply,
    innerₗ_apply_apply, neg_neg, real_inner_comm,
    smul_eq_mul, mul_comm] using h.symm

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelSourceChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric equation has a smooth right-hand side for P - Id.
These localization steps use that remainder and only H1 of the solution. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

/-- Inserting an outer cutoff does not change the inner localization. -/
theorem scalarCutoffNested_mul (ψ χ : S) (h : ScalarCutoffNested ψ χ) (u : T) :
    M ψ (M χ u) = M ψ u := by
  have hm : (χ : V → ℂ) * ψ = ψ := by
    funext x
    by_cases hx : ψ x = 0
    · simp only [Pi.mul_apply, hx, mul_zero]
    · have hmem : x ∈ tsupport (ψ : V → ℂ) := subset_closure hx
      simp only [Pi.mul_apply, (h x hmem).eq_of_nhds, one_mul]
  rw [smulLeftCLM_smulLeftCLM_apply χ.hasTemperateGrowth ψ.hasTemperateGrowth, hm]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelLocalRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local smooth representatives of the original L2 function. The cutoff
is one on a smaller ball, so Fourier regularization returns the given
solution there, not just a solution of a related equation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

def scalarCutoffL2 (φ : S) (u : L2) : L2 :=
  scalarL2Multiply (φ.toLp ∞ volume) u

theorem scalarCutoffL2_distribution (φ : S) (u : L2) :
    (scalarCutoffL2 φ u : T) = M φ (u : T) := by
  unfold scalarCutoffL2
  rw [SchwartzMap.toLp]
  exact scalarL2Multiply_distribution _ φ.hasTemperateGrowth (φ.memLp ∞ volume) u

theorem scalarCutoffL2_ae (φ : S) (u : L2) :
    (scalarCutoffL2 φ u : V → ℂ) =ᵐ[volume] fun x => φ x * u x := by
  change (((φ.toLp ∞ volume) • u : L2) : V → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (φ.toLp ∞ volume) u,
    φ.coeFn_toLp ∞ volume] with x hx hφ
  simpa only [smul_eq_mul, Pi.mul_apply, hφ] using hx

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth zeroth-order potential does not obstruct the local bootstrap.
Only the principal and first-order perturbations need to be small. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

theorem scalarPotential_multipliers_commute (c ψ : S) (u : T) :
    M ψ (M c u) = M c (M ψ u) := by
  rw [smulLeftCLM_smulLeftCLM_apply c.hasTemperateGrowth ψ.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply ψ.hasTemperateGrowth c.hasTemperateGrowth,
    mul_comm (c : V → ℂ) (ψ : V → ℂ)]

variable (a : Fin 4 → Fin 4 → S)
  (b : Fin 4 → S)
  (δ : ℝ)
  (hδ : 0 ≤ δ)
  (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
  (hb : ∀ i x, ‖b i x‖ ≤ δ)
  (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)

include hδ ha hb hsmall

omit hδ ha hb hsmall

def scalarPotentialInnerBump : ContDiffBump (0 : V) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def scalarPotentialInnerCutoff : S :=
  (scalarPotentialInnerBump.hasCompactSupport.comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp scalarPotentialInnerBump.contDiff)

theorem scalarPotentialInnerCutoff_apply (x : V) :
    scalarPotentialInnerCutoff x = (scalarPotentialInnerBump x : ℂ) := rfl

theorem scalarPotentialInnerCutoff_tsupport :
    tsupport (scalarPotentialInnerCutoff : V → ℂ) = closedBall 0 (1 / 2) := by
  have hs : Function.support (scalarPotentialInnerCutoff : V → ℂ) =
      Function.support (scalarPotentialInnerBump : V → ℝ) := by
    ext x
    simp only [Function.mem_support, scalarPotentialInnerCutoff_apply,
      ne_eq, Complex.ofReal_eq_zero]
  rw [tsupport, hs]
  exact scalarPotentialInnerBump.tsupport_eq

theorem scalarPotentialInnerCutoff_one {x : V} (hx : x ∈ ball 0 (1 / 4)) :
    scalarPotentialInnerCutoff x = 1 := by
  rw [scalarPotentialInnerCutoff_apply]
  have h := scalarPotentialInnerBump.one_of_mem_closedBall (ball_subset_closedBall hx)
  simp only [h, Complex.ofReal_one]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarH1EllipticGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local H3 elliptic gain for an actual first-order Sobolev source. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

theorem scalar_localize_eq_of_tests (U : Set V) (u f : T)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = f φ)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U) : M ψ u = M ψ f := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ ψ φ) = f (SchwartzMap.smulLeftCLM ℂ ψ φ)
  apply htest
  · rw [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth]
    exact hc.smul_right
  · intro x hx
    exact hs ((SchwartzMap.tsupport_smulLeftCLM_subset (ψ : V → ℂ) φ hx).2)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarEigenMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorbing the actual scalar eigenvalue into a compact zeroth-order
coefficient, on the ball where the equation is tested. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

theorem scalar_multiplier_constant_on_test (θ ψ : S) (u : T) (κ : ℂ)
    (hθ : ∀ x ∈ tsupport (ψ : V → ℂ), θ x = κ) :
    (M θ u) ψ = κ * u ψ := by
  change u (SchwartzMap.smulLeftCLM ℂ θ ψ) = _
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth]
  change θ x * ψ x = κ * ψ x
  by_cases hx : x ∈ tsupport (ψ : V → ℂ)
  · rw [hθ x hx]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

theorem scalar_multiplier_add (c θ : S) (u : T) : M (c + θ) u = M c u + M θ u := by
  change smulLeftCLM ℂ ((c : V → ℂ) + (θ : V → ℂ)) u = _
  rw [smulLeftCLM_add c.hasTemperateGrowth θ.hasTemperateGrowth]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarHalfBallCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested cutoffs inside the half ball, used after the first local H2 gain. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)

def scalarHalfBumpGap (r : ℝ) (k : ℕ) : ℝ := (1 / 2 - r) * (1 / 4 : ℝ) ^ (k + 1)

theorem scalarHalfBumpGap_pos {r : ℝ} (hr : r < 1 / 2) (k : ℕ) :
    0 < scalarHalfBumpGap r k := by
  exact mul_pos (sub_pos.mpr hr) (pow_pos (by norm_num) _)

theorem scalarHalfBumpGap_lt {r : ℝ} (hr : r < 1 / 2) (k : ℕ) :
    scalarHalfBumpGap r k < 1 / 2 - r := by
  have hp : (1 / 4 : ℝ) ^ (k + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero k)
  simpa only [scalarHalfBumpGap, mul_one] using
    mul_lt_mul_of_pos_left hp (sub_pos.mpr hr)

theorem scalarHalfBumpGap_succ (r : ℝ) (k : ℕ) :
    scalarHalfBumpGap r (k + 1) = scalarHalfBumpGap r k / 4 := by
  simp only [scalarHalfBumpGap, pow_succ]
  ring

/-- A concrete real bump; the gap shrinks geometrically with the index. -/
def scalarHalfNestedRealBump (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) :
    ContDiffBump (0 : V) where
  rIn := 1 / 2 - scalarHalfBumpGap r k
  rOut := 1 / 2 - scalarHalfBumpGap r k / 2
  rIn_pos := by
    have hg := scalarHalfBumpGap_lt hr1 k
    linarith
  rIn_lt_rOut := by
    have hg := scalarHalfBumpGap_pos hr1 k
    linarith

theorem scalarHalfNestedRealBump_inner {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) :
    r < (scalarHalfNestedRealBump r hr0 hr1 k).rIn := by
  change r < 1 / 2 - scalarHalfBumpGap r k
  linarith [scalarHalfBumpGap_lt hr1 k]

theorem scalarHalfNestedRealBump_outer {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) :
    (scalarHalfNestedRealBump r hr0 hr1 k).rOut < 1 / 2 := by
  change 1 / 2 - scalarHalfBumpGap r k / 2 < 1 / 2
  linarith [scalarHalfBumpGap_pos hr1 k]

theorem scalarHalfNestedRealBump_separated {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) :
    (scalarHalfNestedRealBump r hr0 hr1 k).rOut <
      (scalarHalfNestedRealBump r hr0 hr1 (k + 1)).rIn := by
  change 1 / 2 - scalarHalfBumpGap r k / 2 < 1 / 2 - scalarHalfBumpGap r (k + 1)
  rw [scalarHalfBumpGap_succ]
  linarith [scalarHalfBumpGap_pos hr1 k]

/-- Complexification turns the actual compact real bump into a Schwartz cutoff. -/
def scalarHalfNestedBumpSchwartz (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) : S :=
  ((scalarHalfNestedRealBump r hr0 hr1 k).hasCompactSupport.comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (scalarHalfNestedRealBump r hr0 hr1 k).contDiff)

theorem scalarHalfNestedBumpSchwartz_apply (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2)
    (k : ℕ) (x : V) :
    scalarHalfNestedBumpSchwartz r hr0 hr1 k x = (scalarHalfNestedRealBump r hr0 hr1 k x : ℂ) := rfl

theorem scalarHalfNestedBumpSchwartz_tsupport (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1 / 2) (k : ℕ) :
    tsupport (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =
      closedBall 0 (scalarHalfNestedRealBump r hr0 hr1 k).rOut := by
  have hs : Function.support (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =
      Function.support (scalarHalfNestedRealBump r hr0 hr1 k : V → ℝ) := by
    ext x
    simp only [Function.mem_support, scalarHalfNestedBumpSchwartz_apply, ne_eq,
      Complex.ofReal_eq_zero]
  rw [tsupport, hs]
  exact (scalarHalfNestedRealBump r hr0 hr1 k).tsupport_eq

theorem scalarHalfNestedBumpSchwartz_one_nhds (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1 / 2) (k : ℕ) {x : V}
    (hx : x ∈ ball 0 (scalarHalfNestedRealBump r hr0 hr1 k).rIn) :
    (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [(scalarHalfNestedRealBump r hr0 hr1 k).eventuallyEq_one_of_mem_ball hx] with y hy
  simp only [scalarHalfNestedBumpSchwartz_apply, hy, Pi.one_apply, Complex.ofReal_one]

theorem scalarHalfNestedBumpSchwartz_nested (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1 / 2) (k : ℕ) :
    ScalarCutoffNested (scalarHalfNestedBumpSchwartz r hr0 hr1 k)
      (scalarHalfNestedBumpSchwartz r hr0 hr1 (k + 1)) := by
  intro x hx
  rw [scalarHalfNestedBumpSchwartz_tsupport] at hx
  apply scalarHalfNestedBumpSchwartz_one_nhds
  exact (mem_closedBall.mp hx).trans_lt (scalarHalfNestedRealBump_separated hr0 hr1 k)

/-- Every compact cutoff inside a smaller closed ball starts a concrete
infinite nested sequence supported in the open unit ball. -/
theorem exists_scalar_half_nested_cutoffs (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2)
    (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
    (hφ : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    ∃ ψ : ℕ → S, ψ 0 = φ ∧ (∀ k, ScalarCutoffNested (ψ k) (ψ (k + 1))) ∧
      ∀ k, HasCompactSupport (ψ k : V → ℂ) ∧ tsupport (ψ k : V → ℂ) ⊆ ball 0 (1 / 2) := by
  let ψ : ℕ → S := fun k => match k with
    | 0 => φ
    | j + 1 => scalarHalfNestedBumpSchwartz r hr0 hr1 j
  refine ⟨ψ, rfl, ?_, ?_⟩
  · intro k
    cases k with
    | zero =>
        intro x hx
        apply scalarHalfNestedBumpSchwartz_one_nhds
        exact (mem_closedBall.mp (hφ hx)).trans_lt (scalarHalfNestedRealBump_inner hr0 hr1 0)
    | succ k => exact scalarHalfNestedBumpSchwartz_nested r hr0 hr1 k
  · intro k
    cases k with
    | zero =>
        refine ⟨hφc, ?_⟩
        intro x hx
        exact (mem_closedBall.mp (hφ hx)).trans_lt hr1
    | succ k =>
        change HasCompactSupport (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ) ∧ _
        constructor
        · change IsCompact (tsupport (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ))
          rw [scalarHalfNestedBumpSchwartz_tsupport]
          exact isCompact_closedBall _ _
        · intro x hx
          rw [scalarHalfNestedBumpSchwartz_tsupport] at hx
          exact (mem_closedBall.mp hx).trans_lt (scalarHalfNestedRealBump_outer hr0 hr1 k)


end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelLocalTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact tests determine every inner localization of a distribution.
A source smooth only on the test domain becomes a Schwartz source after
localization, and therefore has all Sobolev orders. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

theorem scalarSchwartz_cutoff_compact (ψ φ : S)
    (hc : HasCompactSupport (ψ : V → ℂ)) :
    HasCompactSupport (SchwartzMap.smulLeftCLM ℂ ψ φ : V → ℂ) := by
  rw [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth]
  exact hc.smul_right

theorem scalarSchwartz_cutoff_support (ψ φ : S) {U : Set V}
    (hs : tsupport (ψ : V → ℂ) ⊆ U) :
    tsupport (SchwartzMap.smulLeftCLM ℂ ψ φ : V → ℂ) ⊆ U := by
  intro x hx
  exact hs ((SchwartzMap.tsupport_smulLeftCLM_subset (ψ : V → ℂ) φ hx).2)

theorem scalarLocalSource_smooth (ψ : S) (f : V → ℂ)
    (hf : ∀ x ∈ tsupport (ψ : V → ℂ), ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (ψ : V → ℂ)
  · exact (ψ.smooth ⊤).contDiffAt.mul (hf x hx)
  · have he : (fun y => ψ y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- A smooth source restricted by a compact Schwartz cutoff is Schwartz,
even if it has no regularity or growth control outside the cutoff. -/
def scalarLocalSourceSchwartz (ψ : S) (f : V → ℂ)
    (hc : HasCompactSupport (ψ : V → ℂ))
    (hf : ∀ x ∈ tsupport (ψ : V → ℂ), ContDiffAt ℝ (⊤ : ℕ∞) f x) : S :=
  hc.mul_right.toSchwartzMap (scalarLocalSource_smooth ψ f hf)

theorem scalarLocalSourceSchwartz_apply (ψ : S) (f : V → ℂ)
    (hc : HasCompactSupport (ψ : V → ℂ))
    (hf : ∀ x ∈ tsupport (ψ : V → ℂ), ContDiffAt ℝ (⊤ : ℕ∞) f x) (x : V) :
    scalarLocalSourceSchwartz ψ f hc hf x = ψ x * f x := rfl

/-- The actual compact-test equation identifies the localized source
with a constructed Schwartz function. -/
theorem scalar_localize_eq_smooth_source (U : Set V) (u : T) (f : V → ℂ)
    (hf : ∀ x ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = ∫ x, φ x * f x)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U) :
    M ψ u = (scalarLocalSourceSchwartz ψ f hc (fun x hx => hf x (hs hx)) : T) := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ ψ φ) = _
  rw [htest _ (scalarSchwartz_cutoff_compact ψ φ hc)
    (scalarSchwartz_cutoff_support ψ φ hs), SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth,
    scalarLocalSourceSchwartz_apply, smul_eq_mul]
  ring

/-- A compact-test equation with a locally smooth source supplies all
orders of the inner localized forcing used by the elliptic bootstrap. -/
theorem scalar_localize_smooth_source_memSobolev (U : Set V) (u : T) (f : V → ℂ)
    (hf : ∀ x ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = ∫ x, φ x * f x)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U) (s : ℝ) :
    MemSobolev s 2 (M ψ u) := by
  rw [scalar_localize_eq_smooth_source U u f hf htest ψ hc hs]
  exact SchwartzMap.memSobolev _

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelContinuousEmbedding
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

def h3InverseBounded (v : Lp ℂ 1 (volume : Measure V)) : V →ᵇ ℂ :=
  Real.Lp.fourierTransformInv v

theorem h3InverseBounded_apply (v : Lp ℂ 1 (volume : Measure V)) (x : V) :
    h3InverseBounded v x = (𝓕⁻ (v : V → ℂ)) x := by
  exact Real.Lp.fourierTransformInv_apply v x

theorem h3_inverse_pairing (v : Lp ℂ 1 (volume : Measure V))
    (φ : 𝓢(V, ℂ)) :
    (𝓕⁻ (v : 𝓢'(V, ℂ))) φ = ∫ x : V, φ x * h3InverseBounded v x := by
  simp_rw [h3InverseBounded_apply]
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := -(innerₗ V))
    (μ := (volume : Measure V)) (ν := (volume : Measure V))
    Real.continuous_fourierChar (by
      change Continuous (fun p : V × V => - inner ℝ p.1 p.2)
      fun_prop)
    (memLp_one_iff_integrable.mp (Lp.memLp v)) φ.integrable
  simpa only [SchwartzMap.fourierInv_coe, VectorFourier.fourierIntegral, Real.fourierInv_eq,
    ContinuousLinearMap.mul_apply', LinearMap.neg_apply, LinearMap.flip_apply,
    innerₗ_apply_apply, neg_neg, real_inner_comm, smul_eq_mul, mul_comm] using h.symm

/-- Three L2 Sobolev derivatives in dimension four produce a bounded continuous
function representing the same tempered distribution. -/
theorem scalar_H3_boundedContinuous_representative (u : 𝓢'(V, ℂ))
    (hu : MemSobolev 3 2 u) :
    ∃ f : V →ᵇ ℂ, ∀ φ : 𝓢(V, ℂ), u φ = ∫ x : V, φ x * f x := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 (by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    norm_num)
  refine ⟨h3InverseBounded v, fun φ => ?_⟩
  calc
    u φ = (𝓕⁻ (v : 𝓢'(V, ℂ))) φ := by rw [← hv, fourierInv_fourier_eq]
    _ = _ := h3_inverse_pairing v φ

/-- The bounded continuous representative agrees almost everywhere with any
L2 realization of the original distribution. -/
theorem scalar_L2_H3_boundedContinuous_representative
    (u : Lp ℂ 2 (volume : Measure V)) (hu : MemSobolev 3 2 (u : 𝓢'(V, ℂ))) :
    ∃ f : V →ᵇ ℂ, (u : V → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, heq⟩ := scalar_H3_boundedContinuous_representative (u : 𝓢'(V, ℂ)) hu
  refine ⟨f, ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num)) f.continuous.locallyIntegrable ?_⟩
  intro ψ hψ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hs' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have h := heq (hc'.toSchwartzMap hs')
  rw [Lp.toTemperedDistribution_apply] at h
  change (∫ x : V, (ψ x : ℂ) * u x) = ∫ x : V, (ψ x : ℂ) * f x at h
  simpa only [Complex.real_smul, smul_eq_mul] using h

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarSpectralOrthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthonormal family obtained by combining orthonormal bases of the
eigenspaces of a symmetric scalar operator. -/

namespace PositiveEinsteinFour.Geometry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem scalar_spectral_family_orthonormal (T : V →L[ℝ] V) (hT : T.IsSymmetric)
    [∀ μ : Module.End.Eigenvalues T.toLinearMap,
      FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap μ.val)] :
    Orthonormal ℝ (fun i : (Σ μ : Module.End.Eigenvalues T.toLinearMap,
        Fin (Module.finrank ℝ (Module.End.eigenspace T.toLinearMap μ.val))) =>
      (stdOrthonormalBasis ℝ (Module.End.eigenspace T.toLinearMap i.1.val) i.2).val) :=
  hT.orthogonalFamily_eigenspaces'.orthonormal_sigma_orthonormal
    (fun μ => (stdOrthonormalBasis ℝ (Module.End.eigenspace T.toLinearMap μ.val)).orthonormal)

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

/-! Smooth H2 approximation with strong L4 convergence of first derivatives.
This is the convergence required by the quadratic terms in the nonlinear
Hessian chain rule in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local instance instFactLeENNRealOfNat_solutions_2 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real smooth approximation preserving the L2 second derivatives and
L4 first derivatives of the same real H2 function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local instance instFactLeENNRealOfNat_solutions_4 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single H2 approximation sequence with pointwise convergence as well
as all the strong derivative convergences needed in scalar composition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local instance instFactLeENNRealOfNat_solutions_5 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Euler identity for a normalized Hilbert-energy minimum. -/

namespace PositiveEinsteinFour.Geometry

open Filter
open scoped _root_.Topology

noncomputable section

/-- The quadratic energy has its usual derivative along an affine line in
the completed energy space; no smooth representative is required. -/
theorem scalar_energy_line_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (w b : H) :
    HasDerivAt (fun t : ℝ => ‖w + t • b‖ ^ 2) (2 * inner ℝ w b) 0 := by
  have hline : HasDerivAt (fun t : ℝ => w + t • b) b 0 := by
    simpa only [Pi.add_def, id_eq, zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) w).add ((hasDerivAt_id (0 : ℝ)).smul_const b)
  simpa only [zero_smul, add_zero] using hline.norm_sq

/-- Fermat's rule applied to the homogeneous Sobolev quotient.  The only
analytic ingredient here is the directional derivative of its norm term. -/
theorem scalar_energy_minimum_euler
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : H →L[ℝ] E)
    (w b : H) (hunit : ‖T w‖ = 1)
    (hmin : ∀ v : H, ‖w‖ ^ 2 * ‖T v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (I : ℝ) (hvar : HasDerivAt (fun t : ℝ => ‖T (w + t • b)‖ ^ 2) (2 * I) 0) :
    inner ℝ w b = ‖w‖ ^ 2 * I := by
  let F (t : ℝ) := ‖w + t • b‖ ^ 2 - ‖w‖ ^ 2 * ‖T (w + t • b)‖ ^ 2
  have hlocal : IsLocalMin F 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change F 0 ≤ F t
    simp only [F, zero_smul, add_zero, hunit, one_pow, mul_one, sub_self]
    exact sub_nonneg.mpr (hmin (w + t • b))
  have hdiff : HasDerivAt F (2 * inner ℝ w b - ‖w‖ ^ 2 * (2 * I)) 0 :=
    (scalar_energy_line_hasDerivAt w b).sub (hvar.const_mul (‖w‖ ^ 2))
  have hzero := hlocal.hasDerivAt_eq_zero hdiff
  linarith

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal

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

theorem kato_square_bound {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (h : a ≤ b * c) : a ^ 2 ≤ (b ^ 2 + 1) * c ^ 2 := by
  calc
    a ^ 2 ≤ (b * c) ^ 2 := (sq_le_sq₀ ha (mul_nonneg hb hc)).2 h
    _ ≤ (b ^ 2 + 1) * c ^ 2 := by
      rw [mul_pow]
      nlinarith [sq_nonneg c]

theorem kato_real_inner {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (a b : Lp ℝ 2 μ) :
    inner ℝ a b = ∫ x, a x * b x ∂μ := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]

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

def nonlinearEpsilon (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem nonlinearEpsilon_pos (n : ℕ) : 0 < nonlinearEpsilon n := by
  unfold nonlinearEpsilon
  positivity

theorem nonlinearEpsilon_le_one (n : ℕ) : nonlinearEpsilon n ≤ 1 := by
  apply inv_le_one_of_one_le₀
  change 1 ≤ (n : ℝ) + 1
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem nonlinearEpsilon_tendsto :
    Tendsto nonlinearEpsilon atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

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

/-! The two surviving orders of the signed squared-Gaussian integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeatGaussian_half_tendsto :
    Tendsto (fun t : ℝ => t / 2) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [zero_div, id_eq] using
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t)
        (𝓝[>] 0) (𝓝 0)).div_const (2 : ℝ)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact half_pos ht

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarBoundedPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous test pairings for bounded representatives of local heat output. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem scalarBoundedTest_integrable (φ : 𝓢(V, ℂ)) (f : V →ᵇ ℂ) :
    Integrable (fun x => φ x * f x) :=
  φ.integrable.mul_bdd f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

def scalarBoundedTestPairing (φ : 𝓢(V, ℂ)) : (V →ᵇ ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, φ x * f x
      map_add' := by
        intro f g
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, mul_add]
        exact integral_add (scalarBoundedTest_integrable φ f) (scalarBoundedTest_integrable φ g)
      map_smul' := by
        intro c f
        simp only [BoundedContinuousFunction.coe_smul, mul_smul_comm,
          integral_smul, RingHom.id_apply] }
    (∫ x, ‖φ x‖) (by
      intro f
      calc
        ‖∫ x, φ x * f x‖ ≤ ∫ x, ‖φ x‖ * ‖f‖ := by
          apply norm_integral_le_of_norm_le (φ.integrable.norm.mul_const ‖f‖)
          exact Filter.Eventually.of_forall (fun x => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _))
        _ = (∫ x, ‖φ x‖) * ‖f‖ := integral_mul_const _ _)

theorem scalarBoundedTestPairing_apply (φ : 𝓢(V, ℂ)) (f : V →ᵇ ℂ) :
    scalarBoundedTestPairing φ f = ∫ x, φ x * f x := rfl

theorem scalar_L2_eq_bounded_of_tests (u : Lp ℂ 2 (volume : Measure V)) (f : V →ᵇ ℂ)
    (h : ∀ φ : 𝓢(V, ℂ), (u : 𝓢'(V, ℂ)) φ = scalarBoundedTestPairing φ f) :
    (u : V → ℂ) =ᵐ[volume] f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num)) f.continuous.locallyIntegrable
  intro ψ hψ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hs' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have he := h (hc'.toSchwartzMap hs')
  rw [Lp.toTemperedDistribution_apply, scalarBoundedTestPairing_apply] at he
  change (∫ x : V, (ψ x : ℂ) * u x) = ∫ x : V, (ψ x : ℂ) * f x at he
  simpa only [Complex.real_smul, smul_eq_mul] using he

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarContinuousLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local H3-valued bounded operator has a bounded continuous-function lift.
The norm bound follows from the closed graph theorem and actual test pairings. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : E →L[ℝ] Lp ℂ 2 (volume : Measure V))
  (hA : ∀ f, MemSobolev 3 2 (A f : 𝓢'(V, ℂ)))

def scalarH3Representative (f : E) : V →ᵇ ℂ :=
  (scalar_L2_H3_boundedContinuous_representative (A f) (hA f)).choose

theorem scalarH3Representative_ae (f : E) :
    (A f : V → ℂ) =ᵐ[volume] scalarH3Representative A hA f :=
  (scalar_L2_H3_boundedContinuous_representative (A f) (hA f)).choose_spec

theorem scalarH3Representative_eq (f : E) (g : V →ᵇ ℂ)
    (hg : (A f : V → ℂ) =ᵐ[volume] g) : scalarH3Representative A hA f = g := by
  apply DFunLike.coe_injective
  exact MeasureTheory.Measure.eq_of_ae_eq ((scalarH3Representative_ae A hA f).symm.trans hg)
    (scalarH3Representative A hA f).continuous g.continuous

def scalarH3RepresentativeLinear : E →ₗ[ℝ] (V →ᵇ ℂ) where
  toFun := scalarH3Representative A hA
  map_add' f g := by
    apply scalarH3Representative_eq
    rw [map_add]
    filter_upwards [Lp.coeFn_add (A f) (A g), scalarH3Representative_ae A hA f,
      scalarH3Representative_ae A hA g] with x hadd hf hg
    simp only [hadd, hf, hg, BoundedContinuousFunction.coe_add, Pi.add_apply]
  map_smul' c f := by
    apply scalarH3Representative_eq
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (A f), scalarH3Representative_ae A hA f] with x hsm hf
    simp only [hsm, hf, BoundedContinuousFunction.coe_smul, Pi.smul_apply, RingHom.id_apply]

theorem scalarH3Representative_pairing (f : E) (φ : 𝓢(V, ℂ)) :
    (A f : 𝓢'(V, ℂ)) φ = scalarBoundedTestPairing φ (scalarH3Representative A hA f) := by
  rw [Lp.toTemperedDistribution_apply, scalarBoundedTestPairing_apply]
  apply integral_congr_ae
  filter_upwards [scalarH3Representative_ae A hA f] with x hx
  rw [hx, smul_eq_mul]

theorem scalarH3Representative_graph_closed :
    IsClosed ((scalarH3RepresentativeLinear A hA).graph : Set (E × (V →ᵇ ℂ))) := by
  have heq : ((scalarH3RepresentativeLinear A hA).graph : Set (E × (V →ᵇ ℂ))) =
      ⋂ φ : 𝓢(V, ℂ), {p | (A p.1 : 𝓢'(V, ℂ)) φ = scalarBoundedTestPairing φ p.2} := by
    ext p
    rcases p with ⟨f, g⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    change g = scalarH3Representative A hA f ↔
      ∀ φ : 𝓢(V, ℂ), (A f : 𝓢'(V, ℂ)) φ = scalarBoundedTestPairing φ g
    constructor
    · intro hg φ
      rw [hg]
      exact scalarH3Representative_pairing A hA f φ
    · intro h
      exact (scalarH3Representative_eq A hA f g (scalar_L2_eq_bounded_of_tests (A f) g h)).symm
  rw [heq]
  apply isClosed_iInter
  intro φ
  apply isClosed_eq _ ((scalarBoundedTestPairing φ).continuous.comp continuous_snd)
  exact ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).continuous.comp
    ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp A.continuous)).comp continuous_fst

variable [CompleteSpace E]

def scalarH3ContinuousLift : E →L[ℝ] (V →ᵇ ℂ) :=
  ContinuousLinearMap.ofIsClosedGraph (scalarH3Representative_graph_closed A hA)

theorem scalarH3ContinuousLift_ae (f : E) :
    (A f : V → ℂ) =ᵐ[volume] scalarH3ContinuousLift A hA f :=
  scalarH3Representative_ae A hA f

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarBoundedBessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Bessel bounds for bounded continuous local heat coefficients. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι : Type*} {v : ι → E}

theorem scalarFunctional_bessel (hv : Orthonormal ℝ v) (L : E →L[ℝ] ℝ) (s : Finset ι) :
    ∑ i ∈ s, (L (v i)) ^ 2 ≤ ‖L‖ ^ 2 := by
  have h := hv.sum_inner_products_le (s := s) ((InnerProductSpace.toDual ℝ E).symm L)
  have he (i : ι) : inner ℝ (v i) ((InnerProductSpace.toDual ℝ E).symm L) = L (v i) := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp_rw [he, Real.norm_eq_abs, sq_abs] at h
  exact h.trans_eq (congrArg (fun x : ℝ => x ^ 2) ((InnerProductSpace.toDual ℝ E).symm.norm_map L))

theorem scalarComplexFunctional_bessel (hv : Orthonormal ℝ v) (L : E →L[ℝ] ℂ)
    (s : Finset ι) : ∑ i ∈ s, ‖L (v i)‖ ^ 2 ≤ 2 * ‖L‖ ^ 2 := by
  have hr := scalarFunctional_bessel hv (Complex.reCLM.comp L) s
  have hi := scalarFunctional_bessel hv (Complex.imCLM.comp L) s
  have hR : ‖Complex.reCLM.comp L‖ ≤ ‖L‖ := by
    simpa only [Complex.reCLM_norm, one_mul] using Complex.reCLM.opNorm_comp_le L
  have hI : ‖Complex.imCLM.comp L‖ ≤ ‖L‖ := by
    simpa only [Complex.imCLM_norm, one_mul] using Complex.imCLM.opNorm_comp_le L
  have hsum : (∑ i ∈ s, ‖L (v i)‖ ^ 2) =
      (∑ i ∈ s, ((Complex.reCLM.comp L) (v i)) ^ 2) +
      ∑ i ∈ s, ((Complex.imCLM.comp L) (v i)) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.normSq_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
      Complex.imCLM_apply, pow_two] using Complex.sq_norm (L (v i))
  rw [hsum]
  have hr' := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hi' := pow_le_pow_left₀ (norm_nonneg _) hI 2
  linarith

theorem scalarBoundedOperator_bessel {X : Type*} [TopologicalSpace X]
    (hv : Orthonormal ℝ v) (A : E →L[ℝ] (X →ᵇ ℂ)) (s : Finset ι) (x : X) :
    ∑ i ∈ s, ‖A (v i) x‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 := by
  let L : E →L[ℝ] ℂ := (BoundedContinuousFunction.evalCLM ℝ x).comp A
  have hb : ‖L‖ ≤ ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    exact (BoundedContinuousFunction.norm_coe_le_norm (A u) x).trans (A.le_opNorm u)
  have h := scalarComplexFunctional_bessel hv L s
  exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (by norm_num))

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatForcedScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integrating-factor formula for the scalar forced heat equation,
including a distributional initial value represented by a one-sided limit. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter MeasureTheory
open scoped _root_.Topology

noncomputable section

theorem heat_forced_scalar_formula (f r : ℝ → ℝ) (rate a t : ℝ) (ht : 0 < t)
    (hr : ContinuousOn r (Icc 0 t))
    (h0 : Tendsto f (𝓝[>] 0) (𝓝 a))
    (hd : ∀ s > 0, HasDerivAt f (r s - rate * f s) s) :
    f t = Real.exp (-rate * t) * a +
      ∫ s in (0 : ℝ)..t, Real.exp (-rate * (t - s)) * r s := by
  have hprod (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun s => Real.exp (rate * s) * f s) (Real.exp (rate * s) * r s) s := by
    have he := ((hasDerivAt_id s).const_mul rate).exp
    simp only [id_eq, mul_one] at he
    have h := he.mul (hd s hs)
    convert h using 1 <;> first | rfl | ring
  have hi : IntervalIntegrable (fun s => Real.exp (rate * s) * r s) volume 0 t :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hr).intervalIntegrable_of_Icc ht.le
  have ha : Tendsto (fun s => Real.exp (rate * s) * f s) (𝓝[>] 0) (𝓝 a) := by
    have he : ContinuousAt (fun s : ℝ => Real.exp (rate * s)) 0 := by fun_prop
    simpa only [mul_zero, Real.exp_zero, one_mul] using
      (he.tendsto.mono_left nhdsWithin_le_nhds).mul h0
  have hb : Tendsto (fun s => Real.exp (rate * s) * f s) (𝓝[<] t)
      (𝓝 (Real.exp (rate * t) * f t)) :=
    (hprod t ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht
    (fun s hs => hprod s hs.1) hi ha hb
  have hexp : Real.exp (-rate * t) * Real.exp (rate * t) = 1 := by
    rw [← Real.exp_add]
    rw [show -rate * t + rate * t = 0 by ring, Real.exp_zero]
  have heq : (fun s => Real.exp (-rate * (t - s)) * r s) =
      (fun s => Real.exp (-rate * t) * (Real.exp (rate * s) * r s)) := by
    funext s
    rw [show -rate * (t - s) = -rate * t + rate * s by ring, Real.exp_add]
    ring
  rw [heq, intervalIntegral.integral_const_mul, hFTC]
  calc
    f t = (Real.exp (-rate * t) * Real.exp (rate * t)) * f t := by rw [hexp, one_mul]
    _ = _ := by ring

end
end PositiveEinsteinFour.Geometry

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

/-! Bounded spectral lifts from actual one-forms to their scalar and
closed two-form potentials. The lifts preserve the spectral parameter. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff lp

noncomputable section

def modeSynthesis {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (v : ι → H) (hv : Orthonormal ℝ v) : ℓ²(ι, ℝ) →ₗᵢ[ℝ] H :=
  hv.orthogonalFamily.linearIsometry

theorem modeSynthesis_single {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (v : ι → H) (hv : Orthonormal ℝ v) (i : ι) :
    modeSynthesis v hv (lp.single 2 i (1 : ℝ)) = v i := by
  classical
  change hv.orthogonalFamily.linearIsometry (lp.single 2 i (1 : ℝ)) = _
  rw [OrthogonalFamily.linearIsometry_apply_single, LinearIsometry.toSpanSingleton_apply, one_smul]

theorem modeAnalysis_coordinate {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (v : ι → H) (hv : Orthonormal ℝ v) (u : H) (i : ι) :
    ((modeSynthesis v hv).toContinuousLinearMap.adjoint u) i = inner ℝ (v i) u := by
  classical
  calc
    _ = inner ℝ (lp.single 2 i (1 : ℝ)) ((modeSynthesis v hv).toContinuousLinearMap.adjoint u) := by
      simp only [lp.inner_single_left, Real.inner_apply, one_mul]
    _ = inner ℝ (modeSynthesis v hv (lp.single 2 i (1 : ℝ))) u :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = _ := by rw [modeSynthesis_single]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual positive one-form heat spectrum stays away from zero.
Trace summability leaves only finitely many modes in a bounded interval. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology NNReal

noncomputable section

theorem finite_positive_lower_bound_p1 {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ r i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨ε, hε, hεs⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    refine ⟨min ε (r i), lt_min hε (hr i (Finset.mem_insert_self i s)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hεs j hj)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A residual bounded by B t has an actual continuous zero extension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped _root_.Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V]

def heatResidualAtZero (R : ℝ → V) : ℝ → V := Function.update R 0 0

theorem heatResidual_tendsto_zero (R : ℝ → V) (B T : ℝ) (hT : 0 < T)
    (hR : ∀ t ∈ Ioc 0 T, ‖R t‖ ≤ B * t) :
    Tendsto R (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => B * t) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => B * t) := continuous_const.mul continuous_id
    simpa only [mul_zero] using
      hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply squeeze_zero_norm' _ hlim
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htT
  exact hR t ⟨ht, htT.le⟩

theorem heatResidualAtZero_continuous (R : ℝ → V) (B T : ℝ) (hT : 0 < T)
    (hc : ContinuousOn R (Ioi 0)) (hR : ∀ t ∈ Ioc 0 T, ‖R t‖ ≤ B * t) :
    ContinuousOn (heatResidualAtZero R) (Icc 0 T) := by
  rw [heatResidualAtZero, continuousOn_update_iff, Icc_sdiff_left]
  exact ⟨hc.mono Ioc_subset_Ioi_self, fun _ =>
    (heatResidual_tendsto_zero R B T hT hR).mono_left
      (nhdsWithin_mono _ Ioc_subset_Ioi_self)⟩

theorem heatResidualAtZero_norm (R : ℝ → V) (B T : ℝ)
    (hR : ∀ t ∈ Ioc 0 T, ‖R t‖ ≤ B * t) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖heatResidualAtZero R t‖ ≤ B * t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    simp [heatResidualAtZero]
  · simpa only [heatResidualAtZero, Function.update_of_ne h.ne'] using hR t ⟨h, ht.2⟩

end
end PositiveEinsteinFour.Geometry
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

def complexPhase (t : ℝ) : ℂ := ⟨Real.cos t, Real.sin t⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


