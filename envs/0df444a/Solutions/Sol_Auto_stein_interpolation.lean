-- Prove2me | solution 1 for Auto.stein_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:09.494632+00:00
-- url     : https://prove2.me/submissions/1cb2e731-11fc-48cc-a24a-a23c92469e41

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
private theorem exp_growth_normalize
    {F : ℂ → ℂ} {a C : ℝ}
    (hF : ∀ z : verticalClosedStrip 0 1,
      ‖F z‖ ≤ Real.exp (C * Real.exp (a * |(z : ℂ).im|))) :
    ∀ z : verticalClosedStrip 0 1,
      ‖F z‖ ≤ Real.exp
        (max C 0 * Real.exp (max a 0 * |(z : ℂ).im|)) := by
  intro z
  apply (hF z).trans
  apply Real.exp_le_exp.mpr
  calc
    C * Real.exp (a * |(z : ℂ).im|) ≤
        max C 0 * Real.exp (a * |(z : ℂ).im|) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (max a 0 * |(z : ℂ).im|) := by
      apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
private theorem finite_bisum_exp_growth_of_uniform_factors
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (α : ι → ℂ → ℂ) (β : κ → ℂ → ℂ) (H : ι → κ → ℂ → ℂ)
    {a C A B : ℝ}
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ i ∈ s, ∀ z : verticalClosedStrip 0 1, ‖α i z‖ ≤ A)
    (hβ : ∀ j ∈ t, ∀ z : verticalClosedStrip 0 1, ‖β j z‖ ≤ B)
    (hH : ∀ i ∈ s, ∀ j ∈ t, ∀ z : verticalClosedStrip 0 1,
      ‖H i j z‖ ≤ Real.exp (C * Real.exp (a * |(z : ℂ).im|))) :
    ∀ z : verticalClosedStrip 0 1,
      ‖∑ i ∈ s, ∑ j ∈ t, α i z * β j z * H i j z‖ ≤
        Real.exp
          ((((s.card : ℝ) * (t.card : ℝ) * (A * B)) + C) *
            Real.exp (a * |(z : ℂ).im|)) := by
  intro z
  let E : ℝ := Real.exp (a * |(z : ℂ).im|)
  let N : ℝ := (s.card : ℝ) * (t.card : ℝ) * (A * B)
  have hE : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp (mul_nonneg ha (abs_nonneg _))
  have hN : 0 ≤ N := by
    dsimp [N]
    positivity
  have hsumcoeff :
      ∑ i ∈ s, ∑ j ∈ t, ‖α i z * β j z‖ ≤ N := by
    calc
      ∑ i ∈ s, ∑ j ∈ t, ‖α i z * β j z‖ ≤ ∑ i ∈ s, ∑ j ∈ t, A * B := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul (hα i hi z) (hβ j hj z) (norm_nonneg _) hA
      _ = N := by
        simp [N, mul_assoc]
  calc
    ‖∑ i ∈ s, ∑ j ∈ t, α i z * β j z * H i j z‖ ≤
        ∑ i ∈ s, ∑ j ∈ t, ‖α i z * β j z * H i j z‖ := by
      calc
        ‖∑ i ∈ s, ∑ j ∈ t, α i z * β j z * H i j z‖ ≤
            ∑ i ∈ s, ‖∑ j ∈ t, α i z * β j z * H i j z‖ := by
          exact norm_sum_le s (fun i ↦ ∑ j ∈ t, α i z * β j z * H i j z)
        _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖α i z * β j z * H i j z‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_sum_le t (fun j ↦ α i z * β j z * H i j z)
    _ = ∑ i ∈ s, ∑ j ∈ t, ‖α i z * β j z‖ * ‖H i j z‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul]
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖α i z * β j z‖ * Real.exp (C * E) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (by simpa [E] using hH i hi j hj z) (norm_nonneg _)
    _ = (∑ i ∈ s, ∑ j ∈ t, ‖α i z * β j z‖) * Real.exp (C * E) := by
      rw [Finset.sum_mul]
      congr
      ext i
      rw [Finset.sum_mul]
    _ ≤ N * Real.exp (C * E) :=
      mul_le_mul_of_nonneg_right hsumcoeff (Real.exp_pos _).le
    _ ≤ Real.exp (N + C * E) := by
      calc
        N * Real.exp (C * E) ≤ Real.exp N * Real.exp (C * E) :=
          mul_le_mul_of_nonneg_right (by
            calc
              N ≤ N + 1 := le_add_of_nonneg_right zero_le_one
              _ ≤ Real.exp N := add_one_le_exp N) (Real.exp_pos _).le
        _ = Real.exp (N + C * E) := by rw [Real.exp_add]
    _ ≤ Real.exp ((N + C) * E) := by
      apply Real.exp_le_exp.mpr
      have hNE : N ≤ N * E := by
        calc
          N = N * 1 := (mul_one _).symm
          _ ≤ N * E := mul_le_mul_of_nonneg_left hE hN
      calc
        N + C * E ≤ N * E + C * E := by linarith
        _ = (N + C) * E := by ring
    _ = Real.exp
        ((((s.card : ℝ) * (t.card : ℝ) * (A * B)) + C) *
          Real.exp (a * |(z : ℂ).im|)) := by rfl
private theorem one_le_norm_canonicalFactor
    {R : ℝ} {u z : ℂ} (hR : 0 < R)
    (hu : u ∈ ball 0 R) (hz : z ∈ closedBall 0 R) (hzu : z ≠ u) :
    1 ≤ ‖Complex.canonicalFactor R u z‖ := by
  have hRu : Complex.normSq u < R * R := by
    rw [Complex.normSq_eq_norm_sq]
    rw [mem_ball, dist_zero_right] at hu
    nlinarith [norm_nonneg u]
  have hRz : Complex.normSq z ≤ R * R := by
    rw [Complex.normSq_eq_norm_sq]
    rw [mem_closedBall, dist_zero_right] at hz
    nlinarith [norm_nonneg z]
  have hident :
      Complex.normSq ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z) -
        (R * R) * Complex.normSq (z - u) =
        (R * R - Complex.normSq u) * (R * R - Complex.normSq z) := by
    simp only [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq : (R * ‖z - u‖) ^ 2 ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2 := by
    have hpos : 0 ≤ (R * R - Complex.normSq u) * (R * R - Complex.normSq z) :=
      mul_nonneg (by linarith) (by linarith)
    have hsq' : (R * R) * Complex.normSq (z - u) ≤
        Complex.normSq ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z) := by
      nlinarith [hident]
    calc
      (R * ‖z - u‖) ^ 2 = (R * R) * Complex.normSq (z - u) := by
        rw [mul_pow, Complex.sq_norm]
        ring
      _ ≤ Complex.normSq ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z) := hsq'
      _ = ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2 :=
        Complex.normSq_eq_norm_sq _
  have hnum : R * ‖z - u‖ ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := by
    exact (sq_le_sq₀ (mul_nonneg hR.le (norm_nonneg _)) (norm_nonneg _)).mp hsq
  have hden : 0 < ‖(R : ℂ) * (z - u)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact mul_pos hR (norm_pos_iff.mpr (sub_ne_zero.mpr hzu))
  rw [Complex.canonicalFactor_apply, norm_div]
  apply (le_div_iff₀ hden).mpr
  rw [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  exact hnum
private theorem canonicalNumerator_ne_zero
    {R : ℝ} {u z : ℂ} (hR : 0 < R)
    (hu : u ∈ ball 0 R) (hz : z ∈ closedBall 0 R) :
    (R : ℂ) ^ 2 - (starRingEnd ℂ) u * z ≠ 0 := by
  suffices ‖(starRingEnd ℂ) u * z‖ < ‖(R : ℂ) ^ 2‖ by grind
  suffices ‖u‖ * ‖z‖ < R * R by simpa [sq]
  rw [mem_ball, dist_zero_right] at hu
  rw [mem_closedBall, dist_zero_right] at hz
  nlinarith [norm_nonneg u, norm_nonneg z]
private theorem continuousOn_weighted_log_norm_sub
    {R : ℝ} {u w : ℂ} (_hR : 0 < R)
    (hu : u ∈ ball 0 R) (hw : w ∈ ball 0 R) :
    ContinuousOn
      ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖z - u‖)
      (sphere 0 R) := by
  intro z hz
  have hnz : ‖z‖ = R := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hnu : ‖u‖ < R := by
    simpa [mem_ball, dist_zero_right] using hu
  have hnw : ‖w‖ < R := by
    simpa [mem_ball, dist_zero_right] using hw
  have hzw : z ≠ w := by
    intro h
    rw [h] at hnz
    linarith
  have hzu : z ≠ u := by
    intro h
    rw [h] at hnz
    linarith
  apply ContinuousAt.continuousWithinAt
  simp only [herglotzRieszKernel_fun_def]
  have hnorm : ‖z - u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzu)
  fun_prop (disch := grind)
private theorem harmonicContOnCl_log_norm_canonicalNumerator
    {R : ℝ} {u : ℂ} (hR : 0 < R) (hu : u ∈ ball 0 R) :
    InnerProductSpace.HarmonicContOnCl
      (fun z ↦ Real.log ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖)
      (ball 0 R) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    exact
      (by
        fun_prop : AnalyticAt ℂ (fun z ↦ (R : ℂ) ^ 2 - (starRingEnd ℂ) u * z) z).harmonicAt_log_norm
      (canonicalNumerator_ne_zero hR hu (ball_subset_closedBall hz))
  · intro z hz
    apply ContinuousAt.continuousWithinAt
    have hnorm : ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (canonicalNumerator_ne_zero hR hu
        (closure_ball_subset_closedBall hz))
    fun_prop
private theorem harmonicContOnCl_log_norm_of_analytic_nozero
    {R : ℝ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hgne : ∀ z ∈ closedBall 0 R, g z ≠ 0) :
    InnerProductSpace.HarmonicContOnCl (fun z ↦ Real.log ‖g z‖) (ball 0 R) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    exact (hg z (ball_subset_closedBall hz)).harmonicAt_log_norm
      (hgne z (ball_subset_closedBall hz))
  · intro z hz
    apply ContinuousAt.continuousWithinAt
    have hnorm : ‖g z‖ ≠ 0 := norm_ne_zero_iff.mpr
      (hgne z (closure_ball_subset_closedBall hz))
    have hgcont : ContinuousAt g z :=
      (hg z (closure_ball_subset_closedBall hz)).continuousAt
    fun_prop
private theorem continuousOn_weighted_const
    {R : ℝ} {w : ℂ} (_hR : 0 < R) (hw : w ∈ ball 0 R) (a : ℝ) :
    ContinuousOn
      ((Complex.re ∘ herglotzRieszKernel 0 w) * fun _ ↦ a)
      (sphere 0 R) := by
  intro z hz
  have hnz : ‖z‖ = R := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hnw : ‖w‖ < R := by
    simpa [mem_ball, dist_zero_right] using hw
  have hzw : z ≠ w := by
    intro h
    rw [h] at hnz
    linarith
  apply ContinuousAt.continuousWithinAt
  simp only [herglotzRieszKernel_fun_def]
  fun_prop (disch := grind)
private theorem continuousOn_re_herglotzRieszKernel
    {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R) :
    ContinuousOn (Complex.re ∘ herglotzRieszKernel 0 w) (sphere 0 R) := by
  intro z hz
  have hnz : ‖z‖ = R := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hnw : ‖w‖ < R := by
    simpa [mem_ball, dist_zero_right] using hw
  have hzw : z ≠ w := by
    intro h
    rw [h] at hnz
    linarith
  apply ContinuousAt.continuousWithinAt
  simp only [herglotzRieszKernel_fun_def]
  fun_prop (disch := grind)
private theorem weighted_circleAverage_log_norm_sub_le
    {R : ℝ} {u w : ℂ} (hR : 0 < R)
    (hu : u ∈ ball 0 R) (hw : w ∈ ball 0 R) (hwu : w ≠ u) :
    Real.log ‖w - u‖ ≤
      Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖z - u‖)
        0 R := by
  let P : ℂ → ℝ := Complex.re ∘ herglotzRieszKernel 0 w
  let N : ℂ → ℂ := fun z ↦ (R : ℂ) ^ 2 - (starRingEnd ℂ) u * z
  have hNpoisson :
      Real.circleAverage (P * fun z ↦ Real.log ‖N z‖) 0 R = Real.log ‖N w‖ := by
    simpa only [P, N, smul_eq_mul] using
      (InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
        (harmonicContOnCl_log_norm_canonicalNumerator hR hu) hw)
  have hboundary : Set.EqOn
      (P * fun z ↦ Real.log ‖N z‖)
      (fun z ↦ P z * (Real.log R + Real.log ‖z - u‖))
      (sphere 0 R) := by
    intro z hz
    dsimp [P, N]
    congr 1
    have hzu : z ≠ u := by
      intro h
      have hnz : ‖z‖ = R := by
        simpa [mem_sphere, dist_zero_right] using hz
      rw [h] at hnz
      have hnu : ‖u‖ < R := by
        simpa [mem_ball, dist_zero_right] using hu
      linarith
    have hden : 0 < R * ‖z - u‖ :=
      mul_pos hR (norm_pos_iff.mpr (sub_ne_zero.mpr hzu))
    have hcan := Complex.norm_canonicalFactor_eval_circle_eq_one hu hz
    rw [Complex.canonicalFactor_apply, norm_div, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hcan
    have hnorm : ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ = R * ‖z - u‖ := by
      simpa using (div_eq_iff hden.ne').mp hcan
    rw [hnorm, Real.log_mul hR.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzu))]
  have hconst :
      Real.circleAverage (P * fun _ ↦ Real.log R) 0 R = Real.log R := by
    have hharm : InnerProductSpace.HarmonicContOnCl (fun _ : ℂ ↦ Real.log R) (ball 0 R) := by
      refine ⟨?_, ?_⟩
      · intro z hz
        exact InnerProductSpace.harmonicAt_const _
      · intro z hz
        exact continuousAt_const.continuousWithinAt
    simpa only [P, smul_eq_mul] using
      (InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul hharm hw)
  have hsplit :
      Real.circleAverage (fun z ↦ P z * (Real.log R + Real.log ‖z - u‖)) 0 R =
        Real.log R + Real.circleAverage (P * fun z ↦ Real.log ‖z - u‖) 0 R := by
    calc
      Real.circleAverage (fun z ↦ P z * (Real.log R + Real.log ‖z - u‖)) 0 R =
          Real.circleAverage (fun z ↦ P z * Real.log R + P z * Real.log ‖z - u‖) 0 R := by
        congr 1
        funext z
        ring
      _ = Real.circleAverage (P * fun _ ↦ Real.log R) 0 R +
          Real.circleAverage (P * fun z ↦ Real.log ‖z - u‖) 0 R := by
        apply Real.circleAverage_fun_add
        · exact (continuousOn_weighted_const hR hw _).circleIntegrable hR.le
        · exact (continuousOn_weighted_log_norm_sub hR hu hw).circleIntegrable hR.le
      _ = Real.log R + Real.circleAverage (P * fun z ↦ Real.log ‖z - u‖) 0 R := by
        rw [hconst]
  have hcanw := one_le_norm_canonicalFactor hR hu (ball_subset_closedBall hw) hwu
  have hdenw : 0 < R * ‖w - u‖ :=
    mul_pos hR (norm_pos_iff.mpr (sub_ne_zero.mpr hwu))
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hcanw
  have hnormw : R * ‖w - u‖ ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * w‖ :=
    by simpa using (le_div_iff₀ hdenw).mp hcanw
  have hlog : Real.log R + Real.log ‖w - u‖ ≤
      Real.log ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * w‖ := by
    rw [← Real.log_mul hR.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwu))]
    apply Real.strictMonoOn_log.monotoneOn
    · exact mem_Ioi.mpr hdenw
    · exact mem_Ioi.mpr (norm_pos_iff.mpr
        (canonicalNumerator_ne_zero hR hu (ball_subset_closedBall hw)))
    · exact hnormw
  have hcircle :
      Real.circleAverage (P * fun z ↦ Real.log ‖z - u‖) 0 R =
        Real.log ‖N w‖ - Real.log R := by
    have hrewrite :
        Real.circleAverage (P * fun z ↦ Real.log ‖N z‖) 0 R =
          Real.log R + Real.circleAverage (P * fun z ↦ Real.log ‖z - u‖) 0 R := by
      rw [Real.circleAverage_congr_sphere (by simpa [abs_of_pos hR] using hboundary), hsplit]
    rw [hNpoisson] at hrewrite
    dsimp [N] at hrewrite
    linarith
  dsimp [P] at hcircle ⊢
  linarith
private theorem circleAverage_weighted_finsum_log_norm_sub
    {R : ℝ} {w : ℂ}
    (D : Function.locallyFinsuppWithin (closedBall (0 : ℂ) R) ℤ)
    (hR : 0 < R) (hw : w ∈ ball 0 R) :
    Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) *
          fun z ↦ ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖)
        0 R =
      ∑ u ∈ (D.finiteSupport (isCompact_closedBall 0 R)).toFinset,
        (D u : ℝ) * Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖z - u‖)
          0 R := by
  let s := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
  let A : ℂ → ℂ → ℝ := fun u z ↦ (D u : ℝ) * Real.log ‖z - u‖
  have hA_support : Function.support A ⊆ D.support := by
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    contrapose! hu
    ext z
    simp [A, hu]
  have hAfin : A.HasFiniteSupport :=
    (D.finiteSupport (isCompact_closedBall 0 R)).subset hA_support
  have hsum (z : ℂ) : ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖ =
      ∑ u ∈ s, (D u : ℝ) * Real.log ‖z - u‖ := by
    calc
      ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖ = (∑ᶠ u, A u) z :=
        (finsum_apply hAfin z).symm
      _ = (∑ u ∈ s, A u) z := congrFun
        (finsum_eq_sum_of_support_subset A (by simpa [s] using hA_support)) z
      _ = ∑ u ∈ s, (D u : ℝ) * Real.log ‖z - u‖ := by simp [A]
  calc
    Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) *
          fun z ↦ ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) 0 R =
        Real.circleAverage
          (fun z ↦ ∑ u ∈ s, (D u : ℝ) *
            ((Complex.re ∘ herglotzRieszKernel 0 w) z * Real.log ‖z - u‖)) 0 R := by
      congr 1
      funext z
      change (Complex.re ∘ herglotzRieszKernel 0 w) z *
        (∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) = _
      rw [hsum z]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = ∑ u ∈ s, Real.circleAverage
          (fun z ↦ (D u : ℝ) *
            ((Complex.re ∘ herglotzRieszKernel 0 w) z * Real.log ‖z - u‖)) 0 R := by
      have hfun :
          (fun z ↦ ∑ u ∈ s, (D u : ℝ) *
            ((Complex.re ∘ herglotzRieszKernel 0 w) z * Real.log ‖z - u‖)) =
          ∑ u ∈ s, fun z ↦ (D u : ℝ) *
            ((Complex.re ∘ herglotzRieszKernel 0 w) z * Real.log ‖z - u‖) := by
        ext z
        simp
      rw [hfun, circleAverage_sum]
      intro u hu
      exact ((circleIntegrable_log_norm_sub_const R).mul_of_continuousOn
        (by simpa [abs_of_pos hR] using continuousOn_re_herglotzRieszKernel hw)).const_mul _
    _ = ∑ u ∈ s, (D u : ℝ) * Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖z - u‖) 0 R := by
      apply Finset.sum_congr rfl
      intro u hu
      simpa only [smul_eq_mul, Pi.mul_apply, mul_assoc] using
        (Real.circleAverage_fun_smul
          (f := (Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖z - u‖)
          (a := (D u : ℝ)))
private theorem analytic_weighted_circleAverage_log_norm_le
    {R : ℝ} {f : ℂ → ℂ} {w : ℂ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hw : w ∈ ball 0 R) (hfw : f w ≠ 0) :
    Real.log ‖f w‖ ≤
      Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖f z‖)
        0 R := by
  classical
  let D : Function.locallyFinsuppWithin (closedBall (0 : ℂ) R) ℤ :=
    divisor f (closedBall 0 R)
  let s := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
  have hwc : w ∈ closedBall 0 R := ball_subset_closedBall hw
  have hmf : MeromorphicOn f (closedBall 0 R) := hf.meromorphicOn
  have hDfin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 R)
  let A : ℂ → ℂ → ℝ := fun u z ↦ (D u : ℝ) * Real.log ‖z - u‖
  have hA_support : Function.support A ⊆ D.support := by
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    contrapose! hu
    ext z
    simp [A, hu]
  have hAfin : A.HasFiniteSupport := hDfin.subset hA_support
  have hpoint : (fun z ↦ ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) = ∑ᶠ u, A u := by
    funext z
    exact (finsum_apply hAfin z).symm
  let Fsum : ℂ → ℝ := ∑ᶠ u, A u
  have horder : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤ := by
    rw [← hmf.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall hR.le)]
    refine ⟨⟨w, hwc⟩, ?_⟩
    rw [(hf w hwc).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfw]
    simp
  obtain ⟨g, hgana, hgzero, hfac⟩ := hmf.extract_zeros_poles horder (by simpa [D] using hDfin)
  have hwacc : AccPt w (𝓟 (closedBall (0 : ℂ) R)) := by
    apply accPt_iff_frequently_nhdsNE.mpr
    apply compl_notMem
    apply mem_nhdsWithin.mpr
    refine ⟨ball w (R - ‖w‖), isOpen_ball, mem_ball_self (by
      simpa [mem_ball, dist_zero_right] using hw), ?_⟩
    intro z hz
    rcases hz with ⟨hz, _⟩
    rw [mem_ball] at hz
    rw [mem_closedBall, dist_zero_right]
    apply le_of_lt
    calc
      ‖z‖ = dist z 0 := by rw [dist_zero_right]
      _ ≤ dist z w + dist w 0 := dist_triangle z w 0
      _ < (R - ‖w‖) + ‖w‖ := by
        rw [dist_zero_right]
        linarith
      _ = R := by ring
  have htrail := MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
    ((divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)) hwc hwacc
      (hf w hwc).meromorphicAt
      (hgana w hwc) (hgzero ⟨w, hwc⟩) hfac
  rw [(hf w hwc).meromorphicTrailingCoeffAt_of_ne_zero hfw] at htrail
  have htrailD : Real.log ‖f w‖ =
      (∑ᶠ u, (D u : ℝ) * Real.log ‖w - u‖) + Real.log ‖g w‖ := by
    simpa [D] using htrail
  have hDzero : D w = 0 := by
    dsimp [D]
    rw [hf.divisor_apply hwc,
      (hf w hwc).analyticOrderAt_eq_zero.mpr hfw]
    simp
  have htrail' : Real.log ‖f w‖ =
      (∑ u ∈ s, (D u : ℝ) * Real.log ‖w - u‖) + Real.log ‖g w‖ := by
    rw [htrailD, finsum_eq_sum_of_support_subset _ (s := s)]
    intro u hu
    by_contra hus
    have hDu : D u = 0 := by
      by_contra hDu
      apply hus
      apply (Set.Finite.mem_toFinset hDfin).mpr
      simpa only [Function.mem_support] using hDu
    exact hu (by simp [hDu])
  have hPcont : ContinuousOn (Complex.re ∘ herglotzRieszKernel 0 w) (sphere 0 R) :=
    continuousOn_re_herglotzRieszKernel hw
  have hfactorAvg :
      Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) *
            fun z ↦ ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖)
          0 R =
        ∑ u ∈ s, (D u : ℝ) * Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖z - u‖)
          0 R := by
    simpa only [s] using circleAverage_weighted_finsum_log_norm_sub D hR hw
  have hfactorLe :
      (∑ u ∈ s, (D u : ℝ) * Real.log ‖w - u‖) ≤
        ∑ u ∈ s, (D u : ℝ) * Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖z - u‖)
          0 R := by
    apply Finset.sum_le_sum
    intro u hu
    have husupp : u ∈ D.support := by
      apply (Set.Finite.mem_toFinset hDfin).mp
      simpa only [s] using hu
    have huclosed : u ∈ closedBall 0 R := D.supportWithinDomain husupp
    have hDnonneg : 0 ≤ (D u : ℝ) := by
      dsimp [D]
      exact mod_cast hf.divisor_nonneg u
    apply mul_le_mul_of_nonneg_left _ hDnonneg
    have hwu : w ≠ u := by
      intro h
      subst u
      have : D w ≠ 0 := by simpa only [Function.mem_support] using husupp
      exact this hDzero
    have hunorm : ‖u‖ ≤ R := by
      simpa [mem_closedBall, dist_zero_right] using huclosed
    rcases lt_or_eq_of_le hunorm with huinside | huboundary
    · have huball : u ∈ ball 0 R := by
        simpa [mem_ball, dist_zero_right] using huinside
      exact weighted_circleAverage_log_norm_sub_le hR huball hw hwu
    · have husphere : u ∈ sphere 0 R := by
        simpa [mem_sphere, dist_zero_right] using huboundary
      exact (circleAverage_re_herglotzRieszKernel_mul_log husphere hw).symm.le
  have hgHarm : InnerProductSpace.HarmonicContOnCl
      (fun z ↦ Real.log ‖g z‖) (ball 0 R) :=
    harmonicContOnCl_log_norm_of_analytic_nozero hgana
      (fun z hz ↦ hgzero ⟨z, hz⟩)
  have hgAvg :
      Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖g z‖)
        0 R = Real.log ‖g w‖ := by
    simpa only [smul_eq_mul] using
      (InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul hgHarm hw)
  have hfactorInt : CircleIntegrable
      ((Complex.re ∘ herglotzRieszKernel 0 w) *
        fun z ↦ ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) 0 R := by
    rw [hpoint]
    apply (circleIntegrable_log_norm_factorizedRational D).mul_of_continuousOn
    simpa [abs_of_pos hR] using hPcont
  have hgInt : CircleIntegrable
      ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖g z‖) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply hPcont.mul
    exact hgHarm.continuousOn_ball.mono sphere_subset_closedBall
  have hsplit :
      Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) *
          fun z ↦ (∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) + Real.log ‖g z‖)
        0 R =
      Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) *
            fun z ↦ ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖)
          0 R +
        Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖g z‖)
          0 R := by
    calc
      Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) *
            fun z ↦ (∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) + Real.log ‖g z‖)
          0 R =
          Real.circleAverage
            (fun z ↦
              ((Complex.re ∘ herglotzRieszKernel 0 w) *
                fun z ↦ ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) z +
              ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖g z‖) z)
            0 R := by
        congr 1
        funext z
        simp only [Pi.mul_apply]
        ring
      _ = _ := Real.circleAverage_fun_add hfactorInt hgInt
  have hboundary :
      Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖f z‖)
        0 R =
      Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) *
          fun z ↦ (∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) + Real.log ‖g z‖)
        0 R := by
    apply Real.circleAverage_congr_codiscreteWithin _ hR.ne'
    have hlog := MeromorphicOn.extract_zeros_poles_log hgzero hfac
    have hlogD : (fun x ↦ Real.log ‖f x‖) =ᶠ[codiscreteWithin (closedBall 0 R)]
        (Fsum + fun x ↦ Real.log ‖g x‖) := by
      dsimp [Fsum]
      simpa [A, D] using hlog
    filter_upwards [hlogD.filter_mono
      (codiscreteWithin_mono (by simpa [abs_of_pos hR] using sphere_subset_closedBall))]
      with z hz
    change (Complex.re ∘ herglotzRieszKernel 0 w) z * Real.log ‖f z‖ =
      (Complex.re ∘ herglotzRieszKernel 0 w) z *
        ((∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) + Real.log ‖g z‖)
    rw [hz]
    change (Complex.re ∘ herglotzRieszKernel 0 w) z *
        (Fsum z + Real.log ‖g z‖) = _
    dsimp [Fsum]
    rw [← congrFun hpoint z]
  calc
    Real.log ‖f w‖ =
        (∑ u ∈ s, (D u : ℝ) * Real.log ‖w - u‖) + Real.log ‖g w‖ := htrail'
    _ ≤ (∑ u ∈ s, (D u : ℝ) * Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖z - u‖)
          0 R) + Real.log ‖g w‖ := by linarith [hfactorLe]
    _ = Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) *
            fun z ↦ ∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖)
          0 R +
        Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖g z‖)
          0 R := by
      rw [← hfactorAvg, ← hgAvg]
    _ = Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) *
          fun z ↦ (∑ᶠ u, (D u : ℝ) * Real.log ‖z - u‖) + Real.log ‖g z‖)
        0 R := hsplit.symm
    _ = Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖f z‖)
        0 R := hboundary.symm
private theorem continuousAt_log_max_norm_exp_neg (K : ℝ) (z : ℂ) :
    ContinuousAt (fun x : ℂ ↦ Real.log (max ‖x‖ (Real.exp (-K)))) z := by
  have hpos : max ‖z‖ (Real.exp (-K)) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (Real.exp_pos (-K)) (le_max_right _ _))
  have hcont : ContinuousAt (fun x : ℂ ↦ max ‖x‖ (Real.exp (-K))) z :=
    (continuous_norm.max (continuous_const : Continuous fun _ : ℂ ↦ Real.exp (-K))).continuousAt
  have hlog : ContinuousAt Real.log (max ‖z‖ (Real.exp (-K))) :=
    Real.continuousAt_log hpos
  change ContinuousAt (Real.log ∘ fun x : ℂ ↦ max ‖x‖ (Real.exp (-K))) z
  exact hlog.comp_of_eq hcont rfl
private theorem log_max_norm_exp_neg_eq_max_log_norm {z : ℂ} {K : ℝ} (hz : z ≠ 0) :
    Real.log (max ‖z‖ (Real.exp (-K))) = max (Real.log ‖z‖) (-K) := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases h : ‖z‖ ≤ Real.exp (-K)
  · have hlog : Real.log ‖z‖ ≤ -K :=
      (Real.log_le_iff_le_exp hnorm).mpr (by simpa using h)
    rw [max_eq_right h, Real.log_exp, max_eq_right hlog]
  · have hlt : Real.exp (-K) < ‖z‖ := lt_of_not_ge h
    have hlog : -K ≤ Real.log ‖z‖ :=
      (Real.le_log_iff_exp_le hnorm).mpr hlt.le
    rw [max_eq_left hlt.le, max_eq_left hlog]
private theorem neg_le_log_max_norm_exp_neg (K : ℝ) (z : ℂ) :
    -K ≤ Real.log (max ‖z‖ (Real.exp (-K))) := by
  rw [Real.le_log_iff_exp_le
    (lt_of_lt_of_le (Real.exp_pos (-K)) (le_max_right _ _))]
  exact le_max_right ‖z‖ (Real.exp (-K))
private theorem abs_log_max_norm_exp_neg_le_of_le
    {B K : ℝ} {z : ℂ} (hB : 0 ≤ B) (hK0 : 0 ≤ K) (hKB : K ≤ B)
    (hz : Real.log ‖z‖ ≤ B) :
    |Real.log (max ‖z‖ (Real.exp (-K)) : ℝ)| ≤ B := by
  rw [abs_le]
  constructor
  · linarith [neg_le_log_max_norm_exp_neg K z]
  · rw [Real.log_le_iff_le_exp
      (lt_of_lt_of_le (Real.exp_pos (-K)) (le_max_right _ _))]
    apply max_le
    · exact Real.le_exp_of_log_le hz
    · exact Real.exp_le_exp.mpr (by linarith)
private theorem log_max_norm_exp_neg_le_max_log_of_norm_le
    {K M : ℝ} {z : ℂ} (hM : 0 < M) (hz : ‖z‖ ≤ M) :
    Real.log (max ‖z‖ (Real.exp (-K))) ≤ max (Real.log M) (-K) := by
  calc
    Real.log (max ‖z‖ (Real.exp (-K))) ≤ Real.log (max M (Real.exp (-K))) := by
      apply Real.log_le_log
      · exact lt_of_lt_of_le (Real.exp_pos (-K)) (le_max_right _ _)
      · exact max_le_max hz le_rfl
    _ = max (Real.log M) (-K) := by
      have hM' : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hM)
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM] using
        (log_max_norm_exp_neg_eq_max_log_norm (K := K) hM')
private theorem tendsto_log_max_norm_exp_neg
    {u : ℕ → ℂ} {z : ℂ} {K : ℝ}
    (hu : Tendsto u atTop (𝓝 z)) :
    Tendsto (fun n ↦ Real.log (max ‖u n‖ (Real.exp (-K)))) atTop
      (𝓝 (Real.log (max ‖z‖ (Real.exp (-K)))) ) := by
  exact (continuousAt_log_max_norm_exp_neg K z).tendsto.comp hu
private theorem tendsto_integral_weighted_log_max_norm_exp_neg_of_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W B : α → ℝ} {u : ℕ → α → ℂ} {v : α → ℂ} {K : ℝ}
    (hW : AEStronglyMeasurable W μ)
    (hu_meas : ∀ n, AEStronglyMeasurable
      (fun x ↦ Real.log (max ‖u n x‖ (Real.exp (-K)))) μ)
    (hB_nonneg : ∀ x, 0 ≤ B x) (hK_nonneg : 0 ≤ K)
    (hu_bound : ∀ n x, Real.log ‖u n x‖ ≤ B x)
    (hdom : Integrable (fun x ↦ |W x| * (B x + K)) μ)
    (hu_lim : ∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (v x))) :
    Tendsto
      (fun n ↦ ∫ x, W x * Real.log (max ‖u n x‖ (Real.exp (-K)) ) ∂μ)
      atTop
      (𝓝 (∫ x, W x * Real.log (max ‖v x‖ (Real.exp (-K)) ) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ |W x| * (B x + K))
  · intro n
    exact hW.mul (hu_meas n)
  · exact hdom
  · intro n
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left
      (abs_log_max_norm_exp_neg_le_of_le (by linarith [hB_nonneg x]) hK_nonneg
        (by linarith [hB_nonneg x]) (by linarith [hu_bound n x]))
      (abs_nonneg _)
  · filter_upwards with x
    exact tendsto_const_nhds.mul
      (tendsto_log_max_norm_exp_neg (hu_lim x))
private theorem re_herglotzRieszKernel_nonneg
    {R : ℝ} {w z : ℂ} (hz : z ∈ sphere 0 R) (hw : w ∈ ball 0 R) :
    0 ≤ (Complex.re ∘ herglotzRieszKernel 0 w) z := by
  have hR : 0 < R := by
    rw [mem_ball, dist_zero_right] at hw
    exact lt_of_le_of_lt (norm_nonneg _) hw
  have hlow := le_re_herglotzRieszKernel hz hw
  have hnum : 0 ≤ R - ‖w‖ := by
    rw [mem_ball, dist_zero_right] at hw
    linarith
  have hden : 0 ≤ R + ‖w‖ := by linarith [norm_nonneg w]
  exact le_trans (div_nonneg hnum hden) (by simpa [Function.comp_apply,
    herglotzRieszKernel_fun_def] using hlow)
private theorem analytic_weighted_circleAverage_log_norm_le_floor
    {R : ℝ} {f : ℂ → ℂ} {w : ℂ} {K : ℂ → ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hw : w ∈ ball 0 R) (hfw : f w ≠ 0)
    (hraw : CircleIntegrable
      ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖f z‖) 0 R)
    (hfloor : CircleIntegrable
      ((Complex.re ∘ herglotzRieszKernel 0 w) *
        fun z ↦ Real.log (max ‖f z‖ (Real.exp (-K z)))) 0 R) :
    Real.circleAverage
      ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖f z‖) 0 R ≤
    Real.circleAverage
      ((Complex.re ∘ herglotzRieszKernel 0 w) *
        fun z ↦ Real.log (max ‖f z‖ (Real.exp (-K z)))) 0 R := by
  let P : ℂ → ℝ := Complex.re ∘ herglotzRieszKernel 0 w
  let L : ℂ → ℝ := fun z ↦ Real.log (max ‖f z‖ (Real.exp (-K z)))
  let G : ℂ → ℝ := fun z ↦ P z * max (Real.log ‖f z‖) (L z)
  have hne : ∀ᶠ z in codiscreteWithin (sphere 0 R), f z ≠ 0 :=
    codiscreteWithin_mono sphere_subset_closedBall
      (hf.preimage_zero_mem_codiscreteWithin hfw (ball_subset_closedBall hw)
        (Metric.isConnected_closedBall hR.le))
  have hG_eq : G =ᶠ[codiscreteWithin (sphere 0 R)] P * L := by
    filter_upwards [hne] with z hzne
    dsimp [G, L]
    have hle : Real.log ‖f z‖ ≤ Real.log (max ‖f z‖ (Real.exp (-K z))) := by
      rw [log_max_norm_exp_neg_eq_max_log_norm hzne]
      exact le_max_left _ _
    rw [max_eq_right hle]
  have hG : CircleIntegrable G 0 R :=
    CircleIntegrable.congr_codiscreteWithin
      (by simpa [abs_of_pos hR] using hG_eq.symm)
      (by simpa [P, L] using hfloor)
  have hmono : ∀ z ∈ sphere 0 R, P z * Real.log ‖f z‖ ≤ G z := by
    intro z hz
    dsimp [G]
    apply mul_le_mul_of_nonneg_left (le_max_left _ _)
    exact re_herglotzRieszKernel_nonneg hz hw
  calc
    Real.circleAverage (P * fun z ↦ Real.log ‖f z‖) 0 R ≤
        Real.circleAverage G 0 R :=
      Real.circleAverage_mono (by simpa [P] using hraw) hG
        (by simpa [abs_of_pos hR] using hmono)
    _ = Real.circleAverage (P * L) 0 R :=
      Real.circleAverage_congr_codiscreteWithin
        (by simpa [abs_of_pos hR] using hG_eq) hR.ne'
private theorem im_exp_pi_I_pos {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) :
    0 < (Complex.exp (Real.pi * Complex.I * z)).im := by
  rw [Complex.exp_im]
  have him : (Real.pi * Complex.I * z).im = Real.pi * z.re := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_im, zero_mul, mul_zero, sub_zero]
    ring
  rw [him]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hz.1) (by nlinarith [Real.pi_pos, hz.2]))
private theorem stripToDisc_norm_lt_one {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) :
    ‖(Complex.exp (Real.pi * Complex.I * z) - Complex.I) /
        (Complex.exp (Real.pi * Complex.I * z) + Complex.I)‖ < 1 := by
  let w : ℂ := Complex.exp (Real.pi * Complex.I * z)
  have hwim : 0 < w.im := by simpa [w] using im_exp_pi_I_pos hz
  have hden : 0 < ‖w + Complex.I‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
    linarith
  have hsquares : ‖w - Complex.I‖ ^ 2 < ‖w + Complex.I‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.I_re, sub_zero,
      Complex.sub_im, Complex.I_im, Complex.add_re, add_zero, Complex.add_im]
    nlinarith
  have hnorm : ‖w - Complex.I‖ < ‖w + Complex.I‖ :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares
  change ‖(w - Complex.I) / (w + Complex.I)‖ < 1
  rw [norm_div]
  exact (div_lt_one₀ hden).2 hnorm
private theorem cayleyInverse_im_pos {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (Complex.I * (1 + z) / (1 - z)).im := by
  have hne : 1 - z ≠ 0 := by
    intro h
    have : z = 1 := (sub_eq_zero.mp h).symm
    subst z
    norm_num at hz
  have hsq : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hne
  have hnum : 0 < 1 - Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have him : (Complex.I * (1 + z) / (1 - z)).im =
      (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
    rw [Complex.div_im]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      Complex.mul_re, Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im,
      zero_add, Complex.sub_re, Complex.sub_im]
    field_simp
    simp only [Complex.normSq_apply]
    ring
  rw [him]
  exact div_pos hnum hsq
private theorem realpart_log_cayleyInverse_div_pi_I (q : ℂ) :
    (Complex.log q / (Real.pi * Complex.I)).re = q.arg / Real.pi := by
  rw [Complex.div_re, Complex.log_im]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, Complex.mul_im, zero_add,
    Complex.normSq_apply]
  field_simp
  ring
private theorem discToStrip_mem_verticalStrip {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.log (Complex.I * (1 + z) / (1 - z)) / (Real.pi * Complex.I) ∈
      verticalStrip 0 1 := by
  let q : ℂ := Complex.I * (1 + z) / (1 - z)
  have hqim : 0 < q.im := by
    simpa only [q] using cayleyInverse_im_pos hz
  have harg0 : 0 < q.arg := by
    have hnonneg : 0 ≤ q.arg := Complex.arg_nonneg_iff.mpr hqim.le
    have hne : q.arg ≠ 0 := by
      intro h
      have : q.im = 0 := (Complex.arg_eq_zero_iff.mp h).2
      linarith
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have harg1 : q.arg < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hqim))
  rw [verticalStrip, mem_preimage, mem_Ioo]
  rw [realpart_log_cayleyInverse_div_pi_I]
  constructor
  · exact div_pos harg0 Real.pi_pos
  · exact (div_lt_one₀ Real.pi_pos).mpr harg1
private theorem differentiableOn_discToStrip :
    DifferentiableOn ℂ
      (fun z ↦ Complex.log (Complex.I * (1 + z) / (1 - z)) / (Real.pi * Complex.I))
      (ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by
    simpa [mem_ball, dist_zero_right] using hz
  have hne : 1 - z ≠ 0 := by
    intro h
    have : z = 1 := (sub_eq_zero.mp h).symm
    subst z
    norm_num at hz
  have hq : Complex.I * (1 + z) / (1 - z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inr (ne_of_gt (cayleyInverse_im_pos hz'))
  have hrat : DifferentiableAt ℂ
      (fun z ↦ Complex.I * (1 + z) / (1 - z)) z := by
    fun_prop (disch := exact hne)
  simpa only [Function.comp_apply] using
    (((Complex.differentiableAt_log hq).comp z hrat).div_const
      (Real.pi * Complex.I)).differentiableWithinAt
private theorem analyticOnNhd_discToStrip :
    AnalyticOnNhd ℂ
      (fun z ↦ Complex.log (Complex.I * (1 + z) / (1 - z)) / (Real.pi * Complex.I))
      (ball 0 1) :=
  differentiableOn_discToStrip.analyticOnNhd isOpen_ball
private theorem discToStrip_stripToDisc {z : ℂ} (hz : z ∈ verticalStrip 0 1) :
    Complex.log
        (Complex.I *
          (1 + (Complex.exp (Real.pi * Complex.I * z) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * z) + Complex.I)) /
          (1 - (Complex.exp (Real.pi * Complex.I * z) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * z) + Complex.I))) /
      (Real.pi * Complex.I) = z := by
  let w : ℂ := Complex.exp (Real.pi * Complex.I * z)
  have hwim : 0 < w.im := by
    simpa [w] using im_exp_pi_I_pos hz
  have hden : w + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
    linarith
  have hsub : 1 - (w - Complex.I) / (w + Complex.I) ≠ 0 := by
    intro h
    field_simp [hden] at h
    norm_num at h
  have hq : Complex.I * (1 + (w - Complex.I) / (w + Complex.I)) /
      (1 - (w - Complex.I) / (w + Complex.I)) = w := by
    field_simp [hden, hsub]
    ring
  change Complex.log
      (Complex.I * (1 + (w - Complex.I) / (w + Complex.I)) /
        (1 - (w - Complex.I) / (w + Complex.I))) /
      (Real.pi * Complex.I) = z
  rw [hq]
  have him : (Real.pi * Complex.I * z).im = Real.pi * z.re := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_im, zero_mul, mul_zero, sub_zero]
    ring
  have hlow : -Real.pi < (Real.pi * Complex.I * z).im := by
    rw [him]
    nlinarith [Real.pi_pos, hz.1]
  have hupp : (Real.pi * Complex.I * z).im ≤ Real.pi := by
    rw [him]
    nlinarith [Real.pi_pos, hz.2]
  rw [show w = Complex.exp (Real.pi * Complex.I * z) by rfl,
    Complex.log_exp hlow hupp]
  have hpiI : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)) Complex.I_ne_zero
  field_simp [hpiI]
private theorem exp_pi_I_mul_I_ofReal (t : ℝ) :
    Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) =
      (Real.exp (-Real.pi * t) : ℂ) := by
  have harg : Real.pi * Complex.I * ((t : ℂ) * Complex.I) =
      ((-Real.pi * t : ℝ) : ℂ) := by
    push_cast
    calc
      (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I) =
          ((Real.pi : ℂ) * Complex.I * (t : ℂ)) * Complex.I := by
            ring
      _ =
          (Real.pi : ℂ) * (t : ℂ) * (Complex.I * Complex.I) := by ring
      _ = -((Real.pi : ℂ) * (t : ℂ)) := by rw [Complex.I_mul_I]; ring
      _ = -(Real.pi : ℂ) * (t : ℂ) := by ring
  rw [harg, Complex.ofReal_exp]
private theorem exp_pi_I_one_add_I_ofReal (t : ℝ) :
    Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) =
      -(Real.exp (-Real.pi * t) : ℂ) := by
  have harg : Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I) =
      Real.pi * Complex.I + Real.pi * Complex.I * ((t : ℂ) * Complex.I) := by
    ring
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, exp_pi_I_mul_I_ofReal]
  ring
private theorem angleMap_image :
    (fun t : ℝ ↦ 2 * Real.arctan (Real.exp (Real.pi * t))) '' Set.univ =
      Set.Ioo 0 Real.pi := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    constructor
    · exact mul_pos (by norm_num) (Real.arctan_pos.mpr (Real.exp_pos _))
    · nlinarith [Real.arctan_lt_pi_div_two (Real.exp (Real.pi * t))]
  · intro hx
    rcases hx with ⟨hx0, hxpi⟩
    let t : ℝ := Real.log (Real.tan (x / 2)) / Real.pi
    have hhalf0 : 0 < x / 2 := by linarith
    have hhalfpi : x / 2 < Real.pi / 2 := by linarith
    have htan : 0 < Real.tan (x / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two hhalf0 hhalfpi
    refine ⟨t, Set.mem_univ _, ?_⟩
    dsimp [t]
    rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.exp_log htan,
      Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    ring
private theorem angleMap_injOn :
    Set.InjOn (fun t : ℝ ↦ 2 * Real.arctan (Real.exp (Real.pi * t))) Set.univ := by
  intro x hx y hy hxy
  have hmono : StrictMono (fun t : ℝ ↦ 2 * Real.arctan (Real.exp (Real.pi * t))) := by
    intro u v huv
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    apply Real.arctan_strictMono
    apply Real.exp_strictMono
    exact mul_lt_mul_of_pos_left huv Real.pi_pos
  exact hmono.injective hxy
private theorem angleMap_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ 2 * Real.arctan (Real.exp (Real.pi * t)))
      (Real.pi / Real.cosh (Real.pi * t)) t := by
  have hbase : HasDerivAt
      (fun x : ℝ ↦ Real.arctan (Real.exp (Real.pi * x)))
      ((1 / (1 + Real.exp (Real.pi * t) ^ 2)) *
        (Real.exp (Real.pi * t) * Real.pi)) t := by
    exact (Real.hasDerivAt_arctan (Real.exp (Real.pi * t))).comp t
      ((Real.hasDerivAt_exp (Real.pi * t)).comp t
        (hasDerivAt_const_mul (x := t) Real.pi))
  have hmul := hbase.const_mul 2
  have heq : 2 * ((1 / (1 + Real.exp (Real.pi * t) ^ 2)) *
      (Real.exp (Real.pi * t) * Real.pi)) =
      Real.pi / Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp [ne_of_gt (Real.exp_pos (Real.pi * t))]
    ring
  rw [heq] at hmul
  exact hmul
private theorem integral_angleMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    (∫ x in Set.Ioo (0 : ℝ) Real.pi, g x) =
      ∫ t : ℝ, (Real.pi / Real.cosh (Real.pi * t)) •
        g (2 * Real.arctan (Real.exp (Real.pi * t))) := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun t _ ↦ (angleMap_hasDerivAt t).hasDerivWithinAt)
    angleMap_injOn g
  rw [angleMap_image] at h
  simp only [Measure.restrict_univ] at h
  calc
    (∫ x in Set.Ioo (0 : ℝ) Real.pi, g x) =
        ∫ t : ℝ, |Real.pi / Real.cosh (Real.pi * t)| •
          g (2 * Real.arctan (Real.exp (Real.pi * t))) := h
    _ = ∫ t : ℝ, (Real.pi / Real.cosh (Real.pi * t)) •
          g (2 * Real.arctan (Real.exp (Real.pi * t))) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [abs_of_pos (div_pos Real.pi_pos (Real.cosh_pos _))]
private theorem integral_angleMap_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    (∫ x in Set.Ioo Real.pi (2 * Real.pi), g x) =
      ∫ t : ℝ, (Real.pi / Real.cosh (Real.pi * t)) •
        g (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t))) := by
  have himage :
      (fun t : ℝ ↦ 2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t))) '' Set.univ =
        Set.Ioo Real.pi (2 * Real.pi) := by
    ext x
    constructor
    · rintro ⟨t, -, rfl⟩
      have ht : 2 * Real.arctan (Real.exp (Real.pi * t)) ∈ Set.Ioo 0 Real.pi := by
        rw [← angleMap_image]
        exact ⟨t, Set.mem_univ _, rfl⟩
      change Real.pi < 2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t)) ∧
        2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t)) < 2 * Real.pi
      constructor <;> linarith [ht.1, ht.2]
    · intro hx
      have hy : 2 * Real.pi - x ∈ Set.Ioo 0 Real.pi := by
        constructor <;> linarith [hx.1, hx.2]
      have hy' : 2 * Real.pi - x ∈
          (fun t : ℝ ↦ 2 * Real.arctan (Real.exp (Real.pi * t))) '' Set.univ := by
        simpa only [angleMap_image] using hy
      rcases hy' with ⟨t, -, ht⟩
      refine ⟨t, Set.mem_univ _, ?_⟩
      change 2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t)) = x
      have ht' : 2 * Real.arctan (Real.exp (Real.pi * t)) = 2 * Real.pi - x := by
        simpa only using ht
      rw [ht']
      ring
  have hinj : Set.InjOn
      (fun t : ℝ ↦ 2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t))) Set.univ := by
    intro x hx y hy hxy
    apply angleMap_injOn hx hy
    linarith
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun t _ ↦ ((angleMap_hasDerivAt t).const_sub (2 * Real.pi)).hasDerivWithinAt)
    hinj g
  rw [himage] at h
  simp only [Measure.restrict_univ] at h
  calc
    (∫ x in Set.Ioo Real.pi (2 * Real.pi), g x) =
        ∫ t : ℝ, |-(Real.pi / Real.cosh (Real.pi * t))| •
          g (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t))) := h
    _ = ∫ t : ℝ, (Real.pi / Real.cosh (Real.pi * t)) •
          g (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t))) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [abs_neg, abs_of_pos (div_pos Real.pi_pos (Real.cosh_pos _))]
private theorem circle_average_angleMap_transport
    (G : ℝ → ℝ) (hG : Continuous G) :
    (2 * Real.pi)⁻¹ * (∫ x in (0 : ℝ)..2 * Real.pi, G x) =
      (1 / 2 : ℝ) *
        ((∫ t : ℝ, (Real.cosh (Real.pi * t))⁻¹ *
          G (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t)))) +
          ∫ t : ℝ, (Real.cosh (Real.pi * t))⁻¹ *
            G (2 * Real.arctan (Real.exp (Real.pi * t)))) := by
  have hG₀ : IntervalIntegrable G volume 0 Real.pi := hG.intervalIntegrable _ _
  have hG₁ : IntervalIntegrable G volume Real.pi (2 * Real.pi) :=
    hG.intervalIntegrable _ _
  have hsplit :
      (∫ x in Set.Ioo (0 : ℝ) Real.pi, G x) +
          ∫ x in Set.Ioo Real.pi (2 * Real.pi), G x =
        ∫ x in (0 : ℝ)..2 * Real.pi, G x := by
    calc
      (∫ x in Set.Ioo (0 : ℝ) Real.pi, G x) +
          ∫ x in Set.Ioo Real.pi (2 * Real.pi), G x =
          (∫ x in Set.Ioc (0 : ℝ) Real.pi, G x) +
            ∫ x in Set.Ioc Real.pi (2 * Real.pi), G x := by
          rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
            MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ = (∫ x in (0 : ℝ)..Real.pi, G x) +
            ∫ x in Real.pi..2 * Real.pi, G x := by
          rw [intervalIntegral.integral_of_le (le_of_lt Real.pi_pos),
            intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
      _ = ∫ x in (0 : ℝ)..2 * Real.pi, G x :=
          intervalIntegral.integral_add_adjacent_intervals hG₀ hG₁
  have hleft := integral_angleMap_left G
  have hright := integral_angleMap G
  simp only [smul_eq_mul] at hleft hright
  have hleft_factor :
      (∫ t : ℝ, (Real.pi / Real.cosh (Real.pi * t)) *
          G (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t)))) =
        Real.pi * ∫ t : ℝ, (Real.cosh (Real.pi * t))⁻¹ *
          G (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  have hright_factor :
      (∫ t : ℝ, (Real.pi / Real.cosh (Real.pi * t)) *
          G (2 * Real.arctan (Real.exp (Real.pi * t)))) =
        Real.pi * ∫ t : ℝ, (Real.cosh (Real.pi * t))⁻¹ *
          G (2 * Real.arctan (Real.exp (Real.pi * t))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [← hsplit, hright, hleft, hleft_factor, hright_factor]
  field_simp [Real.pi_ne_zero]
  ring
private theorem cayley_radial_simplify (a r : ℝ)
    (_ha : 0 < a) (hr0 : 0 ≤ r) :
    Complex.I * (1 + (r : ℂ) * ((a - Complex.I) / (a + Complex.I))) /
        (1 - (r : ℂ) * ((a - Complex.I) / (a + Complex.I)) ) =
      Complex.I *
        (((a * (1 + r) : ℝ) : ℂ) + ((1 - r : ℝ) : ℂ) * Complex.I) /
        (((a * (1 - r) : ℝ) : ℂ) + ((1 + r : ℝ) : ℂ) * Complex.I) := by
  have hplus : (a : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hnew : ((a * (1 - r) : ℝ) : ℂ) + ((1 + r : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_add] at hi
    norm_num at hi
    linarith
  have hden : 1 - (r : ℂ) * ((a - Complex.I) / (a + Complex.I)) ≠ 0 := by
    intro h
    have hraw : (a : ℂ) + Complex.I - (r : ℂ) * ((a : ℂ) - Complex.I) = 0 := by
      field_simp [hplus] at h
      simpa using h
    apply hnew
    calc
      ((a * (1 - r) : ℝ) : ℂ) + ((1 + r : ℝ) : ℂ) * Complex.I =
          (a : ℂ) + Complex.I - (r : ℂ) * ((a : ℂ) - Complex.I) := by
            push_cast
            ring
      _ = 0 := hraw
  have hnumEq : 1 + (r : ℂ) * ((a - Complex.I) / (a + Complex.I)) =
      ((((a * (1 + r) : ℝ) : ℂ) + ((1 - r : ℝ) : ℂ) * Complex.I) /
        ((a : ℂ) + Complex.I)) := by
    field_simp [hplus]
    push_cast
    ring
  have hdenEq : 1 - (r : ℂ) * ((a - Complex.I) / (a + Complex.I)) =
      ((((a * (1 - r) : ℝ) : ℂ) + ((1 + r : ℝ) : ℂ) * Complex.I) /
        ((a : ℂ) + Complex.I)) := by
    field_simp [hplus]
    push_cast
    ring
  rw [hnumEq, hdenEq]
  field_simp [hplus, hnew]
private theorem normSq_cayley_radial_boundary (a r : ℝ)
    (ha : 0 < a) (hr0 : 0 ≤ r) :
    Complex.normSq
      (Complex.I * (1 + (r : ℂ) * ((a - Complex.I) / (a + Complex.I))) /
        (1 - (r : ℂ) * ((a - Complex.I) / (a + Complex.I)))) =
      (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2) := by
  rw [cayley_radial_simplify a r ha hr0, Complex.normSq_div, Complex.normSq_mul,
    Complex.normSq_I, Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]
  ring
private theorem cayley_radial_simplify_right (a r : ℝ)
    (hr0 : 0 ≤ r) :
    Complex.I * (1 + (r : ℂ) * (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I))) /
        (1 - (r : ℂ) * (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I))) =
      Complex.I *
        (((a * (1 + r) : ℝ) : ℂ) + ((-(1 - r) : ℝ) : ℂ) * Complex.I) /
        (((a * (1 - r) : ℝ) : ℂ) + ((-(1 + r) : ℝ) : ℂ) * Complex.I) := by
  have hminus : (a : ℂ) - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hnew : ((a * (1 - r) : ℝ) : ℂ) +
      ((-(1 + r) : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_add] at hi
    norm_num at hi
    linarith
  have hden : 1 - (r : ℂ) * (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I)) ≠ 0 := by
    intro h
    have hraw : (a : ℂ) - Complex.I - (r : ℂ) * ((a : ℂ) + Complex.I) = 0 := by
      field_simp [hminus] at h
      simpa using h
    apply hnew
    calc
      ((a * (1 - r) : ℝ) : ℂ) + ((-(1 + r) : ℝ) : ℂ) * Complex.I =
          (a : ℂ) - Complex.I - (r : ℂ) * ((a : ℂ) + Complex.I) := by
            push_cast
            ring
      _ = 0 := hraw
  have hnumEq : 1 + (r : ℂ) * (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I)) =
      ((((a * (1 + r) : ℝ) : ℂ) + ((-(1 - r) : ℝ) : ℂ) * Complex.I) /
        ((a : ℂ) - Complex.I)) := by
    field_simp [hminus]
    push_cast
    ring
  have hdenEq : 1 - (r : ℂ) * (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I)) =
      ((((a * (1 - r) : ℝ) : ℂ) + ((-(1 + r) : ℝ) : ℂ) * Complex.I) /
        ((a : ℂ) - Complex.I)) := by
    field_simp [hminus]
    push_cast
    ring
  rw [hnumEq, hdenEq]
  field_simp [hminus, hnew]
private theorem normSq_cayley_radial_right_boundary (a r : ℝ)
    (hr0 : 0 ≤ r) :
    Complex.normSq
      (Complex.I * (1 + (r : ℂ) * (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I))) /
        (1 - (r : ℂ) * (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I))) ) =
      (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2) := by
  rw [cayley_radial_simplify_right a r hr0, Complex.normSq_div, Complex.normSq_mul,
    Complex.normSq_I, Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]
  ring
private theorem radial_ratio_den_pos (a r : ℝ) (_ha : 0 < a) (hr0 : 0 ≤ r) :
    0 < (1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2 := by
  have hplus : 0 < 1 + r := by linarith
  have hsquare : 0 < (1 + r) ^ 2 := sq_pos_of_pos hplus
  have hother : 0 ≤ a ^ 2 * (1 - r) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith
private theorem radial_ratio_le_one (a r : ℝ) (ha : 0 < a) (hr0 : 0 ≤ r)
    (ha1 : a ≤ 1) :
    (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2) ≤ 1 := by
  apply (div_le_iff₀ (radial_ratio_den_pos a r ha hr0)).mpr
  have hsq : 0 ≤ 1 - a ^ 2 := by
    have hmul : 0 ≤ a * (1 - a) :=
      mul_nonneg ha.le (sub_nonneg.mpr ha1)
    nlinarith
  have hmul : 0 ≤ r * (1 - a ^ 2) := mul_nonneg hr0 hsq
  nlinarith
private theorem radial_ratio_ge_sq (a r : ℝ) (ha : 0 < a) (hr0 : 0 ≤ r)
    (_hr1 : r ≤ 1) (ha1 : a ≤ 1) :
    a ^ 2 ≤ (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2) := by
  apply (le_div_iff₀ (radial_ratio_den_pos a r ha hr0)).mpr
  have hsq : 0 ≤ 1 - a ^ 2 := by
    have hmul : 0 ≤ a * (1 - a) :=
      mul_nonneg ha.le (sub_nonneg.mpr ha1)
    nlinarith
  have hquart : 0 ≤ 1 - a ^ 4 := by
    nlinarith [mul_nonneg hsq (by nlinarith [sq_nonneg a])]
  have hr : 0 ≤ (1 - r) ^ 2 := sq_nonneg _
  have hmul : 0 ≤ (1 - a ^ 4) * (1 - r) ^ 2 := mul_nonneg hquart hr
  nlinarith
private theorem radial_ratio_ge_one (a r : ℝ) (ha : 0 < a) (hr0 : 0 ≤ r)
    (ha1 : 1 ≤ a) :
    1 ≤ (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2) := by
  apply (le_div_iff₀ (radial_ratio_den_pos a r ha hr0)).mpr
  have hsq : 0 ≤ a ^ 2 - 1 := by
    have hmul : 0 ≤ (a - 1) * (a + 1) :=
      mul_nonneg (sub_nonneg.mpr ha1) (by linarith)
    nlinarith
  have hmul : 0 ≤ r * (a ^ 2 - 1) := mul_nonneg hr0 hsq
  nlinarith
private theorem radial_ratio_le_sq (a r : ℝ) (ha : 0 < a) (hr0 : 0 ≤ r)
    (_hr1 : r ≤ 1) (ha1 : 1 ≤ a) :
    (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2) ≤ a ^ 2 := by
  apply (div_le_iff₀ (radial_ratio_den_pos a r ha hr0)).mpr
  have hsq : 0 ≤ a ^ 2 - 1 := by
    have hmul : 0 ≤ (a - 1) * (a + 1) :=
      mul_nonneg (sub_nonneg.mpr ha1) (by linarith)
    nlinarith
  have hquart : 0 ≤ a ^ 4 - 1 := by
    nlinarith [mul_nonneg hsq (by nlinarith [sq_nonneg a])]
  have hr : 0 ≤ (1 - r) ^ 2 := sq_nonneg _
  have hmul : 0 ≤ (a ^ 4 - 1) * (1 - r) ^ 2 := mul_nonneg hquart hr
  nlinarith
private theorem norm_between_of_normSq_radial_ratio (q : ℂ) (a r : ℝ)
    (ha : 0 < a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hnormsq : Complex.normSq q =
      (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2)) :
    min a 1 ≤ ‖q‖ ∧ ‖q‖ ≤ max a 1 := by
  have hsquare : ‖q‖ ^ 2 =
      (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hnormsq
  rcases le_total a 1 with ha1 | ha1
  · have hAlo := radial_ratio_ge_sq a r ha hr0 hr1 ha1
    have hAhi : (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2) ≤ 1 ^ 2 := by
      simpa using radial_ratio_le_one a r ha hr0 ha1
    have hqlo : a ≤ ‖q‖ := by
      apply (sq_le_sq₀ ha.le (norm_nonneg q)).mp
      rw [hsquare]
      exact hAlo
    have hqhi : ‖q‖ ≤ 1 := by
      apply (sq_le_sq₀ (norm_nonneg q) zero_le_one).mp
      rw [hsquare]
      exact hAhi
    constructor
    · simpa [min_eq_left ha1] using hqlo
    · simpa [max_eq_right ha1] using hqhi
  · have hAlo : 1 ^ 2 ≤ (a ^ 2 * (1 + r) ^ 2 + (1 - r) ^ 2) /
        ((1 + r) ^ 2 + a ^ 2 * (1 - r) ^ 2) := by
      simpa using radial_ratio_ge_one a r ha hr0 ha1
    have hAhi := radial_ratio_le_sq a r ha hr0 hr1 ha1
    have hqlo : 1 ≤ ‖q‖ := by
      apply (sq_le_sq₀ zero_le_one (norm_nonneg q)).mp
      rw [hsquare]
      exact hAlo
    have hqhi : ‖q‖ ≤ a := by
      apply (sq_le_sq₀ (norm_nonneg q) ha.le).mp
      rw [hsquare]
      exact hAhi
    constructor
    · simpa [min_eq_right ha1] using hqlo
    · simpa [max_eq_left ha1] using hqhi
private theorem abs_log_norm_of_between (q : ℂ) (a : ℝ) (ha : 0 < a)
    (hlow : min a 1 ≤ ‖q‖) (hhigh : ‖q‖ ≤ max a 1) :
    |Real.log ‖q‖| ≤ |Real.log a| := by
  rcases le_total a 1 with ha1 | ha1
  · have hlow' : a ≤ ‖q‖ := by simpa [min_eq_left ha1] using hlow
    have hhigh' : ‖q‖ ≤ 1 := by simpa [max_eq_right ha1] using hhigh
    have hloga : Real.log a ≤ 0 := Real.log_nonpos ha.le ha1
    have hlogq0 : Real.log ‖q‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hhigh'
    have hlogaq : Real.log a ≤ Real.log ‖q‖ := Real.log_le_log ha hlow'
    rw [abs_of_nonpos hloga]
    apply abs_le.mpr
    constructor <;> linarith
  · have hlow' : 1 ≤ ‖q‖ := by simpa [min_eq_right ha1] using hlow
    have hhigh' : ‖q‖ ≤ a := by simpa [max_eq_left ha1] using hhigh
    have hloga : 0 ≤ Real.log a := Real.log_nonneg ha1
    have hlogq0 : 0 ≤ Real.log ‖q‖ := Real.log_nonneg hlow'
    have hlogqa : Real.log ‖q‖ ≤ Real.log a :=
      Real.log_le_log (lt_of_lt_of_le Real.zero_lt_one hlow') hhigh'
    rw [abs_of_nonneg hloga]
    apply abs_le.mpr
    constructor <;> linarith
private theorem abs_log_norm_cayley_radial_boundary_le (a r : ℝ)
    (ha : 0 < a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.log ‖Complex.I * (1 + (r : ℂ) * ((a - Complex.I) / (a + Complex.I))) /
        (1 - (r : ℂ) * ((a - Complex.I) / (a + Complex.I)))‖| ≤ |Real.log a| := by
  obtain ⟨hlow, hhigh⟩ := norm_between_of_normSq_radial_ratio _ a r ha hr0 hr1
    (normSq_cayley_radial_boundary a r ha hr0)
  exact abs_log_norm_of_between _ a ha hlow hhigh
private theorem abs_log_norm_cayley_radial_right_boundary_le (a r : ℝ)
    (ha : 0 < a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.log ‖Complex.I * (1 + (r : ℂ) * (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I))) /
        (1 - (r : ℂ) * (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I)))‖| ≤ |Real.log a| := by
  obtain ⟨hlow, hhigh⟩ := norm_between_of_normSq_radial_ratio _ a r ha hr0 hr1
    (normSq_cayley_radial_right_boundary a r hr0)
  exact abs_log_norm_of_between _ a ha hlow hhigh
private theorem im_log_div_pi_I (q : ℂ) :
    (Complex.log q / (Real.pi * Complex.I)).im = -Real.log ‖q‖ / Real.pi := by
  rw [Complex.div_im, Complex.log_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, Complex.normSq_apply,
    Complex.mul_im, zero_add]
  field_simp [Real.pi_ne_zero]
  ring
private theorem abs_im_log_div_pi_I_le (q : ℂ) (t : ℝ)
    (h : |Real.log ‖q‖| ≤ Real.pi * |t|) :
    |(Complex.log q / (Real.pi * Complex.I)).im| ≤ |t| := by
  rw [im_log_div_pi_I, abs_div, abs_neg, abs_of_pos Real.pi_pos]
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith
private theorem abs_log_norm_cayley_radial_boundary_exp_le (r t : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.log ‖(Complex.I *
        (1 + (r : ℂ) * (((Real.exp (-Real.pi * t) : ℝ) - Complex.I) /
          ((Real.exp (-Real.pi * t) : ℝ) + Complex.I)))) /
        (1 - (r : ℂ) * (((Real.exp (-Real.pi * t) : ℝ) - Complex.I) /
          ((Real.exp (-Real.pi * t) : ℝ) + Complex.I)))‖| ≤ Real.pi * |t| := by
  have h := abs_log_norm_cayley_radial_boundary_le
    (Real.exp (-Real.pi * t)) r (Real.exp_pos _) hr0 hr1
  rw [Real.log_exp] at h
  simpa [abs_mul, abs_of_pos Real.pi_pos] using h
private theorem im_discToStrip_radial_left_le (r t : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |(Complex.log (Complex.I *
        (1 + (r : ℂ) *
          ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I))) /
        (1 - (r : ℂ) *
          ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)))) /
      (Real.pi * Complex.I)).im| ≤ |t| := by
  rw [exp_pi_I_mul_I_ofReal]
  apply abs_im_log_div_pi_I_le
  exact abs_log_norm_cayley_radial_boundary_exp_le r t hr0 hr1
private theorem neg_cayley_boundary (a : ℝ) :
    ((-(a : ℂ) - Complex.I) / (-(a : ℂ) + Complex.I)) =
      (((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I)) := by
  have hnum : -(a : ℂ) - Complex.I = -((a : ℂ) + Complex.I) := by ring
  have hden : -(a : ℂ) + Complex.I = -((a : ℂ) - Complex.I) := by ring
  rw [hnum, hden, neg_div_neg_eq]
private theorem abs_log_norm_cayley_radial_right_boundary_exp_le (r t : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.log ‖(Complex.I *
        (1 + (r : ℂ) * (((Real.exp (-Real.pi * t) : ℝ) + Complex.I) /
          ((Real.exp (-Real.pi * t) : ℝ) - Complex.I)))) /
        (1 - (r : ℂ) * (((Real.exp (-Real.pi * t) : ℝ) + Complex.I) /
          ((Real.exp (-Real.pi * t) : ℝ) - Complex.I)))‖| ≤ Real.pi * |t| := by
  have h := abs_log_norm_cayley_radial_right_boundary_le
    (Real.exp (-Real.pi * t)) r (Real.exp_pos _) hr0 hr1
  rw [Real.log_exp] at h
  simpa [abs_mul, abs_of_pos Real.pi_pos] using h
private theorem im_discToStrip_radial_right_le (r t : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |(Complex.log (Complex.I *
        (1 + (r : ℂ) *
          ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I))) /
        (1 - (r : ℂ) *
          ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)))) /
      (Real.pi * Complex.I)).im| ≤ |t| := by
  rw [exp_pi_I_one_add_I_ofReal, neg_cayley_boundary]
  apply abs_im_log_div_pi_I_le
  exact abs_log_norm_cayley_radial_right_boundary_exp_le r t hr0 hr1
private theorem normSq_u_plus_I
    (u : ℂ) (c s : ℝ) (hure : u.re = c) (huim : u.im = s)
    (hunorm : Complex.normSq u = 1) :
    Complex.normSq (u + Complex.I) = 2 + 2 * s := by
  rw [Complex.normSq_apply] at hunorm ⊢
  simp only [Complex.add_re, Complex.I_re, add_zero, Complex.add_im, Complex.I_im]
  rw [hure, huim] at hunorm ⊢
  nlinarith
private theorem normSq_u_sub_I
    (u : ℂ) (c s : ℝ) (hure : u.re = c) (huim : u.im = s)
    (hunorm : Complex.normSq u = 1) :
    Complex.normSq (u - Complex.I) = 2 - 2 * s := by
  rw [Complex.normSq_apply] at hunorm ⊢
  simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im]
  rw [hure, huim] at hunorm ⊢
  nlinarith
private theorem normSq_r_plus_I (r : ℝ) :
    Complex.normSq ((r : ℂ) + Complex.I) = r ^ 2 + 1 := by
  rw [Complex.normSq_apply]
  simp
  ring
private theorem cayley_diff_left (u : ℂ) (r : ℝ)
    (hpu : u + Complex.I ≠ 0) (hpr : (r : ℂ) + Complex.I ≠ 0) :
    ((r - Complex.I) / (r + Complex.I) - (u - Complex.I) / (u + Complex.I)) =
      (2 * Complex.I * (r - u)) / (((r : ℂ) + Complex.I) * (u + Complex.I)) := by
  field_simp [hpu, hpr]
  ring
private theorem normSq_r_sub_u
    (u : ℂ) (r c s : ℝ) (hure : u.re = c) (huim : u.im = s)
    (hunorm : Complex.normSq u = 1) :
    Complex.normSq ((r : ℂ) - u) = r ^ 2 - 2 * r * c + 1 := by
  rw [Complex.normSq_apply] at hunorm ⊢
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  rw [hure, huim] at hunorm ⊢
  nlinarith
private theorem normSq_cayley_interior
    (u : ℂ) (c s : ℝ) (hure : u.re = c) (huim : u.im = s)
    (hunorm : Complex.normSq u = 1) :
    Complex.normSq ((u - Complex.I) / (u + Complex.I)) =
      (2 - 2 * s) / (2 + 2 * s) := by
  rw [Complex.normSq_div, normSq_u_sub_I u c s hure huim hunorm,
    normSq_u_plus_I u c s hure huim hunorm]
private theorem normSq_cayley_diff_left
    (u : ℂ) (r c s : ℝ) (hure : u.re = c) (huim : u.im = s)
    (hunorm : Complex.normSq u = 1) (hs : 0 < s) :
    Complex.normSq ((r - Complex.I) / (r + Complex.I) -
          (u - Complex.I) / (u + Complex.I)) =
      4 * (r ^ 2 - 2 * r * c + 1) / ((r ^ 2 + 1) * (2 + 2 * s)) := by
  have hpu : u + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
    rw [huim] at hi
    linarith
  have hpr : (r : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have htwo : Complex.normSq (2 : ℂ) = 4 := by
    norm_num [Complex.normSq_apply]
  rw [cayley_diff_left u r hpu hpr, Complex.normSq_div, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_mul, htwo, Complex.normSq_I,
    normSq_r_sub_u u r c s hure huim hunorm,
    normSq_r_plus_I r, normSq_u_plus_I u c s hure huim hunorm]
  ring
private theorem cayley_poisson_left_normSq
    (u : ℂ) (r c s : ℝ) (hure : u.re = c) (huim : u.im = s)
    (hunorm : Complex.normSq u = 1) (hs : 0 < s) :
    (1 - Complex.normSq ((u - Complex.I) / (u + Complex.I))) /
        Complex.normSq ((r - Complex.I) / (r + Complex.I) -
          (u - Complex.I) / (u + Complex.I)) =
      s * (r ^ 2 + 1) / (r ^ 2 - 2 * r * c + 1) := by
  rw [normSq_cayley_interior u c s hure huim hunorm,
    normSq_cayley_diff_left u r c s hure huim hunorm hs]
  have hplus : 0 < 2 + 2 * s := by linarith
  have hrplus : 0 < r ^ 2 + 1 := by positivity
  have hden : 0 < r ^ 2 - 2 * r * c + 1 := by
    rw [show r ^ 2 - 2 * r * c + 1 = (r - c) ^ 2 + s ^ 2 by
      rw [← hunorm]
      simp only [Complex.normSq_apply, hure, huim]
      ring]
    positivity
  field_simp [ne_of_gt hplus, ne_of_gt hrplus, ne_of_gt hden]
  ring
private theorem cayley_poisson_left_trig (a r : ℝ) (hs : 0 < Real.sin a) :
    (1 - Complex.normSq (((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I - Complex.I) /
          ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I + Complex.I))) /
        Complex.normSq ((r - Complex.I) / (r + Complex.I) -
          ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I - Complex.I) /
            ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I + Complex.I)) =
      Real.sin a * (r ^ 2 + 1) / (r ^ 2 - 2 * r * Real.cos a + 1) := by
  let u : ℂ := (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I
  have hure : u.re = Real.cos a := by
    dsimp only [u]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have huim : u.im = Real.sin a := by
    dsimp only [u]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_add]
    ring
  have hunorm : Complex.normSq u = 1 := by
    change Complex.normSq ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I) = 1
    rw [Complex.normSq_add_mul_I]
    exact Real.cos_sq_add_sin_sq a
  exact cayley_poisson_left_normSq u r (Real.cos a) (Real.sin a) hure huim hunorm hs
private theorem cosh_eq_exp_neg_sq_div (x : ℝ) :
    Real.cosh x = (Real.exp (-x) ^ 2 + 1) / (2 * Real.exp (-x)) := by
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp [ne_of_gt (Real.exp_pos x)]
  ring
private theorem denom_trig_pos (a r : ℝ) (hs : 0 < Real.sin a) :
    0 < r ^ 2 - 2 * r * Real.cos a + 1 := by
  rw [show r ^ 2 - 2 * r * Real.cos a + 1 =
      (r - Real.cos a) ^ 2 + Real.sin a ^ 2 by
    nlinarith [Real.cos_sq_add_sin_sq a]]
  positivity
private theorem exp_rational_eq_cosh (x c : ℝ)
    (hden : 0 < Real.exp (-x) ^ 2 - 2 * Real.exp (-x) * c + 1) :
    (Real.exp (-x) ^ 2 + 1) /
        (Real.exp (-x) ^ 2 - 2 * Real.exp (-x) * c + 1) =
      Real.cosh x / (Real.cosh x - c) := by
  have hr : 0 < Real.exp (-x) := Real.exp_pos _
  have hcm : 0 < (Real.exp (-x) ^ 2 + 1) / (2 * Real.exp (-x)) - c := by
    rw [show (Real.exp (-x) ^ 2 + 1) / (2 * Real.exp (-x)) - c =
      (Real.exp (-x) ^ 2 - 2 * Real.exp (-x) * c + 1) /
        (2 * Real.exp (-x)) by
      field_simp [ne_of_gt hr]
      ring]
    exact div_pos hden (by positivity)
  rw [cosh_eq_exp_neg_sq_div]
  field_simp [ne_of_gt hr, ne_of_gt hden, ne_of_gt hcm]
  ring
private theorem cayley_poisson_left_hyperbolic (a t : ℝ)
    (hs : 0 < Real.sin a) :
    (1 - Complex.normSq (((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I - Complex.I) /
          ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I + Complex.I))) /
        Complex.normSq ((Real.exp (-Real.pi * t) - Complex.I) /
            (Real.exp (-Real.pi * t) + Complex.I) -
          ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I - Complex.I) /
            ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I + Complex.I)) =
      Real.sin a * Real.cosh (Real.pi * t) /
        (Real.cosh (Real.pi * t) - Real.cos a) := by
  have hden : 0 < Real.exp (-Real.pi * t) ^ 2 -
      2 * Real.exp (-Real.pi * t) * Real.cos a + 1 :=
    denom_trig_pos a (Real.exp (-Real.pi * t)) hs
  rw [cayley_poisson_left_trig a (Real.exp (-Real.pi * t)) hs]
  have hratio : (Real.exp (-Real.pi * t) ^ 2 + 1) /
      (Real.exp (-Real.pi * t) ^ 2 - 2 * Real.exp (-Real.pi * t) * Real.cos a + 1) =
      Real.cosh (Real.pi * t) / (Real.cosh (Real.pi * t) - Real.cos a) := by
    convert exp_rational_eq_cosh (Real.pi * t) (Real.cos a) (by simpa using hden) using 1
    all_goals ring_nf
  calc
    Real.sin a * (Real.exp (-Real.pi * t) ^ 2 + 1) /
        (Real.exp (-Real.pi * t) ^ 2 - 2 * Real.exp (-Real.pi * t) * Real.cos a + 1) =
        Real.sin a * ((Real.exp (-Real.pi * t) ^ 2 + 1) /
          (Real.exp (-Real.pi * t) ^ 2 - 2 * Real.exp (-Real.pi * t) * Real.cos a + 1)) := by ring
    _ = Real.sin a * (Real.cosh (Real.pi * t) /
          (Real.cosh (Real.pi * t) - Real.cos a)) := by rw [hratio]
    _ = Real.sin a * Real.cosh (Real.pi * t) /
          (Real.cosh (Real.pi * t) - Real.cos a) := by ring
private theorem denom_trig_pos_right (a r : ℝ) (hs : 0 < Real.sin a) :
    0 < r ^ 2 + 2 * r * Real.cos a + 1 := by
  rw [show r ^ 2 + 2 * r * Real.cos a + 1 =
      (r + Real.cos a) ^ 2 + Real.sin a ^ 2 by
    nlinarith [Real.cos_sq_add_sin_sq a]]
  positivity
private theorem cayley_poisson_right_hyperbolic (a t : ℝ)
    (hs : 0 < Real.sin a) :
    (1 - Complex.normSq (((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I - Complex.I) /
          ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I + Complex.I))) /
        Complex.normSq ((-Real.exp (-Real.pi * t) - Complex.I) /
            (-Real.exp (-Real.pi * t) + Complex.I) -
          ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I - Complex.I) /
            ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I + Complex.I)) =
      Real.sin a * Real.cosh (Real.pi * t) /
        (Real.cosh (Real.pi * t) + Real.cos a) := by
  have hden : 0 < Real.exp (-Real.pi * t) ^ 2 +
      2 * Real.exp (-Real.pi * t) * Real.cos a + 1 :=
    denom_trig_pos_right a (Real.exp (-Real.pi * t)) hs
  have hneg : -(Real.exp (-Real.pi * t) : ℂ) =
      ((-Real.exp (-Real.pi * t) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hneg, cayley_poisson_left_trig a (-Real.exp (-Real.pi * t)) hs]
  have hratio : (Real.exp (-Real.pi * t) ^ 2 + 1) /
      (Real.exp (-Real.pi * t) ^ 2 +
        2 * Real.exp (-Real.pi * t) * Real.cos a + 1) =
      Real.cosh (Real.pi * t) /
        (Real.cosh (Real.pi * t) + Real.cos a) := by
    convert exp_rational_eq_cosh (Real.pi * t) (-Real.cos a) (by simpa using hden) using 1
    all_goals ring_nf
  calc
    Real.sin a * ((-Real.exp (-Real.pi * t)) ^ 2 + 1) /
        ((-Real.exp (-Real.pi * t)) ^ 2 - 2 * (-Real.exp (-Real.pi * t)) *
          Real.cos a + 1) =
        Real.sin a * ((Real.exp (-Real.pi * t) ^ 2 + 1) /
          (Real.exp (-Real.pi * t) ^ 2 +
            2 * Real.exp (-Real.pi * t) * Real.cos a + 1)) := by ring
    _ = Real.sin a * (Real.cosh (Real.pi * t) /
          (Real.cosh (Real.pi * t) + Real.cos a)) := by rw [hratio]
    _ = Real.sin a * Real.cosh (Real.pi * t) /
          (Real.cosh (Real.pi * t) + Real.cos a) := by ring
private theorem exp_pi_I_ofReal (x : ℝ) :
    Complex.exp (Real.pi * Complex.I * (x : ℂ)) =
      (Real.cos (Real.pi * x) : ℂ) + (Real.sin (Real.pi * x) : ℂ) * Complex.I := by
  have harg : Real.pi * Complex.I * (x : ℂ) = (Real.pi * x : ℝ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
private theorem stripToDisc_left_kernel {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (t : ℝ) :
    (1 - Complex.normSq
        ((Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
          (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I))) /
      Complex.normSq
        ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
          (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I) -
          (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)) /
      (2 * Real.cosh (Real.pi * t)) =
        Real.sin (Real.pi * θ) /
          (2 * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
  have harg0 : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ.1
  have harg1 : Real.pi * θ < Real.pi := by
    nlinarith [mul_lt_mul_of_pos_left hθ.2 Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi harg0 harg1
  rw [exp_pi_I_ofReal θ, exp_pi_I_mul_I_ofReal t,
    cayley_poisson_left_hyperbolic (Real.pi * θ) t hs]
  have hcoslt : Real.cos (Real.pi * θ) < 1 := by
    have hsq : Real.cos (Real.pi * θ) ^ 2 < 1 := by
      nlinarith [Real.cos_sq_add_sin_sq (Real.pi * θ), sq_pos_of_pos hs]
    nlinarith [sq_nonneg (Real.cos (Real.pi * θ) + 1)]
  have hcosh_one : 1 ≤ Real.cosh (Real.pi * t) := by
    have hsq : 1 ≤ Real.cosh (Real.pi * t) ^ 2 := by
      rw [Real.cosh_sq']
      nlinarith [sq_nonneg (Real.sinh (Real.pi * t))]
    have hnonneg : 0 ≤ Real.cosh (Real.pi * t) := (Real.cosh_pos _).le
    nlinarith
  have hden : 0 < Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ) := by
    linarith
  field_simp [ne_of_gt (Real.cosh_pos _), ne_of_gt hden]
private theorem stripToDisc_right_kernel {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (t : ℝ) :
    (1 - Complex.normSq
        ((Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
          (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I))) /
      Complex.normSq
        ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
          (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I) -
          (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)) /
      (2 * Real.cosh (Real.pi * t)) =
        Real.sin (Real.pi * θ) /
          (2 * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
  have harg0 : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ.1
  have harg1 : Real.pi * θ < Real.pi := by
    nlinarith [mul_lt_mul_of_pos_left hθ.2 Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi harg0 harg1
  rw [exp_pi_I_ofReal θ, exp_pi_I_one_add_I_ofReal t,
    cayley_poisson_right_hyperbolic (Real.pi * θ) t hs]
  have hcosgt : -1 < Real.cos (Real.pi * θ) := by
    have hsq : Real.cos (Real.pi * θ) ^ 2 < 1 := by
      nlinarith [Real.cos_sq_add_sin_sq (Real.pi * θ), sq_pos_of_pos hs]
    nlinarith [sq_nonneg (Real.cos (Real.pi * θ) - 1)]
  have hcosh_one : 1 ≤ Real.cosh (Real.pi * t) := by
    have hsq : 1 ≤ Real.cosh (Real.pi * t) ^ 2 := by
      rw [Real.cosh_sq']
      nlinarith [sq_nonneg (Real.sinh (Real.pi * t))]
    have hnonneg : 0 ≤ Real.cosh (Real.pi * t) := (Real.cosh_pos _).le
    nlinarith
  have hden : 0 < Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ) := by
    linarith
  field_simp [ne_of_gt (Real.cosh_pos _), ne_of_gt hden]
private theorem cos_two_arctan (x : ℝ) :
    Real.cos (2 * Real.arctan x) = (1 - x ^ 2) / (1 + x ^ 2) := by
  have hD : 0 < 1 + x ^ 2 := by positivity
  have hsqrt : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hD.le
  rw [Real.cos_two_mul, Real.cos_arctan]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hD)]
  nlinarith
private theorem sin_two_arctan (x : ℝ) :
    Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ 2) := by
  have hD : 0 < 1 + x ^ 2 := by positivity
  have hsqrt : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hD.le
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hD)]
  rw [hsqrt]
private theorem exp_two_arctan (x : ℝ) :
    Complex.exp (((2 * Real.arctan x : ℝ) : ℂ) * Complex.I) =
      ((1 : ℂ) + (x : ℂ) * Complex.I) / ((1 : ℂ) - (x : ℂ) * Complex.I) := by
  have hD : 0 < 1 + x ^ 2 := by positivity
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · rw [Complex.div_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.mul_im, Complex.add_im, zero_mul, one_mul,
      mul_zero, zero_add, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      sub_zero, Complex.normSq_apply]
    rw [cos_two_arctan]
    field_simp [hD.ne']
    ring
  · rw [Complex.div_im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.add_re, zero_mul, one_mul,
      mul_zero, zero_add, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      sub_zero, Complex.normSq_apply]
    rw [sin_two_arctan]
    field_simp [hD.ne']
    ring
private theorem circle_rational_inv (x : ℝ) (hx : x ≠ 0) :
    ((1 : ℂ) + (x : ℂ) * Complex.I) / ((1 : ℂ) - (x : ℂ) * Complex.I) =
      (((x⁻¹ : ℝ) : ℂ) + Complex.I) / (((x⁻¹ : ℝ) : ℂ) - Complex.I) := by
  have hleft : (1 : ℂ) - (x : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, zero_mul, Complex.zero_im,
      sub_eq_zero] at hi
    apply hx
    linarith
  have hright : ((x⁻¹ : ℝ) : ℂ) - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  apply (div_eq_div_iff hleft hright).mpr
  push_cast
  field_simp [hx]
private theorem exp_two_ofReal_arctan (x : ℝ) :
    Complex.exp (2 * (Real.arctan x : ℂ) * Complex.I) =
      ((1 : ℂ) + (x : ℂ) * Complex.I) / ((1 : ℂ) - (x : ℂ) * Complex.I) := by
  convert exp_two_arctan x using 1; push_cast; ring
private theorem circleMap_angleMap_eq_right (t : ℝ) :
    circleMap 0 1 (2 * Real.arctan (Real.exp (Real.pi * t))) =
      (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
        (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I) := by
  have hx : Real.exp (Real.pi * t) ≠ 0 := (Real.exp_pos _).ne'
  have hneg : Real.exp (-Real.pi * t) = (Real.exp (Real.pi * t))⁻¹ := by
    rw [show -Real.pi * t = -(Real.pi * t) by ring, Real.exp_neg]
  rw [circleMap_zero]
  norm_num
  rw [exp_two_ofReal_arctan, exp_pi_I_one_add_I_ofReal, neg_cayley_boundary, hneg]
  exact circle_rational_inv _ hx
private theorem exp_neg_two_ofReal_arctan (x : ℝ) :
    Complex.exp (-(2 * (Real.arctan x : ℂ) * Complex.I)) =
      ((1 : ℂ) - (x : ℂ) * Complex.I) / ((1 : ℂ) + (x : ℂ) * Complex.I) := by
  rw [Complex.exp_neg, exp_two_ofReal_arctan, inv_div]
private theorem circle_rational_neg_inv (x : ℝ) (hx : x ≠ 0) :
    ((1 : ℂ) - (x : ℂ) * Complex.I) / ((1 : ℂ) + (x : ℂ) * Complex.I) =
      (((x⁻¹ : ℝ) : ℂ) - Complex.I) / (((x⁻¹ : ℝ) : ℂ) + Complex.I) := by
  have hleft : (1 : ℂ) + (x : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, zero_add, zero_mul,
      Complex.zero_im, add_eq_zero_iff_eq_neg] at hi
    apply hx
    linarith
  have hright : ((x⁻¹ : ℝ) : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  apply (div_eq_div_iff hleft hright).mpr
  push_cast
  field_simp [hx]
private theorem circleMap_angleMap_eq_left (t : ℝ) :
    circleMap 0 1 (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t))) =
      (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
        (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I) := by
  have hx : Real.exp (Real.pi * t) ≠ 0 := (Real.exp_pos _).ne'
  have hneg : Real.exp (-Real.pi * t) = (Real.exp (Real.pi * t))⁻¹ := by
    rw [show -Real.pi * t = -(Real.pi * t) by ring, Real.exp_neg]
  rw [circleMap_zero]
  norm_num
  have harg :
      (2 * (Real.pi : ℂ) - 2 * (Real.arctan (Real.exp (Real.pi * t)) : ℂ)) * Complex.I =
        2 * (Real.pi : ℂ) * Complex.I -
          (2 * (Real.arctan (Real.exp (Real.pi * t)) : ℂ) * Complex.I) := by
    ring
  rw [harg, Complex.exp_sub, Complex.exp_two_pi_mul_I]
  simp only [one_div]
  rw [← Complex.exp_neg, exp_neg_two_ofReal_arctan,
    exp_pi_I_mul_I_ofReal, hneg]
  exact circle_rational_neg_inv _ hx
private theorem circleMap_neg_angleMap_eq_left (t : ℝ) :
    circleMap 0 1 (-(2 * Real.arctan (Real.exp (Real.pi * t)))) =
      (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
        (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I) := by
  have hperiod := periodic_circleMap 0 1 (-(2 * Real.arctan (Real.exp (Real.pi * t))))
  rw [show -(2 * Real.arctan (Real.exp (Real.pi * t))) + 2 * Real.pi =
      2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t)) by ring] at hperiod
  exact hperiod.symm.trans (circleMap_angleMap_eq_left t)
private theorem cayleyInverse_cayley_real (a : ℝ) :
    Complex.I * (1 + ((a : ℂ) - Complex.I) / ((a : ℂ) + Complex.I)) /
        (1 - ((a : ℂ) - Complex.I) / ((a : ℂ) + Complex.I)) = (a : ℂ) := by
  have hplus : (a : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hden : 1 - ((a : ℂ) - Complex.I) / ((a : ℂ) + Complex.I) ≠ 0 := by
    intro h
    field_simp [hplus] at h
    norm_num at h
  field_simp [hplus, hden]
  ring
private theorem discToStrip_left_boundary_eq (t : ℝ) :
    (Complex.log
      (Complex.I *
        (1 + ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
          (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I))) /
        (1 - ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
          (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I))))) /
      (Real.pi * Complex.I) = (t : ℂ) * Complex.I := by
  have hExp : Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) =
      (Real.exp (-Real.pi * t) : ℂ) := exp_pi_I_mul_I_ofReal t
  simp only [hExp]
  rw [cayleyInverse_cayley_real (Real.exp (-Real.pi * t))]
  rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  field_simp [Real.pi_ne_zero]
  rw [Complex.I_sq]
  push_cast
  ring
private theorem tendsto_discToStrip_radial_left
    {α : Type*} {l : Filter α} (r : α → ℝ)
    (hr : Tendsto r l (𝓝 1))
    (_hrange : ∀ᶠ x in l, 0 ≤ r x ∧ r x < 1) (t : ℝ) :
    let b : ℂ :=
      (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
        (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)
    Tendsto
      (fun x ↦ Complex.log (Complex.I * (1 + (r x : ℂ) * b) /
        (1 - (r x : ℂ) * b)) / (Real.pi * Complex.I)) l
      (𝓝 ((t : ℂ) * Complex.I)) := by
  dsimp only
  let b : ℂ :=
    (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)
  let q : ℂ → ℂ := fun z ↦ Complex.I * (1 + z) / (1 - z)
  have hqEval : q b = (Real.exp (-Real.pi * t) : ℂ) := by
    dsimp [q, b]
    rw [exp_pi_I_mul_I_ofReal, cayleyInverse_cayley_real]
  have hden : 1 - b ≠ 0 := by
    intro h
    have hqzero : q b = 0 := by
      dsimp [q]
      rw [h]
      norm_num
    rw [hqEval] at hqzero
    exact (Real.exp_pos _).ne' (Complex.ofReal_eq_zero.mp hqzero)
  have hqcont : ContinuousAt q b := by
    dsimp [q]
    fun_prop (disch := exact hden)
  have hslit : q b ∈ Complex.slitPlane := by
    rw [hqEval]
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (by
      rw [Complex.ofReal_re]
      exact Real.exp_pos (-Real.pi * t))
  have hcont : ContinuousAt (fun z ↦ Complex.log (q z) / (Real.pi * Complex.I)) b :=
    (hqcont.clog hslit).div_const _
  have hrad : Tendsto (fun x ↦ (r x : ℂ) * b) l (𝓝 b) := by
    have hlin : Continuous (fun s : ℝ ↦ (s : ℂ) * b) := by fun_prop
    simpa [Function.comp_def] using hlin.continuousAt.tendsto.comp hr
  have hlim : Tendsto
      (fun x ↦ Complex.log (q ((r x : ℂ) * b)) / (Real.pi * Complex.I)) l
      (𝓝 (Complex.log (q b) / (Real.pi * Complex.I))) := by
    simpa [Function.comp_def] using hcont.tendsto.comp hrad
  dsimp [q] at hlim
  rw [show Complex.log (Complex.I * (1 + b) / (1 - b)) /
      (Real.pi * Complex.I) = (t : ℂ) * Complex.I by
    dsimp [b]
    exact discToStrip_left_boundary_eq t] at hlim
  exact hlim
private theorem tendsto_discToStrip_radial_right
    {α : Type*} {l : Filter α} (r : α → ℝ)
    (hr : Tendsto r l (𝓝 1))
    (hrange : ∀ᶠ x in l, 0 ≤ r x ∧ r x < 1) (t : ℝ) :
    let b : ℂ :=
      (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
        (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)
    Tendsto
      (fun x ↦ Complex.log (Complex.I * (1 + (r x : ℂ) * b) /
        (1 - (r x : ℂ) * b)) / (Real.pi * Complex.I)) l
      (𝓝 (1 + (t : ℂ) * Complex.I)) := by
  dsimp only
  let b : ℂ :=
    (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)
  let q : ℂ → ℂ := fun z ↦ Complex.I * (1 + z) / (1 - z)
  have hqEval : q b = -(Real.exp (-Real.pi * t) : ℂ) := by
    dsimp [q, b]
    rw [exp_pi_I_one_add_I_ofReal]
    convert cayleyInverse_cayley_real (-Real.exp (-Real.pi * t)) using 1 <;>
      push_cast <;> ring
  have hb : ‖b‖ = 1 := by
    dsimp [b]
    rw [← circleMap_angleMap_eq_right t]
    simp
  have hden : 1 - b ≠ 0 := by
    intro h
    have hqzero : q b = 0 := by
      dsimp [q]
      rw [h]
      norm_num
    rw [hqEval] at hqzero
    exact (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.exp_pos _)))) hqzero
  have hqcont : ContinuousAt q b := by
    dsimp [q]
    fun_prop (disch := exact hden)
  have hrad : Tendsto (fun x ↦ (r x : ℂ) * b) l (𝓝 b) := by
    have hlin : Continuous (fun s : ℝ ↦ (s : ℂ) * b) := by fun_prop
    simpa [Function.comp_def] using hlin.continuousAt.tendsto.comp hr
  have hq : Tendsto (fun x ↦ q ((r x : ℂ) * b)) l
      (𝓝 (-(Real.exp (-Real.pi * t) : ℂ))) := by
    rw [← hqEval]
    simpa [Function.comp_def] using hqcont.tendsto.comp hrad
  have hins : ∀ᶠ x in l, ‖(r x : ℂ) * b‖ < 1 := by
    filter_upwards [hrange] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1, hb]
    simpa using hx.2
  have him : ∀ᶠ x in l, 0 ≤ (q ((r x : ℂ) * b)).im := by
    filter_upwards [hins] with x hx
    exact (cayleyInverse_im_pos hx).le
  have hqWithin : Tendsto (fun x ↦ q ((r x : ℂ) * b)) l
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-(Real.exp (-Real.pi * t) : ℂ))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq, him⟩
  have hre : (-(Real.exp (-Real.pi * t) : ℂ)).re < 0 := by
    rw [Complex.neg_re, Complex.ofReal_re]
    exact neg_lt_zero.mpr (Real.exp_pos _)
  have himeq : (-(Real.exp (-Real.pi * t) : ℂ)).im = 0 := by
    rw [Complex.neg_im, Complex.ofReal_im]
    simp
  have hlog :=
    (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre himeq).comp hqWithin
  have hdiv : Tendsto
      (fun x ↦ Complex.log (q ((r x : ℂ) * b)) / (Real.pi * Complex.I)) l
      (𝓝 ((Real.log ‖(-(Real.exp (-Real.pi * t) : ℂ))‖ + Real.pi * Complex.I) /
        (Real.pi * Complex.I))) := by
    have hcont : Continuous (fun z : ℂ ↦ z / (Real.pi * Complex.I)) := by fun_prop
    simpa [Function.comp_def] using hcont.continuousAt.tendsto.comp hlog
  dsimp [q] at hdiv
  have hvalue :
      (Real.log ‖(-(Real.exp (-Real.pi * t) : ℂ))‖ + Real.pi * Complex.I) /
        (Real.pi * Complex.I) = 1 + (t : ℂ) * Complex.I := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.log_exp]
    field_simp [Real.pi_ne_zero]
    have hII : Complex.I * (Complex.I * (t : ℂ)) = -(t : ℂ) := by
      rw [← mul_assoc]
      norm_num
    rw [mul_add, mul_one, mul_assoc, hII]
    push_cast
    ring
  rw [hvalue] at hdiv
  exact hdiv
private theorem radialSequence_nonneg (n : ℕ) :
    0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by
  positivity
private theorem radialSequence_lt_one (n : ℕ) :
    (n : ℝ) / ((n : ℝ) + 1) < 1 := by
  exact (div_lt_one₀ (by positivity)).mpr (by linarith)
private theorem radialSequence_range (n : ℕ) :
    0 ≤ (n : ℝ) / ((n : ℝ) + 1) ∧ (n : ℝ) / ((n : ℝ) + 1) < 1 :=
  ⟨radialSequence_nonneg n, radialSequence_lt_one n⟩
private theorem eventually_radialSequence_range :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℝ) / ((n : ℝ) + 1) ∧
      (n : ℝ) / ((n : ℝ) + 1) < 1 :=
  Filter.Eventually.of_forall radialSequence_range
private theorem tendsto_radialSequence :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
  tendsto_natCast_div_add_atTop 1
private theorem re_herglotzRieszKernel_unit_eq {w z : ℂ} (hz : Complex.normSq z = 1) :
    (Complex.re ∘ herglotzRieszKernel 0 w) z =
      (1 - Complex.normSq w) / Complex.normSq (z - w) := by
  rw [← poissonKernel_eq_re_herglotzRieszKernel, poissonKernel_def]
  simp only [sub_zero]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, hz]
private theorem re_herglotzRieszKernel_left_transport
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (t : ℝ) :
    (Real.cosh (Real.pi * t))⁻¹ *
        (Complex.re ∘ herglotzRieszKernel 0
          ((Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)))
          ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)) =
      Real.sin (Real.pi * θ) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) := by
  let w : ℂ :=
    (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)
  let z : ℂ :=
    (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)
  have hz : Complex.normSq z = 1 := by
    dsimp [z]
    rw [← circleMap_angleMap_eq_left t]
    rw [Complex.normSq_eq_norm_sq, norm_circleMap_zero]
    norm_num
  have hP : (Complex.re ∘ herglotzRieszKernel 0 w) z =
      (1 - Complex.normSq w) / Complex.normSq (z - w) :=
    re_herglotzRieszKernel_unit_eq hz
  have hraw : (1 - Complex.normSq w) / Complex.normSq (z - w) /
      (2 * Real.cosh (Real.pi * t)) =
        Real.sin (Real.pi * θ) /
          (2 * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
    simpa only [w, z] using stripToDisc_left_kernel hθ t
  have harg0 : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ.1
  have harg1 : Real.pi * θ < Real.pi := by
    nlinarith [mul_lt_mul_of_pos_left hθ.2 Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi harg0 harg1
  have hcoslt : Real.cos (Real.pi * θ) < 1 := by
    have hsq : Real.cos (Real.pi * θ) ^ 2 < 1 := by
      nlinarith [Real.cos_sq_add_sin_sq (Real.pi * θ), sq_pos_of_pos hsin]
    nlinarith [sq_nonneg (Real.cos (Real.pi * θ) + 1)]
  have hcosh_one : 1 ≤ Real.cosh (Real.pi * t) := by
    have hsq : 1 ≤ Real.cosh (Real.pi * t) ^ 2 := by
      rw [Real.cosh_sq']
      nlinarith [sq_nonneg (Real.sinh (Real.pi * t))]
    nlinarith [(Real.cosh_pos (Real.pi * t)).le]
  have hden : 0 < Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ) := by
    linarith
  change (Real.cosh (Real.pi * t))⁻¹ *
      (Complex.re ∘ herglotzRieszKernel 0 w) z =
        Real.sin (Real.pi * θ) /
          (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))
  rw [hP]
  calc
    (Real.cosh (Real.pi * t))⁻¹ *
        ((1 - Complex.normSq w) / Complex.normSq (z - w)) =
        2 * (((1 - Complex.normSq w) / Complex.normSq (z - w)) /
          (2 * Real.cosh (Real.pi * t))) := by
      field_simp [ne_of_gt (Real.cosh_pos _)]
    _ = 2 * (Real.sin (Real.pi * θ) /
          (2 * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)))) := by rw [hraw]
    _ = Real.sin (Real.pi * θ) /
          (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) := by
      field_simp [ne_of_gt hden]
private theorem re_herglotzRieszKernel_right_transport
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (t : ℝ) :
    (Real.cosh (Real.pi * t))⁻¹ *
        (Complex.re ∘ herglotzRieszKernel 0
          ((Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)))
          ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)) =
      Real.sin (Real.pi * θ) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)) := by
  let w : ℂ :=
    (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)
  let z : ℂ :=
    (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)
  have hz : Complex.normSq z = 1 := by
    dsimp [z]
    rw [← circleMap_angleMap_eq_right t]
    rw [Complex.normSq_eq_norm_sq, norm_circleMap_zero]
    norm_num
  have hP : (Complex.re ∘ herglotzRieszKernel 0 w) z =
      (1 - Complex.normSq w) / Complex.normSq (z - w) :=
    re_herglotzRieszKernel_unit_eq hz
  have hraw : (1 - Complex.normSq w) / Complex.normSq (z - w) /
      (2 * Real.cosh (Real.pi * t)) =
        Real.sin (Real.pi * θ) /
          (2 * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    simpa only [w, z] using stripToDisc_right_kernel hθ t
  have harg0 : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ.1
  have harg1 : Real.pi * θ < Real.pi := by
    nlinarith [mul_lt_mul_of_pos_left hθ.2 Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi harg0 harg1
  have hcosgt : -1 < Real.cos (Real.pi * θ) := by
    have hsq : Real.cos (Real.pi * θ) ^ 2 < 1 := by
      nlinarith [Real.cos_sq_add_sin_sq (Real.pi * θ), sq_pos_of_pos hsin]
    nlinarith [sq_nonneg (Real.cos (Real.pi * θ) - 1)]
  have hcosh_one : 1 ≤ Real.cosh (Real.pi * t) := by
    have hsq : 1 ≤ Real.cosh (Real.pi * t) ^ 2 := by
      rw [Real.cosh_sq']
      nlinarith [sq_nonneg (Real.sinh (Real.pi * t))]
    nlinarith [(Real.cosh_pos (Real.pi * t)).le]
  have hden : 0 < Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ) := by
    linarith
  have hhalf (u c : ℝ) (hc : c ≠ 0) :
      c⁻¹ * u = 2 * (u / (2 * c)) := by
    field_simp [hc]
  change (Real.cosh (Real.pi * t))⁻¹ *
      (Complex.re ∘ herglotzRieszKernel 0 w) z =
        Real.sin (Real.pi * θ) /
          (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))
  rw [hP]
  calc
    (Real.cosh (Real.pi * t))⁻¹ *
        ((1 - Complex.normSq w) / Complex.normSq (z - w)) =
        2 * (((1 - Complex.normSq w) / Complex.normSq (z - w)) /
          (2 * Real.cosh (Real.pi * t))) := by
      exact hhalf _ _ (ne_of_gt (Real.cosh_pos _))
    _ = 2 * (Real.sin (Real.pi * θ) /
          (2 * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)))) := by rw [hraw]
    _ = Real.sin (Real.pi * θ) /
          (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)) := by
      field_simp [ne_of_gt hden]
private theorem circleAverage_poisson_transport
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) {H : ℂ → ℝ}
    (hH : ContinuousOn H (sphere 0 1)) :
    Real.circleAverage
      ((Complex.re ∘ herglotzRieszKernel 0
        ((Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
          (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I))) * H) 0 1 =
      (Real.sin (Real.pi * θ) / 2) *
        ((∫ t : ℝ,
          H ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)) /
            (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) +
          ∫ t : ℝ,
          H ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)) /
            (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
  let w : ℂ :=
    (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)
  let P : ℂ → ℝ := Complex.re ∘ herglotzRieszKernel 0 w
  let G : ℝ → ℝ := fun x => P (circleMap 0 1 x) * H (circleMap 0 1 x)
  have hθstrip : (θ : ℂ) ∈ verticalStrip 0 1 := by
    simpa [verticalStrip] using hθ
  have hw : w ∈ ball 0 1 := by
    rw [mem_ball, dist_zero_right]
    simpa only [w] using stripToDisc_norm_lt_one hθstrip
  have hP : Continuous (fun x : ℝ => P (circleMap 0 1 x)) := by
    dsimp [P]
    rw [herglotzRieszKernel_fun_def]
    apply Complex.continuous_re.comp
    apply Continuous.div
    · have hnum : Continuous (fun x : ℝ => circleMap 0 1 x + w) :=
        (continuous_circleMap 0 1).add (continuous_const : Continuous fun _ : ℝ => w)
      simpa using hnum
    · have hden : Continuous (fun x : ℝ => circleMap 0 1 x - w) :=
        (continuous_circleMap 0 1).sub (continuous_const : Continuous fun _ : ℝ => w)
      simpa using hden
    · intro x
      simpa using (sub_ne_zero.mpr (circleMap_ne_mem_ball hw x))
  have hHcircle : Continuous (fun x : ℝ => H (circleMap 0 1 x)) := by
    exact hH.comp_continuous (continuous_circleMap 0 1) (fun _x => by simp)
  have hG : Continuous G := hP.mul hHcircle
  have hleft (t : ℝ) :
      (Real.cosh (Real.pi * t))⁻¹ *
          G (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t))) =
        Real.sin (Real.pi * θ) *
          (H ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)) /
            (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
    dsimp [G, P, w]
    rw [circleMap_angleMap_eq_left]
    calc
      (Real.cosh (Real.pi * t))⁻¹ *
          ((Complex.re ∘ herglotzRieszKernel 0
            ((Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)))
            ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)) *
            H ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I))) =
          ((Real.cosh (Real.pi * t))⁻¹ *
            (Complex.re ∘ herglotzRieszKernel 0
              ((Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
                (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)))
              ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
                (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I))) *
            H ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)) := by ring
      _ = (Real.sin (Real.pi * θ) /
            (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) *
            H ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)) := by
          rw [re_herglotzRieszKernel_left_transport hθ t]
      _ = Real.sin (Real.pi * θ) *
          (H ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)) /
            (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by ring
  have hright (t : ℝ) :
      (Real.cosh (Real.pi * t))⁻¹ *
          G (2 * Real.arctan (Real.exp (Real.pi * t))) =
        Real.sin (Real.pi * θ) *
          (H ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)) /
            (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    dsimp [G, P, w]
    rw [circleMap_angleMap_eq_right]
    calc
      (Real.cosh (Real.pi * t))⁻¹ *
          ((Complex.re ∘ herglotzRieszKernel 0
            ((Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)))
            ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)) *
            H ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I))) =
          ((Real.cosh (Real.pi * t))⁻¹ *
            (Complex.re ∘ herglotzRieszKernel 0
              ((Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
                (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)))
              ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
                (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I))) *
            H ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)) := by
          ring
      _ = (Real.sin (Real.pi * θ) /
            (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) *
            H ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)) := by
          rw [re_herglotzRieszKernel_right_transport hθ t]
      _ = Real.sin (Real.pi * θ) *
          (H ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
            (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)) /
            (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by ring
  have hleft_integral :
      (∫ t : ℝ, (Real.cosh (Real.pi * t))⁻¹ *
          G (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t)))) =
        Real.sin (Real.pi * θ) *
          ∫ t : ℝ,
            H ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)) /
              (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) := by
    calc
      (∫ t : ℝ, (Real.cosh (Real.pi * t))⁻¹ *
          G (2 * Real.pi - 2 * Real.arctan (Real.exp (Real.pi * t)))) =
          ∫ t : ℝ, Real.sin (Real.pi * θ) *
            (H ((Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)) /
              (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
            apply integral_congr_ae
            filter_upwards with t
            exact hleft t
      _ = _ := integral_const_mul _ _
  have hright_integral :
      (∫ t : ℝ, (Real.cosh (Real.pi * t))⁻¹ *
          G (2 * Real.arctan (Real.exp (Real.pi * t)))) =
        Real.sin (Real.pi * θ) *
          ∫ t : ℝ,
            H ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)) /
              (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)) := by
    calc
      (∫ t : ℝ, (Real.cosh (Real.pi * t))⁻¹ *
          G (2 * Real.arctan (Real.exp (Real.pi * t)))) =
          ∫ t : ℝ, Real.sin (Real.pi * θ) *
            (H ((Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
              (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)) /
              (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
            apply integral_congr_ae
            filter_upwards with t
            exact hright t
      _ = _ := integral_const_mul _ _
  change Real.circleAverage (P * H) 0 1 = _
  rw [Real.circleAverage_def]
  simp only [smul_eq_mul, Pi.mul_apply]
  change (2 * Real.pi)⁻¹ * (∫ x in (0 : ℝ)..2 * Real.pi, G x) = _
  rw [circle_average_angleMap_transport G hG, hleft_integral, hright_integral]
  ring
private theorem memLp_simpleFunc_of_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ENNReal}
    (f : SimpleFunc X ℂ) (hf : Integrable f μ) : MemLp (f : X → ℂ) p μ := by
  refine f.memLp_of_finite_measure_preimage p ?_
  exact fun y hy ↦
    (SimpleFunc.integrable_iff_finMeasSupp.mp hf).meas_preimage_singleton_ne_zero hy
private theorem integrable_indicator_of_pairing
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u : Y → ℂ}
    (hpair : ∀ g : SimpleFunc Y ℂ, Integrable g ν →
      Integrable (fun y ↦ u y * g y) ν)
    {s : Set Y} (hs : MeasurableSet s) (hsfin : ν s < ∞) :
    Integrable (s.indicator u) ν := by
  let oneS : SimpleFunc Y ℂ := (SimpleFunc.const Y (1 : ℂ)).restrict s
  have honeSfin : oneS.FinMeasSupp ν := by
    rw [SimpleFunc.finMeasSupp_iff_support]
    refine lt_of_le_of_lt (measure_mono ?_) hsfin
    intro y hy
    by_contra hys
    have hz : oneS y = 0 := by
      simp [oneS, SimpleFunc.restrict_apply, hs, hys]
    exact hy hz
  have honeS : Integrable (oneS : Y → ℂ) ν := honeSfin.integrable
  have h := hpair oneS honeS
  convert h using 1
  ext y
  by_cases hys : y ∈ s <;> simp [oneS, SimpleFunc.restrict_apply, hs, hys]
private theorem pairing_bound_of_tendsto_simple
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u g : Y → ℂ}
    {q : ENNReal} {C : ℝ} (gₙ : ℕ → SimpleFunc Y ℂ)
    (hbound : ∀ h : SimpleFunc Y ℂ, Integrable h ν →
      norm (∫ y, u y * h y ∂ν) ≤ C * (eLpNorm (h : Y → ℂ) q ν).toReal)
    (hint : Tendsto (fun n ↦ ∫ y, u y * gₙ n y ∂ν) atTop
      (𝓝 (∫ y, u y * g y ∂ν)))
    (hnorm : Tendsto (fun n ↦ eLpNorm (gₙ n : Y → ℂ) q ν) atTop
      (𝓝 (eLpNorm g q ν)))
    (hgfin : eLpNorm g q ν ≠ ∞)
    (hints : ∀ n, Integrable (gₙ n : Y → ℂ) ν) :
    norm (∫ y, u y * g y ∂ν) ≤ C * (eLpNorm g q ν).toReal := by
  apply le_of_tendsto_of_tendsto hint.norm
    ((tendsto_const_nhds.mul ((ENNReal.tendsto_toReal hgfin).comp hnorm)))
  filter_upwards with n
  exact hbound (gₙ n) (hints n)
private theorem integrable_restrict_simpleFunc_of_measure_lt_top
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (h : SimpleFunc Y ℂ) {s : Set Y} (hs : MeasurableSet s) (hsfin : ν s < ∞) :
    Integrable (h.restrict s : Y → ℂ) ν := by
  apply SimpleFunc.FinMeasSupp.integrable
  rw [SimpleFunc.finMeasSupp_iff_support]
  refine lt_of_le_of_lt (measure_mono ?_) hsfin
  intro y hy
  by_contra hys
  have hz : h.restrict s y = 0 := by
    simp [SimpleFunc.restrict_apply, hs, hys]
  exact hy hz
private theorem tendsto_pairing_restrict_approxBounded
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u g : Y → ℂ}
    {s : Set Y} {A : ℝ} (hs : MeasurableSet s) (hA : 0 ≤ A)
    (hu : Measurable u) (hus : Integrable (s.indicator u) ν)
    (hg : Measurable g) (hgsupp : ∀ y, y ∉ s → g y = 0)
    (hgbound : ∀ y, ‖g y‖ ≤ A) :
    Tendsto
      (fun n ↦ ∫ y, u y * ((hg.stronglyMeasurable.approxBounded A n).restrict s) y ∂ν)
      atTop (𝓝 (∫ y, u y * g y ∂ν)) := by
  let gₙ : ℕ → SimpleFunc Y ℂ := fun n ↦
    (hg.stronglyMeasurable.approxBounded A n).restrict s
  have hgₙ_bound : ∀ n y, ‖gₙ n y‖ ≤ A := by
    intro n y
    by_cases hys : y ∈ s
    · simp only [gₙ, SimpleFunc.restrict_apply _ hs, Set.indicator_of_mem hys]
      exact hg.stronglyMeasurable.norm_approxBounded_le hA n y
    · simp [gₙ, SimpleFunc.restrict_apply, hs, hys, hA]
  have hgₙ_tendsto : ∀ y, Tendsto (fun n ↦ gₙ n y) atTop (𝓝 (g y)) := by
    intro y
    by_cases hys : y ∈ s
    · simpa only [gₙ, SimpleFunc.restrict_apply _ hs, Set.indicator_of_mem hys] using
        hg.stronglyMeasurable.tendsto_approxBounded_of_norm_le (hgbound y)
    · have hgy : g y = 0 := hgsupp y hys
      simp [gₙ, SimpleFunc.restrict_apply, hs, hys, hgy]
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n y ↦ u y * gₙ n y) (f := fun y ↦ u y * g y)
    (fun y ↦ A * ‖s.indicator u y‖) (fun n ↦ by
      change AEStronglyMeasurable (u * (gₙ n : Y → ℂ)) ν
      exact hu.aestronglyMeasurable.mul (gₙ n).stronglyMeasurable.aestronglyMeasurable)
    (hus.norm.const_mul A) ?_ ?_
  · simpa only [gₙ] using h
  · intro n
    filter_upwards with y
    by_cases hys : y ∈ s
    · rw [Set.indicator_of_mem hys, norm_mul]
      calc
        ‖u y‖ * ‖gₙ n y‖ ≤ ‖u y‖ * A :=
          mul_le_mul_of_nonneg_left (hgₙ_bound n y) (norm_nonneg _)
        _ = A * ‖u y‖ := mul_comm _ _
    · have hgzero : gₙ n y = 0 := by
        simp [gₙ, SimpleFunc.restrict_apply, hs, hys]
      rw [hgzero, Set.indicator_of_notMem hys]
      simp
  · filter_upwards with y
    exact tendsto_const_nhds.mul (hgₙ_tendsto y)
private theorem tendsto_eLpNorm_restrict_approxBounded
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {g : Y → ℂ}
    {s : Set Y} {A : ℝ} {q : ENNReal} (hs : MeasurableSet s) (hsfin : ν s < ∞)
    (hA : 0 ≤ A) (hg : Measurable g) (hgsupp : ∀ y, y ∉ s → g y = 0)
    (hgbound : ∀ y, ‖g y‖ ≤ A) (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    Tendsto
      (fun n ↦ eLpNorm ((hg.stronglyMeasurable.approxBounded A n).restrict s : Y → ℂ) q ν)
      atTop (𝓝 (eLpNorm g q ν)) := by
  let gₙ : ℕ → SimpleFunc Y ℂ := fun n ↦
    (hg.stronglyMeasurable.approxBounded A n).restrict s
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hgₙ_bound : ∀ n y, ‖gₙ n y‖ ≤ A := by
    intro n y
    by_cases hys : y ∈ s
    · simp only [gₙ, SimpleFunc.restrict_apply _ hs, Set.indicator_of_mem hys]
      exact hg.stronglyMeasurable.norm_approxBounded_le hA n y
    · simp [gₙ, SimpleFunc.restrict_apply, hs, hys, hA]
  have hgₙ_tendsto : ∀ y, Tendsto (fun n ↦ gₙ n y) atTop (𝓝 (g y)) := by
    intro y
    by_cases hys : y ∈ s
    · simpa only [gₙ, SimpleFunc.restrict_apply _ hs, Set.indicator_of_mem hys] using
        hg.stronglyMeasurable.tendsto_approxBounded_of_norm_le (hgbound y)
    · have hgy : g y = 0 := hgsupp y hys
      simp [gₙ, SimpleFunc.restrict_apply, hs, hys, hgy]
  have hlin := tendsto_lintegral_of_dominated_convergence (μ := ν)
    (f := fun y ↦ ‖g y‖ₑ ^ q.toReal)
    (F := fun n y ↦ ‖gₙ n y‖ₑ ^ q.toReal)
    (s.indicator fun _ ↦ (ENNReal.ofReal A) ^ q.toReal) (fun n ↦ by
      exact ENNReal.continuous_rpow_const.measurable.comp (gₙ n).measurable.enorm) ?_ ?_ ?_
  · change Tendsto (fun n ↦ eLpNorm (gₙ n : Y → ℂ) q ν) atTop (𝓝 (eLpNorm g q ν))
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop]
    convert (ENNReal.continuous_rpow_const (y := 1 / q.toReal)).tendsto _ |>.comp hlin using 1 ;
      rfl
  · intro n
    filter_upwards with y
    by_cases hys : y ∈ s
    · rw [Set.indicator_of_mem hys]
      apply ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hgₙ_bound n y)
    · have hgzero : gₙ n y = 0 := by
        simp [gₙ, SimpleFunc.restrict_apply, hs, hys]
      rw [hgzero, Set.indicator_of_notMem hys]
      simp [ENNReal.zero_rpow_of_pos hqpos]
  · rw [lintegral_indicator hs, setLIntegral_const]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) hsfin.ne
  · filter_upwards with y
    exact (ENNReal.continuous_rpow_const.tendsto _).comp (hgₙ_tendsto y).enorm
private theorem pairing_bound_of_bounded_support
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u g : Y → ℂ}
    {s : Set Y} {A C : ℝ} {q : ENNReal}
    (hs : MeasurableSet s) (hsfin : ν s < ∞) (hA : 0 ≤ A)
    (hu : Measurable u) (hus : Integrable (s.indicator u) ν)
    (hg : Measurable g) (hgsupp : ∀ y, y ∉ s → g y = 0)
    (hgbound : ∀ y, ‖g y‖ ≤ A) (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (hbound : ∀ h : SimpleFunc Y ℂ, Integrable h ν →
      norm (∫ y, u y * h y ∂ν) ≤ C * (eLpNorm (h : Y → ℂ) q ν).toReal) :
    norm (∫ y, u y * g y ∂ν) ≤ C * (eLpNorm g q ν).toReal := by
  let gₙ : ℕ → SimpleFunc Y ℂ := fun n ↦
    (hg.stronglyMeasurable.approxBounded A n).restrict s
  have hsupport : Function.support g ⊆ s := by
    intro y hy
    by_contra hys
    exact hy (hgsupp y hys)
  let : IsFiniteMeasure (ν.restrict s) := isFiniteMeasure_restrict.2 hsfin.ne
  have hmem : MemLp g q (ν.restrict s) :=
    MemLp.of_bound hg.aestronglyMeasurable A (Eventually.of_forall hgbound)
  have hgfin : eLpNorm g q ν ≠ ∞ := by
    rw [← eLpNorm_restrict_eq_of_support_subset hsupport]
    exact hmem.eLpNorm_lt_top.ne
  apply pairing_bound_of_tendsto_simple gₙ hbound
  · simpa only [gₙ] using
      tendsto_pairing_restrict_approxBounded hs hA hu hus hg hgsupp hgbound
  · simpa only [gₙ] using
      tendsto_eLpNorm_restrict_approxBounded hs hsfin hA hg hgsupp hgbound hq0 hqtop
  · exact hgfin
  · intro n
    simpa only [gₙ] using
      integrable_restrict_simpleFunc_of_measure_lt_top
        (hg.stronglyMeasurable.approxBounded A n) hs hsfin
private theorem pairing_bound_top_of_bounded_support
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u g : Y → ℂ}
    {s : Set Y} {C : ℝ}
    (hs : MeasurableSet s) (hsfin : ν s < ∞) (hC : 0 ≤ C)
    (hu : Measurable u) (hus : Integrable (s.indicator u) ν)
    (hg : Measurable g) (hgsupp : ∀ y, y ∉ s → g y = 0)
    (hgbound : ∀ y, ‖g y‖ ≤ 1)
    (hbound : ∀ h : SimpleFunc Y ℂ, Integrable h ν →
      norm (∫ y, u y * h y ∂ν) ≤ C * (eLpNorm (h : Y → ℂ) ∞ ν).toReal) :
    norm (∫ y, u y * g y ∂ν) ≤ C := by
  let gₙ : ℕ → SimpleFunc Y ℂ := fun n ↦
    (hg.stronglyMeasurable.approxBounded 1 n).restrict s
  have hgₙ_bound : ∀ n y, ‖gₙ n y‖ ≤ 1 := by
    intro n y
    by_cases hys : y ∈ s
    · simp only [gₙ, SimpleFunc.restrict_apply _ hs, Set.indicator_of_mem hys]
      exact hg.stronglyMeasurable.norm_approxBounded_le zero_le_one n y
    · simp [gₙ, SimpleFunc.restrict_apply, hs, hys]
  have hgₙLp : ∀ n, eLpNorm (gₙ n : Y → ℂ) ∞ ν ≤ 1 := by
    intro n
    rw [eLpNorm_exponent_top]
    simpa using eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (hgₙ_bound n))
  have hlim := tendsto_pairing_restrict_approxBounded hs zero_le_one hu hus hg hgsupp hgbound
  apply le_of_tendsto hlim.norm
  filter_upwards with n
  calc
    ‖∫ y, u y * gₙ n y ∂ν‖ ≤ C * (eLpNorm (gₙ n : Y → ℂ) ∞ ν).toReal :=
      hbound (gₙ n) (integrable_restrict_simpleFunc_of_measure_lt_top
        (hg.stronglyMeasurable.approxBounded 1 n) hs hsfin)
    _ ≤ C * (1 : ENNReal).toReal :=
      mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ENNReal.one_ne_top (hgₙLp n)) hC
    _ = C := by simp
private theorem measurable_phase {Y : Type*} [MeasurableSpace Y] {u : Y → ℂ}
    (hu : Measurable u) :
    Measurable (fun y ↦ star (u y) / (‖u y‖ : ℂ)) := by
  fun_prop
private theorem norm_phase_le_one (z : ℂ) :
    ‖star z / (‖z‖ : ℂ)‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [norm_div, norm_star, Complex.norm_real, div_le_iff₀]
    · simp
    · simpa using norm_pos_iff.mpr hz
private theorem mul_phase (z : ℂ) :
    z * (star z / (‖z‖ : ℂ)) = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  rw [← mul_div_assoc]
  change z * (starRingEnd ℂ) z / (‖z‖ : ℂ) = (‖z‖ : ℂ)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq : ((‖z‖ ^ 2 : ℝ) : ℂ) = (‖z‖ : ℂ) ^ 2 := by norm_num
  rw [hsq]
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hz).ne'
  field_simp
private theorem setLIntegral_enorm_le_of_phase_pairing
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u : Y → ℂ}
    {s : Set Y} {C : ℝ} (hs : MeasurableSet s) (hsfin : ν s < ∞) (hC : 0 ≤ C)
    (hus : Integrable (s.indicator u) ν)
    (hphase :
      ‖∫ y, u y * s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ)) y ∂ν‖ ≤
        C * (eLpNorm (s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ))) 1 ν).toReal) :
    (∫⁻ y in s, ‖u y‖ₑ ∂ν) ≤ ENNReal.ofReal C * ν s := by
  let g : Y → ℂ := s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ))
  let v : Y → ℝ := s.indicator (fun y ↦ ‖u y‖)
  have hprod : (fun y ↦ u y * g y) = fun y ↦ (v y : ℂ) := by
    funext y
    by_cases hys : y ∈ s
    · simp only [g, v, Set.indicator_of_mem hys]
      exact mul_phase _
    · simp [g, v, hys]
  have hvint : Integrable v ν := by
    have hv_eq : v = fun y ↦ ‖s.indicator u y‖ := by
      funext y
      by_cases hys : y ∈ s <;> simp [v, hys]
    rw [hv_eq]
    exact hus.norm
  have hvnonneg : 0 ≤ ∫ y, v y ∂ν :=
    integral_nonneg fun y ↦ by
      by_cases hys : y ∈ s <;> simp [v, hys, norm_nonneg]
  have hnorm_int : ‖∫ y, u y * g y ∂ν‖ = ∫ y, v y ∂ν := by
    rw [hprod, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hvnonneg]
  have hg_bound : ∀ y, ‖g y‖ ≤ ‖s.indicator (fun _ : Y ↦ (1 : ℂ)) y‖ := by
    intro y
    by_cases hys : y ∈ s
    · simp only [g, Set.indicator_of_mem hys]
      simpa using norm_phase_le_one (u y)
    · simp [g, hys]
  have hgLp : eLpNorm g 1 ν ≤ ν s := by
    refine (eLpNorm_mono_ae (Eventually.of_forall hg_bound)).trans_eq ?_
    rw [eLpNorm_indicator_const hs (by norm_num) (by norm_num)]
    simp
  have hreal : (∫ y, v y ∂ν) ≤ C * (ν s).toReal := by
    calc
      (∫ y, v y ∂ν) = ‖∫ y, u y * g y ∂ν‖ := hnorm_int.symm
      _ ≤ C * (eLpNorm g 1 ν).toReal := by simpa only [g] using hphase
      _ ≤ C * (ν s).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hsfin.ne hgLp) hC
  have hlin : ENNReal.ofReal (∫ y, v y ∂ν) ≤ ENNReal.ofReal C * ν s := by
    calc
      ENNReal.ofReal (∫ y, v y ∂ν) ≤ ENNReal.ofReal (C * (ν s).toReal) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal C * ν s := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hsfin.ne]
  calc
    (∫⁻ y in s, ‖u y‖ₑ ∂ν) = ∫⁻ y, s.indicator (fun y ↦ ‖u y‖ₑ) y ∂ν :=
      (lintegral_indicator hs _).symm
    _ = ∫⁻ y, ENNReal.ofReal (v y) ∂ν := by
      apply lintegral_congr
      intro y
      by_cases hys : y ∈ s <;> simp [v, hys]
    _ = ENNReal.ofReal (∫ y, v y ∂ν) :=
      (ofReal_integral_eq_lintegral_ofReal hvint
        (Eventually.of_forall fun y ↦ by
          by_cases hys : y ∈ s <;> simp [v, hys, norm_nonneg])).symm
    _ ≤ ENNReal.ofReal C * ν s := hlin
private theorem memLp_top_of_phase_tests
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν]
    {u : Y → ℂ} {C : ℝ} (hu : Measurable u) (hC : 0 ≤ C)
    (hlocal_int : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      Integrable (s.indicator u) ν)
    (hlocal : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      Integrable (s.indicator u) ν →
      ‖∫ y, u y * s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ)) y ∂ν‖ ≤
        C * (eLpNorm (s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ))) 1 ν).toReal) :
    MemLp u ∞ ν ∧ eLpNorm u ∞ ν ≤ ENNReal.ofReal C := by
  have hlocal' : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      (∫⁻ y in s, ‖u y‖ₑ ∂ν) ≤ ∫⁻ _y in s, ENNReal.ofReal C ∂ν := by
    intro s hs hsfin
    have hus := hlocal_int s hs hsfin
    rw [setLIntegral_const]
    exact setLIntegral_enorm_le_of_phase_pairing hs hsfin hC hus (hlocal s hs hsfin hus)
  have hae : (fun y ↦ ‖u y‖ₑ) ≤ᵐ[ν] fun _y ↦ ENNReal.ofReal C :=
    MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite hu.enorm hlocal'
  have hnorm : eLpNorm u ∞ ν ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_enorm_bound hae
  exact ⟨⟨hu.aestronglyMeasurable, hnorm.trans_lt ENNReal.ofReal_lt_top⟩, hnorm⟩
private theorem ofReal_norm_integral_phase_eq_setLIntegral_enorm
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u : Y → ℂ}
    {s : Set Y} (hs : MeasurableSet s) (hus : Integrable (s.indicator u) ν) :
    ENNReal.ofReal
        ‖∫ y, u y * s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ)) y ∂ν‖ =
      (∫⁻ y in s, ‖u y‖ₑ ∂ν) := by
  let g : Y → ℂ := s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ))
  let v : Y → ℝ := s.indicator (fun y ↦ ‖u y‖)
  have hprod : (fun y ↦ u y * g y) = fun y ↦ (v y : ℂ) := by
    funext y
    by_cases hys : y ∈ s
    · simp only [g, v, Set.indicator_of_mem hys]
      exact mul_phase _
    · simp [g, v, hys]
  have hvint : Integrable v ν := by
    have hv_eq : v = fun y ↦ ‖s.indicator u y‖ := by
      funext y
      by_cases hys : y ∈ s <;> simp [v, hys]
    rw [hv_eq]
    exact hus.norm
  have hvnonneg : 0 ≤ ∫ y, v y ∂ν :=
    integral_nonneg fun y ↦ by
      by_cases hys : y ∈ s <;> simp [v, hys, norm_nonneg]
  have hnorm_int : ‖∫ y, u y * g y ∂ν‖ = ∫ y, v y ∂ν := by
    rw [hprod, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hvnonneg]
  rw [show (∫ y, u y * s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ)) y ∂ν) =
      ∫ y, u y * g y ∂ν by rfl, hnorm_int]
  calc
    ENNReal.ofReal (∫ y, v y ∂ν) = ∫⁻ y, ENNReal.ofReal (v y) ∂ν :=
      ofReal_integral_eq_lintegral_ofReal hvint
        (Eventually.of_forall fun y ↦ by
          by_cases hys : y ∈ s <;> simp [v, hys, norm_nonneg])
    _ = ∫⁻ y, s.indicator (fun y ↦ ‖u y‖ₑ) y ∂ν := by
      apply lintegral_congr
      intro y
      by_cases hys : y ∈ s <;> simp [v, hys]
    _ = ∫⁻ y in s, ‖u y‖ₑ ∂ν := lintegral_indicator hs _
private theorem memLp_one_of_setLIntegral_le
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν]
    {u : Y → ℂ} {C : ℝ} (hu : Measurable u)
    (hlocal : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      (∫⁻ y in s, ‖u y‖ₑ ∂ν) ≤ ENNReal.ofReal C) :
    MemLp u 1 ν ∧ eLpNorm u 1 ν ≤ ENNReal.ofReal C := by
  let f : ℕ → Y → ENNReal := fun n ↦
    (spanningSets ν n).indicator (fun y ↦ ‖u y‖ₑ)
  have hfmeas : ∀ n, Measurable (f n) := fun n ↦
    hu.enorm.indicator (measurableSet_spanningSets ν n)
  have hfmono : Monotone f := by
    intro m n hmn y
    by_cases hym : y ∈ spanningSets ν m
    · have hyn : y ∈ spanningSets ν n := spanningSets_mono hmn hym
      simp [f, hym, hyn]
    · by_cases hyn : y ∈ spanningSets ν n
      · simp [f, hym, hyn]
      · simp [f, hym, hyn]
  have hfun : (⨆ n, f n) = fun y ↦ ‖u y‖ₑ := by
    funext y
    rw [iSup_apply]
    apply le_antisymm
    · exact iSup_le fun n : ℕ ↦ by
        by_cases hyn : y ∈ spanningSets ν n <;> simp [f, hyn]
    · have hyunion : y ∈ ⋃ n, spanningSets ν n := by
        rw [iUnion_spanningSets]
        trivial
      obtain ⟨n, hyn⟩ := Set.mem_iUnion.mp hyunion
      calc
        ‖u y‖ₑ = f n y := by simp [f, hyn]
        _ ≤ ⨆ n : ℕ, f n y := le_iSup (fun n : ℕ ↦ f n y) n
  have hlin : (∫⁻ y, ‖u y‖ₑ ∂ν) ≤ ENNReal.ofReal C := by
    rw [← hfun]
    rw [show (⨆ n, f n) = fun y ↦ ⨆ n, f n y by
      funext y
      rw [iSup_apply]]
    rw [lintegral_iSup hfmeas hfmono]
    refine iSup_le fun n : ℕ ↦ ?_
    change (∫⁻ y, (spanningSets ν n).indicator (fun y ↦ ‖u y‖ₑ) y ∂ν) ≤ _
    rw [lintegral_indicator (measurableSet_spanningSets ν n)]
    exact hlocal _ (measurableSet_spanningSets ν n) (measure_spanningSets_lt_top ν n)
  have hnorm : eLpNorm u 1 ν ≤ ENNReal.ofReal C := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact hlin
  exact ⟨⟨hu.aestronglyMeasurable, hnorm.trans_lt ENNReal.ofReal_lt_top⟩, hnorm⟩
private theorem memLp_one_of_phase_tests
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν]
    {u : Y → ℂ} {C : ℝ} (hu : Measurable u)
    (hlocal_int : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      Integrable (s.indicator u) ν)
    (hlocal : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      Integrable (s.indicator u) ν →
      ‖∫ y, u y * s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ)) y ∂ν‖ ≤ C) :
    MemLp u 1 ν ∧ eLpNorm u 1 ν ≤ ENNReal.ofReal C := by
  apply memLp_one_of_setLIntegral_le hu
  intro s hs hsfin
  have hus := hlocal_int s hs hsfin
  rw [← ofReal_norm_integral_phase_eq_setLIntegral_enorm hs hus]
  exact ENNReal.ofReal_le_ofReal (hlocal s hs hsfin hus)
private theorem measurable_phase_power
    {Y : Type*} [MeasurableSpace Y] {u : Y → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (hu : Measurable u) :
    Measurable (fun y ↦
      (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ)) := by
  have hp : 0 ≤ r - 1 := sub_nonneg.mpr hr
  fun_prop
private theorem norm_phase_power
    {r : ℝ} (hr : 1 < r) (z : ℂ) :
    ‖(star z / (‖z‖ : ℂ)) * ((‖z‖ ^ (r - 1) : ℝ) : ℂ)‖ = ‖z‖ ^ (r - 1) := by
  by_cases hz : z = 0
  · have hp : 0 < r - 1 := sub_pos.mpr hr
    simpa [hz] using (Real.zero_rpow hp.ne').symm
  · rw [norm_mul, norm_div, norm_star]
    have hp : 0 ≤ ‖z‖ ^ (r - 1) := Real.rpow_nonneg (norm_nonneg _) _
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg hp]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    field_simp
private theorem mul_phase_power
    {r : ℝ} (hr : 1 < r) (z : ℂ) :
    z * ((star z / (‖z‖ : ℂ)) * ((‖z‖ ^ (r - 1) : ℝ) : ℂ)) =
      ((‖z‖ ^ r : ℝ) : ℂ) := by
  by_cases hz : z = 0
  · have hr0 : r ≠ 0 := by linarith
    simp [hz, Real.zero_rpow hr0]
  · rw [← mul_assoc, mul_phase]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hreal : ‖z‖ * ‖z‖ ^ (r - 1) = ‖z‖ ^ r := by
      calc
        ‖z‖ * ‖z‖ ^ (r - 1) = ‖z‖ ^ 1 * ‖z‖ ^ (r - 1) := by rw [Real.rpow_one]
        _ = ‖z‖ ^ (1 + (r - 1)) := (Real.rpow_add hn _ _).symm
        _ = ‖z‖ ^ r := by ring_nf
    exact_mod_cast hreal
private theorem integrable_indicator_norm_rpow_of_bound
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u : Y → ℂ}
    {s : Set Y} {r A : ℝ} (hs : MeasurableSet s) (hsfin : ν s < ∞)
    (hr : 0 ≤ r) (hA : 0 ≤ A) (hu : Measurable u)
    (hubound : ∀ y ∈ s, ‖u y‖ ≤ A) :
    Integrable (s.indicator fun y ↦ ‖u y‖ ^ r) ν := by
  let v : Y → ℝ := s.indicator fun y ↦ ‖u y‖ ^ r
  let c : ℝ := A ^ r
  have hvmeas : AEStronglyMeasurable v ν := by
    dsimp [v]
    exact (by fun_prop : Measurable (fun y ↦ ‖u y‖ ^ r)).aestronglyMeasurable.indicator hs
  have hcint : Integrable (s.indicator fun _ : Y ↦ c) ν := by
    rw [integrable_indicator_iff hs]
    exact integrableOn_const hsfin.ne
  apply hcint.mono hvmeas
  filter_upwards with y
  by_cases hys : y ∈ s
  · simp only [v, c, Set.indicator_of_mem hys]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hA _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hubound y hys) hr
  · simp [v, hys]
private theorem ofReal_norm_integral_phase_power_eq_setLIntegral_enorm_rpow
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u : Y → ℂ}
    {s : Set Y} {r A : ℝ} (hs : MeasurableSet s) (hsfin : ν s < ∞)
    (hr : 1 < r) (hA : 0 ≤ A) (hu : Measurable u)
    (hubound : ∀ y ∈ s, ‖u y‖ ≤ A) :
    ENNReal.ofReal
        ‖∫ y, u y * s.indicator (fun y ↦
          (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ)) y ∂ν‖ =
      (∫⁻ y in s, ‖u y‖ₑ ^ r ∂ν) := by
  let g : Y → ℂ := s.indicator (fun y ↦
    (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ))
  let v : Y → ℝ := s.indicator (fun y ↦ ‖u y‖ ^ r)
  have hprod : (fun y ↦ u y * g y) = fun y ↦ (v y : ℂ) := by
    funext y
    by_cases hys : y ∈ s
    · simp only [g, v, Set.indicator_of_mem hys]
      exact mul_phase_power hr _
    · simp [g, v, hys]
  have hvint : Integrable v ν := by
    exact integrable_indicator_norm_rpow_of_bound hs hsfin (by linarith) hA hu hubound
  have hvnonneg : 0 ≤ ∫ y, v y ∂ν :=
    integral_nonneg fun y ↦ by
      by_cases hys : y ∈ s <;> simp [v, hys, Real.rpow_nonneg]
  have hnorm_int : ‖∫ y, u y * g y ∂ν‖ = ∫ y, v y ∂ν := by
    rw [hprod, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hvnonneg]
  rw [show (∫ y, u y * s.indicator (fun y ↦
      (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ)) y ∂ν) =
      ∫ y, u y * g y ∂ν by rfl, hnorm_int]
  calc
    ENNReal.ofReal (∫ y, v y ∂ν) = ∫⁻ y, ENNReal.ofReal (v y) ∂ν :=
      ofReal_integral_eq_lintegral_ofReal hvint
        (Eventually.of_forall fun y ↦ by
          by_cases hys : y ∈ s <;> simp [v, hys, Real.rpow_nonneg])
    _ = ∫⁻ y, s.indicator (fun y ↦ ‖u y‖ₑ ^ r) y ∂ν := by
      apply lintegral_congr
      intro y
      by_cases hys : y ∈ s
      · simp only [v, Set.indicator_of_mem hys]
        rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]
        rw [ofReal_norm]
      · simp [v, hys]
    _ = ∫⁻ y in s, ‖u y‖ₑ ^ r ∂ν := lintegral_indicator hs _
private theorem eLpNorm_phase_power
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u : Y → ℂ}
    {s : Set Y} {r : ℝ} {q' : ENNReal} (hs : MeasurableSet s)
    (hr : 1 < r) (hq'0 : q' ≠ 0) (hq'top : q' ≠ ∞)
    (hq' : q'.toReal = r / (r - 1)) :
    eLpNorm (s.indicator (fun y ↦
        (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ))) q' ν =
      (∫⁻ y in s, ‖u y‖ₑ ^ r ∂ν) ^ (1 / q'.toReal) := by
  let g : Y → ℂ := s.indicator (fun y ↦
    (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ))
  have hpow : ∀ y : Y, ‖g y‖ₑ ^ q'.toReal =
      s.indicator (fun y ↦ ‖u y‖ₑ ^ r) y := by
    intro y
    by_cases hys : y ∈ s
    · simp only [g, Set.indicator_of_mem hys]
      rw [← ofReal_norm, norm_phase_power hr, ← ofReal_norm]
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]
      rw [← ENNReal.rpow_mul]
      congr 1
      rw [hq']
      field_simp [(sub_pos.mpr hr).ne']
    · simp [g, hys, ENNReal.toReal_pos hq'0 hq'top]
  rw [show (s.indicator (fun y ↦
      (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ))) = g by rfl,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq'0 hq'top]
  rw [show (fun y ↦ ‖g y‖ₑ ^ q'.toReal) =
      s.indicator (fun y ↦ ‖u y‖ₑ ^ r) by funext y; exact hpow y]
  rw [lintegral_indicator hs]
private theorem rpow_inv_le_of_le_mul_rpow
    {I c : ENNReal} {r d : ℝ} (hr : 0 < r) (hdpos : 0 < d)
    (hd : 1 / r + 1 / d = 1)
    (hIfin : I ≠ ∞) (h : I ≤ c * I ^ (1 / d)) :
    I ^ (1 / r) ≤ c := by
  by_cases hI : I = 0
  · have hri : 0 < 1 / r := one_div_pos.mpr hr
    rw [hI, ENNReal.zero_rpow_of_pos hri]
    exact bot_le
  have hIpos : 0 < I := pos_iff_ne_zero.mpr hI
  have hpowpos : 0 < I ^ (1 / d) := ENNReal.rpow_pos hIpos hIfin
  have hpowfin : I ^ (1 / d) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hdpos.le) hIfin
  rw [← ENNReal.mul_le_mul_iff_left hpowpos.ne' hpowfin]
  calc
    I ^ (1 / r) * I ^ (1 / d) = I ^ (1 / r + 1 / d) :=
      (ENNReal.rpow_add _ _ hI hIfin).symm
    _ = I := by rw [hd, ENNReal.rpow_one]
    _ ≤ c * I ^ (1 / d) := h
private theorem eLpNorm_indicator_eq_setLIntegral_enorm_rpow
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u : Y → ℂ}
    {s : Set Y} {r : ℝ} (hs : MeasurableSet s) (hr : 0 < r) :
    eLpNorm (s.indicator u) (ENNReal.ofReal r) ν =
      (∫⁻ y in s, ‖u y‖ₑ ^ r ∂ν) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
  · rw [ENNReal.toReal_ofReal hr.le]
    rw [show (fun y ↦ ‖s.indicator u y‖ₑ ^ r) =
        s.indicator (fun y ↦ ‖u y‖ₑ ^ r) by
      funext y
      by_cases hys : y ∈ s <;> simp [hys,
        ENNReal.zero_rpow_of_pos hr]]
    rw [lintegral_indicator hs]
  · exact ne_of_gt ((ENNReal.ofReal_pos).mpr hr)
  · exact ENNReal.ofReal_ne_top
private theorem conjExponent_ofReal
    {r : ℝ} (hr : 1 < r) :
    (ENNReal.ofReal r).conjExponent = ENNReal.ofReal (r / (r - 1)) := by
  have : ENNReal.HolderConjugate (ENNReal.ofReal r)
      (ENNReal.ofReal (r / (r - 1))) :=
    (Real.HolderConjugate.conjExponent hr).ennrealOfReal
  exact ENNReal.HolderConjugate.conjExponent_eq
private theorem eLpNorm_indicator_le_of_phase_power_pairing
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u : Y → ℂ}
    {s : Set Y} {r C A : ℝ} (hs : MeasurableSet s) (hsfin : ν s < ∞)
    (hr : 1 < r) (hC : 0 ≤ C) (hA : 0 ≤ A) (hu : Measurable u)
    (hubound : ∀ y ∈ s, ‖u y‖ ≤ A)
    (hphase :
      ‖∫ y, u y * s.indicator (fun y ↦
        (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ)) y ∂ν‖ ≤
        C * (eLpNorm (s.indicator (fun y ↦
          (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ)))
          (ENNReal.ofReal (r / (r - 1))) ν).toReal) :
    eLpNorm (s.indicator u) (ENNReal.ofReal r) ν ≤ ENNReal.ofReal C := by
  let q' : ENNReal := ENNReal.ofReal (r / (r - 1))
  let I : ENNReal := ∫⁻ y in s, ‖u y‖ₑ ^ r ∂ν
  have hrpos : 0 < r := by linarith
  have hrsubpos : 0 < r - 1 := by linarith
  have hq'rpos : 0 < r / (r - 1) := div_pos hrpos hrsubpos
  have hq'0 : q' ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos).mpr hq'rpos)
  have hq'top : q' ≠ ∞ := ENNReal.ofReal_ne_top
  have hq'real : q'.toReal = r / (r - 1) :=
    ENNReal.toReal_ofReal hq'rpos.le
  have hid : ENNReal.ofReal
      ‖∫ y, u y * s.indicator (fun y ↦
        (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ)) y ∂ν‖ = I := by
    exact ofReal_norm_integral_phase_power_eq_setLIntegral_enorm_rpow
      hs hsfin hr hA hu hubound
  have hIfin : I ≠ ∞ := by
    rw [← hid]
    exact ENNReal.ofReal_ne_top
  have htestnorm : eLpNorm (s.indicator (fun y ↦
      (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ))) q' ν =
      I ^ (1 / q'.toReal) := by
    exact eLpNorm_phase_power hs hr hq'0 hq'top hq'real
  have htestfin : eLpNorm (s.indicator (fun y ↦
      (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ))) q' ν ≠ ∞ := by
    rw [htestnorm]
    exact ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr (ENNReal.toReal_nonneg)) hIfin
  have hI : I ≤ ENNReal.ofReal C * I ^ (1 / q'.toReal) := by
    calc
      I = ENNReal.ofReal
          ‖∫ y, u y * s.indicator (fun y ↦
            (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ)) y ∂ν‖ := hid.symm
      _ ≤ ENNReal.ofReal (C *
          (eLpNorm (s.indicator (fun y ↦
            (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ))) q' ν).toReal) :=
          ENNReal.ofReal_le_ofReal (by simpa only [q'] using hphase)
      _ = ENNReal.ofReal C *
          eLpNorm (s.indicator (fun y ↦
            (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ))) q' ν := by
          rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal htestfin]
      _ = ENNReal.ofReal C * I ^ (1 / q'.toReal) := by rw [htestnorm]
  have hsplit : 1 / r + 1 / q'.toReal = 1 := by
    rw [hq'real]
    field_simp [hrpos.ne', hrsubpos.ne']
    ring
  have hroot : I ^ (1 / r) ≤ ENNReal.ofReal C :=
    rpow_inv_le_of_le_mul_rpow hrpos (ENNReal.toReal_pos hq'0 hq'top) hsplit hIfin hI
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
  · rw [ENNReal.toReal_ofReal hrpos.le]
    change (∫⁻ y, ‖s.indicator u y‖ₑ ^ r ∂ν) ^ (1 / r) ≤ _
    rw [show (fun y ↦ ‖s.indicator u y‖ₑ ^ r) =
        s.indicator (fun y ↦ ‖u y‖ₑ ^ r) by
      funext y
      by_cases hys : y ∈ s <;> simp [hys,
        ENNReal.zero_rpow_of_pos hrpos]]
    rw [lintegral_indicator hs]
    exact hroot
  · exact ne_of_gt ((ENNReal.ofReal_pos).mpr hrpos)
  · exact ENNReal.ofReal_ne_top
private theorem memLp_of_local_eLpNorm_indicator_le
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν]
    {u : Y → ℂ} {r C : ℝ} (hr : 1 < r) (_hC : 0 ≤ C) (hu : Measurable u)
    (hlocal : ∀ (s : Set Y) (A : ℝ), MeasurableSet s → ν s < ∞ → 0 ≤ A →
      (∀ y ∈ s, ‖u y‖ ≤ A) →
      eLpNorm (s.indicator u) (ENNReal.ofReal r) ν ≤ ENNReal.ofReal C) :
    MemLp u (ENNReal.ofReal r) ν ∧
      eLpNorm u (ENNReal.ofReal r) ν ≤ ENNReal.ofReal C := by
  let s : ℕ → Set Y := fun n ↦
    spanningSets ν n ∩ {y | ‖u y‖ ≤ (n : ℝ)}
  let F : ℕ → Y → ENNReal := fun n ↦
    (s n).indicator (fun y ↦ ‖u y‖ₑ ^ r)
  have hrpos : 0 < r := by linarith
  have hsmeas : ∀ n, MeasurableSet (s n) := by
    intro n
    exact (measurableSet_spanningSets ν n).inter
      (measurableSet_le hu.norm measurable_const)
  have hsfin : ∀ n, ν (s n) < ∞ := by
    intro n
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (measure_spanningSets_lt_top ν n)
  have hsmono : Monotone s := by
    intro m n hmn y hym
    rcases hym with ⟨hyspan, hybound⟩
    constructor
    · exact spanningSets_mono hmn hyspan
    · change ‖u y‖ ≤ (m : ℝ) at hybound
      change ‖u y‖ ≤ (n : ℝ)
      exact hybound.trans (by exact_mod_cast hmn)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    exact (ENNReal.continuous_rpow_const.measurable.comp hu.enorm).indicator (hsmeas n)
  have hFmono : Monotone F := by
    intro m n hmn y
    by_cases hym : y ∈ s m
    · have hyn : y ∈ s n := hsmono hmn hym
      simp [F, hym, hyn]
    · by_cases hyn : y ∈ s n
      · simp [F, hym, hyn]
      · simp [F, hym, hyn]
  have hFsup : (⨆ n, F n) = fun y ↦ ‖u y‖ₑ ^ r := by
    funext y
    rw [iSup_apply]
    apply le_antisymm
    · exact iSup_le fun n : ℕ ↦ by
        by_cases hyn : y ∈ s n <;> simp [F, hyn]
    · have hyspan : y ∈ ⋃ n, spanningSets ν n := by
        rw [iUnion_spanningSets]
        trivial
      obtain ⟨m, hym⟩ := Set.mem_iUnion.mp hyspan
      obtain ⟨n, hyn⟩ := exists_nat_ge ‖u y‖
      let k : ℕ := max m n
      have hyk : y ∈ s k := by
        constructor
        · exact spanningSets_mono (le_max_left _ _) hym
        · exact hyn.trans (by exact_mod_cast (le_max_right m n))
      calc
        ‖u y‖ₑ ^ r = F k y := by simp [F, hyk]
        _ ≤ ⨆ n : ℕ, F n y := le_iSup (fun n : ℕ ↦ F n y) k
  have hlin : (∫⁻ y, ‖u y‖ₑ ^ r ∂ν) ≤ (ENNReal.ofReal C) ^ r := by
    rw [← hFsup]
    rw [show (⨆ n, F n) = fun y ↦ ⨆ n, F n y by
      funext y
      rw [iSup_apply]]
    rw [lintegral_iSup hFmeas hFmono]
    refine iSup_le fun n : ℕ ↦ ?_
    change (∫⁻ y, (s n).indicator (fun y ↦ ‖u y‖ₑ ^ r) y ∂ν) ≤ _
    rw [lintegral_indicator (hsmeas n)]
    have hbound : ∀ y ∈ s n, ‖u y‖ ≤ (n : ℝ) := by
      intro y hy
      exact hy.2
    have hnorm := hlocal (s n) (n : ℝ) (hsmeas n) (hsfin n) (by positivity) hbound
    rw [eLpNorm_indicator_eq_setLIntegral_enorm_rpow (hsmeas n) hrpos] at hnorm
    apply (ENNReal.rpow_inv_le_iff hrpos).mp
    simpa only [one_div] using hnorm
  have hnorm : eLpNorm u (ENNReal.ofReal r) ν ≤ ENNReal.ofReal C := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
    · rw [ENNReal.toReal_ofReal hrpos.le]
      simpa only [one_div] using (ENNReal.rpow_inv_le_iff hrpos).mpr hlin
    · exact ne_of_gt ((ENNReal.ofReal_pos).mpr hrpos)
    · exact ENNReal.ofReal_ne_top
  exact ⟨⟨hu.aestronglyMeasurable, hnorm.trans_lt ENNReal.ofReal_lt_top⟩, hnorm⟩
private theorem memLp_of_pairing_bounds_finite
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν]
    {u : Y → ℂ} {r C : ℝ} (hr : 1 < r) (hC : 0 ≤ C) (hu : Measurable u)
    (hlocal_int : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      Integrable (s.indicator u) ν)
    (hbound : ∀ h : SimpleFunc Y ℂ, Integrable h ν →
      norm (∫ y, u y * h y ∂ν) ≤ C *
        (eLpNorm (h : Y → ℂ) (ENNReal.ofReal (r / (r - 1))) ν).toReal) :
    MemLp u (ENNReal.ofReal r) ν ∧
      eLpNorm u (ENNReal.ofReal r) ν ≤ ENNReal.ofReal C := by
  apply memLp_of_local_eLpNorm_indicator_le hr hC hu
  intro s A hs hsfin hA hubound
  apply eLpNorm_indicator_le_of_phase_power_pairing hs hsfin hr hC hA hu hubound
  let g : Y → ℂ := s.indicator (fun y ↦
    (star (u y) / (‖u y‖ : ℂ)) * ((‖u y‖ ^ (r - 1) : ℝ) : ℂ))
  have hg : Measurable g := by
    exact (measurable_phase_power (by linarith) hu).indicator hs
  have hgsupp : ∀ y, y ∉ s → g y = 0 := by
    intro y hys
    simp [g, hys]
  have hgbound : ∀ y, ‖g y‖ ≤ A ^ (r - 1) := by
    intro y
    by_cases hys : y ∈ s
    · simp only [g, Set.indicator_of_mem hys]
      rw [norm_phase_power hr]
      exact Real.rpow_le_rpow (norm_nonneg _) (hubound y hys) (by linarith)
    · simp [g, hys, Real.rpow_nonneg hA]
  have hq'pos : 0 < r / (r - 1) :=
    div_pos (by linarith) (by linarith)
  have hphase := pairing_bound_of_bounded_support hs hsfin
    (Real.rpow_nonneg hA _) hu (hlocal_int s hs hsfin) hg hgsupp hgbound
    (ne_of_gt ((ENNReal.ofReal_pos).mpr hq'pos)) ENNReal.ofReal_ne_top hbound
  simpa only [g] using hphase
private theorem memLp_of_pairing_bounds_finite_ennreal
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν]
    {u : Y → ℂ} {q : ENNReal} {C : ℝ} (hqone : 1 < q) (hqtop : q ≠ ∞)
    (hC : 0 ≤ C) (hu : Measurable u)
    (hlocal_int : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      Integrable (s.indicator u) ν)
    (hbound : ∀ h : SimpleFunc Y ℂ, Integrable h ν →
      norm (∫ y, u y * h y ∂ν) ≤ C *
        (eLpNorm (h : Y → ℂ) q.conjExponent ν).toReal) :
    MemLp u q ν ∧ eLpNorm u q ν ≤ ENNReal.ofReal C := by
  let r : ℝ := q.toReal
  have hr : 1 < r := by
    dsimp [r]
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqtop).mpr hqone
  have hqeq : ENNReal.ofReal r = q := by
    exact ENNReal.ofReal_toReal hqtop
  have hconj : q.conjExponent = ENNReal.ofReal (r / (r - 1)) := by
    rw [← hqeq]
    exact conjExponent_ofReal hr
  have hbound' : ∀ h : SimpleFunc Y ℂ, Integrable h ν →
      norm (∫ y, u y * h y ∂ν) ≤ C *
        (eLpNorm (h : Y → ℂ) (ENNReal.ofReal (r / (r - 1))) ν).toReal := by
    intro h hh
    simpa only [hconj] using hbound h hh
  simpa only [hqeq] using memLp_of_pairing_bounds_finite hr hC hu hlocal_int hbound'
private theorem memLp_of_pairing_bound
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν]
    {u : Y → ℂ} {q : ENNReal} {C : ℝ} (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hu : Measurable u)
    (hlocal_int : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      Integrable (s.indicator u) ν)
    (hbound : ∀ h : SimpleFunc Y ℂ, Integrable h ν →
      ‖∫ y, u y * h y ∂ν‖ ≤ C *
        (eLpNorm (h : Y → ℂ) q.conjExponent ν).toReal) :
    MemLp u q ν ∧ eLpNorm u q ν ≤ ENNReal.ofReal C := by
  rcases eq_or_lt_of_le hq with hqeq | hqone
  · subst q
    have hconj : (1 : ENNReal).conjExponent = ∞ := by
      simp [ENNReal.conjExponent]
    rw [hconj] at hbound
    apply memLp_one_of_phase_tests hu hlocal_int
    intro s hs hsfin hus
    let g : Y → ℂ := s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ))
    have hg : Measurable g := (measurable_phase hu).indicator hs
    have hgsupp : ∀ y, y ∉ s → g y = 0 := by
      intro y hys
      simp [g, hys]
    have hgbound : ∀ y, ‖g y‖ ≤ 1 := by
      intro y
      by_cases hys : y ∈ s
      · simp only [g, Set.indicator_of_mem hys]
        exact norm_phase_le_one _
      · simp [g, hys]
    exact pairing_bound_top_of_bounded_support hs hsfin hC hu hus hg hgsupp hgbound
      (fun h hh ↦ hbound h hh)
  by_cases hqtop : q = ∞
  · subst q
    have hconj : (∞ : ENNReal).conjExponent = 1 := by
      simp [ENNReal.conjExponent]
    rw [hconj] at hbound
    apply memLp_top_of_phase_tests hu hC hlocal_int
    intro s hs hsfin hus
    let g : Y → ℂ := s.indicator (fun y ↦ star (u y) / (‖u y‖ : ℂ))
    have hg : Measurable g := (measurable_phase hu).indicator hs
    have hgsupp : ∀ y, y ∉ s → g y = 0 := by
      intro y hys
      simp [g, hys]
    have hgbound : ∀ y, ‖g y‖ ≤ 1 := by
      intro y
      by_cases hys : y ∈ s
      · simp only [g, Set.indicator_of_mem hys]
        exact norm_phase_le_one _
      · simp [g, hys]
    exact pairing_bound_of_bounded_support hs hsfin zero_le_one hu hus hg hgsupp hgbound
      one_ne_zero ENNReal.one_ne_top (fun h hh ↦ hbound h hh)
  exact memLp_of_pairing_bounds_finite_ennreal hqone hqtop hC hu hlocal_int hbound
private theorem normalized_simple_smul_eLpNorm_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ENNReal}
    (f : SimpleFunc X ℂ) (hf : MemLp (f : X → ℂ) p μ)
    (hN : eLpNorm (f : X → ℂ) p μ ≠ 0) :
    eLpNorm ((((eLpNorm (f : X → ℂ) p μ).toReal)⁻¹ : ℂ) • f : X → ℂ) p μ ≤ 1 := by
  let N : ENNReal := eLpNorm (f : X → ℂ) p μ
  let a : ℝ := N.toReal
  have hNfin : N ≠ ∞ := hf.eLpNorm_lt_top.ne
  have ha : 0 < a := ENNReal.toReal_pos hN hNfin
  calc
    eLpNorm ((a⁻¹ : ℂ) • (f : X → ℂ)) p μ ≤ ‖(a⁻¹ : ℂ)‖ₑ * N :=
      eLpNorm_const_smul_le
    _ = 1 := by
      rw [← ofReal_norm, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ha]
      rw [ENNReal.ofReal_inv_of_pos ha]
      change (ENNReal.ofReal N.toReal)⁻¹ * N = 1
      rw [ENNReal.ofReal_toReal hNfin, ENNReal.inv_mul_cancel hN hNfin]
private theorem bilinear_zero_left_of_unit
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p r : ENNReal} {C : ℝ}
    (B : SimpleFunc X ℂ → SimpleFunc Y ℂ → ℂ)
    (hleft : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ) (c : ℂ),
      Integrable (f : X → ℂ) μ → B (c • f) g = c * B f g)
    (hright : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ) (c : ℂ),
      B f (c • g) = c * B f g)
    (hunit : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable (f : X → ℂ) μ → Integrable (g : Y → ℂ) ν →
      MemLp (f : X → ℂ) p μ → MemLp (g : Y → ℂ) r ν →
      eLpNorm (f : X → ℂ) p μ ≤ 1 → eLpNorm (g : Y → ℂ) r ν ≤ 1 →
      ‖B f g‖ ≤ C)
    (hzero_right : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable (g : Y → ℂ) ν → eLpNorm (g : Y → ℂ) r ν = 0 → B f g = 0)
    (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ)
    (hf_int : Integrable (f : X → ℂ) μ) (hg_int : Integrable (g : Y → ℂ) ν)
    (hf : MemLp (f : X → ℂ) p μ) (hg : MemLp (g : Y → ℂ) r ν)
    (hNf : eLpNorm (f : X → ℂ) p μ = 0) :
    B f g = 0 := by
  by_cases hNg : eLpNorm (g : Y → ℂ) r ν = 0
  · exact hzero_right f g hg_int hNg
  let Ng : ENNReal := eLpNorm (g : Y → ℂ) r ν
  let b : ℝ := Ng.toReal
  have hNgfin : Ng ≠ ∞ := hg.eLpNorm_lt_top.ne
  have hb : 0 < b := ENNReal.toReal_pos hNg hNgfin
  let g' : SimpleFunc Y ℂ := (b⁻¹ : ℂ) • g
  have hg'_int : Integrable (g' : Y → ℂ) ν := hg_int.smul _
  have hg' : MemLp (g' : Y → ℂ) r ν := hg.const_smul _
  have hgnorm : eLpNorm (g' : Y → ℂ) r ν ≤ 1 := by
    change eLpNorm ((b⁻¹ : ℂ) • (g : Y → ℂ)) r ν ≤ 1
    exact normalized_simple_smul_eLpNorm_le_one g hg hNg
  have hf_n : ∀ n : ℕ, MemLp (((n : ℂ) • f : SimpleFunc X ℂ) : X → ℂ) p μ :=
    fun n ↦ hf.const_smul _
  have hf_n_int : ∀ n : ℕ,
      Integrable (((n : ℂ) • f : SimpleFunc X ℂ) : X → ℂ) μ :=
    fun n ↦ hf_int.smul _
  have hfnorm : ∀ n : ℕ,
      eLpNorm (((n : ℂ) • f : SimpleFunc X ℂ) : X → ℂ) p μ ≤ 1 := by
    intro n
    change eLpNorm ((n : ℂ) • (f : X → ℂ)) p μ ≤ 1
    rw [eLpNorm_const_smul]
    simp [hNf]
  have hfg' : B f g' = 0 := by
    by_contra hfg'
    have hpos : 0 < ‖B f g'‖ := norm_pos_iff.mpr hfg'
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖B f g'‖)
    have hnC : C < (n : ℝ) * ‖B f g'‖ := (div_lt_iff₀ hpos).mp hn
    have hunitn := hunit ((n : ℂ) • f) g' (hf_n_int n) hg'_int
      (hf_n n) hg' (hfnorm n) hgnorm
    have hnle : (n : ℝ) * ‖B f g'‖ ≤ C := by
      calc
        (n : ℝ) * ‖B f g'‖ = ‖(n : ℂ) * B f g'‖ := by
          rw [norm_mul]
          simp
        _ = ‖B ((n : ℂ) • f) g'‖ := by rw [hleft f g' _ hf_int]
        _ ≤ C := hunitn
    linarith
  have hgscale : g = (b : ℂ) • g' := by
    simp [g', hb.ne']
  rw [hgscale, hright, hfg']
  simp
private theorem integral_mul_simpleFunc_eq_zero_of_eLpNorm_eq_zero
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {u : Y → ℂ} {g : SimpleFunc Y ℂ} {q : ENNReal}
    (hq : 1 ≤ q) (hg : Integrable (g : Y → ℂ) ν)
    (hzero : eLpNorm (g : Y → ℂ) q.conjExponent ν = 0) :
    ∫ y, u y * g y ∂ν = 0 := by
  have hq' : q.conjExponent ≠ 0 := by
    apply ne_of_gt
    let q' := q.conjExponent
    have : q.HolderConjugate q' := ENNReal.HolderConjugate.conjExponent hq
    exact zero_lt_one.trans_le (ENNReal.HolderConjugate.one_le q' q)
  have hgLp : MemLp (g : Y → ℂ) q.conjExponent ν :=
    g.memLp_of_finite_measure_preimage _ (SimpleFunc.integrable_iff.mp hg)
  have hzeroae : (g : Y → ℂ) =ᵐ[ν] 0 :=
    (eLpNorm_eq_zero_iff hgLp.1 hq').mp hzero
  apply integral_eq_zero_of_ae
  filter_upwards [hzeroae] with y hy
  simp [hy]
private theorem integral_pairing_smul_left
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ)
    (hT_smul : ∀ (z : verticalClosedStrip 0 1) (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T z (c • f) = c • T z f)
    (z : verticalClosedStrip 0 1) (c : ℂ)
    (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ) (hf : Integrable f μ) :
    (∫ y, T z (c • f) y * g y ∂ν) =
      c * (∫ y, T z f y * g y ∂ν) := by
  rw [hT_smul z c f hf]
  calc
    (∫ y, (c • T z f) y * g y ∂ν) =
        ∫ y, c * (T z f y * g y) ∂ν := by
      congr 1
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c * (∫ y, T z f y * g y ∂ν) := integral_const_mul _ _
private theorem integral_pairing_smul_right
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} (T : ℂ → SimpleFunc X ℂ → Y → ℂ)
    (z : ℂ) (c : ℂ) (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ) :
    (∫ y, T z f y * (c • g) y ∂ν) =
      c * (∫ y, T z f y * g y ∂ν) := by
  calc
    (∫ y, T z f y * (c • g) y ∂ν) =
        ∫ y, c * (T z f y * g y) ∂ν := by
      congr 1
      funext y
      rw [SimpleFunc.smul_apply]
      simp only [smul_eq_mul]
      ring
    _ = c * (∫ y, T z f y * g y ∂ν) := integral_const_mul _ _
private theorem bilinear_bound_of_unit
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p r : ENNReal} {C : ℝ}
    (B : SimpleFunc X ℂ → SimpleFunc Y ℂ → ℂ)
    (hleft : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ) (c : ℂ),
      Integrable (f : X → ℂ) μ → B (c • f) g = c * B f g)
    (hright : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ) (c : ℂ),
      B f (c • g) = c * B f g)
    (hunit : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable (f : X → ℂ) μ → Integrable (g : Y → ℂ) ν →
      MemLp (f : X → ℂ) p μ → MemLp (g : Y → ℂ) r ν →
      eLpNorm (f : X → ℂ) p μ ≤ 1 → eLpNorm (g : Y → ℂ) r ν ≤ 1 →
      ‖B f g‖ ≤ C)
    (hzero_left : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable (f : X → ℂ) μ → Integrable (g : Y → ℂ) ν →
      eLpNorm (f : X → ℂ) p μ = 0 → B f g = 0)
    (hzero_right : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable (g : Y → ℂ) ν → eLpNorm (g : Y → ℂ) r ν = 0 → B f g = 0)
    (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ)
    (hf_int : Integrable (f : X → ℂ) μ) (hg_int : Integrable (g : Y → ℂ) ν)
    (hf : MemLp (f : X → ℂ) p μ) (hg : MemLp (g : Y → ℂ) r ν) :
    ‖B f g‖ ≤ C * (eLpNorm (f : X → ℂ) p μ).toReal *
      (eLpNorm (g : Y → ℂ) r ν).toReal := by
  let Nf : ENNReal := eLpNorm (f : X → ℂ) p μ
  let Ng : ENNReal := eLpNorm (g : Y → ℂ) r ν
  by_cases hNf : Nf = 0
  · have hzero : B f g = 0 := by
      apply hzero_left f g hf_int hg_int
      exact hNf
    change eLpNorm (f : X → ℂ) p μ = 0 at hNf
    rw [hzero]
    simp [hNf]
  by_cases hNg : Ng = 0
  · have hzero : B f g = 0 := by
      apply hzero_right f g hg_int
      exact hNg
    change eLpNorm (g : Y → ℂ) r ν = 0 at hNg
    rw [hzero]
    simp [hNg]
  let a : ℝ := Nf.toReal
  let b : ℝ := Ng.toReal
  have hNf_fin : Nf ≠ ∞ := hf.eLpNorm_lt_top.ne
  have hNg_fin : Ng ≠ ∞ := hg.eLpNorm_lt_top.ne
  have ha : 0 < a := ENNReal.toReal_pos hNf hNf_fin
  have hb : 0 < b := ENNReal.toReal_pos hNg hNg_fin
  let f' : SimpleFunc X ℂ := (a⁻¹ : ℂ) • f
  let g' : SimpleFunc Y ℂ := (b⁻¹ : ℂ) • g
  have hf'_int : Integrable (f' : X → ℂ) μ := hf_int.smul _
  have hg'_int : Integrable (g' : Y → ℂ) ν := hg_int.smul _
  have hf' : MemLp (f' : X → ℂ) p μ := hf.const_smul _
  have hg' : MemLp (g' : Y → ℂ) r ν := hg.const_smul _
  have hfnorm : eLpNorm (f' : X → ℂ) p μ ≤ 1 := by
    change eLpNorm ((a⁻¹ : ℂ) • (f : X → ℂ)) p μ ≤ 1
    exact normalized_simple_smul_eLpNorm_le_one f hf hNf
  have hgnorm : eLpNorm (g' : Y → ℂ) r ν ≤ 1 := by
    change eLpNorm ((b⁻¹ : ℂ) • (g : Y → ℂ)) r ν ≤ 1
    exact normalized_simple_smul_eLpNorm_le_one g hg hNg
  have hunit' : ‖B f' g'‖ ≤ C := hunit f' g' hf'_int hg'_int hf' hg' hfnorm hgnorm
  have hfscale : f = (a : ℂ) • f' := by
    simp [f', ha.ne']
  have hgscale : g = (b : ℂ) • g' := by
    simp [g', hb.ne']
  have hscale : B f g = (a : ℂ) * (b : ℂ) * B f' g' := by
    calc
      B f g = B ((a : ℂ) • f') ((b : ℂ) • g') := by rw [hfscale, hgscale]
      _ = (a : ℂ) * B f' ((b : ℂ) • g') := hleft f' _ _ hf'_int
      _ = (a : ℂ) * (b : ℂ) * B f' g' := by rw [hright]; ring
  calc
    ‖B f g‖ = a * b * ‖B f' g'‖ := by
      rw [hscale, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
    _ ≤ a * b * C := mul_le_mul_of_nonneg_left hunit' (mul_nonneg ha.le hb.le)
    _ = C * Nf.toReal * Ng.toReal := by
      dsimp [a, b]
      ring
private theorem interpolation_from_pairing_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {p q : ENNReal} (T : SimpleFunc X ℂ → Y → ℂ) (hq : 1 ≤ q)
    (hT_measurable : ∀ f : SimpleFunc X ℂ, Integrable f μ → Measurable (T f))
    (hpair_integrable : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν → Integrable (fun y ↦ T f y * g y) ν)
    {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν →
      ‖∫ y, T f y * g y ∂ν‖ ≤ C * (eLpNorm (f : X → ℂ) p μ).toReal *
        (eLpNorm (g : Y → ℂ) q.conjExponent ν).toReal) :
    ∀ f : SimpleFunc X ℂ, Integrable f μ →
      MemLp (T f) q ν ∧
        eLpNorm (T f) q ν ≤ ENNReal.ofReal C * eLpNorm (f : X → ℂ) p μ := by
  intro f hf
  let N : ENNReal := eLpNorm (f : X → ℂ) p μ
  have hfLp : MemLp (f : X → ℂ) p μ := memLp_simpleFunc_of_integrable f hf
  have hNfin : N ≠ ∞ := by
    exact hfLp.eLpNorm_lt_top.ne
  let D : ℝ := C * N.toReal
  have hD : 0 ≤ D := mul_nonneg hC ENNReal.toReal_nonneg
  have hlocal_int : ∀ (s : Set Y), MeasurableSet s → ν s < ∞ →
      Integrable (s.indicator (T f)) ν := by
    intro s hs hsfin
    exact integrable_indicator_of_pairing
      (fun g hg ↦ hpair_integrable f g hf hg) hs hsfin
  obtain ⟨hmem, hnorm⟩ := memLp_of_pairing_bound hq hD (hT_measurable f hf) hlocal_int
    (fun g hg ↦ by
      calc
        ‖∫ y, T f y * g y ∂ν‖ ≤ C * N.toReal *
            (eLpNorm (g : Y → ℂ) q.conjExponent ν).toReal := by
          simpa only [N] using hpair f g hf hg
        _ = D * (eLpNorm (g : Y → ℂ) q.conjExponent ν).toReal := by
          simp only [D])
  refine ⟨hmem, ?_⟩
  calc
    eLpNorm (T f) q ν ≤ ENNReal.ofReal D := hnorm
    _ = ENNReal.ofReal C * N := by
      dsimp [D]
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hNfin]
    _ = ENNReal.ofReal C * eLpNorm (f : X → ℂ) p μ := rfl
private theorem diffContOnCl_const_mul_exp_affine
    (a b c : ℂ) (s : Set ℂ) :
    DiffContOnCl ℂ (fun z ↦ c * Complex.exp (a * z + b)) s := by
  apply Differentiable.diffContOnCl
  exact
    ((Complex.differentiable_exp.comp
      ((differentiable_id.const_mul a).add_const b)).const_mul c)
private theorem integrable_map_of_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) (hf : Integrable f μ) (φ : ℂ → ℂ) (hφ : φ 0 = 0) :
    Integrable (f.map φ : X → ℂ) μ :=
  (SimpleFunc.integrable_iff_finMeasSupp.mp hf).map hφ |>.integrable
private theorem norm_integral_mul_le_eLpNorm_mul
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {u g : Y → ℂ} {q : ENNReal} (hq : 1 ≤ q)
    (hu : MemLp u q ν) (hg : MemLp g q.conjExponent ν) :
    ‖∫ y, u y * g y ∂ν‖ ≤
      (eLpNorm u q ν).toReal * (eLpNorm g q.conjExponent ν).toReal := by
  let : ENNReal.HolderConjugate q q.conjExponent :=
    ENNReal.HolderConjugate.conjExponent hq
  have hprod :
      eLpNorm (fun y ↦ u y * g y) 1 ν ≤
        eLpNorm u q ν * eLpNorm g q.conjExponent ν := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hu.1 hg.1 (fun x y : ℂ ↦ x * y)
        1 (Eventually.of_forall fun _ ↦ by simp))
  calc
    ‖∫ y, u y * g y ∂ν‖ ≤ ∫ y, ‖u y * g y‖ ∂ν :=
      norm_integral_le_integral_norm _
    _ = (∫⁻ y, ‖u y * g y‖ₑ ∂ν).toReal :=
      integral_norm_eq_lintegral_enorm (hu.1.mul hg.1)
    _ = (eLpNorm (fun y ↦ u y * g y) 1 ν).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (eLpNorm u q ν * eLpNorm g q.conjExponent ν).toReal :=
      ENNReal.toReal_mono
        (ENNReal.mul_ne_top hu.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne) hprod
    _ = (eLpNorm u q ν).toReal * (eLpNorm g q.conjExponent ν).toReal :=
      ENNReal.toReal_mul
private theorem endpoint_pairing_bound_normalized
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p q : ENNReal} {M : ℝ}
    (T : SimpleFunc X ℂ → Y → ℂ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hT_measurable : ∀ f : SimpleFunc X ℂ, Integrable f μ → Measurable (T f))
    (hbound : ∀ f : SimpleFunc X ℂ, Integrable f μ →
      eLpNorm (T f) q ν ≤ ENNReal.ofReal M * eLpNorm (f : X → ℂ) p μ)
    (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ)
    (hf : Integrable (f : X → ℂ) μ) (hg : Integrable (g : Y → ℂ) ν)
    (hfnorm : eLpNorm (f : X → ℂ) p μ ≤ 1)
    (hgnorm : eLpNorm (g : Y → ℂ) q.conjExponent ν ≤ 1) :
    ‖∫ y, T f y * g y ∂ν‖ ≤ M := by
  have hTnorm : eLpNorm (T f) q ν ≤ ENNReal.ofReal M := by
    calc
      eLpNorm (T f) q ν ≤ ENNReal.ofReal M * eLpNorm (f : X → ℂ) p μ :=
        hbound f hf
      _ ≤ ENNReal.ofReal M * 1 := mul_le_mul_right hfnorm _
      _ = ENNReal.ofReal M := mul_one _
  have hTmem : MemLp (T f) q ν := by
    refine ⟨(hT_measurable f hf).aestronglyMeasurable, ?_⟩
    exact hTnorm.trans_lt ENNReal.ofReal_lt_top
  have hgmem : MemLp (g : Y → ℂ) q.conjExponent ν :=
    g.memLp_of_finite_measure_preimage _ (SimpleFunc.integrable_iff.mp hg)
  have hTreal : (eLpNorm (T f) q ν).toReal ≤ M := by
    simpa [ENNReal.toReal_ofReal hM] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hTnorm
  have hgreal : (eLpNorm (g : Y → ℂ) q.conjExponent ν).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hgnorm
  calc
    ‖∫ y, T f y * g y ∂ν‖ ≤
        (eLpNorm (T f) q ν).toReal *
          (eLpNorm (g : Y → ℂ) q.conjExponent ν).toReal :=
      norm_integral_mul_le_eLpNorm_mul hq hTmem hgmem
    _ ≤ M * 1 := mul_le_mul hTreal hgreal ENNReal.toReal_nonneg hM
    _ = M := mul_one _
private theorem boundary_pairing_bound_normalized
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p q : ENNReal} {M : ℝ}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ) (z : verticalClosedStrip 0 1)
    (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hT_measurable : ∀ (z : verticalClosedStrip 0 1) (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T z f))
    (hbound : ∀ f : SimpleFunc X ℂ, Integrable f μ →
      eLpNorm (T z f) q ν ≤ ENNReal.ofReal M * eLpNorm (f : X → ℂ) p μ)
    (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ)
    (hf : Integrable (f : X → ℂ) μ) (hg : Integrable (g : Y → ℂ) ν)
    (hfnorm : eLpNorm (f : X → ℂ) p μ ≤ 1)
    (hgnorm : eLpNorm (g : Y → ℂ) q.conjExponent ν ≤ 1) :
    ‖∫ y, T z f y * g y ∂ν‖ ≤ M := by
  exact endpoint_pairing_bound_normalized (T z) hq hM
    (hT_measurable z) hbound f g hf hg hfnorm hgnorm
private theorem left_boundary_pairing_bound_normalized
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p q : ENNReal} {M₀ : ℝ → ℝ}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ) (hq : 1 ≤ q)
    (hT_measurable : ∀ (z : verticalClosedStrip 0 1) (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T z f))
    (hbound₀ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T ((t : ℂ) * Complex.I) f) q ν ≤
        ENNReal.ofReal (M₀ t) * eLpNorm (f : X → ℂ) p μ)
    (hM₀ : ∀ t : ℝ, 0 ≤ M₀ t)
    (t : ℝ) (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ)
    (hf : Integrable (f : X → ℂ) μ) (hg : Integrable (g : Y → ℂ) ν)
    (hfnorm : eLpNorm (f : X → ℂ) p μ ≤ 1)
    (hgnorm : eLpNorm (g : Y → ℂ) q.conjExponent ν ≤ 1) :
    ‖∫ y, T ((t : ℂ) * Complex.I) f y * g y ∂ν‖ ≤ M₀ t := by
  let z : verticalClosedStrip 0 1 := ⟨(t : ℂ) * Complex.I, by
    rw [verticalClosedStrip, Set.mem_preimage, Set.mem_Icc]
    constructor <;> simp⟩
  have hz : (z : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [← hz]
  exact boundary_pairing_bound_normalized T z hq (hM₀ t) hT_measurable
    (hbound₀ t) f g hf hg hfnorm hgnorm
private theorem right_boundary_pairing_bound_normalized
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p q : ENNReal} {M₁ : ℝ → ℝ}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ) (hq : 1 ≤ q)
    (hT_measurable : ∀ (z : verticalClosedStrip 0 1) (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T z f))
    (hbound₁ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T (1 + (t : ℂ) * Complex.I) f) q ν ≤
        ENNReal.ofReal (M₁ t) * eLpNorm (f : X → ℂ) p μ)
    (hM₁ : ∀ t : ℝ, 0 ≤ M₁ t)
    (t : ℝ) (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ)
    (hf : Integrable (f : X → ℂ) μ) (hg : Integrable (g : Y → ℂ) ν)
    (hfnorm : eLpNorm (f : X → ℂ) p μ ≤ 1)
    (hgnorm : eLpNorm (g : Y → ℂ) q.conjExponent ν ≤ 1) :
    ‖∫ y, T (1 + (t : ℂ) * Complex.I) f y * g y ∂ν‖ ≤ M₁ t := by
  let z : verticalClosedStrip 0 1 := ⟨1 + (t : ℂ) * Complex.I, by
    rw [verticalClosedStrip, Set.mem_preimage, Set.mem_Icc]
    constructor <;> simp⟩
  have hz : (z : ℂ) = 1 + (t : ℂ) * Complex.I := rfl
  rw [← hz]
  exact boundary_pairing_bound_normalized T z hq (hM₁ t) hT_measurable
    (hbound₁ t) f g hf hg hfnorm hgnorm
private theorem re_affine_im_mul_ofReal
    (a b l t : ℝ) :
    (((a : ℂ) * ((t : ℂ) * Complex.I) + (b : ℂ)) * (l : ℂ)).re = b * l := by
  simp [Complex.mul_re]
private theorem re_affine_one_im_mul_ofReal
    (a b l t : ℝ) :
    (((a : ℂ) * (1 + (t : ℂ) * Complex.I) + (b : ℂ)) * (l : ℂ)).re =
      (a + b) * l := by
  simp [Complex.mul_re]
private theorem input_deformation_at_theta
    {a₀ a₁ θ : ℝ}
    (hθ : a₀ + θ * (a₁ - a₀) = 1) (c : ℂ) :
    (if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (θ : ℂ) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))) = c := by
  by_cases hc : c = 0
  · simp [hc]
  · simp only [if_neg hc]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have harg :
        ((((a₁ - a₀ : ℝ) : ℂ) * (θ : ℂ) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ)) =
          ((Real.log ‖c‖ : ℝ) : ℂ) := by
      norm_cast
      have hcoef : (a₁ - a₀) * θ + a₀ = 1 := by linarith [hθ]
      rw [hcoef]
      ring
    rw [harg, ← Complex.ofReal_exp, Real.exp_log hcn]
    field_simp [hcn.ne']
private theorem norm_input_deformation_left_coeff
    {a₀ a₁ t : ℝ} (ha₀ : 0 < a₀) (c : ℂ) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))‖ =
      ‖c‖ ^ a₀ := by
  by_cases hc : c = 0
  · simp [hc, Real.zero_rpow ha₀.ne']
  · rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [div_self hcn.ne', one_mul,
      re_affine_im_mul_ofReal (a₁ - a₀) a₀ (Real.log ‖c‖) t,
      Real.rpow_def_of_pos hcn]
    ring_nf
private theorem norm_input_deformation_right_coeff
    {a₀ a₁ t : ℝ} (ha₁ : 0 < a₁) (c : ℂ) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))‖ =
      ‖c‖ ^ a₁ := by
  by_cases hc : c = 0
  · simp [hc, Real.zero_rpow ha₁.ne']
  · rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [div_self hcn.ne', one_mul,
      re_affine_one_im_mul_ofReal (a₁ - a₀) a₀ (Real.log ‖c‖) t,
      Real.rpow_def_of_pos hcn]
    congr 1
    ring
private theorem diffContOnCl_input_deformation_coeff
    {a₀ a₁ : ℝ} (c : ℂ) (U : Set ℂ) :
    DiffContOnCl ℂ (fun z ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * z + (a₀ : ℂ)) *
          ((Real.log ‖c‖ : ℝ) : ℂ))) U := by
  by_cases hc : c = 0
  · simpa [hc] using (diffContOnCl_const (𝕜 := ℂ) (s := U) (c := (0 : ℂ)))
  · simp only [if_neg hc]
    convert diffContOnCl_const_mul_exp_affine
      (((a₁ - a₀ : ℝ) : ℂ) * ((Real.log ‖c‖ : ℝ) : ℂ))
      ((a₀ : ℂ) * ((Real.log ‖c‖ : ℝ) : ℂ))
      (c / (‖c‖ : ℂ)) U using 1
    funext z
    congr 2
    ring
private theorem rpow_affine_le_max_one
    {r a₀ a₁ x : ℝ} (hr : 0 ≤ r) (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hx : x ∈ Set.Icc 0 1) :
    r ^ (a₀ + x * (a₁ - a₀)) ≤ max 1 (r ^ max a₀ a₁) := by
  have he_nonneg : 0 ≤ a₀ + x * (a₁ - a₀) := by
    rcases le_total a₀ a₁ with h | h
    · have : 0 ≤ x * (a₁ - a₀) := mul_nonneg hx.1 (sub_nonneg.mpr h)
      linarith
    · have h' : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
      have hrewrite : a₀ + x * (a₁ - a₀) = x * a₁ + (1 - x) * a₀ := by ring
      rw [hrewrite]
      exact add_nonneg (mul_nonneg hx.1 ha₁) (mul_nonneg h' ha₀)
  have he_le : a₀ + x * (a₁ - a₀) ≤ max a₀ a₁ := by
    rcases le_total a₀ a₁ with h | h
    · rw [max_eq_right h]
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr h),
        mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h)]
    · rw [max_eq_left h]
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr h),
        mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h)]
  rcases le_total r 1 with hr1 | hr1
  · exact (Real.rpow_le_one hr hr1 he_nonneg).trans (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le hr1 he_le).trans (le_max_right _ _)
private theorem norm_input_deformation_coeff_uniform
    {a₀ a₁ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (c z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * z + (a₀ : ℂ)) *
          ((Real.log ‖c‖ : ℝ) : ℂ))‖ ≤
      max 1 (‖c‖ ^ max a₀ a₁) := by
  by_cases hc : c = 0
  · simp [hc]
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hre : z.re ∈ Set.Icc 0 1 := hz
  have hpow := rpow_affine_le_max_one (r := ‖c‖) (norm_nonneg c) ha₀ ha₁ hre
  rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [div_self hcn.ne', one_mul]
  have hreal :
      (((((a₁ - a₀ : ℝ) : ℂ) * z + (a₀ : ℂ)) *
        ((Real.log ‖c‖ : ℝ) : ℂ))).re =
        (a₀ + z.re * (a₁ - a₀)) * Real.log ‖c‖ := by
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero]
    ring
  rw [hreal]
  calc
    Real.exp ((a₀ + z.re * (a₁ - a₀)) * Real.log ‖c‖) =
        ‖c‖ ^ (a₀ + z.re * (a₁ - a₀)) := by
      rw [Real.rpow_def_of_pos hcn]
      congr 1
      ring
    _ ≤ max 1 (‖c‖ ^ max a₀ a₁) := hpow
private theorem eLpNorm_simpleFunc_map_of_norm_rpow
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (φ : ℂ → ℂ) (hφ : ∀ c : ℂ, ‖φ c‖ = ‖c‖ ^ (r / s)) :
    eLpNorm (f.map φ : X → ℂ) (ENNReal.ofReal s) μ =
      eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ^ (r / s) := by
  have hrs : 0 ≤ r / s := (div_pos hr hs).le
  have hleft_int :
      (∫⁻ x, ‖(f.map φ : X → ℂ) x‖ₑ ^ s ∂μ) =
        ∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ r ∂μ := by
    apply lintegral_congr
    intro x
    rw [SimpleFunc.map_apply, ← ofReal_norm, hφ, ← ofReal_norm]
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hrs]
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [hr.ne', hs.ne']
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
  · rw [ENNReal.toReal_ofReal hs.le, hleft_int]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
    · rw [ENNReal.toReal_ofReal hr.le, ← ENNReal.rpow_mul]
      congr 1
      field_simp [hr.ne', hs.ne']
    · exact ne_of_gt ((ENNReal.ofReal_pos).mpr hr)
    · exact ENNReal.ofReal_ne_top
  · exact ne_of_gt ((ENNReal.ofReal_pos).mpr hs)
  · exact ENNReal.ofReal_ne_top
private theorem real_inv_interpolation
    {p p₀ p₁ : ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) :
    p.toReal⁻¹ = (1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹ := by
  have hθ0 : 0 ≤ θ := hθ.1.le
  have h1θ0 : 0 ≤ 1 - θ := by linarith [hθ.2]
  have hp₀0 : p₀ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp₀)
  have hp₁0 : p₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp₁)
  have hleft_top : ENNReal.ofReal (1 - θ) * p₀⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hp₀0)
  have hright_top : ENNReal.ofReal θ * p₁⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hp₁0)
  have h := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_inv, ENNReal.toReal_add hleft_top hright_top,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_inv] at h
  simpa [ENNReal.toReal_ofReal h1θ0, ENNReal.toReal_ofReal hθ0] using h
private theorem input_coeff_at_theta_of_interp_general
    {p p₀ p₁ : ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp : 1 ≤ p) (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp_top : p ≠ ∞)
    (hint : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    (p.toReal * p₀⁻¹.toReal) + θ *
      (p.toReal * p₁⁻¹.toReal - p.toReal * p₀⁻¹.toReal) = 1 := by
  have hreal := real_inv_interpolation hθ hint hp₀ hp₁
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hrpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have halg :
      (1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹ =
        p₀.toReal⁻¹ + θ * (p₁.toReal⁻¹ - p₀.toReal⁻¹) := by
    ring
  rw [halg] at hreal
  simp only [ENNReal.toReal_inv]
  calc
    p.toReal * p₀.toReal⁻¹ + θ *
        (p.toReal * p₁.toReal⁻¹ - p.toReal * p₀.toReal⁻¹) =
        p.toReal * (p₀.toReal⁻¹ + θ * (p₁.toReal⁻¹ - p₀.toReal⁻¹)) := by ring
    _ = p.toReal * p.toReal⁻¹ := by rw [hreal]
    _ = 1 := mul_inv_cancel₀ hrpos.ne'
private theorem simpleFunc_input_deformation_at_theta
    {X : Type*} [MeasurableSpace X] (f : SimpleFunc X ℂ)
    {a₀ a₁ θ : ℝ} (hθ : a₀ + θ * (a₁ - a₀) = 1) :
    f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (θ : ℂ) + (a₀ : ℂ)) *
          ((Real.log ‖c‖ : ℝ) : ℂ))) = f := by
  ext x
  rw [SimpleFunc.map_apply]
  exact input_deformation_at_theta hθ (f x)
private theorem norm_input_deformation_left_coeff_zero
    {a₀ a₁ t : ℝ} (ha₀ : a₀ = 0) (c : ℂ) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [div_self hcn.ne', one_mul,
      re_affine_im_mul_ofReal (a₁ - a₀) a₀ (Real.log ‖c‖) t, ha₀]
    norm_num
private theorem norm_input_deformation_right_coeff_zero
    {a₀ a₁ t : ℝ} (ha₁ : a₁ = 0) (c : ℂ) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [div_self hcn.ne', one_mul,
      re_affine_one_im_mul_ofReal (a₁ - a₀) a₀ (Real.log ‖c‖) t]
    have hsum : a₁ - a₀ + a₀ = 0 := by linarith
    rw [hsum]
    norm_num
private theorem eLpNorm_input_deformation_left_coeff_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {a₀ a₁ t : ℝ} (ha₀ : a₀ = 0) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ) ∞ μ ≤ 1 := by
  rw [eLpNorm_exponent_top]
  convert eLpNormEssSup_le_of_ae_bound (μ := μ)
    (f := (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ))
    (ae_of_all _ fun x ↦ by
      rw [SimpleFunc.map_apply]
      exact norm_input_deformation_left_coeff_zero ha₀ (f x)) using 1; norm_num
private theorem eLpNorm_input_deformation_right_coeff_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {a₀ a₁ t : ℝ} (ha₁ : a₁ = 0) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ) ∞ μ ≤ 1 := by
  rw [eLpNorm_exponent_top]
  convert eLpNormEssSup_le_of_ae_bound (μ := μ)
    (f := (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ))
    (ae_of_all _ fun x ↦ by
      rw [SimpleFunc.map_apply]
      exact norm_input_deformation_right_coeff_zero ha₁ (f x)) using 1; norm_num
private theorem eLpNorm_input_deformation_left_coeff
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s a₀ a₁ t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha₀ : a₀ = r / s) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ)
      (ENNReal.ofReal s) μ =
      eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ^ (r / s) := by
  apply eLpNorm_simpleFunc_map_of_norm_rpow f hr hs
  intro c
  rw [norm_input_deformation_left_coeff (by rw [ha₀]; exact div_pos hr hs)]
  rw [ha₀]
private theorem eLpNorm_input_deformation_right_coeff
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s a₀ a₁ t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha₁ : a₁ = r / s) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ)
      (ENNReal.ofReal s) μ =
      eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ^ (r / s) := by
  apply eLpNorm_simpleFunc_map_of_norm_rpow f hr hs
  intro c
  rw [norm_input_deformation_right_coeff (by rw [ha₁]; exact div_pos hr hs)]
  rw [ha₁]
private theorem interpolation_weights_sum_one {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) :
    ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ = 1 := by
  rw [← ENNReal.ofReal_add (by linarith [hθ.2]) hθ.1.le]
  norm_num
private theorem conjExponent_inv_interpolation
    {q q₀ q₁ : ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hqone : 1 ≤ q) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hint : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    q.conjExponent⁻¹ =
      ENNReal.ofReal (1 - θ) * q₀.conjExponent⁻¹ +
        ENNReal.ofReal θ * q₁.conjExponent⁻¹ := by
  let w₀ : ENNReal := ENNReal.ofReal (1 - θ)
  let w₁ : ENNReal := ENNReal.ofReal θ
  have hw : w₀ + w₁ = 1 := by
    simpa only [w₀, w₁] using interpolation_weights_sum_one hθ
  let q' : ENNReal := q.conjExponent
  let q₀' : ENNReal := q₀.conjExponent
  let q₁' : ENNReal := q₁.conjExponent
  have : q.HolderConjugate q' := ENNReal.HolderConjugate.conjExponent hqone
  have : q₀.HolderConjugate q₀' := ENNReal.HolderConjugate.conjExponent hq₀
  have : q₁.HolderConjugate q₁' := ENNReal.HolderConjugate.conjExponent hq₁
  have hq' : q'⁻¹ = 1 - q⁻¹ := (ENNReal.HolderConjugate.one_sub_inv q q').symm
  have hq₀' : q₀'⁻¹ = 1 - q₀⁻¹ := (ENNReal.HolderConjugate.one_sub_inv q₀ q₀').symm
  have hq₁' : q₁'⁻¹ = 1 - q₁⁻¹ := (ENNReal.HolderConjugate.one_sub_inv q₁ q₁').symm
  have hq₀_inv : q₀⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hq₀
  have hq₁_inv : q₁⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hq₁
  have hsum :
      (w₀ * (1 - q₀⁻¹) + w₁ * (1 - q₁⁻¹)) +
        (w₀ * q₀⁻¹ + w₁ * q₁⁻¹) = 1 := by
    calc
      (w₀ * (1 - q₀⁻¹) + w₁ * (1 - q₁⁻¹)) +
          (w₀ * q₀⁻¹ + w₁ * q₁⁻¹) =
          w₀ * ((1 - q₀⁻¹) + q₀⁻¹) +
            w₁ * ((1 - q₁⁻¹) + q₁⁻¹) := by ring
      _ = w₀ * 1 + w₁ * 1 := by
        rw [tsub_add_cancel_of_le hq₀_inv, tsub_add_cancel_of_le hq₁_inv]
      _ = 1 := by simpa using hw
  change q'⁻¹ = w₀ * q₀'⁻¹ + w₁ * q₁'⁻¹
  rw [hq', hq₀', hq₁']
  rw [hint]
  change 1 - (w₀ * q₀⁻¹ + w₁ * q₁⁻¹) =
    w₀ * (1 - q₀⁻¹) + w₁ * (1 - q₁⁻¹)
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hqone)
  have hA : w₀ * q₀⁻¹ + w₁ * q₁⁻¹ ≠ ∞ := by
    rw [← hint]
    exact ENNReal.inv_ne_top.mpr hq0
  symm
  apply ENNReal.eq_sub_of_add_eq hA
  simpa [add_comm] using hsum
private theorem toReal_mul_toReal_inv_eq_div (r s : ENNReal) :
    r.toReal * (s⁻¹).toReal = r.toReal / s.toReal := by
  rw [ENNReal.toReal_inv, div_eq_mul_inv]
private theorem conjExponent_ne_top_of_ne_one {q : ENNReal} (hq : 1 ≤ q) (h : q ≠ 1) :
    q.conjExponent ≠ ∞ := by
  let q' := q.conjExponent
  have : q.HolderConjugate q' := ENNReal.HolderConjugate.conjExponent hq
  change q' ≠ ∞
  exact (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr h
private theorem one_le_conjExponent (q : ENNReal) (hq : 1 ≤ q) :
    1 ≤ q.conjExponent := by
  let q' := q.conjExponent
  have : q.HolderConjugate q' := ENNReal.HolderConjugate.conjExponent hq
  change 1 ≤ q'
  exact ENNReal.HolderConjugate.one_le q' q
private theorem eLpNorm_input_deformation_left_coeff_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s a₀ a₁ t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha₀ : a₀ = r / s)
    (hf : eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ≤ 1) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ)
      (ENNReal.ofReal s) μ ≤ 1 := by
  rw [eLpNorm_input_deformation_left_coeff f hr hs ha₀]
  exact ENNReal.rpow_le_one hf (div_nonneg hr.le hs.le)
private theorem eLpNorm_input_deformation_right_coeff_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s a₀ a₁ t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha₁ : a₁ = r / s)
    (hf : eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ≤ 1) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ)
      (ENNReal.ofReal s) μ ≤ 1 := by
  rw [eLpNorm_input_deformation_right_coeff f hr hs ha₁]
  exact ENNReal.rpow_le_one hf (div_nonneg hr.le hs.le)
private theorem eLpNorm_input_deformation_left_coeff_ennreal_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {p p₀ : ENNReal} {a₀ a₁ t : ℝ}
    (hp : 1 ≤ p) (hp₀ : 1 ≤ p₀) (hp_top : p ≠ ∞)
    (ha₀ : a₀ = p.toReal * (p₀⁻¹).toReal)
    (hf : eLpNorm (f : X → ℂ) p μ ≤ 1) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ) p₀ μ ≤ 1 := by
  by_cases hp₀_top : p₀ = ∞
  · have ha₀_zero : a₀ = 0 := by simpa [hp₀_top] using ha₀
    simpa [hp₀_top] using
      eLpNorm_input_deformation_left_coeff_top (μ := μ) f (a₁ := a₁) (t := t) ha₀_zero
  · have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
    have hp₀0 : p₀ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp₀)
    have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
    have hs : 0 < p₀.toReal := ENNReal.toReal_pos hp₀0 hp₀_top
    have ha₀' : a₀ = p.toReal / p₀.toReal := by
      rw [← toReal_mul_toReal_inv_eq_div]
      exact ha₀
    rw [← ENNReal.ofReal_toReal hp₀_top]
    apply eLpNorm_input_deformation_left_coeff_le_one f hr hs ha₀'
    simpa only [ENNReal.ofReal_toReal hp_top] using hf
private theorem eLpNorm_input_deformation_right_coeff_ennreal_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {p p₁ : ENNReal} {a₀ a₁ t : ℝ}
    (hp : 1 ≤ p) (hp₁ : 1 ≤ p₁) (hp_top : p ≠ ∞)
    (ha₁ : a₁ = p.toReal * (p₁⁻¹).toReal)
    (hf : eLpNorm (f : X → ℂ) p μ ≤ 1) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ) p₁ μ ≤ 1 := by
  by_cases hp₁_top : p₁ = ∞
  · have ha₁_zero : a₁ = 0 := by simpa [hp₁_top] using ha₁
    simpa [hp₁_top] using
      eLpNorm_input_deformation_right_coeff_top (μ := μ) f (a₀ := a₀) (t := t) ha₁_zero
  · have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
    have hp₁0 : p₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp₁)
    have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
    have hs : 0 < p₁.toReal := ENNReal.toReal_pos hp₁0 hp₁_top
    have ha₁' : a₁ = p.toReal / p₁.toReal := by
      rw [← toReal_mul_toReal_inv_eq_div]
      exact ha₁
    rw [← ENNReal.ofReal_toReal hp₁_top]
    apply eLpNorm_input_deformation_right_coeff_le_one f hr hs ha₁'
    simpa only [ENNReal.ofReal_toReal hp_top] using hf
private theorem simpleFunc_output_deformation_at_theta
    {Y : Type*} [MeasurableSpace Y] (g : SimpleFunc Y ℂ)
    {q q₀ q₁ : ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hq : 1 ≤ q) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq_ne_one : q ≠ 1)
    (hint : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    g.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        (((((q.conjExponent.toReal * (q₁.conjExponent⁻¹).toReal -
              q.conjExponent.toReal * (q₀.conjExponent⁻¹).toReal : ℝ) : ℂ) *
            (θ : ℂ)) +
          ((q.conjExponent.toReal * (q₀.conjExponent⁻¹).toReal : ℝ) : ℂ)) *
          ((Real.log ‖c‖ : ℝ) : ℂ))) = g := by
  apply simpleFunc_input_deformation_at_theta
  apply input_coeff_at_theta_of_interp_general hθ
  · exact one_le_conjExponent q hq
  · exact one_le_conjExponent q₀ hq₀
  · exact one_le_conjExponent q₁ hq₁
  · exact conjExponent_ne_top_of_ne_one hq hq_ne_one
  · exact conjExponent_inv_interpolation hθ hq hq₀ hq₁ hint
private theorem eLpNorm_output_deformation_left_le_one
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (g : SimpleFunc Y ℂ) {q q₀ q₁ : ENNReal} {t : ℝ}
    (hq : 1 ≤ q) (hq₀ : 1 ≤ q₀) (_hq₁ : 1 ≤ q₁) (hq_ne_one : q ≠ 1)
    (hg : eLpNorm (g : Y → ℂ) q.conjExponent ν ≤ 1) :
    eLpNorm (g.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((q.conjExponent.toReal * (q₁.conjExponent⁻¹).toReal -
              q.conjExponent.toReal * (q₀.conjExponent⁻¹).toReal : ℝ) : ℂ) *
            ((t : ℂ) * Complex.I) +
          ((q.conjExponent.toReal * (q₀.conjExponent⁻¹).toReal : ℝ) : ℂ)) *
          ((Real.log ‖c‖ : ℝ) : ℂ))): Y → ℂ) q₀.conjExponent ν ≤ 1 := by
  apply eLpNorm_input_deformation_left_coeff_ennreal_le_one
    (p := q.conjExponent) (p₀ := q₀.conjExponent)
  · exact one_le_conjExponent q hq
  · exact one_le_conjExponent q₀ hq₀
  · exact conjExponent_ne_top_of_ne_one hq hq_ne_one
  · rfl
  · exact hg
private theorem eLpNorm_output_deformation_right_le_one
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (g : SimpleFunc Y ℂ) {q q₀ q₁ : ENNReal} {t : ℝ}
    (hq : 1 ≤ q) (_hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq_ne_one : q ≠ 1)
    (hg : eLpNorm (g : Y → ℂ) q.conjExponent ν ≤ 1) :
    eLpNorm (g.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((q.conjExponent.toReal * (q₁.conjExponent⁻¹).toReal -
              q.conjExponent.toReal * (q₀.conjExponent⁻¹).toReal : ℝ) : ℂ) *
            (1 + (t : ℂ) * Complex.I) +
          ((q.conjExponent.toReal * (q₀.conjExponent⁻¹).toReal : ℝ) : ℂ)) *
          ((Real.log ‖c‖ : ℝ) : ℂ))): Y → ℂ) q₁.conjExponent ν ≤ 1 := by
  apply eLpNorm_input_deformation_right_coeff_ennreal_le_one
    (p := q.conjExponent) (p₁ := q₁.conjExponent)
  · exact one_le_conjExponent q hq
  · exact one_le_conjExponent q₁ hq₁
  · exact conjExponent_ne_top_of_ne_one hq hq_ne_one
  · rfl
  · exact hg
private theorem output_deformation_top_at_theta
    {Y : Type*} [MeasurableSpace Y] (g : SimpleFunc Y ℂ) :
    g.map (fun c ↦ c) = g := by
  ext x
  rw [SimpleFunc.map_apply]
private theorem output_deformation_top_boundary_le_one
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (g : SimpleFunc Y ℂ) {r r₀ r₁ : ENNReal}
    (hr₀ : r₀ = r) (hr₁ : r₁ = r)
    (hg : eLpNorm (g : Y → ℂ) r ν ≤ 1) :
    eLpNorm (g : Y → ℂ) r₀ ν ≤ 1 ∧ eLpNorm (g : Y → ℂ) r₁ ν ≤ 1 := by
  simpa only [hr₀, hr₁] using And.intro hg hg
private theorem restrict_one_preimage_singleton_apply
    {X : Type*} [MeasurableSpace X] (f : SimpleFunc X ℂ) (c : ℂ) (x : X) :
    ((SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})) x = if f x = c then 1 else 0 := by
  rw [SimpleFunc.restrict_apply _ (f.measurableSet_preimage _)]
  by_cases h : f x = c
  · rw [Set.indicator_of_mem (by simpa using h)]
    simp [h]
  · rw [Set.indicator_of_notMem (by simpa using h)]
    simp [h]
private theorem map_eq_sum_smul_restrict
    {X : Type*} [MeasurableSpace X] (f : SimpleFunc X ℂ) (φ : ℂ → ℂ)
    (hφ : φ 0 = 0) :
    f.map φ = ∑ c ∈ f.range.erase 0,
      φ c • (SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c}) := by
  classical
  ext x
  have hsum_apply (S : Finset ℂ) :
      (∑ c ∈ S, φ c • (SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})) x =
        ∑ c ∈ S, φ c * ((SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})) x := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, SimpleFunc.coe_add,
        SimpleFunc.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih]
  rw [hsum_apply]
  simp_rw [restrict_one_preimage_singleton_apply]
  by_cases hx : f x = 0
  · simp [SimpleFunc.map_apply, hx, hφ]
  · have hmem : f x ∈ f.range.erase 0 := by
      exact Finset.mem_erase.mpr ⟨hx, f.mem_range_self x⟩
    rw [Finset.sum_eq_single (f x)]
    · simp [SimpleFunc.map_apply]
    · intro b hb hne
      have hbx : f x ≠ b := by
        intro h
        exact hne h.symm
      simp [hbx]
    · exact fun h ↦ (h hmem).elim
private theorem integrable_basis_of_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) (hf : Integrable f μ) {c : ℂ}
    (hc : c ∈ f.range.erase 0) :
    Integrable ((SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c}) : X → ℂ) μ := by
  have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
  have hfin : μ (f ⁻¹' {c}) < ∞ :=
    (SimpleFunc.integrable_iff_finMeasSupp.mp hf).meas_preimage_singleton_ne_zero hc0
  apply SimpleFunc.FinMeasSupp.integrable
  rw [SimpleFunc.finMeasSupp_iff_support]
  refine lt_of_le_of_lt (measure_mono ?_) hfin
  intro x hx
  by_contra hxc
  have hzero : ((SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})) x = 0 := by
    rw [SimpleFunc.restrict_apply _ (f.measurableSet_preimage _)]
    rw [Set.indicator_of_notMem hxc]
  exact hx hzero
private theorem map_finset_sum_smul
    {X Y ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : SimpleFunc X ℂ → Y → ℂ)
    (hT_add : ∀ (f g : SimpleFunc X ℂ),
      Integrable f μ → Integrable g μ → T (f + g) = T f + T g)
    (hT_smul : ∀ (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T (c • f) = c • T f)
    (s : Finset ι) (a : ι → ℂ) (e : ι → SimpleFunc X ℂ)
    (he : ∀ i ∈ s, Integrable (e i : X → ℂ) μ) :
    T (∑ i ∈ s, a i • e i) = ∑ i ∈ s, a i • T (e i) := by
  classical
  have hsum : ∀ t : Finset ι, (∀ i ∈ t, Integrable (e i : X → ℂ) μ) →
      Integrable (∑ i ∈ t, a i • e i : SimpleFunc X ℂ) μ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp
    | insert b t hbt ih =>
      intro ht
      rw [Finset.sum_insert hbt]
      simpa only [SimpleFunc.coe_add, SimpleFunc.coe_smul, Pi.add_apply, Pi.smul_apply] using
        ((ht b (Finset.mem_insert_self _ _)).smul (a b)).add
          (ih fun i hi ↦ ht i (Finset.mem_insert_of_mem hi))
  induction s using Finset.induction_on with
  | empty =>
    have hzero : T (0 : SimpleFunc X ℂ) = 0 := by
      have h0 : Integrable ((0 : SimpleFunc X ℂ) : X → ℂ) μ := by simp
      simpa using hT_smul 0 (0 : SimpleFunc X ℂ) h0
    simp [hzero]
  | insert b s hbs ih =>
    rw [Finset.sum_insert hbs, hT_add]
    · rw [hT_smul]
      · rw [ih (fun i hi ↦ he i (Finset.mem_insert_of_mem hi))]
        simp only [Finset.sum_insert hbs]
      · exact he b (Finset.mem_insert_self _ _)
    · exact (he b (Finset.mem_insert_self _ _)).smul (a b)
    · exact hsum s fun i hi ↦ he i (Finset.mem_insert_of_mem hi)
private theorem integral_finset_bisum_mul
    {Y ι κ : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (s : Finset ι) (t : Finset κ) (a : ι → ℂ) (b : κ → ℂ)
    (u : ι → Y → ℂ) (v : κ → Y → ℂ)
    (hint : ∀ i ∈ s, ∀ j ∈ t, Integrable (fun y ↦ u i y * v j y) ν) :
    (∫ y, (∑ i ∈ s, a i • u i) y * (∑ j ∈ t, b j • v j) y ∂ν) =
      ∑ i ∈ s, ∑ j ∈ t, a i * b j * (∫ y, u i y * v j y ∂ν) := by
  have hpoint : (fun y ↦ (∑ i ∈ s, a i • u i) y * (∑ j ∈ t, b j • v j) y) =
      fun y ↦ ∑ i ∈ s, ∑ j ∈ t, a i * b j * (u i y * v j y) := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hpoint, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      change (∫ y, (a i * b j) * (u i y * v j y) ∂ν) = _
      rw [integral_const_mul]
    · intro j hj
      exact (hint i hi j hj).const_mul _
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (hint i hi j hj).const_mul _
private theorem diffContOnCl_finset_sum
    {ι : Type*} (s : Finset ι) (A : ι → ℂ → ℂ) (U : Set ℂ)
    (hA : ∀ i ∈ s, DiffContOnCl ℂ (A i) U) :
    DiffContOnCl ℂ (fun z ↦ ∑ i ∈ s, A i z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (diffContOnCl_const (𝕜 := ℂ) (s := U) (c := (0 : ℂ)))
  | insert i s his ih =>
    simp only [Finset.sum_insert his]
    change DiffContOnCl ℂ (A i + fun z ↦ ∑ j ∈ s, A j z) U
    exact (hA i (by simp)).add (ih fun j hj ↦ hA j (by simp [hj]))
private theorem diffContOnCl_finset_bisum
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (α : ι → ℂ → ℂ) (β : κ → ℂ → ℂ) (H : ι → κ → ℂ → ℂ)
    (U : Set ℂ)
    (hα : ∀ i ∈ s, DiffContOnCl ℂ (α i) U)
    (hβ : ∀ j ∈ t, DiffContOnCl ℂ (β j) U)
    (hH : ∀ i ∈ s, ∀ j ∈ t, DiffContOnCl ℂ (H i j) U)
    {F : ℂ → ℂ}
    (hF : F = fun z ↦ ∑ i ∈ s, ∑ j ∈ t, α i z * β j z * H i j z) :
    DiffContOnCl ℂ F U := by
  rw [hF]
  apply diffContOnCl_finset_sum s (fun i z ↦ ∑ j ∈ t, α i z * β j z * H i j z) U
  intro i hi
  apply diffContOnCl_finset_sum t (fun j z ↦ α i z * β j z * H i j z) U
  intro j hj
  simpa only [smul_eq_mul, mul_assoc] using (hα i hi).smul ((hβ j hj).smul (hH i hi j hj))
private theorem DiffContOnCl.congr_eqOn_closure
    {F G : ℂ → ℂ} {U : Set ℂ}
    (hG : DiffContOnCl ℂ G U) (hFG : Set.EqOn F G (closure U)) :
    DiffContOnCl ℂ F U :=
  ⟨hG.differentiableOn.congr fun _ hz ↦ hFG (subset_closure hz),
    hG.continuousOn.congr hFG⟩
private theorem diffContOnCl_pairing_of_simple_deformations
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ)
    (hT_add : ∀ (z : verticalClosedStrip 0 1) (f g : SimpleFunc X ℂ),
      Integrable f μ → Integrable g μ → T z (f + g) = T z f + T z g)
    (hT_smul : ∀ (z : verticalClosedStrip 0 1) (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T z (c • f) = c • T z f)
    (hpair_integrable : ∀ (z : verticalClosedStrip 0 1)
      (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν → Integrable (fun y ↦ T z f y * g y) ν)
    (hanalytic : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν →
      DiffContOnCl ℂ (fun z ↦ ∫ y, T z f y * g y ∂ν) (verticalStrip 0 1))
    (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ) (hf : Integrable f μ) (hg : Integrable g ν)
    (φ ψ : ℂ → ℂ → ℂ)
    (hφ0 : ∀ z, φ z 0 = 0) (hψ0 : ∀ z, ψ z 0 = 0)
    (hφ : ∀ c ∈ f.range.erase 0,
      DiffContOnCl ℂ (fun z ↦ φ z c) (verticalStrip 0 1))
    (hψ : ∀ d ∈ g.range.erase 0,
      DiffContOnCl ℂ (fun z ↦ ψ z d) (verticalStrip 0 1)) :
    DiffContOnCl ℂ
      (fun z ↦ ∫ y, T z (f.map (φ z)) y * (g.map (ψ z)) y ∂ν)
      (verticalStrip 0 1) := by
  classical
  let e : ℂ → SimpleFunc X ℂ := fun c ↦
    (SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})
  let d : ℂ → SimpleFunc Y ℂ := fun c ↦
    (SimpleFunc.const Y (1 : ℂ)).restrict (g ⁻¹' {c})
  have he : ∀ c ∈ f.range.erase 0, Integrable (e c : X → ℂ) μ := by
    intro c hc
    simpa only [e] using integrable_basis_of_integrable f hf hc
  have hd : ∀ c ∈ g.range.erase 0, Integrable (d c : Y → ℂ) ν := by
    intro c hc
    simpa only [d] using integrable_basis_of_integrable g hg hc
  let G : ℂ → ℂ := fun z ↦
    ∑ c ∈ f.range.erase 0, ∑ k ∈ g.range.erase 0,
      φ z c * ψ z k * (∫ y, T z (e c) y * d k y ∂ν)
  have hG : DiffContOnCl ℂ G (verticalStrip 0 1) := by
    apply diffContOnCl_finset_bisum (f.range.erase 0) (g.range.erase 0)
      (fun c z ↦ φ z c) (fun k z ↦ ψ z k)
      (fun c k z ↦ ∫ y, T z (e c) y * d k y ∂ν) (verticalStrip 0 1)
    · intro c hc
      exact hφ c hc
    · intro k hk
      exact hψ k hk
    · intro c hc k hk
      exact hanalytic (e c) (d k) (he c hc) (hd k hk)
    · rfl
  refine DiffContOnCl.congr_eqOn_closure hG ?_
  have hcl : closure (verticalStrip 0 1) = verticalClosedStrip 0 1 := by
    rw [verticalStrip, verticalClosedStrip, ← closure_Ioo zero_ne_one,
      ← Complex.closure_preimage_re]
  intro z hz
  rw [hcl] at hz
  have hfm : f.map (φ z) = ∑ c ∈ f.range.erase 0, φ z c • e c := by
    simpa only [e] using map_eq_sum_smul_restrict f (φ z) (hφ0 z)
  have hgm : g.map (ψ z) = ∑ k ∈ g.range.erase 0, ψ z k • d k := by
    simpa only [d] using map_eq_sum_smul_restrict g (ψ z) (hψ0 z)
  change (∫ y, T z (f.map (φ z)) y * (g.map (ψ z)) y ∂ν) = G z
  rw [hfm, hgm, map_finset_sum_smul (T z)
    (fun u v hu hv ↦ hT_add ⟨z, hz⟩ u v hu hv)
    (fun a u hu ↦ hT_smul ⟨z, hz⟩ a u hu)
    (f.range.erase 0) (φ z) e he]
  have hgm_coe :
      ((↑(∑ k ∈ g.range.erase 0, ψ z k • d k) : Y → ℂ)) =
        ∑ k ∈ g.range.erase 0, ψ z k • (d k : Y → ℂ) := by
    induction g.range.erase 0 using Finset.induction_on with
    | empty => simp
    | insert k s hks ih =>
      rw [Finset.sum_insert hks, Finset.sum_insert hks]
      change ψ z k • (d k : Y → ℂ) + ↑(∑ x ∈ s, ψ z x • d x) =
        ψ z k • (d k : Y → ℂ) + ∑ x ∈ s, ψ z x • (d x : Y → ℂ)
      rw [ih]
  rw [hgm_coe]
  simpa only [G] using
    (integral_finset_bisum_mul (ν := ν) (f.range.erase 0) (g.range.erase 0)
      (φ z) (ψ z) (fun c ↦ T z (e c)) (fun k ↦ (d k : Y → ℂ))
      (fun c hc k hk ↦ hpair_integrable ⟨z, hz⟩ (e c) (d k) (he c hc) (hd k hk)))
private theorem family_growth_of_simple_deformations
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ)
    (hT_add : ∀ (z : verticalClosedStrip 0 1) (f g : SimpleFunc X ℂ),
      Integrable f μ → Integrable g μ → T z (f + g) = T z f + T z g)
    (hT_smul : ∀ (z : verticalClosedStrip 0 1) (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T z (c • f) = c • T z f)
    (hpair_integrable : ∀ (z : verticalClosedStrip 0 1)
      (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν → Integrable (fun y ↦ T z f y * g y) ν)
    (hfamily_growth : ∃ a : ℝ, a < Real.pi ∧
      ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
        Integrable f μ → Integrable g ν →
        ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
          ‖∫ y, T z f y * g y ∂ν‖ ≤
            Real.exp (C * Real.exp (a * |(z : ℂ).im|)))
    (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ)
    (hf : Integrable f μ) (hg : Integrable g ν)
    (φ ψ : ℂ → ℂ → ℂ)
    (hφ0 : ∀ z, φ z 0 = 0) (hψ0 : ∀ z, ψ z 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hφ : ∀ c ∈ f.range.erase 0, ∀ z : verticalClosedStrip 0 1, ‖φ z c‖ ≤ A)
    (hψ : ∀ k ∈ g.range.erase 0, ∀ z : verticalClosedStrip 0 1, ‖ψ z k‖ ≤ B) :
    ∃ a : ℝ, a < Real.pi ∧ ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
      ‖∫ y, T z (f.map (φ z)) y * (g.map (ψ z)) y ∂ν‖ ≤
        Real.exp (C * Real.exp (a * |(z : ℂ).im|)) := by
  classical
  let s : Finset ℂ := f.range.erase 0
  let t : Finset ℂ := g.range.erase 0
  let e : ℂ → SimpleFunc X ℂ := fun c ↦
    (SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})
  let d : ℂ → SimpleFunc Y ℂ := fun k ↦
    (SimpleFunc.const Y (1 : ℂ)).restrict (g ⁻¹' {k})
  have he : ∀ c ∈ s, Integrable (e c : X → ℂ) μ := by
    intro c hc
    simpa only [s, e] using integrable_basis_of_integrable f hf hc
  have hd : ∀ k ∈ t, Integrable (d k : Y → ℂ) ν := by
    intro k hk
    simpa only [t, d] using integrable_basis_of_integrable g hg hk
  obtain ⟨a, ha, hfamily⟩ := hfamily_growth
  let a' : ℝ := max a 0
  have ha' : a' < Real.pi := by
    dsimp [a']
    exact max_lt ha Real.pi_pos
  have ha'nonneg : 0 ≤ a' := by
    dsimp [a']
    exact le_max_right _ _
  have hC_exists : ∀ c ∈ s, ∀ k ∈ t, ∃ C : ℝ,
      ∀ z : verticalClosedStrip 0 1,
        ‖∫ y, T z (e c) y * d k y ∂ν‖ ≤
          Real.exp (C * Real.exp (a' * |(z : ℂ).im|)) := by
    intro c hc k hk
    obtain ⟨C, hC⟩ := hfamily (e c) (d k) (he c hc) (hd k hk)
    refine ⟨max C 0, ?_⟩
    simpa only [a'] using
      (exp_growth_normalize
        (F := fun z : ℂ => ∫ y, T z (e c) y * d k y ∂ν) hC)
  let S : Finset (ℂ × ℂ) := s.product t
  have hS : ∀ u : {u // u ∈ S}, ∃ C : ℝ,
      ∀ z : verticalClosedStrip 0 1,
        ‖∫ y, T z (e u.1.1) y * d u.1.2 y ∂ν‖ ≤
          Real.exp (C * Real.exp (a' * |(z : ℂ).im|)) := by
    rintro ⟨⟨c, k⟩, hck⟩
    have hck' : (c, k) ∈ s.product t := by simpa [S] using hck
    exact hC_exists c (Finset.mem_product.mp hck').1 k
      (Finset.mem_product.mp hck').2
  choose D hD using hS
  let C : ℝ := ∑ u ∈ S.attach, max (D u) 0
  have hD_le (c k : ℂ) (hc : c ∈ s) (hk : k ∈ t) :
      D ⟨(c, k), by
        have hck : (c, k) ∈ s.product t := Finset.mem_product.mpr ⟨hc, hk⟩
        simpa [S] using hck⟩ ≤ C := by
    let u : {u // u ∈ S} := ⟨(c, k), by
      have hck : (c, k) ∈ s.product t := Finset.mem_product.mpr ⟨hc, hk⟩
      simpa [S] using hck⟩
    change D u ≤ C
    calc
      D u ≤ max (D u) 0 := le_max_left _ _
      _ ≤ C := by
        dsimp [C]
        exact Finset.single_le_sum (s := S.attach) (f := fun v ↦ max (D v) 0)
          (fun v hv ↦ le_max_right _ _) (by simp [u])
  have hH : ∀ c ∈ s, ∀ k ∈ t, ∀ z : verticalClosedStrip 0 1,
      ‖∫ y, T z (e c) y * d k y ∂ν‖ ≤
        Real.exp (C * Real.exp (a' * |(z : ℂ).im|)) := by
    intro c hc k hk z
    let u : {u // u ∈ S} := ⟨(c, k), by
      have hck : (c, k) ∈ s.product t := Finset.mem_product.mpr ⟨hc, hk⟩
      simpa [S] using hck⟩
    calc
      ‖∫ y, T z (e c) y * d k y ∂ν‖ ≤
          Real.exp (D u * Real.exp (a' * |(z : ℂ).im|)) := by
        simpa only [u] using hD u z
      _ ≤ Real.exp (C * Real.exp (a' * |(z : ℂ).im|)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (by simpa only [u] using hD_le c k hc hk)
          (Real.exp_nonneg _)
  have hfm (z : ℂ) : f.map (φ z) = ∑ c ∈ s, φ z c • e c := by
    simpa only [s, e] using map_eq_sum_smul_restrict f (φ z) (hφ0 z)
  have hgm (z : ℂ) : g.map (ψ z) = ∑ k ∈ t, ψ z k • d k := by
    simpa only [t, d] using map_eq_sum_smul_restrict g (ψ z) (hψ0 z)
  have hpairing (z : verticalClosedStrip 0 1) :
      (∫ y, T z (f.map (φ z)) y * (g.map (ψ z)) y ∂ν) =
        ∑ c ∈ s, ∑ k ∈ t,
          φ z c * ψ z k * (∫ y, T z (e c) y * d k y ∂ν) := by
    rw [hfm z, hgm z, map_finset_sum_smul (T z)
      (fun u v hu hv ↦ hT_add z u v hu hv)
      (fun a u hu ↦ hT_smul z a u hu) s (φ z) e he]
    have hgm_coe : ((↑(∑ k ∈ t, ψ z k • d k) : Y → ℂ)) =
        ∑ k ∈ t, ψ z k • (d k : Y → ℂ) := by
      induction t using Finset.induction_on with
      | empty => simp
      | insert k t hkt ih =>
        rw [Finset.sum_insert hkt, Finset.sum_insert hkt]
        change ψ z k • (d k : Y → ℂ) + ↑(∑ x ∈ t, ψ z x • d x) =
          ψ z k • (d k : Y → ℂ) + ∑ x ∈ t, ψ z x • (d x : Y → ℂ)
        rw [ih]
    rw [hgm_coe]
    simpa only using
      (integral_finset_bisum_mul (ν := ν) s t (φ z) (ψ z)
        (fun c ↦ T z (e c)) (fun k ↦ (d k : Y → ℂ))
        (fun c hc k hk ↦ hpair_integrable z (e c) (d k) (he c hc) (hd k hk)))
  refine ⟨a', ha', (s.card : ℝ) * (t.card : ℝ) * (A * B) + C, ?_⟩
  intro z
  rw [hpairing z]
  simpa only using finite_bisum_exp_growth_of_uniform_factors s t
    (fun c z ↦ φ z c) (fun k z ↦ ψ z k)
    (fun c k z ↦ ∫ y, T z (e c) y * d k y ∂ν)
    ha'nonneg hA hB
    (fun c hc z ↦ hφ c (by simpa only [s] using hc) z)
    (fun k hk z ↦ hψ k (by simpa only [t] using hk) z) hH z
private theorem finite_range_uniform_bound
    {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ s, w x ≤ A := by
  refine ⟨(∑ x ∈ s, w x), Finset.sum_nonneg fun x hx ↦ hw x hx, ?_⟩
  intro x hx
  exact Finset.single_le_sum (s := s) (f := w) (fun y hy ↦ hw y hy) hx
private theorem inv_eq_zero_iff_eq_top_of_interp
    {r r₀ r₁ : ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hr : r⁻¹ = ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹) :
    r = ∞ ↔ r₀ = ∞ ∧ r₁ = ∞ := by
  rw [← ENNReal.inv_eq_zero, hr]
  constructor
  · intro h
    have hleft : ENNReal.ofReal (1 - θ) * r₀⁻¹ = 0 := by
      apply le_antisymm
      · calc
          ENNReal.ofReal (1 - θ) * r₀⁻¹ ≤
              ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹ :=
            le_add_of_nonneg_right bot_le
          _ = 0 := h
      · exact bot_le
    have hright : ENNReal.ofReal θ * r₁⁻¹ = 0 := by
      apply le_antisymm
      · calc
          ENNReal.ofReal θ * r₁⁻¹ ≤
              ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹ :=
            le_add_of_nonneg_left bot_le
          _ = 0 := h
      · exact bot_le
    constructor
    · apply ENNReal.inv_eq_zero.mp
      rcases mul_eq_zero.mp hleft with hweight | hzero
      · exact False.elim ((ENNReal.ofReal_pos.mpr (by linarith [hθ.2])).ne' hweight)
      · exact hzero
    · apply ENNReal.inv_eq_zero.mp
      rcases mul_eq_zero.mp hright with hweight | hzero
      · exact False.elim ((ENNReal.ofReal_pos.mpr hθ.1).ne' hweight)
      · exact hzero
  · rintro ⟨hr₀, hr₁⟩
    simp [hr₀, hr₁]
private theorem eq_one_iff_eq_one_of_interp
    {r r₀ r₁ : ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hr₀ : 1 ≤ r₀) (hr₁ : 1 ≤ r₁)
    (hr : r⁻¹ = ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹) :
    r = 1 ↔ r₀ = 1 ∧ r₁ = 1 := by
  have hθnonneg : 0 ≤ θ := hθ.1.le
  have h1θnonneg : 0 ≤ 1 - θ := by linarith [hθ.2]
  have hweights : ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_add h1θnonneg hθnonneg]
    norm_num
  have hw₀ : ENNReal.ofReal (1 - θ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith [hθ.2])).ne'
  have hw₁ : ENNReal.ofReal θ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hθ.1).ne'
  constructor
  · intro hrone
    have hsum : ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹ = 1 := by
      simpa [hrone] using hr.symm
    have h₀le : r₀⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hr₀
    have h₁le : r₁⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hr₁
    have hprod₀le : ENNReal.ofReal (1 - θ) * r₀⁻¹ ≤ ENNReal.ofReal (1 - θ) := by
      simpa using mul_le_mul_right h₀le (ENNReal.ofReal (1 - θ))
    have hprod₁le : ENNReal.ofReal θ * r₁⁻¹ ≤ ENNReal.ofReal θ := by
      simpa using mul_le_mul_right h₁le (ENNReal.ofReal θ)
    have hprod₀top : ENNReal.ofReal (1 - θ) * r₀⁻¹ ≠ ∞ :=
      (lt_of_le_of_lt hprod₀le ENNReal.ofReal_lt_top).ne
    have hprod₁top : ENNReal.ofReal θ * r₁⁻¹ ≠ ∞ :=
      (lt_of_le_of_lt hprod₁le ENNReal.ofReal_lt_top).ne
    have hprod₀ge : ENNReal.ofReal (1 - θ) ≤ ENNReal.ofReal (1 - θ) * r₀⁻¹ := by
      apply (ENNReal.add_le_add_iff_right hprod₁top).mp
      calc
        ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ * r₁⁻¹ ≤
            ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ :=
          add_le_add_right hprod₁le _
        _ = 1 := hweights
        _ = ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹ := hsum.symm
    have hprod₁ge : ENNReal.ofReal θ ≤ ENNReal.ofReal θ * r₁⁻¹ := by
      apply (ENNReal.add_le_add_iff_right hprod₀top).mp
      calc
        ENNReal.ofReal θ + ENNReal.ofReal (1 - θ) * r₀⁻¹ ≤
            ENNReal.ofReal θ + ENNReal.ofReal (1 - θ) :=
          add_le_add_right hprod₀le _
        _ = 1 := by simpa [add_comm] using hweights
        _ = ENNReal.ofReal θ * r₁⁻¹ + ENNReal.ofReal (1 - θ) * r₀⁻¹ := by
          simpa [add_comm] using hsum.symm
    constructor
    · apply ENNReal.inv_eq_one.mp
      apply le_antisymm h₀le
      apply (ENNReal.mul_le_mul_iff_right hw₀ ENNReal.ofReal_lt_top.ne).mp
      simpa using hprod₀ge
    · apply ENNReal.inv_eq_one.mp
      apply le_antisymm h₁le
      apply (ENNReal.mul_le_mul_iff_right hw₁ ENNReal.ofReal_lt_top.ne).mp
      simpa using hprod₁ge
  · rintro ⟨hr₀one, hr₁one⟩
    apply ENNReal.inv_eq_one.mp
    rw [hr, hr₀one, hr₁one]
    simpa using hweights
private theorem one_le_of_interp
    {r r₀ r₁ : ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hr₀ : 1 ≤ r₀) (hr₁ : 1 ≤ r₁)
    (hr : r⁻¹ = ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹) :
    1 ≤ r := by
  have hθnonneg : 0 ≤ θ := hθ.1.le
  have h1θnonneg : 0 ≤ 1 - θ := by linarith [hθ.2]
  have hweights : ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_add h1θnonneg hθnonneg]
    norm_num
  apply ENNReal.inv_le_one.mp
  rw [hr]
  calc
    ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹ ≤
        ENNReal.ofReal (1 - θ) * 1 + ENNReal.ofReal θ * 1 :=
      add_le_add
        (mul_le_mul_right (ENNReal.inv_le_one.mpr hr₀) _)
        (mul_le_mul_right (ENNReal.inv_le_one.mpr hr₁) _)
    _ = 1 := by simpa using hweights
private theorem affine_kernel (c s : ℝ) (hs : 0 < s) :
    (∫ u in Ioi 0, ((u - c) ^ 2 + s ^ 2)⁻¹) =
      s⁻¹ * (Real.pi / 2 - Real.arctan (-c / s)) := by
  let φ : ℝ → ℝ := fun x => s * x + c
  have hφ_image : φ '' Ioi (-c / s) = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      change -c / s < x at hx
      dsimp [φ]
      have hzero : s * (-c / s) + c = 0 := by
        field_simp
        ring
      have hmul := mul_lt_mul_of_pos_left hx hs
      calc
        0 = s * (-c / s) + c := hzero.symm
        _ < s * x + c := by linarith
    · intro hu
      change 0 < u at hu
      refine ⟨(u - c) / s, ?_, ?_⟩
      · change -c / s < (u - c) / s
        rw [div_lt_div_iff_of_pos_right hs]
        linarith
      · dsimp [φ]
        field_simp
        ring
  have hφ_deriv : ∀ x ∈ Ioi (-c / s),
      HasDerivWithinAt φ s (Ioi (-c / s)) x := by
    intro x hx
    exact (hasDerivAt_const_mul (x := x) s).add_const c |>.hasDerivWithinAt
  have hcv := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (-c / s)) measurableSet_Ioi hφ_deriv (fun x _ y _ hxy => by
      dsimp [φ] at hxy
      apply mul_left_cancel₀ hs.ne'
      linarith) (fun u : ℝ => ((u - c) ^ 2 + s ^ 2)⁻¹)
  rw [hφ_image] at hcv
  calc
    (∫ u in Ioi 0, ((u - c) ^ 2 + s ^ 2)⁻¹) =
        ∫ x in Ioi (-c / s), |s| • ((φ x - c) ^ 2 + s ^ 2)⁻¹ := hcv
    _ = ∫ x in Ioi (-c / s), s⁻¹ * (1 + x ^ 2)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp [φ]
      rw [abs_of_pos hs]
      field_simp [hs.ne']
      ring
    _ = s⁻¹ * (Real.pi / 2 - Real.arctan (-c / s)) := by
      rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
private theorem kernel_left_raw (a : ℝ) (ha0 : 0 < a) (hapi : a < Real.pi) :
    (∫ t : ℝ, (Real.cosh (Real.pi * t) - Real.cos a)⁻¹) =
      2 * (Real.pi - a) / (Real.pi * Real.sin a) := by
  let ψ : ℝ → ℝ := fun t => Real.exp (Real.pi * t)
  have hψ_image : ψ '' Set.univ = Set.Ioi 0 := by
    ext u
    constructor
    · rintro ⟨t, -, rfl⟩
      exact Real.exp_pos _
    · intro hu
      refine ⟨Real.log u / Real.pi, Set.mem_univ _, ?_⟩
      dsimp [ψ]
      rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.exp_log hu]
  have hψ_deriv : ∀ t ∈ Set.univ,
      HasDerivWithinAt ψ (Real.exp (Real.pi * t) * Real.pi) Set.univ t := by
    intro t ht
    exact ((Real.hasDerivAt_exp (Real.pi * t)).comp t
      (hasDerivAt_const_mul (x := t) Real.pi)).hasDerivWithinAt
  have hψ_inj : Set.InjOn ψ Set.univ := by
    intro x hx y hy hxy
    dsimp [ψ] at hxy
    have hxy' := Real.exp_injective hxy
    nlinarith [Real.pi_pos]
  let g : ℝ → ℝ := fun u => 2 / (Real.pi * (u ^ 2 - 2 * Real.cos a * u + 1))
  have hcv := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ hψ_deriv hψ_inj g
  rw [hψ_image] at hcv
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hchange :
      (∫ t : ℝ, (Real.cosh (Real.pi * t) - Real.cos a)⁻¹) =
        ∫ t in Set.univ, |Real.exp (Real.pi * t) * Real.pi| • g (ψ t) := by
    rw [← setIntegral_univ]
    apply integral_congr_ae
    filter_upwards with t
    let u : ℝ := Real.exp (Real.pi * t)
    have hu : 0 < u := Real.exp_pos _
    have hD : 0 < u ^ 2 - 2 * Real.cos a * u + 1 := by
      calc
        u ^ 2 - 2 * Real.cos a * u + 1 = (u - Real.cos a) ^ 2 + (Real.sin a) ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq a]
        _ > 0 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hsin)
    have hcosh : Real.cosh (Real.pi * t) - Real.cos a =
        (u ^ 2 - 2 * Real.cos a * u + 1) / (2 * u) := by
      dsimp [u]
      rw [Real.cosh_eq, Real.exp_neg]
      field_simp [hu.ne']
      ring
    change (Real.cosh (Real.pi * t) - Real.cos a)⁻¹ =
      |Real.exp (Real.pi * t) * Real.pi| * g (Real.exp (Real.pi * t))
    dsimp [g]
    rw [abs_of_pos (mul_pos hu Real.pi_pos)]
    change (Real.cosh (Real.pi * t) - Real.cos a)⁻¹ =
      (u * Real.pi) * (2 / (Real.pi * (u ^ 2 - 2 * Real.cos a * u + 1)))
    rw [hcosh]
    field_simp [hu.ne', hD.ne', Real.pi_ne_zero]
  calc
    (∫ t : ℝ, (Real.cosh (Real.pi * t) - Real.cos a)⁻¹) =
        ∫ t in Set.univ, |Real.exp (Real.pi * t) * Real.pi| • g (ψ t) := hchange
    _ = ∫ u in Set.Ioi 0, g u := hcv.symm
    _ = ∫ u in Set.Ioi 0, (2 / Real.pi) *
        ((u - Real.cos a) ^ 2 + (Real.sin a) ^ 2)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp [g]
      have hD : u ^ 2 - 2 * Real.cos a * u + 1 =
          (u - Real.cos a) ^ 2 + (Real.sin a) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq a]
      rw [hD]
      field_simp [Real.pi_ne_zero]
    _ = (2 / Real.pi) * (∫ u in Set.Ioi 0,
        ((u - Real.cos a) ^ 2 + (Real.sin a) ^ 2)⁻¹) := by
      rw [integral_const_mul]
    _ = (2 / Real.pi) *
        ((Real.sin a)⁻¹ * (Real.pi / 2 - Real.arctan (-Real.cos a / Real.sin a))) := by
      rw [affine_kernel (Real.cos a) (Real.sin a) hsin]
    _ = 2 * (Real.pi - a) / (Real.pi * Real.sin a) := by
      have harctan : Real.arctan (-Real.cos a / Real.sin a) = a - Real.pi / 2 := by
        calc
          Real.arctan (-Real.cos a / Real.sin a) =
              Real.arctan (Real.tan (a - Real.pi / 2)) := by
            congr 1
            rw [show a - Real.pi / 2 = -(Real.pi / 2 - a) by ring,
              Real.tan_neg, Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos]
            field_simp [hsin.ne']
          _ = a - Real.pi / 2 := Real.arctan_tan (by linarith [Real.pi_pos])
            (by linarith [Real.pi_pos])
      rw [harctan]
      field_simp [hsin.ne', Real.pi_ne_zero]
      ring
private theorem integrable_kernel_left {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) :
    Integrable (fun t : ℝ =>
      (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹) := by
  have ha0 : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ.1
  have hapi : Real.pi * θ < Real.pi := by
    calc
      Real.pi * θ < Real.pi * 1 := mul_lt_mul_of_pos_left hθ.2 Real.pi_pos
      _ = Real.pi := mul_one _
  have hsin : 0 < Real.sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  by_contra h
  have hzero := integral_undef h
  rw [kernel_left_raw (Real.pi * θ) ha0 hapi] at hzero
  have hpos : 0 < 2 * (Real.pi - Real.pi * θ) /
      (Real.pi * Real.sin (Real.pi * θ)) := by positivity
  linarith
private theorem integrable_kernel_right {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) :
    Integrable (fun t : ℝ =>
      (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹) := by
  have hθ' : 1 - θ ∈ Set.Ioo 0 1 := by
    constructor <;> linarith [hθ.1, hθ.2]
  have harg : Real.pi * (1 - θ) = Real.pi - Real.pi * θ := by ring
  have h := integrable_kernel_left hθ'
  rw [harg, Real.cos_pi_sub] at h
  simpa only [sub_neg_eq_add] using h
private theorem integrable_exp_neg_mul_abs {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => exp (-δ * |t|)) := by
  suffices h : IntegrableOn (fun t : ℝ => exp (-δ * |t|)) (Iic 0 ∪ Ioi 0) volume by
    simpa only [Iic_union_Ioi, integrableOn_univ] using h
  apply IntegrableOn.union
  · change Integrable (fun t : ℝ => exp (-δ * |t|)) (volume.restrict (Iic 0))
    have h := integrableOn_exp_mul_Iic hδ 0
    change Integrable (fun t : ℝ => exp (δ * t)) (volume.restrict (Iic 0)) at h
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    rw [abs_of_nonpos ht]
    congr 1
    ring
  · change Integrable (fun t : ℝ => exp (-δ * |t|)) (volume.restrict (Ioi 0))
    have h := integrableOn_exp_mul_Ioi (a := -δ) (by linarith) 0
    change Integrable (fun t : ℝ => exp ((-δ) * t)) (volume.restrict (Ioi 0)) at h
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [abs_of_pos ht]
private theorem cosh_add_lower_bound {s x : ℝ} (hs : |s| < 1) :
    (1 - |s|) / 2 * exp x ≤ cosh x + s := by
  have hcosh_sq : 1 ≤ cosh x ^ 2 := by
    rw [Real.cosh_sq']
    nlinarith [sq_nonneg (sinh x)]
  have hcosh_nonneg : 0 ≤ cosh x := (Real.cosh_pos x).le
  have hcosh_one : 1 ≤ cosh x := by
    nlinarith
  have hcosh_exp : exp x / 2 ≤ cosh x := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-x)]
  have hq_nonneg : 0 ≤ |s| := abs_nonneg s
  have hq_le : |s| ≤ 1 := le_of_lt hs
  have hsub : (1 - |s|) * cosh x ≤ cosh x - |s| := by
    nlinarith [mul_nonneg hq_nonneg (sub_nonneg.mpr hcosh_one)]
  have hmul := mul_le_mul_of_nonneg_left hcosh_exp (sub_nonneg.mpr hq_le)
  calc
    (1 - |s|) / 2 * exp x = (1 - |s|) * (exp x / 2) := by ring
    _ ≤ (1 - |s|) * cosh x := hmul
    _ ≤ cosh x - |s| := hsub
    _ ≤ cosh x + s := by linarith [neg_abs_le s]
private theorem exp_growth_factor {A b q a : ℝ} (hq : q ≠ 0) :
    A * exp (b * a) =
      ((2 * A / q) * exp (-(Real.pi - b) * a)) *
        ((q / 2) * exp (Real.pi * a)) := by
  have hconst : (2 * A / q) * (q / 2) = A := by
    field_simp
  have hexp : exp (-(Real.pi - b) * a) * exp (Real.pi * a) = exp (b * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    A * exp (b * a) = A * (exp (-(Real.pi - b) * a) * exp (Real.pi * a)) := by
      rw [hexp]
    _ = ((2 * A / q) * (q / 2)) *
        (exp (-(Real.pi - b) * a) * exp (Real.pi * a)) :=
      congrArg (fun z => z * (exp (-(Real.pi - b) * a) * exp (Real.pi * a))) hconst.symm
    _ = ((2 * A / q) * exp (-(Real.pi - b) * a)) *
        ((q / 2) * exp (Real.pi * a)) := by ring
private theorem integrable_div_cosh_add
    {u : ℝ → ℝ} {A b s : ℝ} (hu : Measurable u)
    (hgrowth : ∀ t : ℝ, |u t| ≤ A * exp (b * |t|))
    (hb : b < Real.pi) (hs : |s| < 1) :
    Integrable (fun t : ℝ => u t / (cosh (Real.pi * t) + s)) := by
  have hA : 0 ≤ A := by
    have h := le_trans (abs_nonneg (u 0)) (hgrowth 0)
    simpa using h
  have hδ : 0 < Real.pi - b := sub_pos.mpr hb
  have hq : 0 < 1 - |s| := sub_pos.mpr hs
  have hq_ne : 1 - |s| ≠ 0 := ne_of_gt hq
  have hden_lower (t : ℝ) :
      ((1 - |s|) / 2) * exp (Real.pi * |t|) ≤ cosh (Real.pi * t) + s := by
    calc
      ((1 - |s|) / 2) * exp (Real.pi * |t|) ≤
          cosh (Real.pi * |t|) + s := cosh_add_lower_bound hs
      _ = cosh (Real.pi * t) + s := by
        have habs : |Real.pi * t| = Real.pi * |t| := by
          rw [abs_mul, abs_of_pos Real.pi_pos]
        rw [← habs, Real.cosh_abs]
  have hden_pos (t : ℝ) : 0 < cosh (Real.pi * t) + s := by
    have hc : 0 < (1 - |s|) / 2 := div_pos hq (by norm_num)
    exact lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hden_lower t)
  have hK : 0 ≤ 2 * A / (1 - |s|) := by
    exact div_nonneg (mul_nonneg (by norm_num) hA) hq.le
  have hf_meas : AEStronglyMeasurable
      (fun t : ℝ => u t / (cosh (Real.pi * t) + s)) volume := by
    exact
      (hu.div ((measurable_const.mul measurable_id).cosh.add measurable_const)).aestronglyMeasurable
  apply Integrable.mono'
      ((integrable_exp_neg_mul_abs hδ).const_mul (2 * A / (1 - |s|))) hf_meas
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hden_pos t)]
  apply (div_le_iff₀ (hden_pos t)).2
  calc
    |u t| ≤ A * exp (b * |t|) := hgrowth t
    _ = ((2 * A / (1 - |s|)) * exp (-(Real.pi - b) * |t|)) *
          (((1 - |s|) / 2) * exp (Real.pi * |t|)) :=
      exp_growth_factor hq_ne
    _ ≤ ((2 * A / (1 - |s|)) * exp (-(Real.pi - b) * |t|)) *
          (cosh (Real.pi * t) + s) :=
      mul_le_mul_of_nonneg_left (hden_lower t)
        (mul_nonneg hK (Real.exp_nonneg _))
private theorem abs_cos_pi_mul_lt_one {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    |cos (Real.pi * θ)| < 1 := by
  have harg_pos : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ.1
  have harg_lt : Real.pi * θ < Real.pi := by
    nlinarith [mul_lt_mul_of_pos_left hθ.2 Real.pi_pos]
  have hsin : 0 < sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi harg_pos harg_lt
  have hsq : cos (Real.pi * θ) ^ 2 < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * θ), sq_pos_of_pos hsin]
  rw [← sq_abs] at hsq
  have hnonneg : 0 ≤ |cos (Real.pi * θ)| := abs_nonneg _
  nlinarith
private theorem integrable_log_div_left_kernel
    {M : ℝ → ℝ} {A b θ : ℝ} (hM : Measurable M)
    (hgrowth : ∀ t : ℝ, |log (M t)| ≤ A * exp (b * |t|))
    (hb : b < Real.pi) (hθ : θ ∈ Ioo 0 1) :
    Integrable (fun t : ℝ =>
      log (M t) / (cosh (Real.pi * t) - cos (Real.pi * θ))) := by
  have h := integrable_div_cosh_add (u := fun t => log (M t))
    (A := A) (b := b) (s := -cos (Real.pi * θ))
    hM.log hgrowth hb (by simpa using abs_cos_pi_mul_lt_one hθ)
  simpa [sub_eq_add_neg] using h
private theorem integrable_log_div_right_kernel
    {M : ℝ → ℝ} {A b θ : ℝ} (hM : Measurable M)
    (hgrowth : ∀ t : ℝ, |log (M t)| ≤ A * exp (b * |t|))
    (hb : b < Real.pi) (hθ : θ ∈ Ioo 0 1) :
    Integrable (fun t : ℝ =>
      log (M t) / (cosh (Real.pi * t) + cos (Real.pi * θ))) := by
  exact integrable_div_cosh_add (u := fun t => log (M t))
    (A := A) (b := b) (s := cos (Real.pi * θ))
    hM.log hgrowth hb (abs_cos_pi_mul_lt_one hθ)
private theorem abs_max_log_neg_natCast_le (x : ℝ) (n : ℕ) :
    |max x (-(n : ℝ))| ≤ |x| := by
  by_cases hx : 0 ≤ x
  · have hn : -(n : ℝ) ≤ x := by
      have : 0 ≤ (n : ℝ) := by positivity
      linarith
    rw [max_eq_left hn, abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hn : -(n : ℝ) ≤ 0 := by
      have : 0 ≤ (n : ℝ) := by positivity
      linarith
    have hmax : max x (-(n : ℝ)) ≤ 0 := max_le hx' hn
    rw [abs_of_nonpos hmax, abs_of_nonpos hx']
    exact neg_le_neg (le_max_left _ _)
private theorem tendsto_integral_weighted_max_log_neg_natCast
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W M : α → ℝ}
    (hW : AEStronglyMeasurable W μ) (hM : Measurable M)
    (hdom : Integrable (fun x ↦ |W x| * |Real.log (M x)|) μ) :
    Tendsto
      (fun n : ℕ ↦ ∫ x, W x * max (Real.log (M x)) (-(n : ℝ)) ∂μ)
      atTop
      (𝓝 (∫ x, W x * Real.log (M x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x ↦ |W x| * |Real.log (M x)|)
  · intro n
    exact hW.mul ((hM.log.max measurable_const).aestronglyMeasurable)
  · exact hdom
  · intro n
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (abs_max_log_neg_natCast_le (Real.log (M x)) n) (abs_nonneg _)
  · filter_upwards with x
    have hnat : ∀ᶠ n : ℕ in atTop, -Real.log (M x) ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hnat] with n hn
    rw [max_eq_left (by linarith)]
private theorem cosh_sub_cos_pi_mul_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    0 < Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ) := by
  have hq : 0 < 1 - |-(Real.cos (Real.pi * θ))| :=
    sub_pos.mpr (by simpa using abs_cos_pi_mul_lt_one hθ)
  exact lt_of_lt_of_le
    (mul_pos (div_pos hq (by norm_num)) (Real.exp_pos _))
    (cosh_add_lower_bound (s := -Real.cos (Real.pi * θ))
      (x := Real.pi * t) (by simpa using abs_cos_pi_mul_lt_one hθ))
private theorem cosh_add_cos_pi_mul_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    0 < Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ) := by
  have hq : 0 < 1 - |Real.cos (Real.pi * θ)| :=
    sub_pos.mpr (abs_cos_pi_mul_lt_one hθ)
  exact lt_of_lt_of_le
    (mul_pos (div_pos hq (by norm_num)) (Real.exp_pos _))
    (cosh_add_lower_bound (s := Real.cos (Real.pi * θ))
      (x := Real.pi * t) (abs_cos_pi_mul_lt_one hθ))
private theorem log_le_hirschman_integral_of_floors
    {θ x : ℝ} {M₀ M₁ : ℝ → ℝ}
    (hθ : θ ∈ Ioo 0 1) (hM : Measurable M₀ ∧ Measurable M₁)
    (hMgrowth : ∃ b A : ℝ, b < Real.pi ∧ ∀ t : ℝ,
      |Real.log (M₀ t)| ≤ A * Real.exp (b * |t|) ∧
        |Real.log (M₁ t)| ≤ A * Real.exp (b * |t|))
    (hfloor : ∀ n : ℕ, x ≤
      (Real.sin (Real.pi * θ) / 2) *
        ((∫ t : ℝ,
          max (Real.log (M₀ t)) (-(n : ℝ)) /
            (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) +
         (∫ t : ℝ,
          max (Real.log (M₁ t)) (-(n : ℝ)) /
            (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)))) ) :
    x ≤ (Real.sin (Real.pi * θ) / 2) *
      ∫ t : ℝ,
        Real.log (M₀ t) /
          (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) +
        Real.log (M₁ t) /
          (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)) := by
  obtain ⟨b, A, hb, hbound⟩ := hMgrowth
  have hi₀ := integrable_log_div_left_kernel hM.1 (fun t ↦ (hbound t).1) hb hθ
  have hi₁ := integrable_log_div_right_kernel hM.2 (fun t ↦ (hbound t).2) hb hθ
  have hdom₀ : Integrable (fun t : ℝ ↦
      |(Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹| *
        |Real.log (M₀ t)|) := by
    convert hi₀.norm using 1
    ext t
    rw [Real.norm_eq_abs, abs_div, abs_inv, abs_of_pos (cosh_sub_cos_pi_mul_pos hθ t)]
    ring
  have hdom₁ : Integrable (fun t : ℝ ↦
      |(Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹| *
        |Real.log (M₁ t)|) := by
    convert hi₁.norm using 1
    ext t
    rw [Real.norm_eq_abs, abs_div, abs_inv, abs_of_pos (cosh_add_cos_pi_mul_pos hθ t)]
    ring
  have hW₀ : AEStronglyMeasurable (fun t : ℝ ↦
      (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹) volume :=
    (((measurable_const.mul measurable_id).cosh.sub measurable_const).inv.aestronglyMeasurable)
  have hW₁ : AEStronglyMeasurable (fun t : ℝ ↦
      (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹) volume :=
    (((measurable_const.mul measurable_id).cosh.add measurable_const).inv.aestronglyMeasurable)
  have ht₀ := tendsto_integral_weighted_max_log_neg_natCast
    (W := fun t : ℝ ↦
      (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹)
    hW₀ hM.1 hdom₀
  have ht₁ := tendsto_integral_weighted_max_log_neg_natCast
    (W := fun t : ℝ ↦
      (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹)
    hW₁ hM.2 hdom₁
  have hlim := ((ht₀.add ht₁).const_mul (Real.sin (Real.pi * θ) / 2))
  have hlim' : Tendsto
      (fun n : ℕ ↦
        (Real.sin (Real.pi * θ) / 2) *
          ((∫ t : ℝ,
            max (Real.log (M₀ t)) (-(n : ℝ)) /
              (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) +
           (∫ t : ℝ,
            max (Real.log (M₁ t)) (-(n : ℝ)) /
              (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)))))
      atTop
      (𝓝 ((Real.sin (Real.pi * θ) / 2) *
        ((∫ t : ℝ,
          Real.log (M₀ t) /
            (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) +
          (∫ t : ℝ,
           Real.log (M₁ t) /
             (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)))))) := by
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlim
  rw [integral_add hi₀ hi₁]
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim'
  filter_upwards with n
  simpa only [div_eq_mul_inv, mul_add] using hfloor n
private theorem integrable_left_kernel_growth_plus
    {θ C a N : ℝ} (hθ : θ ∈ Ioo 0 1) (hC : 0 ≤ C) (ha : a < Real.pi)
    (_hN : 0 ≤ N) :
    Integrable (fun t : ℝ ↦
      |(Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹| *
        (C * Real.exp (a * |t|) + N)) := by
  let B : ℝ → ℝ := fun t ↦ C * Real.exp (a * |t|)
  have hB_meas : Measurable B := by
    dsimp [B]
    fun_prop
  have hB_bound : ∀ t : ℝ, |B t| ≤ C * Real.exp (a * |t|) := by
    intro t
    rw [abs_of_nonneg (mul_nonneg hC (Real.exp_nonneg _))]
  have hB_int := integrable_div_cosh_add (u := B) (A := C) (b := a)
    (s := -Real.cos (Real.pi * θ))
    hB_meas hB_bound ha (by simpa using abs_cos_pi_mul_lt_one hθ)
  have hN_int : Integrable (fun t : ℝ ↦
      N / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
    simpa only [div_eq_mul_inv] using (integrable_kernel_left hθ).const_mul N
  have hB_int' : Integrable (fun t : ℝ ↦
      B t / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
    simpa only [sub_eq_add_neg] using hB_int
  have hsum : Integrable (fun t : ℝ ↦
      B t / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) +
        N / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
    rw [show (fun t : ℝ ↦
        B t / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) +
          N / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) =
        (fun t : ℝ ↦ B t / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) +
          (fun t : ℝ ↦ N / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) by rfl]
    exact hB_int'.add hN_int
  rw [show (fun t : ℝ ↦
      |(Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹| *
        (C * Real.exp (a * |t|) + N)) =
      (fun t : ℝ ↦
        B t / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) +
          N / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) by
    funext t
    rw [abs_inv, abs_of_pos (cosh_sub_cos_pi_mul_pos hθ t)]
    dsimp [B]
    ring]
  exact hsum
private theorem integrable_right_kernel_growth_plus
    {θ C a N : ℝ} (hθ : θ ∈ Ioo 0 1) (hC : 0 ≤ C) (ha : a < Real.pi)
    (_hN : 0 ≤ N) :
    Integrable (fun t : ℝ ↦
      |(Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹| *
        (C * Real.exp (a * |t|) + N)) := by
  let B : ℝ → ℝ := fun t ↦ C * Real.exp (a * |t|)
  have hB_meas : Measurable B := by
    dsimp [B]
    fun_prop
  have hB_bound : ∀ t : ℝ, |B t| ≤ C * Real.exp (a * |t|) := by
    intro t
    rw [abs_of_nonneg (mul_nonneg hC (Real.exp_nonneg _))]
  have hB_int := integrable_div_cosh_add (u := B) (A := C) (b := a)
    hB_meas hB_bound ha (abs_cos_pi_mul_lt_one hθ)
  have hN_int : Integrable (fun t : ℝ ↦
      N / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    simpa only [div_eq_mul_inv] using (integrable_kernel_right hθ).const_mul N
  have hsum : Integrable (fun t : ℝ ↦
      B t / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)) +
        N / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    rw [show (fun t : ℝ ↦
        B t / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)) +
          N / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) =
        (fun t : ℝ ↦ B t / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) +
          (fun t : ℝ ↦ N / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) by rfl]
    exact hB_int.add hN_int
  rw [show (fun t : ℝ ↦
      |(Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹| *
        (C * Real.exp (a * |t|) + N)) =
      (fun t : ℝ ↦
        B t / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)) +
          N / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) by
    funext t
    rw [abs_inv, abs_of_pos (cosh_add_cos_pi_mul_pos hθ t)]
    dsimp [B]
    ring]
  exact hsum
private theorem integral_left_log_max_norm_exp_neg_le
    {F : ℂ → ℂ} {M : ℝ → ℝ} {θ : ℝ} (N : ℕ)
    (hθ : θ ∈ Ioo 0 1) (hF : DiffContOnCl ℂ F (verticalStrip 0 1))
    (hM : Measurable M) (hMpos : ∀ t : ℝ, 0 < M t)
    (hMgrowth : ∃ b A : ℝ, b < Real.pi ∧ ∀ t : ℝ,
      |Real.log (M t)| ≤ A * Real.exp (b * |t|))
    (hbound : ∀ t : ℝ, ‖F ((t : ℂ) * Complex.I)‖ ≤ M t) :
    (∫ t : ℝ,
      Real.log (max ‖F ((t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) ≤
      ∫ t : ℝ,
        max (Real.log (M t)) (-(N : ℝ)) /
          (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) := by
  obtain ⟨b, A, hb, hMgrowth⟩ := hMgrowth
  have hA : 0 ≤ A := by
    have h := hMgrowth 0
    have hexp : 0 < Real.exp (b * |(0 : ℝ)|) := Real.exp_pos _
    nlinarith [abs_nonneg (Real.log (M 0))]
  have hcl : closure (verticalStrip 0 1) = verticalClosedStrip 0 1 := by
    rw [verticalStrip, verticalClosedStrip, ← closure_Ioo zero_ne_one,
      ← Complex.closure_preimage_re]
  have hFleft : Continuous (fun t : ℝ ↦ F ((t : ℂ) * Complex.I)) := by
    apply hF.continuousOn.comp_continuous
      (Complex.continuous_ofReal.mul continuous_const)
    intro t
    rw [hcl, verticalClosedStrip, Set.mem_preimage, Set.mem_Icc]
    simp
  have hfloor_cont : Continuous (fun z : ℂ ↦
      Real.log (max ‖z‖ (Real.exp (-(N : ℝ))))) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact continuousAt_log_max_norm_exp_neg _ z
  have hleft_meas : AEStronglyMeasurable (fun t : ℝ ↦
      Real.log (max ‖F ((t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) volume := by
    apply Measurable.aestronglyMeasurable
    exact (hfloor_cont.comp hFleft).measurable.div
      ((measurable_const.mul measurable_id).cosh.sub measurable_const)
  have hleft_bound (t : ℝ) :
      |Real.log (max ‖F ((t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ))))| ≤
        A * Real.exp (b * |t|) + (N : ℝ) := by
    have hB : 0 ≤ A * Real.exp (b * |t|) + (N : ℝ) :=
      add_nonneg (mul_nonneg hA (Real.exp_nonneg _)) (by positivity)
    have hK : 0 ≤ (N : ℝ) := by positivity
    have hnonneg : 0 ≤ A * Real.exp (b * |t|) :=
      mul_nonneg hA (Real.exp_nonneg (b * |t|))
    have hKB : (N : ℝ) ≤ A * Real.exp (b * |t|) + (N : ℝ) := by
      linarith
    apply abs_log_max_norm_exp_neg_le_of_le hB hK hKB
    by_cases hzero : F ((t : ℂ) * Complex.I) = 0
    · simp [hzero, hB]
    · apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr hzero)).mpr
      calc
        ‖F ((t : ℂ) * Complex.I)‖ ≤ M t := hbound t
        _ = Real.exp (Real.log (M t)) := (Real.exp_log (hMpos t)).symm
        _ ≤ Real.exp |Real.log (M t)| := Real.exp_le_exp.mpr (le_abs_self _)
        _ ≤ Real.exp (A * Real.exp (b * |t|) + (N : ℝ)) := by
          apply Real.exp_le_exp.mpr
          calc
            |Real.log (M t)| ≤ A * Real.exp (b * |t|) := hMgrowth t
            _ ≤ A * Real.exp (b * |t|) + (N : ℝ) :=
              le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hleft_int : Integrable (fun t : ℝ ↦
      Real.log (max ‖F ((t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
    apply Integrable.mono'
      (integrable_left_kernel_growth_plus hθ hA hb (by exact Nat.cast_nonneg N)) hleft_meas
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_div, abs_inv,
      abs_of_pos (cosh_sub_cos_pi_mul_pos hθ t)]
    calc
      |Real.log (max ‖F ((t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ))))| /
          (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) =
          (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹ *
            |Real.log (max ‖F ((t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ))))| := by
            rw [div_eq_mul_inv]
            ring
      _ ≤ (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹ *
            (A * Real.exp (b * |t|) + (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (hleft_bound t)
            (inv_nonneg.mpr (cosh_sub_cos_pi_mul_pos hθ t).le)
  have hright_base : Integrable (fun t : ℝ ↦
      Real.log (M t) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) :=
    integrable_log_div_left_kernel hM hMgrowth hb hθ
  have hright_meas : AEStronglyMeasurable (fun t : ℝ ↦
      max (Real.log (M t)) (-(N : ℝ)) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) volume := by
    apply Measurable.aestronglyMeasurable
    exact ((hM.log.max measurable_const).div
      ((measurable_const.mul measurable_id).cosh.sub measurable_const))
  have hright_int : Integrable (fun t : ℝ ↦
      max (Real.log (M t)) (-(N : ℝ)) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
    apply Integrable.mono' hright_base.norm hright_meas
    filter_upwards with t
    change |max (Real.log (M t)) (-(N : ℝ)) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))| ≤
      |Real.log (M t) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))|
    rw [abs_div, abs_div]
    exact div_le_div_of_nonneg_right
      (abs_max_log_neg_natCast_le (Real.log (M t)) N) (abs_nonneg _)
  apply integral_mono hleft_int hright_int
  intro t
  apply (div_le_div_iff_of_pos_right (cosh_sub_cos_pi_mul_pos hθ t)).mpr
  exact log_max_norm_exp_neg_le_max_log_of_norm_le (hMpos t) (hbound t)
private theorem integral_right_log_max_norm_exp_neg_le
    {F : ℂ → ℂ} {M : ℝ → ℝ} {θ : ℝ} (N : ℕ)
    (hθ : θ ∈ Ioo 0 1) (hF : DiffContOnCl ℂ F (verticalStrip 0 1))
    (hM : Measurable M) (hMpos : ∀ t : ℝ, 0 < M t)
    (hMgrowth : ∃ b A : ℝ, b < Real.pi ∧ ∀ t : ℝ,
      |Real.log (M t)| ≤ A * Real.exp (b * |t|))
    (hbound : ∀ t : ℝ, ‖F (1 + (t : ℂ) * Complex.I)‖ ≤ M t) :
    (∫ t : ℝ,
      Real.log (max ‖F (1 + (t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) ≤
      ∫ t : ℝ,
        max (Real.log (M t)) (-(N : ℝ)) /
          (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)) := by
  obtain ⟨b, A, hb, hMgrowth⟩ := hMgrowth
  have hA : 0 ≤ A := by
    have h := hMgrowth 0
    have hexp : 0 < Real.exp (b * |(0 : ℝ)|) := Real.exp_pos _
    nlinarith [abs_nonneg (Real.log (M 0))]
  have hcl : closure (verticalStrip 0 1) = verticalClosedStrip 0 1 := by
    rw [verticalStrip, verticalClosedStrip, ← closure_Ioo zero_ne_one,
      ← Complex.closure_preimage_re]
  have hFright : Continuous (fun t : ℝ ↦ F (1 + (t : ℂ) * Complex.I)) := by
    apply hF.continuousOn.comp_continuous
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    intro t
    rw [hcl, verticalClosedStrip, Set.mem_preimage, Set.mem_Icc]
    simp
  have hfloor_cont : Continuous (fun z : ℂ ↦
      Real.log (max ‖z‖ (Real.exp (-(N : ℝ))))) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact continuousAt_log_max_norm_exp_neg _ z
  have hleft_meas : AEStronglyMeasurable (fun t : ℝ ↦
      Real.log (max ‖F (1 + (t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) volume := by
    apply Measurable.aestronglyMeasurable
    exact (hfloor_cont.comp hFright).measurable.div
      ((measurable_const.mul measurable_id).cosh.add measurable_const)
  have hleft_bound (t : ℝ) :
      |Real.log (max ‖F (1 + (t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ))))| ≤
        A * Real.exp (b * |t|) + (N : ℝ) := by
    have hB : 0 ≤ A * Real.exp (b * |t|) + (N : ℝ) :=
      add_nonneg (mul_nonneg hA (Real.exp_nonneg _)) (by positivity)
    have hK : 0 ≤ (N : ℝ) := by positivity
    have hnonneg : 0 ≤ A * Real.exp (b * |t|) :=
      mul_nonneg hA (Real.exp_nonneg (b * |t|))
    have hKB : (N : ℝ) ≤ A * Real.exp (b * |t|) + (N : ℝ) := by
      linarith
    apply abs_log_max_norm_exp_neg_le_of_le hB hK hKB
    by_cases hzero : F (1 + (t : ℂ) * Complex.I) = 0
    · simp [hzero, hB]
    · apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr hzero)).mpr
      calc
        ‖F (1 + (t : ℂ) * Complex.I)‖ ≤ M t := hbound t
        _ = Real.exp (Real.log (M t)) := (Real.exp_log (hMpos t)).symm
        _ ≤ Real.exp |Real.log (M t)| := Real.exp_le_exp.mpr (le_abs_self _)
        _ ≤ Real.exp (A * Real.exp (b * |t|) + (N : ℝ)) := by
          apply Real.exp_le_exp.mpr
          calc
            |Real.log (M t)| ≤ A * Real.exp (b * |t|) := hMgrowth t
            _ ≤ A * Real.exp (b * |t|) + (N : ℝ) :=
              le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hleft_int : Integrable (fun t : ℝ ↦
      Real.log (max ‖F (1 + (t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    apply Integrable.mono'
      (integrable_right_kernel_growth_plus hθ hA hb (by exact Nat.cast_nonneg N)) hleft_meas
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_div, abs_inv,
      abs_of_pos (cosh_add_cos_pi_mul_pos hθ t)]
    calc
      |Real.log (max ‖F (1 + (t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ))))| /
          (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)) =
          (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹ *
            |Real.log (max ‖F (1 + (t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ))))| := by
            rw [div_eq_mul_inv]
            ring
      _ ≤ (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹ *
            (A * Real.exp (b * |t|) + (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (hleft_bound t)
            (inv_nonneg.mpr (cosh_add_cos_pi_mul_pos hθ t).le)
  have hright_base : Integrable (fun t : ℝ ↦
      Real.log (M t) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) :=
    integrable_log_div_right_kernel hM hMgrowth hb hθ
  have hright_meas : AEStronglyMeasurable (fun t : ℝ ↦
      max (Real.log (M t)) (-(N : ℝ)) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) volume := by
    apply Measurable.aestronglyMeasurable
    exact ((hM.log.max measurable_const).div
      ((measurable_const.mul measurable_id).cosh.add measurable_const))
  have hright_int : Integrable (fun t : ℝ ↦
      max (Real.log (M t)) (-(N : ℝ)) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    apply Integrable.mono' hright_base.norm hright_meas
    filter_upwards with t
    change |max (Real.log (M t)) (-(N : ℝ)) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))| ≤
      |Real.log (M t) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))|
    rw [abs_div, abs_div]
    exact div_le_div_of_nonneg_right
      (abs_max_log_neg_natCast_le (Real.log (M t)) N) (abs_nonneg _)
  apply integral_mono hleft_int hright_int
  intro t
  apply (div_le_div_iff_of_pos_right (cosh_add_cos_pi_mul_pos hθ t)).mpr
  exact log_max_norm_exp_neg_le_max_log_of_norm_le (hMpos t) (hbound t)
private theorem analyticOnNhd_radial_discToStrip
    {F : ℂ → ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hF : AnalyticOnNhd ℂ F (verticalStrip 0 1)) :
    AnalyticOnNhd ℂ
      (fun z ↦ F
        (Complex.log (Complex.I * (1 + (r : ℂ) * z) / (1 - (r : ℂ) * z)) /
          (Real.pi * Complex.I)))
      (closedBall 0 1) := by
  have hscale : AnalyticOnNhd ℂ (fun z : ℂ ↦ (r : ℂ) * z) (closedBall 0 1) := by
    convert ((analyticOnNhd_id (𝕜 := ℂ) (E := ℂ)).const_smul (c := (r : ℂ))).mono
      (Set.subset_univ _) using 1
    ext z
    simp
  have hscale_map : MapsTo (fun z : ℂ ↦ (r : ℂ) * z) (closedBall 0 1) (ball 0 1) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    calc
      r * ‖z‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hz hr0
      _ = r := mul_one _
      _ < 1 := hr1
  have hDscale : AnalyticOnNhd ℂ
      ((fun z ↦ Complex.log (Complex.I * (1 + z) / (1 - z)) /
        (Real.pi * Complex.I)) ∘ fun z : ℂ ↦ (r : ℂ) * z)
      (closedBall 0 1) :=
    analyticOnNhd_discToStrip.comp hscale hscale_map
  have hDscale_map : MapsTo
      ((fun z ↦ Complex.log (Complex.I * (1 + z) / (1 - z)) /
        (Real.pi * Complex.I)) ∘ fun z : ℂ ↦ (r : ℂ) * z)
      (closedBall 0 1) (verticalStrip 0 1) := by
    intro z hz
    apply discToStrip_mem_verticalStrip
    simpa [mem_ball, dist_zero_right] using hscale_map hz
  convert hF.comp hDscale hDscale_map using 1
  ext z
  rfl
private theorem log_norm_le_of_norm_le_exp {z : ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hz : ‖z‖ ≤ Real.exp A) :
    Real.log ‖z‖ ≤ A := by
  by_cases hzero : z = 0
  · simp [hzero, hA]
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hzero)).mpr hz
private theorem hirschman_three_lines
    {F : ℂ → ℂ} {θ : ℝ} {M₀ M₁ : ℝ → ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hF : DiffContOnCl ℂ F (verticalStrip 0 1))
    (hF_growth : ∃ a : ℝ, a < Real.pi ∧ ∃ C : ℝ,
      ∀ z : ℂ, z ∈ verticalClosedStrip 0 1 →
        ‖F z‖ ≤ Real.exp (C * Real.exp (a * |z.im|)))
    (hM : Measurable M₀ ∧ Measurable M₁)
    (hMpos : ∀ t : ℝ, 0 < M₀ t ∧ 0 < M₁ t)
    (hMgrowth : ∃ b A : ℝ, b < Real.pi ∧ ∀ t : ℝ,
      |Real.log (M₀ t)| ≤ A * Real.exp (b * |t|) ∧
        |Real.log (M₁ t)| ≤ A * Real.exp (b * |t|))
    (hbound₀ : ∀ t : ℝ, ‖F ((t : ℂ) * Complex.I)‖ ≤ M₀ t)
    (hbound₁ : ∀ t : ℝ, ‖F (1 + (t : ℂ) * Complex.I)‖ ≤ M₁ t) :
    ‖F (θ : ℂ)‖ ≤
      Real.exp ((Real.sin (Real.pi * θ) / 2) *
        ∫ t : ℝ,
          Real.log (M₀ t) /
              (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) +
            Real.log (M₁ t) /
              (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
  classical
  obtain ⟨a, ha, C, hC⟩ := hF_growth
  let a' : ℝ := max a 0
  let C' : ℝ := max C 0
  have ha' : a' < Real.pi := by
    dsimp [a']
    exact max_lt ha Real.pi_pos
  have ha'nonneg : 0 ≤ a' := by
    dsimp [a']
    exact le_max_right _ _
  have hC' : 0 ≤ C' := by
    dsimp [C']
    exact le_max_right _ _
  have hFnorm : ∀ z : verticalClosedStrip 0 1,
      ‖F z‖ ≤ Real.exp (C' * Real.exp (a' * |(z : ℂ).im|)) := by
    simpa [a', C'] using
      (exp_growth_normalize (F := F) (fun z ↦ hC z z.2))
  have hFbound (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) :
      ‖F z‖ ≤ Real.exp (C' * Real.exp (a' * |z.im|)) := by
    simpa using hFnorm ⟨z, hz⟩
  have hVSsub : verticalStrip 0 1 ⊆ verticalClosedStrip 0 1 := by
    intro z hz
    change z.re ∈ Set.Ioo 0 1 at hz
    change z.re ∈ Set.Icc 0 1
    exact ⟨hz.1.le, hz.2.le⟩
  have hcl : closure (verticalStrip 0 1) = verticalClosedStrip 0 1 := by
    rw [verticalStrip, verticalClosedStrip, ← closure_Ioo zero_ne_one,
      ← Complex.closure_preimage_re]
  have hFcont : ContinuousOn F (verticalClosedStrip 0 1) := by
    rw [← hcl]
    exact hF.continuousOn
  have hopen : IsOpen (verticalStrip 0 1) := by
    rw [verticalStrip]
    exact Complex.continuous_re.isOpen_preimage _ isOpen_Ioo
  have hFanalytic : AnalyticOnNhd ℂ F (verticalStrip 0 1) :=
    hF.differentiableOn.analyticOnNhd hopen
  let r : ℕ → ℝ := fun n ↦ (n : ℝ) / ((n : ℝ) + 1)
  have hr0 (n : ℕ) : 0 ≤ r n := by
    simpa [r] using radialSequence_nonneg n
  have hr1 (n : ℕ) : r n < 1 := by
    simpa [r] using radialSequence_lt_one n
  have hrrange : ∀ᶠ n : ℕ in atTop, 0 ≤ r n ∧ r n < 1 := by
    simpa [r] using eventually_radialSequence_range
  have hr : Tendsto r atTop (𝓝 1) := by
    simpa [r] using tendsto_radialSequence
  let D : ℂ → ℂ := fun z ↦
    Complex.log (Complex.I * (1 + z) / (1 - z)) / (Real.pi * Complex.I)
  let w : ℂ :=
    (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * (θ : ℂ)) + Complex.I)
  let f : ℕ → ℂ → ℂ := fun n z ↦ F (D ((r n : ℂ) * z))
  have hθstrip : (θ : ℂ) ∈ verticalStrip 0 1 := by
    simpa [verticalStrip] using hθ
  have hw_norm : ‖w‖ < 1 := by
    simpa [w] using stripToDisc_norm_lt_one hθstrip
  have hw : w ∈ ball 0 1 := by
    simpa [mem_ball, dist_zero_right] using hw_norm
  have hDw : D w = (θ : ℂ) := by
    simpa [D, w] using discToStrip_stripToDisc hθstrip
  have hfanalytic (n : ℕ) : AnalyticOnNhd ℂ (f n) (closedBall 0 1) := by
    simpa [f, D] using
      (analyticOnNhd_radial_discToStrip (F := F) (r := r n) (hr0 n) (hr1 n) hFanalytic)
  have hDcenter : Tendsto (fun n : ℕ ↦ D ((r n : ℂ) * w)) atTop (𝓝 (θ : ℂ)) := by
    have hscale : Tendsto (fun n : ℕ ↦ (r n : ℂ) * w) atTop (𝓝 w) := by
      have hcont : Continuous (fun s : ℝ ↦ (s : ℂ) * w) := by fun_prop
      simpa [Function.comp_def] using hcont.continuousAt.tendsto.comp hr
    have hcont := (analyticOnNhd_discToStrip w hw).continuousAt
    rw [← hDw]
    simpa only [Function.comp_def, D] using hcont.tendsto.comp hscale
  have hDcenter_mem (n : ℕ) : D ((r n : ℂ) * w) ∈ verticalStrip 0 1 := by
    apply discToStrip_mem_verticalStrip
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n)]
    calc
      r n * ‖w‖ ≤ r n * 1 :=
        mul_le_mul_of_nonneg_left hw_norm.le (hr0 n)
      _ = r n := mul_one _
      _ < 1 := hr1 n
  have hDcenterWithin : Tendsto (fun n : ℕ ↦ D ((r n : ℂ) * w)) atTop
      (𝓝[verticalClosedStrip 0 1] (θ : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hDcenter,
      Filter.Eventually.of_forall fun n ↦ hVSsub (hDcenter_mem n)⟩
  have hθclosed : (θ : ℂ) ∈ verticalClosedStrip 0 1 := hVSsub hθstrip
  have hfcenter : Tendsto (fun n : ℕ ↦ f n w) atTop (𝓝 (F (θ : ℂ))) := by
    simpa only [Function.comp_def, f] using
      (hFcont (θ : ℂ) hθclosed).tendsto.comp hDcenterWithin
  by_cases hFθ : F (θ : ℂ) = 0
  · rw [hFθ]
    simpa using (Real.exp_pos _).le
  have hfcenter_ne : ∀ᶠ n : ℕ in atTop, f n w ≠ 0 := hfcenter.eventually_ne hFθ
  let b₀ : ℝ → ℂ := fun t ↦
    (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * ((t : ℂ) * Complex.I)) + Complex.I)
  let b₁ : ℝ → ℂ := fun t ↦
    (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) - Complex.I) /
      (Complex.exp (Real.pi * Complex.I * (1 + (t : ℂ) * Complex.I)) + Complex.I)
  have hb₀_eq (t : ℝ) : b₀ t =
      circleMap 0 1 (-(2 * Real.arctan (Real.exp (Real.pi * t)))) := by
    simpa [b₀] using (circleMap_neg_angleMap_eq_left t).symm
  have hb₁_eq (t : ℝ) : b₁ t =
      circleMap 0 1 (2 * Real.arctan (Real.exp (Real.pi * t))) := by
    simpa [b₁] using (circleMap_angleMap_eq_right t).symm
  have hb₀_cont : Continuous b₀ := by
    let α : ℝ → ℝ := fun t ↦ -(2 * Real.arctan (Real.exp (Real.pi * t)))
    have hα : Continuous α := by
      dsimp [α]
      fun_prop
    have hcircle : Continuous (fun t : ℝ ↦ circleMap 0 1 (α t)) :=
      (continuous_circleMap 0 1).comp hα
    exact hcircle.congr fun t ↦ by simpa [α] using (hb₀_eq t).symm
  have hb₁_cont : Continuous b₁ := by
    let α : ℝ → ℝ := fun t ↦ 2 * Real.arctan (Real.exp (Real.pi * t))
    have hα : Continuous α := by
      dsimp [α]
      fun_prop
    have hcircle : Continuous (fun t : ℝ ↦ circleMap 0 1 (α t)) :=
      (continuous_circleMap 0 1).comp hα
    exact hcircle.congr fun t ↦ by simpa [α] using (hb₁_eq t).symm
  have hb₀sphere (t : ℝ) : b₀ t ∈ sphere 0 1 := by
    rw [hb₀_eq t]
    simp
  have hb₁sphere (t : ℝ) : b₁ t ∈ sphere 0 1 := by
    rw [hb₁_eq t]
    simp
  have hb₀norm (t : ℝ) : ‖b₀ t‖ = 1 := by
    simpa [mem_sphere, dist_zero_right] using hb₀sphere t
  have hb₁norm (t : ℝ) : ‖b₁ t‖ = 1 := by
    simpa [mem_sphere, dist_zero_right] using hb₁sphere t
  have hD₀_mem (n : ℕ) (t : ℝ) : D ((r n : ℂ) * b₀ t) ∈ verticalStrip 0 1 := by
    apply discToStrip_mem_verticalStrip
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n), hb₀norm t]
    simpa using hr1 n
  have hD₁_mem (n : ℕ) (t : ℝ) : D ((r n : ℂ) * b₁ t) ∈ verticalStrip 0 1 := by
    apply discToStrip_mem_verticalStrip
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n), hb₁norm t]
    simpa using hr1 n
  have hD₀_lim (t : ℝ) : Tendsto (fun n : ℕ ↦ D ((r n : ℂ) * b₀ t)) atTop
      (𝓝 ((t : ℂ) * Complex.I)) := by
    simpa [D, b₀] using tendsto_discToStrip_radial_left r hr hrrange t
  have hD₁_lim (t : ℝ) : Tendsto (fun n : ℕ ↦ D ((r n : ℂ) * b₁ t)) atTop
      (𝓝 (1 + (t : ℂ) * Complex.I)) := by
    simpa [D, b₁] using tendsto_discToStrip_radial_right r hr hrrange t
  have hleft_mem (t : ℝ) : (t : ℂ) * Complex.I ∈ verticalClosedStrip 0 1 := by
    change ((t : ℂ) * Complex.I).re ∈ Set.Icc 0 1
    simp
  have hright_mem (t : ℝ) : 1 + (t : ℂ) * Complex.I ∈ verticalClosedStrip 0 1 := by
    change (1 + (t : ℂ) * Complex.I).re ∈ Set.Icc 0 1
    simp
  have hD₀_within (t : ℝ) : Tendsto (fun n : ℕ ↦ D ((r n : ℂ) * b₀ t)) atTop
      (𝓝[verticalClosedStrip 0 1] ((t : ℂ) * Complex.I)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hD₀_lim t,
      Filter.Eventually.of_forall fun n ↦ hVSsub (hD₀_mem n t)⟩
  have hD₁_within (t : ℝ) : Tendsto (fun n : ℕ ↦ D ((r n : ℂ) * b₁ t)) atTop
      (𝓝[verticalClosedStrip 0 1] (1 + (t : ℂ) * Complex.I)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hD₁_lim t,
      Filter.Eventually.of_forall fun n ↦ hVSsub (hD₁_mem n t)⟩
  have hf₀_lim (t : ℝ) : Tendsto (fun n : ℕ ↦ f n (b₀ t)) atTop
      (𝓝 (F ((t : ℂ) * Complex.I))) := by
    simpa only [Function.comp_def, f] using
      (hFcont _ (hleft_mem t)).tendsto.comp (hD₀_within t)
  have hf₁_lim (t : ℝ) : Tendsto (fun n : ℕ ↦ f n (b₁ t)) atTop
      (𝓝 (F (1 + (t : ℂ) * Complex.I))) := by
    simpa only [Function.comp_def, f] using
      (hFcont _ (hright_mem t)).tendsto.comp (hD₁_within t)
  have hf₀_cont (n : ℕ) : Continuous (fun t : ℝ ↦ f n (b₀ t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      ((hfanalytic n _ (sphere_subset_closedBall (hb₀sphere t))).continuousAt.comp
        hb₀_cont.continuousAt)
  have hf₁_cont (n : ℕ) : Continuous (fun t : ℝ ↦ f n (b₁ t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      ((hfanalytic n _ (sphere_subset_closedBall (hb₁sphere t))).continuousAt.comp
        hb₁_cont.continuousAt)
  let B : ℝ → ℝ := fun t ↦ C' * Real.exp (a' * |t|)
  have hB_nonneg (t : ℝ) : 0 ≤ B t := by
    dsimp [B]
    exact mul_nonneg hC' (Real.exp_nonneg _)
  have hf₀_bound (n : ℕ) (t : ℝ) : Real.log ‖f n (b₀ t)‖ ≤ B t := by
    apply log_norm_le_of_norm_le_exp (hB_nonneg t)
    apply (hFbound _ (hVSsub (hD₀_mem n t))).trans
    apply Real.exp_le_exp.mpr
    dsimp [B]
    apply mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by simpa [D, b₀] using
          im_discToStrip_radial_left_le (r n) t (hr0 n) (hr1 n).le) ha'nonneg)) hC'
  have hf₁_bound (n : ℕ) (t : ℝ) : Real.log ‖f n (b₁ t)‖ ≤ B t := by
    apply log_norm_le_of_norm_le_exp (hB_nonneg t)
    apply (hFbound _ (hVSsub (hD₁_mem n t))).trans
    apply Real.exp_le_exp.mpr
    dsimp [B]
    apply mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by simpa [D, b₁] using
          im_discToStrip_radial_right_le (r n) t (hr0 n) (hr1 n).le) ha'nonneg)) hC'
  have hW₀ : AEStronglyMeasurable (fun t : ℝ ↦
      (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹) volume :=
    (((measurable_const.mul measurable_id).cosh.sub measurable_const).inv.aestronglyMeasurable)
  have hW₁ : AEStronglyMeasurable (fun t : ℝ ↦
      (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹) volume :=
    (((measurable_const.mul measurable_id).cosh.add measurable_const).inv.aestronglyMeasurable)
  have hfloor₀_meas (N n : ℕ) : AEStronglyMeasurable (fun t : ℝ ↦
      Real.log (max ‖f n (b₀ t)‖ (Real.exp (-(N : ℝ))))) volume := by
    have houter : Continuous (fun z : ℂ ↦
        Real.log (max ‖z‖ (Real.exp (-(N : ℝ))))) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact continuousAt_log_max_norm_exp_neg (N : ℝ) z
    have hcont : Continuous (fun t : ℝ ↦
        Real.log (max ‖f n (b₀ t)‖ (Real.exp (-(N : ℝ))))) := by
      simpa only [Function.comp_def] using houter.comp (hf₀_cont n)
    exact hcont.aestronglyMeasurable
  have hfloor₁_meas (N n : ℕ) : AEStronglyMeasurable (fun t : ℝ ↦
      Real.log (max ‖f n (b₁ t)‖ (Real.exp (-(N : ℝ))))) volume := by
    have houter : Continuous (fun z : ℂ ↦
        Real.log (max ‖z‖ (Real.exp (-(N : ℝ))))) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact continuousAt_log_max_norm_exp_neg (N : ℝ) z
    have hcont : Continuous (fun t : ℝ ↦
        Real.log (max ‖f n (b₁ t)‖ (Real.exp (-(N : ℝ))))) := by
      simpa only [Function.comp_def] using houter.comp (hf₁_cont n)
    exact hcont.aestronglyMeasurable
  have hdom₀ (N : ℕ) : Integrable (fun t : ℝ ↦
      |(Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹| * (B t + (N : ℝ))) := by
    simpa [B] using
      (integrable_left_kernel_growth_plus (θ := θ) (C := C') (a := a') (N := (N : ℝ))
        hθ hC' ha' (Nat.cast_nonneg N))
  have hdom₁ (N : ℕ) : Integrable (fun t : ℝ ↦
      |(Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹| * (B t + (N : ℝ))) := by
    simpa [B] using
      (integrable_right_kernel_growth_plus (θ := θ) (C := C') (a := a') (N := (N : ℝ))
        hθ hC' ha' (Nat.cast_nonneg N))
  have hI₀_lim (N : ℕ) : Tendsto (fun n : ℕ ↦ ∫ t : ℝ,
      Real.log (max ‖f n (b₀ t)‖ (Real.exp (-(N : ℝ)))) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) atTop
      (𝓝 (∫ t : ℝ,
        Real.log (max ‖F ((t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
          (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)))) := by
    have h := tendsto_integral_weighted_log_max_norm_exp_neg_of_bound
      (W := fun t : ℝ ↦
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹)
      (B := B) (u := fun n t ↦ f n (b₀ t))
      (v := fun t ↦ F ((t : ℂ) * Complex.I)) (K := (N : ℝ))
      hW₀ (hfloor₀_meas N) hB_nonneg (Nat.cast_nonneg N) hf₀_bound (hdom₀ N) hf₀_lim
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hI₁_lim (N : ℕ) : Tendsto (fun n : ℕ ↦ ∫ t : ℝ,
      Real.log (max ‖f n (b₁ t)‖ (Real.exp (-(N : ℝ)))) /
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) atTop
      (𝓝 (∫ t : ℝ,
        Real.log (max ‖F (1 + (t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
          (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)))) := by
    have h := tendsto_integral_weighted_log_max_norm_exp_neg_of_bound
      (W := fun t : ℝ ↦
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹)
      (B := B) (u := fun n t ↦ f n (b₁ t))
      (v := fun t ↦ F (1 + (t : ℂ) * Complex.I)) (K := (N : ℝ))
      hW₁ (hfloor₁_meas N) hB_nonneg (Nat.cast_nonneg N) hf₁_bound (hdom₁ N) hf₁_lim
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hraw (n : ℕ) : CircleIntegrable
      ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖f n z‖) 0 1 := by
    have hmero : MeromorphicOn (f n) (sphere 0 |(1 : ℝ)|) := by
      intro z hz
      exact (hfanalytic n z (sphere_subset_closedBall (by simpa using hz))).meromorphicAt
    have hlog : CircleIntegrable (fun z ↦ Real.log ‖f n z‖) 0 1 :=
      hmero.circleIntegrable_log_norm
    simpa only [Pi.mul_apply] using
      hlog.mul_of_continuousOn (continuousOn_re_herglotzRieszKernel (by simpa using hw))
  have hfloor_circle (n N : ℕ) : ContinuousOn (fun z : ℂ ↦
      Real.log (max ‖f n z‖ (Real.exp (-(N : ℝ))))) (sphere 0 1) := by
    intro z hz
    change ContinuousWithinAt ((fun x : ℂ ↦
      Real.log (max ‖x‖ (Real.exp (-(N : ℝ)))) ) ∘ f n) (sphere 0 1) z
    exact ((continuousAt_log_max_norm_exp_neg (N : ℝ) (f n z)).comp
      (hfanalytic n z (sphere_subset_closedBall hz)).continuousAt).continuousWithinAt
  have hfloor_int (n N : ℕ) : CircleIntegrable
      ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦
        Real.log (max ‖f n z‖ (Real.exp (-(N : ℝ))))) 0 1 := by
    simpa only [Pi.mul_apply] using
      ((continuousOn_re_herglotzRieszKernel hw).mul (hfloor_circle n N)).circleIntegrable
        (by norm_num : (0 : ℝ) ≤ 1)
  have hfinite (N : ℕ) : ∀ᶠ n : ℕ in atTop,
      Real.log ‖f n w‖ ≤
        (Real.sin (Real.pi * θ) / 2) *
          ((∫ t : ℝ,
            Real.log (max ‖f n (b₀ t)‖ (Real.exp (-(N : ℝ)))) /
              (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) +
           ∫ t : ℝ,
            Real.log (max ‖f n (b₁ t)‖ (Real.exp (-(N : ℝ)))) /
              (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    filter_upwards [hfcenter_ne] with n hn
    calc
      Real.log ‖f n w‖ ≤
          Real.circleAverage
            ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦ Real.log ‖f n z‖) 0 1 :=
        analytic_weighted_circleAverage_log_norm_le (f := f n) (w := w) (by norm_num)
          (hfanalytic n) hw hn
      _ ≤ Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z ↦
            Real.log (max ‖f n z‖ (Real.exp (-(N : ℝ))))) 0 1 :=
        analytic_weighted_circleAverage_log_norm_le_floor (f := f n) (w := w)
          (K := fun _ : ℂ ↦ (N : ℝ)) (by norm_num) (hfanalytic n) hw hn (hraw n)
          (hfloor_int n N)
      _ = (Real.sin (Real.pi * θ) / 2) *
          ((∫ t : ℝ,
            Real.log (max ‖f n (b₀ t)‖ (Real.exp (-(N : ℝ)))) /
              (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) +
           ∫ t : ℝ,
            Real.log (max ‖f n (b₁ t)‖ (Real.exp (-(N : ℝ)))) /
              (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
        simpa [w, b₀, b₁] using
          (circleAverage_poisson_transport hθ (hfloor_circle n N))
  have hlogcenter : Tendsto (fun n : ℕ ↦ Real.log ‖f n w‖) atTop
      (𝓝 (Real.log ‖F (θ : ℂ)‖)) := by
    simpa only [Function.comp_def] using
      (Real.continuousAt_log (norm_ne_zero_iff.mpr hFθ)).tendsto.comp hfcenter.norm
  have hfloor_bound (N : ℕ) : Real.log ‖F (θ : ℂ)‖ ≤
      (Real.sin (Real.pi * θ) / 2) *
        ((∫ t : ℝ,
          Real.log (max ‖F ((t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
            (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) +
         ∫ t : ℝ,
          Real.log (max ‖F (1 + (t : ℂ) * Complex.I)‖ (Real.exp (-(N : ℝ)))) /
            (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    apply le_of_tendsto_of_tendsto hlogcenter
      (((hI₀_lim N).add (hI₁_lim N)).const_mul (Real.sin (Real.pi * θ) / 2))
    exact hfinite N
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * θ) / 2 := by
    have harg0 : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ.1
    have harg1 : Real.pi * θ < Real.pi := by
      nlinarith [mul_lt_mul_of_pos_left hθ.2 Real.pi_pos]
    exact div_nonneg (Real.sin_pos_of_pos_of_lt_pi harg0 harg1).le (by norm_num)
  have hMgrowth₀ : ∃ b A : ℝ, b < Real.pi ∧ ∀ t : ℝ,
      |Real.log (M₀ t)| ≤ A * Real.exp (b * |t|) := by
    rcases hMgrowth with ⟨b, A, hb, hbound⟩
    exact ⟨b, A, hb, fun t ↦ (hbound t).1⟩
  have hMgrowth₁ : ∃ b A : ℝ, b < Real.pi ∧ ∀ t : ℝ,
      |Real.log (M₁ t)| ≤ A * Real.exp (b * |t|) := by
    rcases hMgrowth with ⟨b, A, hb, hbound⟩
    exact ⟨b, A, hb, fun t ↦ (hbound t).2⟩
  have hboundary (N : ℕ) : Real.log ‖F (θ : ℂ)‖ ≤
      (Real.sin (Real.pi * θ) / 2) *
        ((∫ t : ℝ,
          max (Real.log (M₀ t)) (-(N : ℝ)) /
            (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) +
         ∫ t : ℝ,
          max (Real.log (M₁ t)) (-(N : ℝ)) /
            (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    have hleft := integral_left_log_max_norm_exp_neg_le (F := F) (M := M₀) N hθ hF hM.1
      (fun t ↦ (hMpos t).1) hMgrowth₀ hbound₀
    have hright := integral_right_log_max_norm_exp_neg_le (F := F) (M := M₁) N hθ hF hM.2
      (fun t ↦ (hMpos t).2) hMgrowth₁ hbound₁
    calc
      Real.log ‖F (θ : ℂ)‖ ≤ _ := hfloor_bound N
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hleft hright) hsin_nonneg
  exact Real.le_exp_of_log_le
    (log_le_hirschman_integral_of_floors hθ hM hMgrowth hboundary)
private theorem normalized_pairing_bound_of_deformations
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {p₀ p₁ q₀ q₁ : ENNReal} {θ : ℝ} {M₀ M₁ : ℝ → ℝ}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hθ : θ ∈ Set.Ioo 0 1)
    (hT_add : ∀ (z : verticalClosedStrip 0 1) (f g : SimpleFunc X ℂ),
      Integrable f μ → Integrable g μ → T z (f + g) = T z f + T z g)
    (hT_smul : ∀ (z : verticalClosedStrip 0 1) (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T z (c • f) = c • T z f)
    (hT_measurable : ∀ (z : verticalClosedStrip 0 1) (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T z f))
    (hpair_integrable : ∀ (z : verticalClosedStrip 0 1)
      (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν → Integrable (fun y ↦ T z f y * g y) ν)
    (hanalytic : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν →
      DiffContOnCl ℂ (fun z ↦ ∫ y, T z f y * g y ∂ν) (verticalStrip 0 1))
    (hfamily_growth : ∃ a : ℝ, a < Real.pi ∧
      ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
        Integrable f μ → Integrable g ν →
        ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
          ‖∫ y, T z f y * g y ∂ν‖ ≤
            Real.exp (C * Real.exp (a * |(z : ℂ).im|)))
    (hM_measurable : Measurable M₀ ∧ Measurable M₁)
    (hM_pos : ∀ t : ℝ, 0 < M₀ t ∧ 0 < M₁ t)
    (hM_growth : ∃ b A : ℝ, b < Real.pi ∧ ∀ t : ℝ,
      |Real.log (M₀ t)| ≤ A * Real.exp (b * |t|) ∧
        |Real.log (M₁ t)| ≤ A * Real.exp (b * |t|))
    (hbound₀ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T ((t : ℂ) * Complex.I) f) q₀ ν ≤
        ENNReal.ofReal (M₀ t) * eLpNorm (f : X → ℂ) p₀ μ)
    (hbound₁ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T (1 + (t : ℂ) * Complex.I) f) q₁ ν ≤
        ENNReal.ofReal (M₁ t) * eLpNorm (f : X → ℂ) p₁ μ)
    (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ)
    (hf : Integrable (f : X → ℂ) μ) (hg : Integrable (g : Y → ℂ) ν)
    (φ ψ : ℂ → ℂ → ℂ)
    (hφzero : ∀ z, φ z 0 = 0) (hψzero : ∀ z, ψ z 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hφbound : ∀ c ∈ f.range.erase 0, ∀ z : verticalClosedStrip 0 1, ‖φ z c‖ ≤ A)
    (hψbound : ∀ c ∈ g.range.erase 0, ∀ z : verticalClosedStrip 0 1, ‖ψ z c‖ ≤ B)
    (hφanalytic : ∀ c ∈ f.range.erase 0,
      DiffContOnCl ℂ (fun z ↦ φ z c) (verticalStrip 0 1))
    (hψanalytic : ∀ c ∈ g.range.erase 0,
      DiffContOnCl ℂ (fun z ↦ ψ z c) (verticalStrip 0 1))
    (hφtheta : f.map (φ (θ : ℂ)) = f) (hψtheta : g.map (ψ (θ : ℂ)) = g)
    (hφleft : ∀ t : ℝ,
      eLpNorm (f.map (φ ((t : ℂ) * Complex.I)) : X → ℂ) p₀ μ ≤ 1)
    (hφright : ∀ t : ℝ,
      eLpNorm (f.map (φ (1 + (t : ℂ) * Complex.I)) : X → ℂ) p₁ μ ≤ 1)
    (hψleft : ∀ t : ℝ,
      eLpNorm (g.map (ψ ((t : ℂ) * Complex.I)) : Y → ℂ) q₀.conjExponent ν ≤ 1)
    (hψright : ∀ t : ℝ,
      eLpNorm (g.map (ψ (1 + (t : ℂ) * Complex.I)) : Y → ℂ) q₁.conjExponent ν ≤ 1) :
    ‖∫ y, T (θ : ℂ) f y * g y ∂ν‖ ≤
      Real.exp
        ((Real.sin (Real.pi * θ) / 2) *
          ∫ t : ℝ,
            Real.log (M₀ t) / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) +
              Real.log (M₁ t) / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
  let F : ℂ → ℂ := fun z ↦
    ∫ y, T z (f.map (φ z)) y * (g.map (ψ z)) y ∂ν
  have hF : DiffContOnCl ℂ F (verticalStrip 0 1) := by
    simpa only [F] using
      (diffContOnCl_pairing_of_simple_deformations T hT_add hT_smul hpair_integrable
        hanalytic f g hf hg φ ψ hφzero hψzero hφanalytic hψanalytic)
  have hF_growth : ∃ a : ℝ, a < Real.pi ∧ ∃ C : ℝ,
      ∀ z : ℂ, z ∈ verticalClosedStrip 0 1 →
        ‖F z‖ ≤ Real.exp (C * Real.exp (a * |z.im|)) := by
    obtain ⟨a, ha, C, hC⟩ :=
      family_growth_of_simple_deformations T hT_add hT_smul hpair_integrable hfamily_growth
        f g hf hg φ ψ hφzero hψzero hA hB hφbound hψbound
    refine ⟨a, ha, C, ?_⟩
    intro z hz
    simpa only [F] using hC ⟨z, hz⟩
  have hFbound₀ : ∀ t : ℝ, ‖F ((t : ℂ) * Complex.I)‖ ≤ M₀ t := by
    intro t
    dsimp only [F]
    exact left_boundary_pairing_bound_normalized T hq₀ hT_measurable hbound₀
      (fun s ↦ (hM_pos s).1.le) t
      (f.map (φ ((t : ℂ) * Complex.I))) (g.map (ψ ((t : ℂ) * Complex.I)))
      (integrable_map_of_integrable f hf _ (hφzero _))
      (integrable_map_of_integrable g hg _ (hψzero _))
      (hφleft t) (hψleft t)
  have hFbound₁ : ∀ t : ℝ, ‖F (1 + (t : ℂ) * Complex.I)‖ ≤ M₁ t := by
    intro t
    dsimp only [F]
    exact right_boundary_pairing_bound_normalized T hq₁ hT_measurable hbound₁
      (fun s ↦ (hM_pos s).2.le) t
      (f.map (φ (1 + (t : ℂ) * Complex.I)))
      (g.map (ψ (1 + (t : ℂ) * Complex.I)))
      (integrable_map_of_integrable f hf _ (hφzero _))
      (integrable_map_of_integrable g hg _ (hψzero _))
      (hφright t) (hψright t)
  simpa only [F, hφtheta, hψtheta] using
    (hirschman_three_lines hθ hF hF_growth hM_measurable hM_pos hM_growth hFbound₀ hFbound₁)
section
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {p₀ p₁ p q₀ q₁ q : ENNReal} {θ : ℝ} {M₀ M₁ : ℝ → ℝ}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hT_add : ∀ (z : verticalClosedStrip 0 1) (f g : SimpleFunc X ℂ),
      Integrable f μ → Integrable g μ → T z (f + g) = T z f + T z g)
    (hT_smul : ∀ (z : verticalClosedStrip 0 1) (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T z (c • f) = c • T z f)
    (hT_measurable : ∀ (z : verticalClosedStrip 0 1) (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T z f))
    (hpair_integrable : ∀ (z : verticalClosedStrip 0 1)
      (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν → Integrable (fun y ↦ T z f y * g y) ν)
    (hanalytic : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν →
      DiffContOnCl ℂ (fun z ↦ ∫ y, T z f y * g y ∂ν) (verticalStrip 0 1))
    (hfamily_growth : ∃ a : ℝ, a < Real.pi ∧
      ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
        Integrable f μ → Integrable g ν →
        ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
          ‖∫ y, T z f y * g y ∂ν‖ ≤ exp (C * exp (a * |(z : ℂ).im|)))
    (hM_measurable : Measurable M₀ ∧ Measurable M₁)
    (hM_pos : ∀ t : ℝ, 0 < M₀ t ∧ 0 < M₁ t)
    (hM_growth : ∃ b A : ℝ, b < Real.pi ∧ ∀ t : ℝ,
      |log (M₀ t)| ≤ A * exp (b * |t|) ∧ |log (M₁ t)| ≤ A * exp (b * |t|))
    (hbound₀ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T ((t : ℂ) * Complex.I) f) q₀ ν ≤
        ENNReal.ofReal (M₀ t) * eLpNorm (f : X → ℂ) p₀ μ)
    (hbound₁ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T (1 + (t : ℂ) * Complex.I) f) q₁ ν ≤
        ENNReal.ofReal (M₁ t) * eLpNorm (f : X → ℂ) p₁ μ) :
    ∀ f : SimpleFunc X ℂ, Integrable f μ →
      MemLp (T (θ : ℂ) f) q ν ∧
      eLpNorm (T (θ : ℂ) f) q ν ≤
        ENNReal.ofReal
          (exp
            ((sin (Real.pi * θ) / 2) *
              ∫ t : ℝ,
                log (M₀ t) / (cosh (Real.pi * t) - cos (Real.pi * θ)) +
                  log (M₁ t) / (cosh (Real.pi * t) + cos (Real.pi * θ)))) *
          eLpNorm (f : X → ℂ) p μ := by
  have hpone : 1 ≤ p := one_le_of_interp hθ hp₀ hp₁ hp
  have hqone : 1 ≤ q := one_le_of_interp hθ hq₀ hq₁ hq
  let zθ : verticalClosedStrip 0 1 := ⟨(θ : ℂ), by
    rw [verticalClosedStrip, Set.mem_preimage, Set.mem_Icc]
    exact ⟨hθ.1.le, hθ.2.le⟩⟩
  let K : ℝ := exp
    ((sin (Real.pi * θ) / 2) *
      ∫ t : ℝ,
        log (M₀ t) / (cosh (Real.pi * t) - cos (Real.pi * θ)) +
          log (M₁ t) / (cosh (Real.pi * t) + cos (Real.pi * θ)))
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hunit : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable (f : X → ℂ) μ → Integrable (g : Y → ℂ) ν →
      MemLp (f : X → ℂ) p μ → MemLp (g : Y → ℂ) q.conjExponent ν →
      eLpNorm (f : X → ℂ) p μ ≤ 1 →
      eLpNorm (g : Y → ℂ) q.conjExponent ν ≤ 1 →
      ‖∫ y, T (θ : ℂ) f y * g y ∂ν‖ ≤ K := by
    classical
    intro f g hf hg _ _ hfnorm hgnorm
    by_cases hp_top : p = ∞
    · have hpends : p₀ = ∞ ∧ p₁ = ∞ :=
        (inv_eq_zero_iff_eq_top_of_interp hθ hp).mp hp_top
      by_cases hq_one : q = 1
      · have hqends : q₀ = 1 ∧ q₁ = 1 :=
          (eq_one_iff_eq_one_of_interp hθ hq₀ hq₁ hq).mp hq_one
        have hq₀conj : q₀.conjExponent = q.conjExponent := by
          simp [hqends.1, hq_one]
        have hq₁conj : q₁.conjExponent = q.conjExponent := by
          simp [hqends.2, hq_one]
        have hgnorms :=
          output_deformation_top_boundary_le_one g hq₀conj hq₁conj hgnorm
        obtain ⟨A, hA, hAbound⟩ :=
          finite_range_uniform_bound (f.range.erase 0) (fun c : ℂ ↦ ‖c‖)
            (fun c hc ↦ norm_nonneg c)
        obtain ⟨B, hB, hBbound⟩ :=
          finite_range_uniform_bound (g.range.erase 0) (fun c : ℂ ↦ ‖c‖)
            (fun c hc ↦ norm_nonneg c)
        simpa only [K] using
          (normalized_pairing_bound_of_deformations T hq₀ hq₁ hθ hT_add hT_smul
            hT_measurable hpair_integrable hanalytic hfamily_growth hM_measurable hM_pos
            hM_growth hbound₀ hbound₁ f g hf hg (fun _ c ↦ c) (fun _ c ↦ c)
            (by intro z; rfl) (by intro z; rfl) hA hB
            (by
              intro c hc z
              exact hAbound c hc)
            (by
              intro c hc z
              exact hBbound c hc)
            (by
              intro c hc
              simpa using
                (diffContOnCl_const (𝕜 := ℂ) (s := verticalStrip 0 1) (c := c)))
            (by
              intro c hc
              simpa using
                (diffContOnCl_const (𝕜 := ℂ) (s := verticalStrip 0 1) (c := c)))
            (by simpa using output_deformation_top_at_theta f)
            (by simpa using output_deformation_top_at_theta g)
            (by
              intro t
              rw [output_deformation_top_at_theta f]
              simpa [hpends.1, hp_top] using hfnorm)
            (by
              intro t
              rw [output_deformation_top_at_theta f]
              simpa [hpends.2, hp_top] using hfnorm)
            (by
              intro t
              rw [output_deformation_top_at_theta g]
              exact hgnorms.1)
            (by
              intro t
              rw [output_deformation_top_at_theta g]
              exact hgnorms.2))
      · let b₀ : ℝ := q.conjExponent.toReal * (q₀.conjExponent⁻¹).toReal
        let b₁ : ℝ := q.conjExponent.toReal * (q₁.conjExponent⁻¹).toReal
        let ψ : ℂ → ℂ → ℂ := fun z c ↦ if c = 0 then 0 else
          c / (‖c‖ : ℂ) * Complex.exp
            ((((b₁ - b₀ : ℝ) : ℂ) * z + (b₀ : ℂ)) *
              ((Real.log ‖c‖ : ℝ) : ℂ))
        have hb₀ : 0 ≤ b₀ := by
          dsimp [b₀]
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        have hb₁ : 0 ≤ b₁ := by
          dsimp [b₁]
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        obtain ⟨A, hA, hAbound⟩ :=
          finite_range_uniform_bound (f.range.erase 0) (fun c : ℂ ↦ ‖c‖)
            (fun c hc ↦ norm_nonneg c)
        obtain ⟨B, hB, hBbound⟩ :=
          finite_range_uniform_bound (g.range.erase 0)
            (fun c : ℂ ↦ max 1 (‖c‖ ^ max b₀ b₁))
            (fun c hc ↦ zero_le_one.trans (le_max_left _ _))
        simpa only [K] using
          (normalized_pairing_bound_of_deformations T hq₀ hq₁ hθ hT_add hT_smul
            hT_measurable hpair_integrable hanalytic hfamily_growth hM_measurable hM_pos
            hM_growth hbound₀ hbound₁ f g hf hg (fun _ c ↦ c) ψ
            (by intro z; rfl) (by intro z; simp [ψ]) hA hB
            (by
              intro c hc z
              exact hAbound c hc)
            (by
              intro c hc z
              simpa only [ψ] using
                (norm_input_deformation_coeff_uniform hb₀ hb₁ c (z : ℂ) z.2).trans
                  (hBbound c hc))
            (by
              intro c hc
              simpa using
                (diffContOnCl_const (𝕜 := ℂ) (s := verticalStrip 0 1) (c := c)))
            (by
              intro c hc
              simpa only [ψ] using
                (diffContOnCl_input_deformation_coeff (a₀ := b₀) (a₁ := b₁) c
                  (verticalStrip 0 1)))
            (by simpa using output_deformation_top_at_theta f)
            (by
              simpa only [ψ, b₀, b₁] using
                (simpleFunc_output_deformation_at_theta g hθ hqone hq₀ hq₁ hq_one hq))
            (by
              intro t
              rw [output_deformation_top_at_theta f]
              simpa [hpends.1, hp_top] using hfnorm)
            (by
              intro t
              rw [output_deformation_top_at_theta f]
              simpa [hpends.2, hp_top] using hfnorm)
            (by
              intro t
              simpa only [ψ, b₀, b₁] using
                (eLpNorm_output_deformation_left_le_one g hqone hq₀ hq₁ hq_one hgnorm))
            (by
              intro t
              simpa only [ψ, b₀, b₁] using
                (eLpNorm_output_deformation_right_le_one g hqone hq₀ hq₁ hq_one hgnorm)))
    · by_cases hq_one : q = 1
      · have hqends : q₀ = 1 ∧ q₁ = 1 :=
          (eq_one_iff_eq_one_of_interp hθ hq₀ hq₁ hq).mp hq_one
        have hq₀conj : q₀.conjExponent = q.conjExponent := by
          simp [hqends.1, hq_one]
        have hq₁conj : q₁.conjExponent = q.conjExponent := by
          simp [hqends.2, hq_one]
        have hgnorms :=
          output_deformation_top_boundary_le_one g hq₀conj hq₁conj hgnorm
        let a₀ : ℝ := p.toReal * (p₀⁻¹).toReal
        let a₁ : ℝ := p.toReal * (p₁⁻¹).toReal
        let φ : ℂ → ℂ → ℂ := fun z c ↦ if c = 0 then 0 else
          c / (‖c‖ : ℂ) * Complex.exp
            ((((a₁ - a₀ : ℝ) : ℂ) * z + (a₀ : ℂ)) *
              ((Real.log ‖c‖ : ℝ) : ℂ))
        have ha₀ : 0 ≤ a₀ := by
          dsimp [a₀]
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        have ha₁ : 0 ≤ a₁ := by
          dsimp [a₁]
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        obtain ⟨A, hA, hAbound⟩ :=
          finite_range_uniform_bound (f.range.erase 0)
            (fun c : ℂ ↦ max 1 (‖c‖ ^ max a₀ a₁))
            (fun c hc ↦ zero_le_one.trans (le_max_left _ _))
        obtain ⟨B, hB, hBbound⟩ :=
          finite_range_uniform_bound (g.range.erase 0) (fun c : ℂ ↦ ‖c‖)
            (fun c hc ↦ norm_nonneg c)
        simpa only [K] using
          (normalized_pairing_bound_of_deformations T hq₀ hq₁ hθ hT_add hT_smul
            hT_measurable hpair_integrable hanalytic hfamily_growth hM_measurable hM_pos
            hM_growth hbound₀ hbound₁ f g hf hg φ (fun _ c ↦ c)
            (by intro z; simp [φ]) (by intro z; rfl) hA hB
            (by
              intro c hc z
              simpa only [φ] using
                (norm_input_deformation_coeff_uniform ha₀ ha₁ c (z : ℂ) z.2).trans
                  (hAbound c hc))
            (by
              intro c hc z
              exact hBbound c hc)
            (by
              intro c hc
              simpa only [φ] using
                (diffContOnCl_input_deformation_coeff (a₀ := a₀) (a₁ := a₁) c
                  (verticalStrip 0 1)))
            (by
              intro c hc
              simpa using
                (diffContOnCl_const (𝕜 := ℂ) (s := verticalStrip 0 1) (c := c)))
            (by
              simpa only [φ, a₀, a₁] using
                (simpleFunc_input_deformation_at_theta f
                  (input_coeff_at_theta_of_interp_general hθ hpone hp₀ hp₁ hp_top hp)))
            (by simpa using output_deformation_top_at_theta g)
            (by
              intro t
              simpa only [φ, a₀, a₁] using
                (eLpNorm_input_deformation_left_coeff_ennreal_le_one f hpone hp₀ hp_top
                  rfl hfnorm))
            (by
              intro t
              simpa only [φ, a₀, a₁] using
                (eLpNorm_input_deformation_right_coeff_ennreal_le_one f hpone hp₁ hp_top
                  rfl hfnorm))
            (by
              intro t
              rw [output_deformation_top_at_theta g]
              exact hgnorms.1)
            (by
              intro t
              rw [output_deformation_top_at_theta g]
              exact hgnorms.2))
      · let a₀ : ℝ := p.toReal * (p₀⁻¹).toReal
        let a₁ : ℝ := p.toReal * (p₁⁻¹).toReal
        let b₀ : ℝ := q.conjExponent.toReal * (q₀.conjExponent⁻¹).toReal
        let b₁ : ℝ := q.conjExponent.toReal * (q₁.conjExponent⁻¹).toReal
        let φ : ℂ → ℂ → ℂ := fun z c ↦ if c = 0 then 0 else
          c / (‖c‖ : ℂ) * Complex.exp
            ((((a₁ - a₀ : ℝ) : ℂ) * z + (a₀ : ℂ)) *
              ((Real.log ‖c‖ : ℝ) : ℂ))
        let ψ : ℂ → ℂ → ℂ := fun z c ↦ if c = 0 then 0 else
          c / (‖c‖ : ℂ) * Complex.exp
            ((((b₁ - b₀ : ℝ) : ℂ) * z + (b₀ : ℂ)) *
              ((Real.log ‖c‖ : ℝ) : ℂ))
        have ha₀ : 0 ≤ a₀ := by
          dsimp [a₀]
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        have ha₁ : 0 ≤ a₁ := by
          dsimp [a₁]
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        have hb₀ : 0 ≤ b₀ := by
          dsimp [b₀]
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        have hb₁ : 0 ≤ b₁ := by
          dsimp [b₁]
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        obtain ⟨A, hA, hAbound⟩ :=
          finite_range_uniform_bound (f.range.erase 0)
            (fun c : ℂ ↦ max 1 (‖c‖ ^ max a₀ a₁))
            (fun c hc ↦ zero_le_one.trans (le_max_left _ _))
        obtain ⟨B, hB, hBbound⟩ :=
          finite_range_uniform_bound (g.range.erase 0)
            (fun c : ℂ ↦ max 1 (‖c‖ ^ max b₀ b₁))
            (fun c hc ↦ zero_le_one.trans (le_max_left _ _))
        simpa only [K] using
          (normalized_pairing_bound_of_deformations T hq₀ hq₁ hθ hT_add hT_smul
            hT_measurable hpair_integrable hanalytic hfamily_growth hM_measurable hM_pos
            hM_growth hbound₀ hbound₁ f g hf hg φ ψ
            (by intro z; simp [φ]) (by intro z; simp [ψ]) hA hB
            (by
              intro c hc z
              simpa only [φ] using
                (norm_input_deformation_coeff_uniform ha₀ ha₁ c (z : ℂ) z.2).trans
                  (hAbound c hc))
            (by
              intro c hc z
              simpa only [ψ] using
                (norm_input_deformation_coeff_uniform hb₀ hb₁ c (z : ℂ) z.2).trans
                  (hBbound c hc))
            (by
              intro c hc
              simpa only [φ] using
                (diffContOnCl_input_deformation_coeff (a₀ := a₀) (a₁ := a₁) c
                  (verticalStrip 0 1)))
            (by
              intro c hc
              simpa only [ψ] using
                (diffContOnCl_input_deformation_coeff (a₀ := b₀) (a₁ := b₁) c
                  (verticalStrip 0 1)))
            (by
              simpa only [φ, a₀, a₁] using
                (simpleFunc_input_deformation_at_theta f
                  (input_coeff_at_theta_of_interp_general hθ hpone hp₀ hp₁ hp_top hp)))
            (by
              simpa only [ψ, b₀, b₁] using
                (simpleFunc_output_deformation_at_theta g hθ hqone hq₀ hq₁ hq_one hq))
            (by
              intro t
              simpa only [φ, a₀, a₁] using
                (eLpNorm_input_deformation_left_coeff_ennreal_le_one f hpone hp₀ hp_top
                  rfl hfnorm))
            (by
              intro t
              simpa only [φ, a₀, a₁] using
                (eLpNorm_input_deformation_right_coeff_ennreal_le_one f hpone hp₁ hp_top
                  rfl hfnorm))
            (by
              intro t
              simpa only [ψ, b₀, b₁] using
                (eLpNorm_output_deformation_left_le_one g hqone hq₀ hq₁ hq_one hgnorm))
            (by
              intro t
              simpa only [ψ, b₀, b₁] using
                (eLpNorm_output_deformation_right_le_one g hqone hq₀ hq₁ hq_one hgnorm)))
  change ∀ f : SimpleFunc X ℂ, Integrable f μ →
    MemLp (T (θ : ℂ) f) q ν ∧
      eLpNorm (T (θ : ℂ) f) q ν ≤ ENNReal.ofReal K * eLpNorm (f : X → ℂ) p μ
  apply interpolation_from_pairing_bound (T (θ : ℂ)) hqone
  · intro f hf
    exact hT_measurable zθ f hf
  · intro f g hf hg
    exact hpair_integrable zθ f g hf hg
  · exact hK
  intro f g hf hg
  let B : SimpleFunc X ℂ → SimpleFunc Y ℂ → ℂ :=
    fun u v ↦ ∫ y, T (θ : ℂ) u y * v y ∂ν
  have hleft : ∀ (u : SimpleFunc X ℂ) (v : SimpleFunc Y ℂ) (c : ℂ),
      Integrable (u : X → ℂ) μ → B (c • u) v = c * B u v := by
    intro u v c hu
    exact integral_pairing_smul_left T hT_smul zθ c u v hu
  have hright : ∀ (u : SimpleFunc X ℂ) (v : SimpleFunc Y ℂ) (c : ℂ),
      B u (c • v) = c * B u v := by
    intro u v c
    exact integral_pairing_smul_right T (θ : ℂ) c u v
  have hzero_right : ∀ (u : SimpleFunc X ℂ) (v : SimpleFunc Y ℂ),
      Integrable (v : Y → ℂ) ν →
      eLpNorm (v : Y → ℂ) q.conjExponent ν = 0 → B u v = 0 := by
    intro u v hv hvzero
    exact integral_mul_simpleFunc_eq_zero_of_eLpNorm_eq_zero hqone hv hvzero
  have hzero_left : ∀ (u : SimpleFunc X ℂ) (v : SimpleFunc Y ℂ),
      Integrable (u : X → ℂ) μ → Integrable (v : Y → ℂ) ν →
      eLpNorm (u : X → ℂ) p μ = 0 → B u v = 0 := by
    intro u v hu hv huzero
    exact bilinear_zero_left_of_unit B hleft hright hunit hzero_right u v hu hv
      (memLp_simpleFunc_of_integrable u hu)
      (memLp_simpleFunc_of_integrable v hv) huzero
  exact bilinear_bound_of_unit B hleft hright hunit hzero_left hzero_right f g hf hg
    (memLp_simpleFunc_of_integrable f hf) (memLp_simpleFunc_of_integrable g hg)
end Auto
