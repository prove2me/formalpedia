-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:22:39.981065+00:00
-- url     : https://prove2.me/theorems/d11ffd4f-fcf9-45c5-b131-86144d86211a
-- title:
--   Local smoothness of exponential-weight integrals
-- statement:
--   If $e^{t\|x\|}\|g(x)\|$ is integrable for every $t<r$, `weightedExpD_integrable_lt` transfers this condition to the derivative amplitude $\langle\cdot,x\rangle g(x)$, and `weightedExp_integral_hasFDerivAt_of_lt` gives differentiation under the integral at every $z$ with $\|z\|<r$. The declarations `weighted_integral_contDiffOn_nat` and `weighted_integral_contDiffOn` then state that $z\mapsto\int e^{\langle z,x\rangle}g(x)\,d\mu$ is $C^n$, respectively $C^\infty$, on the open metric ball `Metric.ball 0 r`. All conclusions retain the strong a.e. measurability and local exponential-integrability hypotheses.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   theorem weightedExpD_integrable_lt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
--       {μ : Measure E} {g : E → F} (hg : AEStronglyMeasurable g μ) {r : ℝ}
--       (hgi : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ) :
--       ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖weightedExpD g x‖) μ
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Local.lean) · `FunctionalInequalities.Analysis.BakryEmery.Tilt.Local` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Local.lean#L27-L228 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Local`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
section Local
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- **Local amplitude integrability.** -/
theorem weightedExpD_integrable_lt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} {g : E → F} (hg : AEStronglyMeasurable g μ) {r : ℝ}
    (hgi : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ) :
    ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖weightedExpD g x‖) μ := by
    intro t htr
    let ε : ℝ := (r - t) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hte : t + ε < r := by
      dsimp [ε]
      linarith
    have hmeas :
        AEStronglyMeasurable
          (fun x : E => Real.exp (t * ‖x‖) * ‖weightedExpD g x‖) μ :=
      ((by
          fun_prop : Continuous (fun x : E => Real.exp (t * ‖x‖))).aestronglyMeasurable).mul
        (weightedExpD_meas hg).norm
    refine ((hgi (t + ε) hte).const_mul ε⁻¹).mono' hmeas ?_
    filter_upwards [] with x
    have hleft :
        0 ≤ Real.exp (t * ‖x‖) * ‖weightedExpD g x‖ := by
      positivity
    rw [Real.norm_of_nonneg hleft]
    have hεq :
        ε * ‖x‖ ≤ Real.exp (ε * ‖x‖) := by
      have h := Real.add_one_le_exp (ε * ‖x‖)
      linarith
    have hq :
        ‖x‖ ≤ ε⁻¹ * Real.exp (ε * ‖x‖) := by
      calc
        ‖x‖ = ε⁻¹ * (ε * ‖x‖) := by
          field_simp [ne_of_gt hε]
        _ ≤ ε⁻¹ * Real.exp (ε * ‖x‖) := by
          gcongr
    calc
      Real.exp (t * ‖x‖) * ‖weightedExpD g x‖ =
          Real.exp (t * ‖x‖) * (‖x‖ * ‖g x‖) := by
        simp [weightedExpD, ContinuousLinearMap.norm_smulRight_apply,
          innerSL_apply_norm]
      _ ≤ Real.exp (t * ‖x‖) *
            ((ε⁻¹ * Real.exp (ε * ‖x‖)) * ‖g x‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
            (by positivity)
      _ = ε⁻¹ *
            ((Real.exp (t * ‖x‖) * Real.exp (ε * ‖x‖)) * ‖g x‖) := by
        ring
      _ = ε⁻¹ * (Real.exp ((t + ε) * ‖x‖) * ‖g x‖) := by
        rw [← Real.exp_add]
        congr 2
        ring
omit [CompleteSpace E] in
/-- **Local differentiation under the integral.** -/
theorem weightedExp_integral_hasFDerivAt_of_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {r : ℝ}
    (hgi : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ) {z : E} (hz : ‖z‖ < r) :
    HasFDerivAt (fun w => ∫ x, Real.exp ⟪w, x⟫ • g x ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ • weightedExpD g x ∂μ) z := by
    let δ : ℝ := (r - ‖z‖) / 4
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hδr : ‖z‖ + 2 * δ < r := by
      dsimp [δ]
      linarith
    let s : Set E := Metric.ball z δ
    let B : E → ℝ :=
      fun x => δ⁻¹ * Real.exp ((‖z‖ + 2 * δ) * ‖x‖) * ‖g x‖
    have hB : Integrable B μ := by
      have h := hgi (‖z‖ + 2 * δ) hδr
      simpa [B, mul_assoc] using h.const_mul δ⁻¹
    have hmeas : ∀ w : E, AEStronglyMeasurable
        (fun x => Real.exp ⟪w, x⟫ • g x) μ := by
      intro w
      exact
        (by fun_prop : Continuous (fun x : E => Real.exp ⟪w, x⟫)).aestronglyMeasurable.smul hg
    have hmeas' : ∀ w : E, AEStronglyMeasurable
        (fun x => Real.exp ⟪w, x⟫ • weightedExpD g x) μ := by
      intro w
      exact
        (by fun_prop : Continuous (fun x : E => Real.exp ⟪w, x⟫)).aestronglyMeasurable.smul
          (weightedExpD_meas hg)
    have hInt : Integrable (fun x => Real.exp ⟪z, x⟫ • g x) μ := by
      refine (hgi ‖z‖ hz).mono' (hmeas z) ?_
      filter_upwards [] with x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      gcongr
      exact real_inner_le_norm z x
    have hbound : ∀ᵐ x ∂μ, ∀ w ∈ s,
        ‖Real.exp ⟪w, x⟫ • weightedExpD g x‖ ≤ B x := by
      filter_upwards [] with x w hw
      have hdist : ‖w - z‖ < δ := by
        simpa [s, dist_eq_norm] using hw
      have hw' : ‖w‖ ≤ ‖z‖ + δ := by
        have h₁ : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          calc
            ‖w‖ = ‖w - z + z‖ := by
              congr 1
              abel
            _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        linarith
      have hx : ‖x‖ ≤ δ⁻¹ * Real.exp (δ * ‖x‖) := by
        have he : δ * ‖x‖ ≤ Real.exp (δ * ‖x‖) := by
          have h := Real.add_one_le_exp (δ * ‖x‖)
          linarith
        calc
          ‖x‖ = δ⁻¹ * (δ * ‖x‖) := by
            field_simp
          _ ≤ δ⁻¹ * Real.exp (δ * ‖x‖) :=
            mul_le_mul_of_nonneg_left he (le_of_lt (inv_pos.mpr hδ))
      have hew : ⟪w, x⟫ ≤ (‖z‖ + δ) * ‖x‖ := by
        calc
          ⟪w, x⟫ ≤ ‖w‖ * ‖x‖ := real_inner_le_norm w x
          _ ≤ (‖z‖ + δ) * ‖x‖ := by gcongr
      have hexp : Real.exp ⟪w, x⟫ ≤
          Real.exp ((‖z‖ + δ) * ‖x‖) :=
        Real.exp_le_exp.mpr hew
      have hnorm : ‖weightedExpD g x‖ = ‖x‖ * ‖g x‖ := by
        simp [weightedExpD]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hnorm]
      calc
        Real.exp ⟪w, x⟫ * (‖x‖ * ‖g x‖) ≤
            Real.exp ((‖z‖ + δ) * ‖x‖) *
              (δ⁻¹ * Real.exp (δ * ‖x‖) * ‖g x‖) := by
          gcongr
        _ = δ⁻¹ *
            (Real.exp ((‖z‖ + δ) * ‖x‖) *
              Real.exp (δ * ‖x‖)) * ‖g x‖ := by ring
        _ = δ⁻¹ *
            Real.exp (((‖z‖ + δ) * ‖x‖) + δ * ‖x‖) * ‖g x‖ := by
          rw [← Real.exp_add]
        _ = B x := by
          dsimp [B]
          congr 2
          congr 1
          ring
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds z hδ)
      (Filter.Eventually.of_forall (fun w => hmeas w))
      hInt (hmeas' z) hbound hB ?_
    filter_upwards [] with x w hw
    exact weightedExp_hasFDeriv g x w
end Local
section Assembly
universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem weighted_integral_contDiffOn_nat
    {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) (n : ℕ) {g : E → F} (hg : AEStronglyMeasurable g μ) {r : ℝ}
    (hgi : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ) :
    ContDiffOn ℝ n (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) (Metric.ball 0 r) := by
  induction n generalizing F with
  | zero =>
    apply contDiffOn_zero.2
    intro z hz
    have hz' : ‖z‖ < r := by simpa using hz
    exact (weightedExp_integral_hasFDerivAt_of_lt μ hg hgi hz').continuousAt.continuousWithinAt
  | succ n IH =>
    simp only [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      Metric.isOpen_ball.uniqueDiffOn).2
    refine ⟨?_, (fun z => ∫ x, Real.exp ⟪z, x⟫ • weightedExpD g x ∂μ), ?_, ?_⟩
    · simp
    · exact IH (weightedExpD_meas hg) (weightedExpD_integrable_lt hg hgi)
    · intro z hz
      have hz' : ‖z‖ < r := by simpa using hz
      exact (weightedExp_integral_hasFDerivAt_of_lt μ hg hgi hz').hasFDerivWithinAt
theorem weighted_integral_contDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) {g : E → F} (hg : AEStronglyMeasurable g μ) {r : ℝ}
    (hgi : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ) :
    ContDiffOn ℝ ∞ (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) (Metric.ball 0 r) := by
  let L : ULift.{u} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  have hgl : AEStronglyMeasurable (fun x => L.symm (g x)) μ :=
    L.symm.toContinuousLinearEquiv.toContinuousLinearMap.continuous.comp_aestronglyMeasurable hg
  have hgil : ∀ t < r,
      Integrable (fun x => Real.exp (t * ‖x‖) * ‖L.symm (g x)‖) μ := by
    simpa only [L.symm.norm_map] using hgi
  have hs := (contDiffOn_infty.2 (fun n =>
    weighted_integral_contDiffOn_nat μ n hgl hgil)).continuousLinearMap_comp
      L.toContinuousLinearEquiv.toContinuousLinearMap
  apply hs.congr
  intro z _hz
  change (∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) =
    L.toContinuousLinearEquiv (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ)
  rw [← L.toContinuousLinearEquiv.integral_comp_comm]
  simp [L]
end Assembly
end BakryEmery
end Analysis
end FunctionalInequalities


