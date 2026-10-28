-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionApi
-- name    : KLSModular_LevyStochCalc_Brownian_ItoL2CompletionApi
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:19:15.383446+00:00
-- url     : https://prove2.me/theorems/2726bba3-f240-429d-9052-e494c979e1f0
-- title:
--   Public L² Brownian Itô integral API and difference isometry
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `stochasticIntegral` exposes the constructed process $t\mapsto\int_0^t H_s\,dW_s$ as the representative `stochasticIntegralBrownian`; `martingale_stochasticIntegral` states existence of a filtration, specifically the right-continuous Brownian filtration in the construction, with respect to which it is a martingale. `isometry_diff_stochasticIntegralBrownian` gives the per-difference isometry for two progressively measurable square-integrable integrands at every positive $T$, with both sides expressed as iterated $\operatorname{ENNReal}$ squared-norm integrals. The auxiliary `tendsto_lintegral_nnnorm_sq_of_eLpNorm` transfers $L^2$ convergence to convergence of squared norm integrals.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoL2CompletionQuadVar
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def stochasticIntegral
--       {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
--       (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       (H : Ω → ℝ → ℝ)
--       (h_meas : Measurable (Function.uncurry H))
--       (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
--       (h_sq_int_global : ∀ T, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--           (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (T : ℝ) : Ω → ℝ :=
--     stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global T
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoL2CompletionQuadVar`](https://prove2.me/theorems/6062fba0-aa8d-4423-8c5c-de5c7abb85aa).
--
--   Theorems in source order:
--
--   - [`martingale_rightCont_quadVar_stochasticIntegralBrownian`](https://prove2.me/theorems/0df2e8f2-7807-4907-a708-b5a34a8e6b9e)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionApi.lean) · `LevyStochCalc.Brownian.ItoL2CompletionApi` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionApi.lean#L205-L559 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionApi`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoL2CompletionApi`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionApi.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **`L²`-convergence ⇒ convergence of the squared mass.** If `gₙ → g` in `L²(μ)`
(with `‖g‖₂ < ⊤`), then `∫⁻ ‖gₙ‖₊² → ∫⁻ ‖g‖₊²`. The `L²`-norm is continuous under
`L²`-convergence (squeeze via the triangle inequality both ways), and `x ↦ x²` is
continuous on `ℝ≥0∞`. Underlies the per-difference Itô isometry (#17). -/
lemma tendsto_lintegral_nnnorm_sq_of_eLpNorm
    {β : Type*} [MeasurableSpace β] {μ : MeasureTheory.Measure β}
    {ι : Type*} {l : Filter ι} {gₙ : ι → β → ℝ} {g : β → ℝ}
    (hgₙ : ∀ n, MeasureTheory.AEStronglyMeasurable (gₙ n) μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ)
    (hgfin : MeasureTheory.eLpNorm g 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n - g) 2 μ) l (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ x, (‖gₙ n x‖₊ : ℝ≥0∞) ^ 2 ∂μ) l
      (nhds (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ)) := by
  -- `eLpNorm gₙ 2 → eLpNorm g 2` by the two-sided triangle bound.
  have hnorm : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n) 2 μ) l
      (nhds (MeasureTheory.eLpNorm g 2 μ)) := by
    have hlo : Filter.Tendsto (fun n => MeasureTheory.eLpNorm g 2 μ
        - MeasureTheory.eLpNorm (gₙ n - g) 2 μ) l (nhds (MeasureTheory.eLpNorm g 2 μ)) := by
      have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := MeasureTheory.eLpNorm g 2 μ))
        htend (Or.inl hgfin)
      simpa using this
    have hhi : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n - g) 2 μ
        + MeasureTheory.eLpNorm g 2 μ) l (nhds (MeasureTheory.eLpNorm g 2 μ)) := by
      have := htend.add (tendsto_const_nhds (x := MeasureTheory.eLpNorm g 2 μ))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
      (Filter.Eventually.of_forall (fun n => ?_)) (Filter.Eventually.of_forall (fun n => ?_))
    · refine tsub_le_iff_left.mpr ?_
      calc MeasureTheory.eLpNorm g 2 μ
          = MeasureTheory.eLpNorm (gₙ n - (gₙ n - g)) 2 μ := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
            simp only [Pi.sub_apply]; ring
        _ ≤ MeasureTheory.eLpNorm (gₙ n - g) 2 μ + MeasureTheory.eLpNorm (gₙ n) 2 μ := by
            refine le_trans (MeasureTheory.eLpNorm_sub_le (hgₙ n)
              ((hgₙ n).sub hg) (by norm_num)) ?_
            rw [add_comm]
    · calc MeasureTheory.eLpNorm (gₙ n) 2 μ
          = MeasureTheory.eLpNorm ((gₙ n - g) + g) 2 μ := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
            simp only [Pi.add_apply, Pi.sub_apply]; ring
        _ ≤ MeasureTheory.eLpNorm (gₙ n - g) 2 μ + MeasureTheory.eLpNorm g 2 μ :=
            MeasureTheory.eLpNorm_add_le ((hgₙ n).sub hg) hg (by norm_num)
  have hconv : ∀ x : β → ℝ,
      MeasureTheory.eLpNorm x 2 μ * MeasureTheory.eLpNorm x 2 μ
        = ∫⁻ y, (‖x y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    intro x
    rw [← eLpNorm_sq_eq_lintegral_nnnorm_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  simp_rw [← hconv]
  exact ENNReal.Tendsto.mul hnorm (Or.inr hgfin) hnorm (Or.inr hgfin)
/-- **Cross-integrand simple difference isometry.** For two integrands `H₁, H₂`, their
`masterApprox n` simple integrals satisfy `∫⁻‖Iₙ(H₁) − Iₙ(H₂)‖² = ∫⁻∫⁻‖evalₙ(H₁) −
evalₙ(H₂)‖²` at every `t ≥ 0`. Both `masterApprox · n` live on horizon `n+1`; extend
each to the common horizon `n+2` via `appendInterval` (which preserves `simpleIntegral`
and `eval`) and apply `simpleIntegral_intermediate_diff_isometry`. -/
theorem masterApprox_cross_diff_isometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) (H₁ H₂ : Ω → ℝ → ℝ)
    (h_meas₁ : Measurable (Function.uncurry H₁)) (h_meas₂ : Measurable (Function.uncurry H₂))
    (h_progMeas₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (h_progMeas₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (h_sq₁ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_sq₂ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (n : ℕ) {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n) t ω
        - simpleIntegral W (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval s ω
            - (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
  set Gn := masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n with hGn
  set Gm := masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n with hGm
  have hKn : Gn.partition (Fin.last Gn.N) < (n : ℝ) + 2 := by
    have h1 : Gn.partition (Fin.last Gn.N) ≤ (n : ℝ) + 1 := Gn.partition_le_T
    linarith
  have hKm : Gm.partition (Fin.last Gm.N) < (n : ℝ) + 2 := by
    have h1 : Gm.partition (Fin.last Gm.N) ≤ (n : ℝ) + 1 := Gm.partition_le_T
    linarith
  have h_eq : (Gn.appendInterval hKn).partition (Fin.last (Gn.appendInterval hKn).N)
      = (Gm.appendInterval hKm).partition (Fin.last (Gm.appendInterval hKm).N) :=
    (Gn.appendInterval_partition_last hKn).trans (Gm.appendInterval_partition_last hKm).symm
  have ha_n := Gn.appendInterval_adapt ℱ hKn
    (masterApprox_adapt ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n)
  have ha_m := Gm.appendInterval_adapt ℱ hKm
    (masterApprox_adapt ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n)
  have hiso := simpleIntegral_intermediate_diff_isometry W ℱ hℱ (Gn.appendInterval hKn)
    (Gm.appendInterval hKm) h_eq ha_n ha_m ht_nn
  have hL : ∫⁻ ω, (‖simpleIntegral W Gn t ω - simpleIntegral W Gm t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (Gn.appendInterval hKn) t ω
          - simpleIntegral W (Gm.appendInterval hKm) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [Gn.appendInterval_simpleIntegral W hKn t ω, Gm.appendInterval_simpleIntegral W hKm t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(Gn.appendInterval hKn).eval s ω - (Gm.appendInterval hKm).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P := by
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [Gn.appendInterval_eval hKn s ω, Gm.appendInterval_eval hKm s ω]
  rw [hL, hR]; exact hiso
/-- **Per-difference L²-isometry of the Brownian Itô integral.**
`∫⁻‖∫₀ᵀ H₁ dW − ∫₀ᵀ H₂ dW‖² = ∫⁻∫⁻_{[0,T]}‖H₁ − H₂‖²`. Both the integral difference
and the integrand difference are realized as `L²`-limits of the same simple-integral
difference sequence (`masterApprox_cross_diff_isometry`); `tendsto_lintegral_nnnorm_sq_of_eLpNorm`
identifies each limit, and `tendsto_nhds_unique` equates them. -/
theorem isometry_diff_stochasticIntegralBrownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) (H₁ H₂ : Ω → ℝ → ℝ)
    (h_meas₁ : Measurable (Function.uncurry H₁)) (h_meas₂ : Measurable (Function.uncurry H₂))
    (h_progMeas₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (h_progMeas₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (h_sq₁ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_sq₂ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ T ω
        - stochasticIntegralBrownian W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have ht_nn : (0 : ℝ) ≤ T := le_of_lt hT
  set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  -- abbreviations for the two simple-integral sequences and the two limits
  have hImeas : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : Probability.ProgressivelyMeasurable ℱ H)
      (hs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (n : ℕ),
      Measurable (fun ω => simpleIntegral W (masterApprox ℱ H hm hp hs n) T ω) := by
    intro H hm hp hs n
    unfold simpleIntegral
    exact Finset.measurable_sum _ (fun i _ =>
      ((masterApprox ℱ H hm hp hs n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _)))
  -- the bridge `∫⁻_{P⊗ν} ‖f‖² = ∫⁻∫⁻_{[0,T]} ‖f(ω,s)‖²`
  have hbridge : ∀ f : Ω × ℝ → ℝ, Measurable f →
      ∫⁻ p, (‖f p‖₊ : ℝ≥0∞) ^ 2 ∂(P.prod ν)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro f hf
    rw [MeasureTheory.lintegral_prod _
      (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
  -- `eval_n(H) → H` in `L²(P⊗ν)` for each integrand.
  have hevalL2 : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : Probability.ProgressivelyMeasurable ℱ H)
      (hs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun p : Ω × ℝ => (masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2) 2 (P.prod ν))
        Filter.atTop (nhds 0) := by
    intro H hm hp hs
    have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun p : Ω × ℝ => (masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2) 2 (P.prod ν)
        ^ (2 : ℝ)) Filter.atTop (nhds 0) := by
      have he := masterApprox_eval_tendsto (t := T) ℱ H hm hp hs
      refine he.congr (fun n => ?_)
      rw [eLpNorm_sq_eq_lintegral_nnnorm_sq,
        hbridge (fun p : Ω × ℝ => (masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2)
          (((masterApprox ℱ H hm hp hs n).eval_jointly_measurable).sub hm)]
      refine lintegral_congr (fun ω => ?_)
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
      rw [show (‖H ω s - (masterApprox ℱ H hm hp hs n).eval s ω‖₊ : ℝ≥0∞)
          = ‖(masterApprox ℱ H hm hp hs n).eval s ω - H ω s‖₊ from by
        rw [← nnnorm_neg]; congr 1; ring_nf]
    have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr (fun n => ?_)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- LHS: `∫⁻‖Iₙ(H₁)−Iₙ(H₂)‖² → ∫⁻‖F₁−F₂‖²`
  have hLHS : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W (masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n) T ω
        - simpleIntegral W (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds (∫⁻ ω,
        (‖stochasticIntegralBrownian W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ T ω
          - stochasticIntegralBrownian W ℱ hℱ H₂ h_meas₂ h_progMeas₂
            h_sq₂ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)) := by
    refine tendsto_lintegral_nnnorm_sq_of_eLpNorm
      (fun n => ((hImeas H₁ h_meas₁ h_progMeas₁ h_sq₁ n).sub
        (hImeas H₂ h_meas₂ h_progMeas₂ h_sq₂ n)).aestronglyMeasurable)
      ((stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁
        h_sq₁ T).aestronglyMeasurable.sub
        (stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂
          h_sq₂ T).aestronglyMeasurable)
      (by
        refine (lt_of_le_of_lt (MeasureTheory.eLpNorm_sub_le
          (stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁
            h_sq₁ T).aestronglyMeasurable
          (stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂
            h_sq₂ T).aestronglyMeasurable
          (by norm_num)) (ENNReal.add_lt_top.mpr
            ⟨(stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ T).2,
              (stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ T).2⟩)).ne)
      ?_
    have hsum := (masterApprox_tendsto_L2 W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ ht_nn).add
      (masterApprox_tendsto_L2 W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ ht_nn)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hsum)
      (Filter.Eventually.of_forall (fun n => bot_le))
      (Filter.Eventually.of_forall (fun n => ?_))
    refine le_trans ?_ (MeasureTheory.eLpNorm_sub_le
      ((hImeas H₁ h_meas₁ h_progMeas₁ h_sq₁ n).aestronglyMeasurable.sub
        (stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁
          h_sq₁ T).aestronglyMeasurable)
      ((hImeas H₂ h_meas₂ h_progMeas₂ h_sq₂ n).aestronglyMeasurable.sub
        (stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂
          h_sq₂ T).aestronglyMeasurable)
      (by norm_num))
    exact le_of_eq (MeasureTheory.eLpNorm_congr_ae
      (Filter.Eventually.of_forall (fun ω => by simp only [Pi.sub_apply]; ring)))
  -- RHS: `∫⁻∫⁻‖evalₙ(H₁)−evalₙ(H₂)‖² → ∫⁻∫⁻‖H₁−H₂‖²`
  have hHdfin : MeasureTheory.eLpNorm (fun p : Ω × ℝ => H₁ p.1 p.2 - H₂ p.1 p.2) 2 (P.prod ν)
      ≠ ⊤ :=
    (lt_of_le_of_lt (MeasureTheory.eLpNorm_sub_le
      (compensatorH_memLp_prod H₁ h_meas₁ h_sq₁ hT).1
      (compensatorH_memLp_prod H₂ h_meas₂ h_sq₂ hT).1 (by norm_num))
      (ENNReal.add_lt_top.mpr ⟨(compensatorH_memLp_prod H₁ h_meas₁ h_sq₁ hT).2,
        (compensatorH_memLp_prod H₂ h_meas₂ h_sq₂ hT).2⟩)).ne
  have hRHS' := tendsto_lintegral_nnnorm_sq_of_eLpNorm
    (μ := P.prod ν)
    (gₙ := fun n p => (masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval p.2 p.1
      - (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval p.2 p.1)
    (g := fun p => H₁ p.1 p.2 - H₂ p.1 p.2)
    (fun n => (((masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval_jointly_measurable).sub
      ((masterApprox ℱ H₂ h_meas₂ h_progMeas₂
        h_sq₂ n).eval_jointly_measurable)).aestronglyMeasurable)
    (h_meas₁.aestronglyMeasurable.sub h_meas₂.aestronglyMeasurable) hHdfin
    (by
      have hsum := (hevalL2 H₁ h_meas₁ h_progMeas₁ h_sq₁).add
        (hevalL2 H₂ h_meas₂ h_progMeas₂ h_sq₂)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hsum)
        (Filter.Eventually.of_forall (fun n => bot_le))
        (Filter.Eventually.of_forall (fun n => ?_))
      refine le_trans ?_ (MeasureTheory.eLpNorm_sub_le
        (((masterApprox ℱ H₁ h_meas₁ h_progMeas₁
          h_sq₁ n).eval_jointly_measurable).aestronglyMeasurable.sub
          h_meas₁.aestronglyMeasurable)
        (((masterApprox ℱ H₂ h_meas₂ h_progMeas₂
          h_sq₂ n).eval_jointly_measurable).aestronglyMeasurable.sub
          h_meas₂.aestronglyMeasurable) (by norm_num))
      exact le_of_eq (MeasureTheory.eLpNorm_congr_ae
        (Filter.Eventually.of_forall (fun p => by simp only [Pi.sub_apply]; ring))))
  rw [hbridge (fun p : Ω × ℝ => H₁ p.1 p.2 - H₂ p.1 p.2) (h_meas₁.sub h_meas₂)] at hRHS'
  have hRHS : Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval s ω
        - (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
    refine hRHS'.congr' (Filter.Eventually.of_forall (fun n => ?_))
    exact (hbridge _ (((masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval_jointly_measurable).sub
      ((masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval_jointly_measurable)))
  -- the two sequences agree (cross diff isometry); equate the limits.
  refine tendsto_nhds_unique (hLHS.congr' (Filter.Eventually.of_forall (fun n => ?_))) hRHS
  exact masterApprox_cross_diff_isometry W ℱ hℱ H₁ H₂ h_meas₁ h_meas₂ h_progMeas₁ h_progMeas₂
    h_sq₁ h_sq₂ n ht_nn
/-- The *L² Itô integral* `M_t = ∫_0^t H_s dW_s` against a Brownian motion `W`.

The **constructed** L²-limit process `stochasticIntegralBrownian` (the coherent
`L²`-limit of the `masterApprox` simple integrals), not a `Classical.choose`
witness — so it is genuinely linear-friendly (used by `itoIsometry_diff_brownian`). -/
noncomputable def stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global T
/-- **The L² Itô integral is a martingale.**

The Itô integral `M_t = ∫_0^t H_s dW_s` is a martingale with respect to some
filtration (the statement does not name it; the pinned form for `ℱ.rightCont`
is `martingale_rightCont_stochasticIntegralBrownian`).

Extracts conjunct 1 (martingale property) of `itoIsometry_brownian_unified_existence`. -/
theorem martingale_stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) F P := by
  unfold stochasticIntegral
  exact ⟨ℱ.rightCont,
    martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global⟩
end Ito
end Brownian
end LevyStochCalc


