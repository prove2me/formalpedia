-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence
-- name    : KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:08:14.755226+00:00
-- url     : https://prove2.me/theorems/7052eb64-0ceb-40e0-81f7-f59b0f13c887
-- title:
--   L¹/L² convergence and martingale-limit auxiliary results
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `martingale_of_tendsto_eLpNorm_one` states that a sequence of integrable martingales converging pointwise in time in $L^1$ to an adapted integrable process has a martingale limit. `tendsto_eLpNorm_one_of_eLpNorm_two` specializes this transfer from $L^2$ convergence under a probability measure. The bundle also contains the right-continuity estimate for iterated horizon integrals, the Pythagorean increment identity for square-integrable martingales, finite-energy and zero-time lemmas for simple Brownian integrals, and extraction of one adapted simple approximant within a prescribed strict $\operatorname{ENNReal}$ tolerance.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoL2CompletionIncrement
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   lemma martingale_of_tendsto_eLpNorm_one
--       {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
--       [MeasureTheory.IsFiniteMeasure μ] {ℱ : MeasureTheory.Filtration ℝ m0}
--       {M : ℕ → ℝ → Ω → ℝ} {F : ℝ → Ω → ℝ}
--       (hM : ∀ n, MeasureTheory.Martingale (M n) ℱ μ)
--       (hMint : ∀ n t, MeasureTheory.Integrable (M n t) μ)
--       (hadapt : MeasureTheory.StronglyAdapted ℱ F)
--       (hint : ∀ t, MeasureTheory.Integrable (F t) μ)
--       (htend : ∀ t, Filter.Tendsto
--         (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ) Filter.atTop (nhds 0)) :
--       MeasureTheory.Martingale F ℱ μ
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoL2CompletionIncrement`](https://prove2.me/theorems/32aee3b1-b8a1-4c27-9868-1b8897f31160).
--
--   Theorems in source order:
--
--   - [`eLpNorm_one_mul_le`](https://prove2.me/theorems/11203bf2-6375-4c0c-9036-2bedd1d686fd)
--   - [`tendsto_eLpNorm_one_sq_sub`](https://prove2.me/theorems/f09a6b4b-92fc-4d7f-afe6-745f7f468f5b)
--   - [`condExp_sq_increment_of_martingale`](https://prove2.me/theorems/9248f0a4-cf9c-4337-bd6c-ca5656254c6a)
--   - [`integral_factor_increment_sq`](https://prove2.me/theorems/a261136e-59cf-42dc-be13-44c2ab2acb19)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean) · `LevyStochCalc.Brownian.ItoL2CompletionConvergence` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean#L27-L521 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionConvergence`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionIncrement

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
omit [MeasurableSpace Ω] in
/-- **L¹-limit of martingales is a martingale.** If each `M n` is an
`ℱ`-martingale and `M n t → F t` in `L¹(μ)` for every `t` (with `F` adapted and
integrable), then `F` is an `ℱ`-martingale. The conditional expectation is an
`L¹`-contraction (`eLpNorm_one_condExp_le_eLpNorm`), so the martingale identity
`μ[M n t | ℱ s] =ᵐ M n s` passes to the limit. Reusable for the L²-Itô integral
(#5) and its compensated analogue (#6). -/
lemma martingale_of_tendsto_eLpNorm_one
    {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {ℱ : MeasureTheory.Filtration ℝ m0}
    {M : ℕ → ℝ → Ω → ℝ} {F : ℝ → Ω → ℝ}
    (hM : ∀ n, MeasureTheory.Martingale (M n) ℱ μ)
    (hMint : ∀ n t, MeasureTheory.Integrable (M n t) μ)
    (hadapt : MeasureTheory.StronglyAdapted ℱ F)
    (hint : ∀ t, MeasureTheory.Integrable (F t) μ)
    (htend : ∀ t, Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ) Filter.atTop (nhds 0)) :
    MeasureTheory.Martingale F ℱ μ := by
  refine ⟨hadapt, fun s t hst => ?_⟩
  have haesmC : MeasureTheory.AEStronglyMeasurable (μ[F t | ℱ s]) μ :=
    MeasureTheory.integrable_condExp.aestronglyMeasurable
  have haesm : MeasureTheory.AEStronglyMeasurable (μ[F t | ℱ s] - F s) μ :=
    haesmC.sub (hint s).1
  -- The target seminorm is bounded by `‖Mₙt − Ft‖₁ + ‖Mₙs − Fs‖₁` for every `n`.
  have hbound : ∀ n, MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ
      ≤ MeasureTheory.eLpNorm (M n t - F t) 1 μ
        + MeasureTheory.eLpNorm (M n s - F s) 1 μ := by
    intro n
    have hdecomp : (μ[F t | ℱ s] - F s)
        = (μ[F t | ℱ s] - μ[M n t | ℱ s]) + (μ[M n t | ℱ s] - F s) := by ring
    calc MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ
        = MeasureTheory.eLpNorm
            ((μ[F t | ℱ s] - μ[M n t | ℱ s]) + (μ[M n t | ℱ s] - F s)) 1 μ := by
          rw [hdecomp]
      _ ≤ MeasureTheory.eLpNorm (μ[F t | ℱ s] - μ[M n t | ℱ s]) 1 μ
          + MeasureTheory.eLpNorm (μ[M n t | ℱ s] - F s) 1 μ :=
          MeasureTheory.eLpNorm_add_le
            (haesmC.sub MeasureTheory.integrable_condExp.aestronglyMeasurable)
            (MeasureTheory.integrable_condExp.aestronglyMeasurable.sub (hint s).1) (by norm_num)
      _ ≤ MeasureTheory.eLpNorm (M n t - F t) 1 μ
          + MeasureTheory.eLpNorm (M n s - F s) 1 μ := by
          gcongr
          · have h_sub : (μ[F t | ℱ s] - μ[M n t | ℱ s]) =ᵐ[μ] μ[F t - M n t | ℱ s] :=
              (MeasureTheory.condExp_sub (hint t) (hMint n t) (ℱ s)).symm
            rw [MeasureTheory.eLpNorm_congr_ae h_sub]
            calc MeasureTheory.eLpNorm (μ[F t - M n t | ℱ s]) 1 μ
                ≤ MeasureTheory.eLpNorm (F t - M n t) 1 μ :=
                  MeasureTheory.eLpNorm_condExp_le_eLpNorm (F t - M n t) (le_refl 1)
              _ = MeasureTheory.eLpNorm (M n t - F t) 1 μ := by
                  rw [show F t - M n t = -(M n t - F t) from by ring,
                      MeasureTheory.eLpNorm_neg]
          · refine le_of_eq (MeasureTheory.eLpNorm_congr_ae ?_)
            exact ((hM n).condExp_ae_eq hst).sub (Filter.EventuallyEq.refl _ (F s))
  -- Send `n → ∞`: the bound tends to `0`, so the (constant) target seminorm is `0`.
  have hzero : MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ = 0 := by
    have htend2 : Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ
          + MeasureTheory.eLpNorm (M n s - F s) 1 μ) Filter.atTop (nhds 0) := by
      simpa using (htend t).add (htend s)
    refine le_antisymm ?_ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend2
      (Filter.Eventually.of_forall hbound)
  rw [MeasureTheory.eLpNorm_eq_zero_iff haesm (by norm_num)] at hzero
  filter_upwards [hzero] with ω hω
  simpa [Pi.sub_apply, sub_eq_zero] using hω
/-- **L²-convergence ⇒ L¹-convergence** (probability measure). The `L¹` seminorm
is dominated by the `L²` seminorm when `μ` is a probability measure, so an
`L²`-null sequence is `L¹`-null. Bridges the `L²`-Cauchy approximating sequence
(`cauchySeq_simpleIntegralLp_brownian`) to the `L¹` hypothesis of
`martingale_of_tendsto_eLpNorm_one`. -/
lemma tendsto_eLpNorm_one_of_eLpNorm_two
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {g : ℕ → Ω → ℝ} (hg : ∀ n, MeasureTheory.AEStronglyMeasurable (g n) μ)
    (h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (g n) 2 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (g n) 1 μ)
      Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => bot_le)
    (fun n => MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hg n))
/-- **Right-continuity of the horizon integral.** For measurable `φ : Ω → ℝ → ℝ≥0∞`
integrable (iterated) over `[0, T]`, the slab integral over `(s₀, r]` tends to `0`
as `r ↓ s₀` (for `0 ≤ s₀ < T`). Tonelli (`setLIntegral_prod`) reduces this to
`tendsto_setLIntegral_zero` for `P ⊗ volume` on the sets `univ ×ˢ (s₀, r]`, of
product measure `ofReal (r − s₀) → 0`. Underlies the right-`L²`-continuity of the
L² Itô integral's slices (`‖F_r − F_{s₀}‖₂² = ∫∫_{(s₀,r]}‖H‖²`). -/
lemma tendsto_setLIntegral_Ioc_prod_zero
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (φ : Ω → ℝ → ℝ≥0∞) (hφ : Measurable (Function.uncurry φ))
    {s₀ T : ℝ} (hs₀ : 0 ≤ s₀) (hs₀T : s₀ < T)
    (h_fin : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, φ ω u ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Ioc s₀ r, φ ω u ∂volume ∂P)
      (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
  have hset : MeasurableSet ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Icc
  set f : Ω × ℝ → ℝ≥0∞ :=
    ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T).indicator (Function.uncurry φ) with hf
  have h_tot : ∫⁻ z, f z ∂(P.prod volume) ≠ ⊤ := by
    rw [hf, MeasureTheory.lintegral_indicator hset,
        MeasureTheory.setLIntegral_prod _ (hφ.aemeasurable.restrict),
        MeasureTheory.Measure.restrict_univ]
    simpa using h_fin
  have h_meas_to_zero : Filter.Tendsto
      (fun r => (P.prod volume) ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r))
      (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
    have hval : (fun r => (P.prod volume) ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r))
        = fun r => ENNReal.ofReal (r - s₀) := by
      funext r
      rw [MeasureTheory.Measure.prod_prod, measure_univ, one_mul, Real.volume_Ioc]
    rw [hval]
    have h1 : Filter.Tendsto (fun r => r - s₀)
        (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
      have h0 : Filter.Tendsto (fun r => r - s₀) (nhds s₀) (nhds (s₀ - s₀)) :=
        (continuous_sub_right s₀).tendsto s₀
      rw [sub_self] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    simpa [Function.comp_def] using this
  have h_zero := MeasureTheory.tendsto_setLIntegral_zero (μ := P.prod volume) (f := f)
    (s := fun r => (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r) h_tot h_meas_to_zero
  refine h_zero.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hs₀T] with r hr
  have hsub : (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r ⊆ (Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T :=
    Set.prod_mono (le_refl _) (fun u hu => ⟨le_of_lt (lt_of_le_of_lt hs₀ hu.1),
      le_of_lt (lt_of_le_of_lt hu.2 hr.2)⟩)
  have hset' : MeasurableSet ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc
  have hstep1 : ∫⁻ z in (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r, f z ∂(P.prod volume)
      = ∫⁻ z in (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r, Function.uncurry φ z ∂(P.prod volume) := by
    refine MeasureTheory.setLIntegral_congr_fun hset' (fun z hz => ?_)
    rw [hf, Set.indicator_of_mem (hsub hz)]
  rw [hstep1, MeasureTheory.setLIntegral_prod _ (hφ.aemeasurable.restrict),
      MeasureTheory.Measure.restrict_univ]
  rfl
/-- **Orthogonal-increment identity for L² martingales.** For an `ℱ`-martingale
`M` on `ℝ` with square-integrable time-slices, the increment from `s` to `t ≥ s`
is `L²`-orthogonal to `M s`, giving the Pythagoras identity
`𝔼[(M t − M s)²] = 𝔼[(M t)²] − 𝔼[(M s)²]`. Cross term: `M s` is `ℱ s`-measurable,
so `𝔼[M s · M t] = 𝔼[M s · 𝔼[M t | ℱ s]] = 𝔼[(M s)²]` by the pull-out property and
the martingale identity. This underlies the increment isometry of the L² Itô
integral and the right-`L²`-continuity of its time-slices. -/
lemma integral_sq_increment_eq_of_martingale
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    ∫ ω, (M t ω - M s ω) ^ 2 ∂P
      = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by
  have hm : ℱ s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hcr : MeasureTheory.Integrable (fun ω => M s ω * M t ω) P :=
    hMs.integrable_mul hMt
  -- cross term: `∫ M s · M t = ∫ (M s)²` via pull-out + martingale identity.
  have h_cross : ∫ ω, M s ω * M t ω ∂P = ∫ ω, (M s ω) ^ 2 ∂P := by
    have h_pull : P[(fun ω => M s ω * M t ω) | ℱ s]
        =ᵐ[P] fun ω => M s ω * P[M t | ℱ s] ω := by
      have := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := ℱ s) (hmart.stronglyAdapted s) hcr (hmart.integrable t)
      exact this
    calc ∫ ω, M s ω * M t ω ∂P
        = ∫ ω, P[(fun ω => M s ω * M t ω) | ℱ s] ω ∂P :=
          (MeasureTheory.integral_condExp hm).symm
      _ = ∫ ω, M s ω * P[M t | ℱ s] ω ∂P := integral_congr_ae h_pull
      _ = ∫ ω, M s ω * M s ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hmart.condExp_ae_eq hst] with ω hω using by rw [hω]
      _ = ∫ ω, (M s ω) ^ 2 ∂P := by simp_rw [pow_two]
  have hMt2 : MeasureTheory.Integrable (fun ω => (M t ω) ^ 2) P := hMt.integrable_sq
  have hMs2 : MeasureTheory.Integrable (fun ω => (M s ω) ^ 2) P := hMs.integrable_sq
  calc ∫ ω, (M t ω - M s ω) ^ 2 ∂P
      = ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_)); ring
    _ = (∫ ω, (M t ω) ^ 2 ∂P) - 2 * (∫ ω, M s ω * M t ω ∂P) + ∫ ω, (M s ω) ^ 2 ∂P := by
        have e1 : ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P
            = (∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P) + ∫ ω, (M s ω) ^ 2 ∂P :=
          integral_add (hMt2.sub (hcr.const_mul 2)) hMs2
        have e2 : ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P
            = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, 2 * (M s ω * M t ω) ∂P :=
          integral_sub hMt2 (hcr.const_mul 2)
        have e3 : ∫ ω, 2 * (M s ω * M t ω) ∂P = 2 * ∫ ω, M s ω * M t ω ∂P :=
          integral_const_mul 2 _
        rw [e1, e2, e3]
    _ = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by rw [h_cross]; ring
/-- **A single adapted simple approximant within `ε` on `[0, T]`.** Extracted from
the convergent dense sequence `adaptedSimple_dense_L2_brownian`. -/
lemma exists_adaptedSimple_within
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    {T : ℝ} (hT : 0 < T)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ G : SimplePredictable Ω T,
      (∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (G.partition i.castSucc)) (G.ξ i)) ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε := by
  obtain ⟨Hn, h_adapt, h_tend⟩ :=
    adaptedSimple_dense_L2_brownian ℱ hT H h_meas h_progMeas h_sq_int
  have hev : ∀ᶠ m in Filter.atTop,
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε :=
    h_tend (Iio_mem_nhds hε)
  obtain ⟨m, hm⟩ := hev.exists
  exact ⟨Hn m, h_adapt m, hm⟩
/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊² ∂μ`. -/
lemma eLpNorm_two_rpow_eq_lintegral_sq {μ : MeasureTheory.Measure Ω} (g : Ω → ℝ) :
    MeasureTheory.eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (2 : NNReal))
    (f := g) (by norm_num)
  rw [show ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
      show ((2 : NNReal) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]
  refine lintegral_congr (fun ω => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊² ∂μ`, over an arbitrary base type. -/
lemma eLpNorm_sq_eq_lintegral_nnnorm_sq {β : Type*} [MeasurableSpace β]
    {μ : MeasureTheory.Measure β} (g : β → ℝ) :
    MeasureTheory.eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (2 : NNReal))
    (f := g) (by norm_num)
  rw [show ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
      show ((2 : NNReal) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]; refine lintegral_congr (fun x => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
/-- `eval` is bounded by the sum of the coefficient bounds. -/
lemma eval_abs_le_sum_bounds {T : ℝ} (H : SimplePredictable Ω T) (s : ℝ) (ω : Ω) :
    |H.eval s ω| ≤ ∑ i : Fin H.N, (H.ξ_bounded i).choose := by
  unfold SimplePredictable.eval
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  have hM : ∀ ω, |H.ξ i ω| ≤ (H.ξ_bounded i).choose := (H.ξ_bounded i).choose_spec
  have hM0 : 0 ≤ (H.ξ_bounded i).choose := le_trans (abs_nonneg _) (hM ω)
  split_ifs with h
  · exact hM ω
  · simpa using hM0
/-- For any `SimplePredictable` and any horizon `T`, the squared `L²(λ⊗P)` mass of
`eval` over `[0, T]` is finite (`eval` is uniformly bounded). -/
lemma eval_lintegral_sq_finite
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {T' : ℝ} (H : SimplePredictable Ω T') (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  set C : ℝ := ∑ i : Fin H.N, (H.ξ_bounded i).choose with hC
  have hbound : ∀ ω s, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (C ^ 2) := by
    intro ω s
    rw [show (‖H.eval s ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H.eval s ω‖
          from (ofReal_norm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖H.eval s ω‖ ≤ C := by
      rw [Real.norm_eq_abs]; exact eval_abs_le_sum_bounds H s ω
    nlinarith [h1, norm_nonneg (H.eval s ω)]
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono (fun ω =>
    le_trans (MeasureTheory.lintegral_mono (fun s => hbound ω s))
      (le_of_eq (MeasureTheory.setLIntegral_const _ _)))) ?_
  rw [MeasureTheory.lintegral_const]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top) (measure_lt_top _ _)
/-- `simpleIntegral W H t = 0` for `t ≤ 0` (all increments `W_t − W_t` vanish). -/
lemma simpleIntegral_eq_zero_of_nonpos
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    simpleIntegral W H t ω = 0 := by
  unfold simpleIntegral
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hp1 : 0 ≤ H.partition i.succ := by
    have := H.partition_strictMono.monotone (Fin.zero_le i.succ)
    rwa [H.partition_zero] at this
  have hp2 : 0 ≤ H.partition i.castSucc := by
    have := H.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [H.partition_zero] at this
  rw [min_eq_right (ht.trans hp1), min_eq_right (ht.trans hp2), sub_self, mul_zero]
/-- `∫⁻ ‖g‖₊² = ofReal (∫ g²)` for `g ∈ L²`. -/
lemma lintegral_nnnorm_sq_eq_ofReal_integral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : MeasureTheory.MemLp g 2 P) :
    ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (g ω) ^ 2 ∂P) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  refine lintegral_congr (fun ω => ?_)
  rw [show (‖g ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖g ω‖ from (ofReal_norm _).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
end Ito
end Brownian
end LevyStochCalc


