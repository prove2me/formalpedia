-- Prove2me | Definitions.Def_SourceProof_c881239cef4c0ad2e7f9696d
-- name    : SourceProof_c881239cef4c0ad2e7f9696d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:36:20.399171+00:00
-- url     : https://prove2.me/theorems/59701ecd-7518-481f-89b7-04dfb7ecb1c8
-- title:
--   LevyStochCalc source module: SourceProof_c881239cef4c0ad2e7f9696d
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Stability.integral_sub_mul_self_le_of_lipschitz` comes from the `LevyStochCalc.Ito.StabilityEstimate` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F001
import Definitions.Def_SourceProof_0122a571e95691a0e466a41c

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted stability estimates for Itô–Lévy processes

The difference of two Itô–Lévy processes over the same Lévy driver and filtration is again an
Itô–Lévy process, with the differenced data (`isItoLevyProcess_sub`). Feeding it to the
exponentially weighted second-moment identity turns a bound on the rate

`2 𝔼[ΔX_s Δb_s] + ∑_j 𝔼[|Δσ_j(s)|²] + 𝔼 ∫_E |Δγ(s, e)|² ν(de) ≤ c 𝔼[|ΔX_s|²]`

into the stability estimate `𝔼[|ΔX_T|²] ≤ e^{cT} 𝔼[|ΔX₀|²]`, with no Grönwall lemma: the
exponential weight does the work. A drift, diffusion and jump coefficient Lipschitz in the state
gives such a rate bound with `c = 2L + 2L²`, and equal initial values then force the two
processes to agree at the horizon.

## Main statements

* `integral_mul_self_le_of_rate_le` — the weighted identity as a bound: a rate bounded by
  `c 𝔼[X_s²]` at almost every time of the window gives `𝔼[X_T²] ≤ e^{cT} 𝔼[X₀²]`.
* `isItoLevyProcess_sub` — the difference of two Itô–Lévy processes over the same driver is an
  Itô–Lévy process with the differenced initial value, drift, diffusion and jump coefficient.
* `integral_sub_mul_self_le_of_rate_le` — the stability estimate under a rate bound on the
  difference.
* `integral_sub_mul_self_le_of_lipschitz` — the stability estimate under pointwise Lipschitz
  bounds on the differences of the coefficients, with `c = 2L + 2L²`.
* `ae_eq_of_lipschitz_of_ae_eq_initial` — two Itô–Lévy processes with Lipschitz-close
  coefficients and almost surely equal initial values agree almost surely at every horizon.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.Stability

open LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section RateBound

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end RateBound

section Difference

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

variable {d : ℕ} {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X Y : ℝ → Ω → ℝ} {X₀ Y₀ : Ω → ℝ} {b b' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → Fin d → ℝ}
  {γ γ' : Ω → ℝ → E → ℝ}

end Difference

section Stability

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X Y : ℝ → Ω → ℝ} {X₀ Y₀ : Ω → ℝ} {b b' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → Fin d → ℝ}
  {γ γ' : Ω → ℝ → E → ℝ}


theorem _root_.Prove2MeSourceProof.h_c881239cef4c0ad2e7f9696d
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN Y Y₀ b' σ' γ')
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hY₀ : StronglyMeasurable[ℱ 0] Y₀) (hY₀2 : MemLp Y₀ 2 P)
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hb'p : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b' s ω)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {L : ℝ}
    (hbLip : ∀ s ω, (X s ω - Y s ω) * (b s ω - b' s ω)
      ≤ L * ((X s ω - Y s ω) * (X s ω - Y s ω)))
    (hσLip : ∀ s ω, (∑ j : Fin d, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal (L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))))
    (hγLip : ∀ s ω, (∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      ≤ ENNReal.ofReal (L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))))
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, (X T ω - Y T ω) * (X T ω - Y T ω) ∂P
      ≤ Real.exp ((2 * L + 2 * L ^ 2) * T)
        * ∫ ω, (X₀ ω - Y₀ ω) * (X₀ ω - Y₀ ω) ∂P := by
  classical
  have hΔ := _root_.Prove2MeSourceProof.h_5f001695308f2960cc01c3ca h h' hbm hb'm hbq hb'q
  have hΔbm : Measurable (Function.uncurry fun ω s => b s ω - b' s ω) := hbm.sub hb'm
  have hΔbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω - b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293
      (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hbm hb'm hbq hb'q
  -- the `L²` facts of the difference, at every time of the window
  have hΔ2 : ∀ s : ℝ, 0 ≤ s → MemLp (fun ω => X s ω - Y s ω) 2 P := fun s hs =>
    _root_.Prove2MeSourceProof.h_0122a571e95691a0e466a41c hΔ (hX₀2.sub hY₀2) hΔbm hΔbq hs
  have hsw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hΔbs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      MemLp (fun ω => b s ω - b' s ω) 2 P :=
    LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b s ω - b' s ω) hΔbm (hΔbq T hT)
  refine LevyStochCalc.Ito.Stability.integral_sub_mul_self_le_of_rate_le h h' 𝒲 hX₀ hX₀2 hbm hbp hbq hY₀ hY₀2 hb'm hb'p
    hb'q hT ?_
  filter_upwards [hsw, hΔbs] with s hs hΔbs2
  set Q : ℝ := ∫ ω, (X s ω - Y s ω) * (X s ω - Y s ω) ∂P with hQdef
  have hQi : Integrable (fun ω => (X s ω - Y s ω) * (X s ω - Y s ω)) P :=
    (hΔ2 s hs.1).integrable_mul (hΔ2 s hs.1)
  have hQ0 : 0 ≤ Q := integral_nonneg fun ω => mul_self_nonneg _
  -- the drift pairing
  have hdrift : 2 * ∫ ω, (X s ω - Y s ω) * (b s ω - b' s ω) ∂P ≤ 2 * (L * Q) := by
    have h1 : ∫ ω, (X s ω - Y s ω) * (b s ω - b' s ω) ∂P
        ≤ ∫ ω, L * ((X s ω - Y s ω) * (X s ω - Y s ω)) ∂P :=
      integral_mono ((hΔ2 s hs.1).integrable_mul hΔbs2) (hQi.const_mul L) fun ω => hbLip s ω
    rw [integral_const_mul] at h1
    linarith
  -- the diffusion energy
  have hLQ0 : ∀ ω, 0 ≤ L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω)) := fun ω =>
    mul_nonneg (sq_nonneg L) (mul_self_nonneg _)
  have hLQi : Integrable (fun ω => L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))) P :=
    hQi.const_mul _
  have hσmeas : ∀ j : Fin d, Measurable fun ω => (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 := by
    intro j
    have hu : Measurable (Function.uncurry fun ω s => σ s ω j - σ' s ω j) :=
      (h.σ_meas j).sub (h'.σ_meas j)
    have hslice : Measurable fun ω => σ s ω j - σ' s ω j :=
      hu.comp measurable_prodMk_right
    exact hslice.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hsumeq : ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∑ j : Fin d, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    (lintegral_finsetSum _ fun j _ => hσmeas j).symm
  obtain ⟨hσle, hσfin⟩ := LevyStochCalc.Ito.Stability.toReal_lintegral_le_of_le (P := P)
    (f := fun ω => ∑ j : Fin d, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2) hLQi hLQ0 fun ω => hσLip s ω
  have hσeach : ∀ j : Fin d, (∫⁻ ω, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top hσfin (lintegral_mono fun ω =>
      Finset.single_le_sum (f := fun k : Fin d => (‖σ s ω k - σ' s ω k‖₊ : ℝ≥0∞) ^ 2)
        (fun k _ => by simp) (Finset.mem_univ j))
  have hdiff : (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      ≤ L ^ 2 * Q := by
    rw [← ENNReal.toReal_sum fun j _ => hσeach j, hsumeq]
    rw [hQdef, ← integral_const_mul]
    exact hσle
  -- the jump energy
  obtain ⟨hγle, -⟩ := LevyStochCalc.Ito.Stability.toReal_lintegral_le_of_le (P := P)
    (f := fun ω => ∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) hLQi hLQ0 fun ω => hγLip s ω
  have hjump : (∫⁻ ω, ∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal ≤ L ^ 2 * Q := by
    rw [hQdef, ← integral_const_mul]
    exact hγle
  linarith
end Stability

end LevyStochCalc.Ito.Stability


