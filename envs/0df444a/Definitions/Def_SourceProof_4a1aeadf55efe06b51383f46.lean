-- Prove2me | Definitions.Def_SourceProof_4a1aeadf55efe06b51383f46
-- name    : SourceProof_4a1aeadf55efe06b51383f46
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:34:33.720697+00:00
-- url     : https://prove2.me/theorems/0f78ec2c-259c-4ef3-9400-833d646fab33
-- title:
--   LevyStochCalc source module: SourceProof_4a1aeadf55efe06b51383f46
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_of_picardOutput_of_two_le` comes from the `LevyStochCalc.BSDEJ.PicardContractionContraction` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionBounds_F000
import Definitions.Def_SourceProof_0d4bbf4d74ab573facc6d9df
import Definitions.Def_SourceProof_21431cc356d9363f35d4c54e
import Definitions.Def_SourceProof_388a40baa407d0b0ae15b23c
import Definitions.Def_SourceProof_74549f342024460457cb4481
import Definitions.Def_SourceProof_794ef092072b35a646ccf766
import Definitions.Def_SourceProof_8bb8c09ab790bf7a224b8ffd
import Definitions.Def_SourceProof_8dd2bd144165bcf825664aac

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard contraction

One Picard step contracts the exponentially weighted `L²` norm of a triple: the weighted norm of
the difference of two Picard outputs is at most `6 L² / β` times the weighted norm of the
difference of their input triples at every Young weight `β ≥ 2`, and hence at most `1 / 4` times
it at the Young weight `β = max 2 (24 L²)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Contraction

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}


theorem _root_.Prove2MeSourceProof.h_4a1aeadf55efe06b51383f46
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {T : ℝ} (hT : 0 < T) {ξ : Ω → ℝ}
    {Y'₁ Y₁ Y'₂ Y₂ : ℝ → Ω → ℝ} {Z'₁ Z₁ Z'₂ Z₂ : ℝ → Ω → (Fin d → ℝ)}
    {U'₁ U₁ U'₂ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : PicardOutput D f ξ T Y'₁ Z'₁ U'₁ Y₁ Z₁ U₁)
    (h₂ : PicardOutput D f ξ T Y'₂ Z'₂ U'₂ Y₂ Z₂ U₂)
    (hY'm : Measurable (Function.uncurry fun ω s => Y'₁ s ω - Y'₂ s ω))
    (hZ'm : ∀ j, Measurable (Function.uncurry fun ω s => Z'₁ s ω j - Z'₂ s ω j))
    (hU'm : Measurable fun p : Ω × ℝ × E => U'₁ p.2.1 p.1 p.2.2 - U'₂ p.2.1 p.1 p.2.2)
    {b₁ b₂ : Ω → ℝ → ℝ} (hb₁m : Measurable (Function.uncurry b₁))
    (hb₁p : Probability.ProgressivelyMeasurable (augJoint D) b₁)
    (hb₁z : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b₁ ω s = 0)
    (hb₁q : Brownian.Ito.energy P T b₁ ≠ ⊤)
    (hb₁ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₁ p.1 p.2 = f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1))
    (hb₂m : Measurable (Function.uncurry b₂))
    (hb₂p : Probability.ProgressivelyMeasurable (augJoint D) b₂)
    (hb₂z : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b₂ ω s = 0)
    (hb₂q : Brownian.Ito.energy P T b₂ ≠ ⊤)
    (hb₂ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₂ p.1 p.2 = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1))
    {β : ℝ} (hβ : 2 ≤ β)
    (hin : wNorm P ν β T (fun t ω => Y'₁ t ω - Y'₂ t ω) (fun t ω => Z'₁ t ω - Z'₂ t ω)
      (fun t ω e => U'₁ t ω e - U'₂ t ω e) ≠ ⊤) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
        (fun t ω e => U₁ t ω e - U₂ t ω e)
      ≤ ENNReal.ofReal (6 * L ^ 2 / β) * wNorm P ν β T (fun t ω => Y'₁ t ω - Y'₂ t ω)
        (fun t ω => Z'₁ t ω - Z'₂ t ω) (fun t ω e => U'₁ t ω e - U'₂ t ω e) := by
  classical
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le (by norm_num) hβ
  -- measurability of the output triples
  have hCm₁ : Measurable (Function.uncurry fun ω s => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω) :=
    (LevyStochCalc.BSDEJ.Solves.measurable_uncurry_clampT h₁.Y_meas).comp (measurable_snd.prodMk measurable_fst)
  have hCm₂ : Measurable (Function.uncurry fun ω s => LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) :=
    (LevyStochCalc.BSDEJ.Solves.measurable_uncurry_clampT h₂.Y_meas).comp (measurable_snd.prodMk measurable_fst)
  have hXm : Measurable (Function.uncurry fun ω s => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) :=
    hCm₁.sub hCm₂
  have hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j) :=
    fun j => (h₁.Z_meas j).sub (h₂.Z_meas j)
  have hUm : Measurable fun p : Ω × ℝ × E => U₁ p.2.1 p.1 p.2.2 - U₂ p.2.1 p.1 p.2.2 :=
    h₁.U_meas.sub h₂.U_meas
  -- energies of the output triple
  have hEY₁ : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω) ≠ ⊤ := by
    rw [LevyStochCalc.BSDEJ.Solves.energy_clampT]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₁.Y_sup.ne) _root_.Prove2MeSourceProof.h_8bb8c09ab790bf7a224b8ffd
  have hEY₂ : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) ≠ ⊤ := by
    rw [LevyStochCalc.BSDEJ.Solves.energy_clampT]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₂.Y_sup.ne) _root_.Prove2MeSourceProof.h_8bb8c09ab790bf7a224b8ffd
  have hEX : LevyStochCalc.Brownian.Ito.energy P T
      (fun ω s => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) ≠ ⊤ :=
    _root_.Prove2MeSourceProof.h_21431cc356d9363f35d4c54e hCm₁ hCm₂ hEY₁ hEY₂
  have hEZ : ∀ j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z₁ s ω j - Z₂ s ω j) ≠ ⊤ :=
    fun j => _root_.Prove2MeSourceProof.h_21431cc356d9363f35d4c54e (h₁.Z_meas j) (h₂.Z_meas j) (h₁.Z_sq j) (h₂.Z_sq j)
  have hEU : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => U₁ s ω e - U₂ s ω e) ≠ ⊤ :=
    (_root_.Prove2MeSourceProof.h_388a40baa407d0b0ae15b23c (φ := fun ω s e => U₁ s ω e)
      (ψ := fun ω s e => U₂ s ω e) h₁.U_meas h₂.U_meas
      (lt_top_iff_ne_top.mpr h₁.U_sq) (lt_top_iff_ne_top.mpr h₂.U_sq)).ne
  have hEb : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => b₁ ω s - b₂ ω s) ≠ ⊤ :=
    _root_.Prove2MeSourceProof.h_21431cc356d9363f35d4c54e hb₁m hb₂m hb₁q hb₂q
  -- the differenced Itô–Lévy process
  have hI₁ := (_root_.Prove2MeSourceProof.h_0d4bbf4d74ab573facc6d9df h₁) hT hb₁m hb₁z hb₁q hb₁
  have hI₂ := (_root_.Prove2MeSourceProof.h_0d4bbf4d74ab573facc6d9df h₂) hT hb₂m hb₂z hb₂q hb₂
  have hd₁q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖-b₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' _ => LevyStochCalc.BSDEJ.Solves.neg_drift_sq_int_global hb₁z hb₁q T'
  have hd₂q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖-b₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' _ => LevyStochCalc.BSDEJ.Solves.neg_drift_sq_int_global hb₂z hb₂q T'
  have hXproc := _root_.Prove2MeSourceProof.h_5f001695308f2960cc01c3ca hI₁ hI₂ hb₁m.neg hb₂m.neg hd₁q hd₂q
  -- the data of the backward weighted energy inequality
  have hX₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0]
      (fun ω => Y₁ 0 ω - Y₂ 0 ω) :=
    (D.stronglyMeasurable_augFiltration_zero (h₁.Y_adapted 0).stronglyMeasurable).sub
      (D.stronglyMeasurable_augFiltration_zero (h₂.Y_adapted 0).stronglyMeasurable)
  have hmem : ∀ Y : ℝ → Ω → ℝ, Measurable (Function.uncurry Y) →
      (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) → MemLp (Y 0) 2 P := by
    intro Y hYm hsup
    refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
      (hYm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hsup
    exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) 0
      ⟨le_rfl, hT.le⟩
  have hX₀2 : MemLp (fun ω => Y₁ 0 ω - Y₂ 0 ω) 2 P :=
    (hmem Y₁ h₁.Y_meas h₁.Y_sup).sub (hmem Y₂ h₂.Y_meas h₂.Y_sup)
  have hbm' : Measurable (Function.uncurry fun ω s => -b₁ ω s - -b₂ ω s) :=
    hb₁m.neg.sub hb₂m.neg
  have hbp' : LevyStochCalc.Probability.ProgressivelyMeasurable (LevyStochCalc.Brownian.augFiltration D.filtration P)
      fun ω s => -b₁ ω s - -b₂ ω s :=
    (continuous_neg.comp_progressivelyMeasurable neg_zero hb₁p).sub
      (continuous_neg.comp_progressivelyMeasurable neg_zero hb₂p)
  have hbq' : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖-b₁ ω s - -b₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293 (K := fun ω s => -b₁ ω s - -b₂ ω s)
      (H₁ := fun ω s => -b₁ ω s) (H₂ := fun ω s => -b₂ ω s)
      (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hb₁m.neg hb₂m.neg hd₁q hd₂q
  have hXT : (fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω) T =ᵐ[P] 0 := by
    filter_upwards [h₁.Y_terminal, h₂.Y_terminal] with ω k1 k2
    simp only [clampT_apply, min_self, Pi.zero_apply]
    rw [k1, k2, sub_self]
  have hL15 := _root_.Prove2MeSourceProof.h_bef53116327c6e62a058219e hXproc hX₀ hX₀2 hbm' hbp'
    hbq' β hT hXT
  -- the real integrands
  have hWout : LevyStochCalc.BSDEJ.Solves.wNorm P ν β T (fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
      (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ≠ ⊤ :=
    _root_.Prove2MeSourceProof.h_74549f342024460457cb4481 (ν := ν) (Y := fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
      (Z := fun t ω => Z₁ t ω - Z₂ t ω) (U := fun t ω e => U₁ t ω e - U₂ t ω e)
      hβ0.le hXm hZm hEX hEZ hEU
  have hAint : IntegrableOn (fun s => Real.exp (β * s) * ∫ ω,
      (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) ∂P)
      (Set.Icc (0 : ℝ) T) :=
    LevyStochCalc.Ito.SecondMoment.integrableOn_exp_mul β
      (LevyStochCalc.Ito.SecondMoment.integrableOn_integral_mul_self hXproc D.crossWitness.aug hX₀ hX₀2
        hbm' hbp' hbq' hT)
  have hGoutint := LevyStochCalc.BSDEJ.Solves.integrableOn_exp_mul_toReal_density (ν := ν)
      (Y := fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
      (Z := fun t ω => Z₁ t ω - Z₂ t ω) (U := fun t ω e => U₁ t ω e - U₂ t ω e)
      hβ0.le hXm hZm hUm hWout
  have hGinint := LevyStochCalc.BSDEJ.Solves.integrableOn_exp_mul_toReal_density (ν := ν) (Y := fun t ω => Y'₁ t ω - Y'₂ t ω)
      (Z := fun t ω => Z'₁ t ω - Z'₂ t ω) (U := fun t ω e => U'₁ t ω e - U'₂ t ω e)
      hβ0.le hY'm hZ'm hU'm hin
  have hVint : IntegrableOn (fun s => Real.exp (β * s) * (2 * ∫ ω,
      (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P)) (Set.Icc (0 : ℝ) T) := by
    refine LevyStochCalc.Ito.SecondMoment.integrableOn_exp_mul β ?_
    refine Integrable.congr ((_root_.Prove2MeSourceProof.h_d8b446e22164b7620e52d72e hXproc hX₀2
      hbm' hbp' hbq' hT).const_mul (-2)) ?_
    filter_upwards with s
    have hsw : ∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P
        = -∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * (-b₁ ω s - -b₂ ω s) ∂P := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    rw [hsw]; ring
  -- the pointwise Young bound
  have hpt := _root_.Prove2MeSourceProof.h_8dd2bd144165bcf825664aac (ν := ν) (T := T) hL hlip hβ0
    (X := fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
    (ΔY := fun t ω => Y'₁ t ω - Y'₂ t ω) (ΔZ := fun t ω => Z'₁ t ω - Z'₂ t ω)
    (ΔU := fun t ω e => U'₁ t ω e - U'₂ t ω e)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hXm
    (lt_top_iff_ne_top.mpr hEX) hb₁m hb₂m (lt_top_iff_ne_top.mpr hEb) hb₁ hb₂
    hY'm hZ'm hU'm hin
  -- the output density splits at almost every time
  have hXmem := LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval
    (f := fun ω s => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) hXm (lt_top_iff_ne_top.mpr hEX)
  have hZfin : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ j : Fin d, (∫⁻ ω, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤ :=
    ae_all_iff.mpr fun j => LevyStochCalc.BSDEJ.Solves.ae_lintegral_ne_top (LevyStochCalc.BSDEJ.Solves.measurable_uncurry_sq_value (hZm j)) (hEZ j)
  have hUfin : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (∫⁻ ω, ∫⁻ e, (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P) ≠ ⊤ :=
    LevyStochCalc.BSDEJ.Solves.ae_lintegral_ne_top (LevyStochCalc.BSDEJ.Solves.measurable_uncurry_sq_jump hUm) hEU
  have hGout : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (∫⁻ ω, LevyStochCalc.BSDEJ.Solves.density ν (fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
          (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ω s ∂P).toReal
        = (∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω)
              * (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) ∂P)
            + (∑ j, (∫⁻ ω, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal := by
    filter_upwards [hXmem, hZfin, hUfin] with s hXs hZs hUs
    have hfinA := (LevyStochCalc.Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two hXs).ne
    have hfinS : (∑ j, ∫⁻ ω, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun j _ => hZs j
    rw [LevyStochCalc.BSDEJ.Solves.lintegral_density_slice_eq (ν := ν) (Y := fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
      (Z := fun t ω => Z₁ t ω - Z₂ t ω) (U := fun t ω e => U₁ t ω e - U₂ t ω e) hXm hZm s]
    simp only [Pi.sub_apply]
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfinA, hfinS⟩) hUs,
      ENNReal.toReal_add hfinA hfinS, ENNReal.toReal_sum fun j _ => hZs j,
      ← LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_toReal hXs]
  -- the backward inequality in the shape of the real core
  have hLconv : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
        * ((∫⁻ ω, LevyStochCalc.BSDEJ.Solves.density ν (fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
              (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ω s ∂P).toReal
          + (β - 1) * ∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω)
              * (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) ∂P)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (2 * ∫ ω,
          (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P) := by
    have e1 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Real.exp (β * s)
          * ((∫⁻ ω, LevyStochCalc.BSDEJ.Solves.density ν (fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
                (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ω s ∂P).toReal
            + (β - 1) * ∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω)
                * (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) ∂P)
        = Real.exp (β * s) * (β * ∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω)
              * (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) ∂P
            + (∑ j, (∫⁻ ω, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
      filter_upwards [hGout] with s hs
      rw [hs]; ring
    have e2 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Real.exp (β * s) * (2 * ∫ ω,
          (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * -(-b₁ ω s - -b₂ ω s) ∂P)
        = Real.exp (β * s) * (2 * ∫ ω,
          (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P) := by
      filter_upwards with s
      have : ∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * -(-b₁ ω s - -b₂ ω s) ∂P
          = ∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      rw [this]
    rw [integral_congr_ae e1, ← integral_congr_ae e2]
    exact hL15
  have hcore := _root_.Prove2MeSourceProof.h_794ef092072b35a646ccf766 (β := β) (c := 6 * L ^ 2 / β) (T := T)
    (A := fun s => ∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω)
      * (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) ∂P)
    (Gout := fun s => (∫⁻ ω, LevyStochCalc.BSDEJ.Solves.density ν (fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
      (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ω s ∂P).toReal)
    (Gin := fun s => (∫⁻ ω, LevyStochCalc.BSDEJ.Solves.density ν (fun t ω => Y'₁ t ω - Y'₂ t ω)
      (fun t ω => Z'₁ t ω - Z'₂ t ω) (fun t ω e => U'₁ t ω e - U'₂ t ω e) ω s ∂P).toReal)
    (V := fun s => 2 * ∫ ω, (LevyStochCalc.BSDEJ.Solves.clampT T Y₁ s ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P)
    hβ (fun s => integral_nonneg fun ω => mul_self_nonneg _) hAint hGoutint hGinint hVint
    hLconv hpt
  rw [← LevyStochCalc.BSDEJ.Solves.wNorm_clampT_sub_eq (Y₁ := Y₁) (Y₂ := Y₂),
    LevyStochCalc.BSDEJ.Solves.wNorm_eq_ofReal_setIntegral (ν := ν) (Y := fun t ω => LevyStochCalc.BSDEJ.Solves.clampT T Y₁ t ω - LevyStochCalc.BSDEJ.Solves.clampT T Y₂ t ω)
      (Z := fun t ω => Z₁ t ω - Z₂ t ω) (U := fun t ω e => U₁ t ω e - U₂ t ω e)
      hβ0.le hXm hZm hUm hWout,
    LevyStochCalc.BSDEJ.Solves.wNorm_eq_ofReal_setIntegral (ν := ν) (Y := fun t ω => Y'₁ t ω - Y'₂ t ω)
      (Z := fun t ω => Z'₁ t ω - Z'₂ t ω) (U := fun t ω e => U'₁ t ω e - U'₂ t ω e)
      hβ0.le hY'm hZ'm hU'm hin,
    ← ENNReal.ofReal_mul (div_nonneg (by positivity) hβ0.le)]
  exact ENNReal.ofReal_le_ofReal hcore
end Contraction

end LevyStochCalc.BSDEJ.Solves


