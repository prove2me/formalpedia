-- Prove2me | Definitions.Def_SourceProof_39fe24509dab75a4c4176089
-- name    : SourceProof_39fe24509dab75a4c4176089
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:58:09.414738+00:00
-- url     : https://prove2.me/theorems/f99b2ef3-071f-419d-b281-af86b89cd082
-- title:
--   LevyStochCalc source proof: LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_two_mul_mid
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The geometric Cauchy estimate for the Picard iterates

The exponentially weighted norm `wNorm` at a nonnegative weight dominates the energies of the
value process, of the diffusion coordinates and of the jump integrand, and is subadditive along
an intermediate triple up to a factor of two. Combined with the one-step contraction at the Young
weight `β = max 2 (24 L²)`, this gives a geometric bound with ratio `1/4` on the weighted norm of
consecutive Picard iterates, and hence a Cauchy estimate for the iterates in the weighted norm
and in the unweighted energies on the horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Subadditivity and lower bounds for the weighted norm -/

section WNorm

variable {β T : ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_39fe24509dab75a4c4176089 {Y₁ Y₂ Y₃ : ℝ → Ω → ℝ} {Z₁ Z₂ Z₃ : ℝ → Ω → (Fin d → ℝ)}
    {U₁ U₂ U₃ : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y₁ s ω - Y₂ s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U₁ p.2.1 p.1 p.2.2 - U₂ p.2.1 p.1 p.2.2) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₃ t ω) (fun t ω => Z₁ t ω - Z₃ t ω)
        (fun t ω e => U₁ t ω e - U₃ t ω e)
      ≤ 2 * wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
            (fun t ω e => U₁ t ω e - U₂ t ω e)
        + 2 * wNorm P ν β T (fun t ω => Y₂ t ω - Y₃ t ω) (fun t ω => Z₂ t ω - Z₃ t ω)
            (fun t ω e => U₂ t ω e - U₃ t ω e) := by
  have hwm : Measurable fun s : ℝ => ENNReal.ofReal (Real.exp (β * s)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hdm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ENNReal.ofReal (Real.exp (β * s))
        * LevyStochCalc.BSDEJ.Solves.density ν (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
            (fun t ω e => U₁ t ω e - U₂ t ω e) ω s) :=
    (hwm.comp measurable_snd).mul (LevyStochCalc.BSDEJ.Solves.measurable_uncurry_density hYm hZm hUm)
  simp only [wNorm_eq_lintegral_density]
  refine LevyStochCalc.BSDEJ.Solves.lintegral_Icc_le_two_mul_add hdm fun ω s => ?_
  have hU : Measurable fun e => U₁ s ω e - U₂ s ω e :=
    hUm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  refine le_trans (mul_le_mul' le_rfl (LevyStochCalc.BSDEJ.Solves.density_sub_le_two_mul_mid ν Y₂ Z₂ ω s hU))
    (le_of_eq ?_)
  ring
end WNorm

/-! ### The geometric Cauchy estimate along the iterates -/

section Cauchy

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}
  (hT : 0 < T)
  (hf : ∀ u : E → ℝ, Measurable fun q : ℝ × ℝ × (Fin d → ℝ) => f q.1 q.2.1 q.2.2 u)
  (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
    (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
  (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
  (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)

end Cauchy

end LevyStochCalc.BSDEJ.Solves


