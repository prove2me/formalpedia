-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionContraction_F000
-- name    : LevyStochCalc_BSDEJ_PicardContractionContraction_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:39:05.729179+00:00
-- url     : https://prove2.me/theorems/e4535da6-230a-435c-939f-5f7ab4b26f0d
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardContractionContraction
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardContractionContraction. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionBounds_F000
import Definitions.Def_SourceProof_4a1aeadf55efe06b51383f46

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

/-- **One Picard step contracts the weighted norm by `1/4`** at the Young weight
`β = max 2 (24 L²)`. -/
theorem wNorm_sub_le_of_picardOutput
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
    (hin : wNorm P ν (max 2 (24 * L ^ 2)) T (fun t ω => Y'₁ t ω - Y'₂ t ω)
      (fun t ω => Z'₁ t ω - Z'₂ t ω) (fun t ω e => U'₁ t ω e - U'₂ t ω e) ≠ ⊤) :
    wNorm P ν (max 2 (24 * L ^ 2)) T (fun t ω => Y₁ t ω - Y₂ t ω)
        (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e)
      ≤ 4⁻¹ * wNorm P ν (max 2 (24 * L ^ 2)) T (fun t ω => Y'₁ t ω - Y'₂ t ω)
        (fun t ω => Z'₁ t ω - Z'₂ t ω) (fun t ω e => U'₁ t ω e - U'₂ t ω e) := by
  obtain ⟨hfac, hβ⟩ := Contraction.contraction_factor_le L
  refine (_root_.Prove2MeSourceProof.h_4a1aeadf55efe06b51383f46 hL hlip hT h₁ h₂ hY'm hZ'm hU'm hb₁m hb₁p
    hb₁z hb₁q hb₁ hb₂m hb₂p hb₂z hb₂q hb₂ hβ hin).trans (mul_le_mul' ?_ le_rfl)
  have h4 : ENNReal.ofReal (1 / 4 : ℝ) = (4 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat, one_div]
  rw [← h4]
  exact ENNReal.ofReal_le_ofReal hfac
end Contraction

end LevyStochCalc.BSDEJ.Solves


