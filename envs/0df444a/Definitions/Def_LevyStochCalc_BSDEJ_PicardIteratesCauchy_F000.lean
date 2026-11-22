-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F000
-- name    : LevyStochCalc_BSDEJ_PicardIteratesCauchy_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:53:10.142451+00:00
-- url     : https://prove2.me/theorems/9c7a876c-9d62-4574-9003-b57bc6605309
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardIteratesCauchy
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardIteratesCauchy. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesStep_F000

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

/-- The extended norm of a difference of reals is symmetric. -/
theorem coe_nnnorm_sub_comm (x y : ℝ) : (‖x - y‖₊ : ℝ≥0∞) = (‖y - x‖₊ : ℝ≥0∞) := by
  have h : ‖x - y‖₊ = ‖y - x‖₊ := by rw [← nnnorm_neg (x - y), neg_sub]
  rw [h]
/-- The squared extended norm of a difference is dominated by twice the sum of the squares of
the two differences through an intermediate point. -/
theorem sq_nnnorm_sub_le_two_mul_mid (a b c : ℝ) :
    (‖a - c‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a - b‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b - c‖₊ : ℝ≥0∞) ^ 2 := by
  have h := Brownian.Ito.sq_nnnorm_sub_le_two_mul (a - b) (c - b)
  rw [show a - b - (c - b) = a - c by ring, coe_nnnorm_sub_comm c b] at h
  refine h.trans (le_of_eq ?_)
  ring
omit [MeasurableSpace Ω] in
/-- The pointwise energy density of a difference is dominated by twice the sum of the densities
of the two differences through an intermediate triple. -/
theorem density_sub_le_two_mul_mid (ν : Measure E) {Y₁ Y₃ : ℝ → Ω → ℝ}
    (Y₂ : ℝ → Ω → ℝ) {Z₁ Z₃ : ℝ → Ω → (Fin d → ℝ)} (Z₂ : ℝ → Ω → (Fin d → ℝ))
    {U₁ U₂ U₃ : ℝ → Ω → E → ℝ} (ω : Ω) (s : ℝ)
    (hU : Measurable fun e => U₁ s ω e - U₂ s ω e) :
    density ν (fun t ω => Y₁ t ω - Y₃ t ω) (fun t ω => Z₁ t ω - Z₃ t ω)
        (fun t ω e => U₁ t ω e - U₃ t ω e) ω s
      ≤ 2 * density ν (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
            (fun t ω e => U₁ t ω e - U₂ t ω e) ω s
        + 2 * density ν (fun t ω => Y₂ t ω - Y₃ t ω) (fun t ω => Z₂ t ω - Z₃ t ω)
            (fun t ω e => U₂ t ω e - U₃ t ω e) ω s := by
  classical
  simp only [density, Pi.sub_apply]
  have hY := sq_nnnorm_sub_le_two_mul_mid (Y₁ s ω) (Y₂ s ω) (Y₃ s ω)
  have hZ : ∑ j, (‖Z₁ s ω j - Z₃ s ω j‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (∑ j, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2)
        + 2 * ∑ j, (‖Z₂ s ω j - Z₃ s ω j‖₊ : ℝ≥0∞) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => sq_nnnorm_sub_le_two_mul_mid _ _ _
  have hUi : (∫⁻ e, (‖U₁ s ω e - U₃ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      ≤ 2 * (∫⁻ e, (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        + 2 * ∫⁻ e, (‖U₂ s ω e - U₃ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    have hm : Measurable fun e => 2 * (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 :=
      measurable_const.mul (hU.nnnorm.coe_nnreal_ennreal.pow_const 2)
    refine le_trans (lintegral_mono fun e => sq_nnnorm_sub_le_two_mul_mid _ (U₂ s ω e) _)
      (le_of_eq ?_)
    rw [lintegral_add_left hm, lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
  refine le_trans (add_le_add (add_le_add hY hZ) hUi) (le_of_eq ?_)
  ring
omit [IsProbabilityMeasure P] in
/-- A window integral dominated pointwise by twice the sum of two others is dominated by twice
the sum of their window integrals. -/
theorem lintegral_Icc_le_two_mul_add {G G₁ G₂ : Ω → ℝ → ℝ≥0∞}
    (hG₁ : Measurable (Function.uncurry G₁)) (hle : ∀ ω s, G ω s ≤ 2 * G₁ ω s + 2 * G₂ ω s) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, G ω s ∂volume ∂P
      ≤ 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, G₁ ω s ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, G₂ ω s ∂volume ∂P := by
  have h1 : ∀ ω : Ω, Measurable fun s => G₁ ω s := fun ω =>
    hG₁.comp (measurable_const.prodMk measurable_id)
  have hin : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, G ω s ∂volume
      ≤ 2 * (∫⁻ s in Set.Icc (0 : ℝ) T, G₁ ω s ∂volume)
        + 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, G₂ ω s ∂volume := by
    intro ω
    refine le_trans (lintegral_mono fun s => hle ω s) (le_of_eq ?_)
    rw [lintegral_add_left ((h1 ω).const_mul 2), lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
  refine le_trans (lintegral_mono hin) (le_of_eq ?_)
  have hout : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T, G₁ ω s ∂volume :=
    hG₁.lintegral_prod_right'
  rw [lintegral_add_left (hout.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num)]
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


