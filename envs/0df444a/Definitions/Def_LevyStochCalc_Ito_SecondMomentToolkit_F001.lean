-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F001
-- name    : LevyStochCalc_Ito_SecondMomentToolkit_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:19:01.830016+00:00
-- url     : https://prove2.me/theorems/1eca90e8-e9e8-4c98-80b8-74c10bba5522
-- title:
--   Source declarations: LevyStochCalc.Ito.SecondMomentToolkit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SecondMomentToolkit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F000
import Definitions.Def_SourceProof_190a5767e8f1b936b4a6a09f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Auxiliary lemmas for the second moment of an Itô–Lévy process

The `L²` lemmas behind the expectation form of the quadratic Itô formula: the second moment of a
square-integrable variable as the real part of its energy, the expansion of the square of a sum,
the evaluation of a square-integrable martingale paired against a variable measurable at an
earlier time, and the exchange of a time integral with a pairing. The running integral
`∫_0^s b_r dr` of a drift over a window `[0, T]` is introduced as a jointly measurable function of
the sample point and the time, together with the pathwise identities
`(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds` and, for two integrable functions,
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`; and the polarised isometry for
the Brownian integral, the expected product of two Brownian integrals at a time being the expected
time integral of the product of their integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Toolkit

/-- Pairing a square-integrable martingale at a later time against a square-integrable variable
measurable at an earlier time reads the martingale at the earlier time. -/
theorem integral_mul_martingale_eq {𝒢 : Filtration ℝ ‹MeasurableSpace Ω›} {M : ℝ → Ω → ℝ}
    (hM : Martingale M 𝒢 P) {a t : ℝ} (hat : a ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝒢 a] Z) (hZ2 : MemLp Z 2 P) (hMt : MemLp (M t) 2 P) :
    ∫ ω, Z ω * M t ω ∂P = ∫ ω, Z ω * M a ω ∂P := by
  haveI : SigmaFinite (P.trim (𝒢.le a)) := (isFiniteMeasure_trim (𝒢.le a)).toSigmaFinite
  have hZt : Integrable (fun ω => Z ω * M t ω) P := hZ2.integrable_mul hMt
  have hMtInt : Integrable (M t) P := hMt.integrable one_le_two
  have hce : P[(fun ω => Z ω * M t ω) | 𝒢 a] =ᵐ[P] fun ω => Z ω * (P[M t | 𝒢 a]) ω :=
    condExp_mul_of_stronglyMeasurable_left hZ hZt hMtInt
  have hma : P[M t | 𝒢 a] =ᵐ[P] M a := hM.condExp_ae_eq hat
  rw [← integral_condExp (𝒢.le a)]
  refine integral_congr_ae (hce.trans ?_)
  filter_upwards [hma] with ω hω
  rw [hω]
/-- A square-integrable martingale vanishing at an earlier time is orthogonal to every
square-integrable variable measurable at that time. -/
theorem integral_mul_martingale_eq_zero {𝒢 : Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ} (hM : Martingale M 𝒢 P) {a t : ℝ} (hat : a ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝒢 a] Z) (hZ2 : MemLp Z 2 P) (hMt : MemLp (M t) 2 P)
    (hMa : M a =ᵐ[P] 0) : ∫ ω, Z ω * M t ω ∂P = 0 := by
  rw [integral_mul_martingale_eq hM hat hZ hZ2 hMt]
  have h0 : (fun ω => Z ω * M a ω) =ᵐ[P] fun _ => (0 : ℝ) := by
    filter_upwards [hMa] with ω hω
    rw [hω, Pi.zero_apply, mul_zero]
  rw [integral_congr_ae h0, integral_zero]
omit [IsProbabilityMeasure P] in
/-- A square-integrable integrand on a window is square integrable for the product measure. -/
theorem memLp_two_prod {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    MemLp (fun p : Ω × ℝ => f p.1 p.2) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hf.aestronglyMeasurable ?_
  exact lt_of_eq_of_lt (lintegral_prod _ (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable)
    hfq
omit [IsProbabilityMeasure P] in
/-- A square-integrable variable, read at the sample point, is square integrable for the product
measure with a bounded window. -/
theorem memLp_two_prod_fst {g : Ω → ℝ} (hg : MemLp g 2 P) {T : ℝ} :
    MemLp (fun p : Ω × ℝ => g p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
    hg.aestronglyMeasurable.aemeasurable.comp_fst.aestronglyMeasurable ?_
  have hgm : AEMeasurable (fun ω => (‖g ω‖₊ : ℝ≥0∞) ^ 2) P :=
    hg.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal.pow_const 2
  rw [lintegral_prod _ hgm.comp_fst]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top (lintegral_sq_lt_top_of_memLp_two hg) ENNReal.ofReal_lt_top
/-- **The pairing of a time integral against a square-integrable variable is the time integral
of the pairings.** -/
theorem integral_setIntegral_mul {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    {T : ℝ}
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {g : Ω → ℝ} (hg : MemLp g 2 P) :
    ∫ ω, (∫ s in Set.Icc (0 : ℝ) T, f ω s) * g ω ∂P
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, f ω s * g ω ∂P := by
  have hint : Integrable (fun p : Ω × ℝ => f p.1 p.2 * g p.1)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (memLp_two_prod hf hfq).integrable_mul (memLp_two_prod_fst hg)
  calc ∫ ω, (∫ s in Set.Icc (0 : ℝ) T, f ω s) * g ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, f ω s * g ω ∂volume ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        exact (integral_mul_const (g ω) fun s => f ω s).symm
    _ = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, f ω s * g ω ∂P :=
        integral_integral_swap (f := fun ω s => f ω s * g ω) hint
omit [IsProbabilityMeasure P] in
/-- The time integral of a square-integrable integrand is square integrable. -/
theorem memLp_two_setIntegral {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (hT : 0 ≤ T)
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) T, f ω s) 2 P := by
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top ?_ ?_
  · exact (hf.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T))).aestronglyMeasurable
  · exact lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_190a5767e8f1b936b4a6a09f hf hT hfq)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfq)
end Toolkit

section Running

variable (b : ℝ → Ω → ℝ) (T : ℝ)

variable {b T}

end Running

section Polarised

end Polarised

section PolarisedDrift

end PolarisedDrift

end LevyStochCalc.Ito.SecondMoment


