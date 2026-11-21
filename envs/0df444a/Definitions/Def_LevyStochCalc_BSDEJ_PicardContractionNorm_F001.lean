-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F001
-- name    : LevyStochCalc_BSDEJ_PicardContractionNorm_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:22:06.261049+00:00
-- url     : https://prove2.me/theorems/33588389-973d-4df1-a856-cf88140c8672
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardContractionNorm
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardContractionNorm. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponentially weighted norm of a triple

The exponentially weighted `L²` norm `wNorm` of a triple `(Y, Z, U)` over a horizon `[0, T]`
weights the squared value, the squared diffusion coordinates and the marked energy of the jump
integrand by `e^{βs}` and integrates them over the horizon and the sample space. Its integrand at
a sample point and a time is the pointwise energy density `density`; the norm is finite when the
value, the diffusion coordinates and the jump integrand have finite energy on the horizon, and it
is then the real integral over the horizon of the weighted sample energy density.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Norm

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {d : ℕ}

variable {P : Measure Ω} {ν : Measure E} {β T : ℝ}

variable [SigmaFinite ν]

/-- The weighted norm, with the time integral outside. -/
theorem wNorm_eq_setLIntegral [SFinite P] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    wNorm P ν β T Y Z U = ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (β * s))
      * (∫⁻ ω, density ν Y Z U ω s ∂P) ∂volume := by
  have hm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ENNReal.ofReal (Real.exp (β * s)) * density ν Y Z U ω s) := by
    refine Measurable.mul ?_ (measurable_uncurry_density hYm hZm hUm)
    exact (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_snd)))
  rw [wNorm_eq_lintegral_density, lintegral_lintegral_swap (μ := P)
    (ν := volume.restrict (Set.Icc (0 : ℝ) T)) hm.aemeasurable]
  exact setLIntegral_congr_fun measurableSet_Icc fun s _ =>
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
omit [SigmaFinite ν] in
/-- The energy of the pointwise density on the horizon is finite when the weighted norm is. -/
theorem lintegral_density_ne_top_of_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (hfin : wNorm P ν β T Y Z U ≠ ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume ∂P ≠ ⊤ := by
  refine ne_top_of_le_ne_top hfin ?_
  rw [wNorm_eq_lintegral_density]
  refine lintegral_mono fun ω => lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal]
  exact Real.one_le_exp (mul_nonneg hβ hs.1)
/-- The sample energy at each time of a finite window energy is almost everywhere finite. -/
theorem ae_lintegral_ne_top [SFinite P] {F : Ω → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), (∫⁻ ω, F ω s ∂P) ≠ ⊤ := by
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P
      = ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, F ω s ∂P) ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      hF.aemeasurable
  rw [hswap] at hfin
  filter_upwards [ae_lt_top hF.lintegral_prod_left hfin] with s hs
  exact hs.ne
/-- The sample energy density of a triple of finite weighted norm is almost everywhere finite in
time. -/
theorem ae_lintegral_density_ne_top [SFinite P] (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hfin : wNorm P ν β T Y Z U ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), (∫⁻ ω, density ν Y Z U ω s ∂P) ≠ ⊤ := by
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume ∂P
      = ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, density ν Y Z U ω s ∂P) ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      (measurable_uncurry_density hYm hZm hUm).aemeasurable
  have h := lintegral_density_ne_top_of_wNorm hβ hfin
  rw [hswap] at h
  filter_upwards [ae_lt_top (measurable_lintegral_density hYm hZm hUm) h] with s hs
  exact hs.ne
/-- The weighted sample energy density of a triple of finite weighted norm is integrable in
time on the horizon. -/
theorem integrableOn_exp_mul_toReal_density [IsProbabilityMeasure P] (hβ : 0 ≤ β)
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hfin : wNorm P ν β T Y Z U ≠ ⊤) :
    IntegrableOn (fun s => Real.exp (β * s) * (∫⁻ ω, density ν Y Z U ω s ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
  Ito.SecondMoment.integrableOn_exp_mul β
    (Ito.SecondMoment.integrableOn_toReal_lintegral (measurable_uncurry_density hYm hZm hUm)
      (lt_top_iff_ne_top.mpr (lintegral_density_ne_top_of_wNorm hβ hfin)))
omit [SigmaFinite ν] in
/-- A finite, integrable time density integrates to the same weighted total in `ℝ≥0∞` and in
`ℝ`. -/
theorem setLIntegral_exp_mul_eq_ofReal {G : ℝ → ℝ≥0∞}
    (hfin : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), G s ≠ ⊤)
    (hint : IntegrableOn (fun s => Real.exp (β * s) * (G s).toReal) (Set.Icc (0 : ℝ) T)) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (β * s)) * G s ∂volume
      = ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (G s).toReal) := by
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun s => by positivity)]
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with s hs
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_toReal hs]
/-- A finite weighted norm, as a real integral of the weighted sample energy density. -/
theorem wNorm_eq_ofReal_setIntegral [IsProbabilityMeasure P] (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hfin : wNorm P ν β T Y Z U ≠ ⊤) :
    wNorm P ν β T Y Z U = ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) T,
      Real.exp (β * s) * (∫⁻ ω, density ν Y Z U ω s ∂P).toReal) := by
  rw [wNorm_eq_setLIntegral hYm hZm hUm]
  exact setLIntegral_exp_mul_eq_ofReal (ae_lintegral_density_ne_top hβ hYm hZm hUm hfin)
    (integrableOn_exp_mul_toReal_density hβ hYm hZm hUm hfin)
/-- At each time, the energy density of a triple is measurable in the sample point. -/
theorem measurable_density_slice {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) (s : ℝ) :
    Measurable fun ω : Ω => density ν Y Z U ω s := by
  classical
  have hA : Measurable fun ω : Ω => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 :=
    (measurable_uncurry_sq_value hYm).comp (measurable_id.prodMk measurable_const)
  have hB : ∀ j : Fin d, Measurable fun ω : Ω => (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 := fun j =>
    (measurable_uncurry_sq_value (hZm j)).comp (measurable_id.prodMk measurable_const)
  have hC : Measurable fun ω : Ω => ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    (measurable_uncurry_sq_jump hUm).comp (measurable_id.prodMk measurable_const)
  simp only [density]
  exact (hA.add (Finset.measurable_sum _ fun j _ => hB j)).add hC
end Norm

end LevyStochCalc.BSDEJ.Solves


