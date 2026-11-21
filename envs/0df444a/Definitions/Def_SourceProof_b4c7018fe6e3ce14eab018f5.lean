-- Prove2me | Definitions.Def_SourceProof_b4c7018fe6e3ce14eab018f5
-- name    : SourceProof_b4c7018fe6e3ce14eab018f5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:29:23.827278+00:00
-- url     : https://prove2.me/theorems/3d92de8b-f8df-464b-aa56-620cc91059fb
-- title:
--   LevyStochCalc source proof: LevyStochCalc.BSDEJ.Generator.energy_generator_along_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorEnergy_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Energy of a BSDEJ generator along a triple of processes

A generator `f` that is Lipschitz in `(y, z, u)` for the `L²(ν)` distance of the jump variable has
linear growth: `‖f s y z u‖` is at most `‖f s 0 0 0‖ + L * (‖y‖ + ‖z‖ + ‖u‖_{L²(ν)})`, and the
square of that bound splits into four terms. Evaluated along processes `(Y, Z, U)` the splitting
dominates the energy of `s ↦ f s (Y s) (Z s) (U s)` on the horizon `[0, T]` by the energy of `Y`,
the energies of the coordinates of `Z` and the marked energy of `U`; in particular the generator
has finite energy along a triple of processes of finite energy.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Generator

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

/-! ### Elementary inequalities in `ℝ≥0∞` -/

/-! ### Linear growth of a Lipschitz generator -/

/-! ### Energy along a triple of processes -/


theorem _root_.Prove2MeSourceProof.h_b4c7018fe6e3ce14eab018f5 [IsProbabilityMeasure P] [SigmaFinite ν]
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hYm : Measurable (Function.uncurry Y))
    (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    Brownian.Ito.energy P T (fun ω s => f s (Y s ω) (Z s ω) (U s ω))
      ≤ 4 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2)
          + ENNReal.ofReal L ^ 2 * Brownian.Ito.energy P T (fun ω s => Y s ω)
          + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i)
          + ENNReal.ofReal L ^ 2 *
              Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by
  classical
  have ha : Measurable fun p : Ω × ℝ => (‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2 := by
    have h : Measurable fun p : Ω × ℝ => f p.2 0 0 0 :=
      (LevyStochCalc.BSDEJ.Generator.measurable_generator_zero hf).comp measurable_snd
    exact (h.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hb : Measurable fun p : Ω × ℝ => (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2 := by
    have h : Measurable fun p : Ω × ℝ => Y p.2 p.1 :=
      hYm.comp (measurable_snd.prodMk measurable_fst)
    exact (h.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hc : ∀ i : Fin d, Measurable fun p : Ω × ℝ => (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2 := by
    intro i
    have h : Measurable fun p : Ω × ℝ => Z p.2 p.1 i := hZm i
    exact (h.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hcsum : Measurable fun p : Ω × ℝ => ∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hc i
  have hw : Measurable fun p : Ω × ℝ => ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    have h : Measurable fun q : (Ω × ℝ) × E => U q.1.2 q.1.1 q.2 :=
      hUm.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact ((h.nnnorm.coe_nnreal_ennreal).pow_const 2).lintegral_prod_right'
  have hM : Measurable fun p : Ω × ℝ => 4 * ((‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν) :=
    (((ha.add (hb.const_mul _)).add (hcsum.const_mul _)).add (hw.const_mul _)).const_mul _
  have hprod : ∀ g : Ω × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, g (ω, s) ∂volume ∂P
        = ∫⁻ p, g p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := fun g hg =>
    lintegral_lintegral (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      (f := fun ω s => g (ω, s)) hg.aemeasurable
  have e1 : ∫⁻ p, (‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 := by
    rw [← hprod _ ha]
    simp only [lintegral_const, measure_univ, mul_one]
  have e2 : ∫⁻ p, (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = LevyStochCalc.Brownian.Ito.energy P T fun ω s => Y s ω := (hprod _ hb).symm
  have e3 : ∫⁻ p, (∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = ∑ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T fun ω s => Z s ω i := by
    rw [lintegral_finsetSum _ fun i _ => hc i]
    exact Finset.sum_congr rfl fun i _ => (hprod _ (hc i)).symm
  have e4 : ∫⁻ p, (∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = LevyStochCalc.Poisson.Compensated.markedEnergy P ν T fun ω s e => U s ω e := (hprod _ hw).symm
  calc LevyStochCalc.Brownian.Ito.energy P T (fun ω s => f s (Y s ω) (Z s ω) (U s ω))
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, 4 * ((‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * (‖Y s ω‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P := by
        simp only [LevyStochCalc.Brownian.Ito.energy]
        refine lintegral_mono fun ω => lintegral_mono fun s => ?_
        refine (LevyStochCalc.BSDEJ.Generator.sq_enorm_generator_le hlip s (Y s ω) (Z s ω) (U s ω)).trans ?_
        gcongr
        exact LevyStochCalc.BSDEJ.Generator.sq_enorm_pi_le_sum (Z s ω)
    _ = ∫⁻ p, 4 * ((‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hprod _ hM
    _ = 4 * ((∫⁻ p, (‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2
              ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
          + ENNReal.ofReal L ^ 2 * ∫⁻ p, (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2
              ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
          + ENNReal.ofReal L ^ 2 * ∫⁻ p, (∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2)
              ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
          + ENNReal.ofReal L ^ 2 * ∫⁻ p, (∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
              ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))) :=
        LevyStochCalc.BSDEJ.Generator.lintegral_four_terms ha hb hcsum (by finiteness)
    _ = 4 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2)
          + ENNReal.ofReal L ^ 2 * LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Y s ω)
          + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i)
          + ENNReal.ofReal L ^ 2 *
              LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by
        rw [e1, e2, e3, e4]
end LevyStochCalc.BSDEJ.Generator


