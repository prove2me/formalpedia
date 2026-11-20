-- Prove2me | Definitions.Def_SourceProof_2118dd8af0bc41a167ea34d2
-- name    : SourceProof_2118dd8af0bc41a167ea34d2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:00:14.657568+00:00
-- url     : https://prove2.me/theorems/8f681902-c00d-4bb7-89ba-d143f88e1bbf
-- title:
--   LevyStochCalc source module: SourceProof_2118dd8af0bc41a167ea34d2
-- statement:
--   The original source theorem `MathFin.integral_bilinear_pairing` comes from the `MathFin.Foundations.PoissonCompensatedBilinear` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_4f9efcc273d3e7aeacb70fad

open private compensated_measurable_regionSigma pastSigma_le_regionSigma_sub pastSigma_mono from Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F001
/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

/-!
# The compensated Poisson random measure is an orthogonal martingale measure

The diagonal second moment `𝔼[Ñ(B)²] = ν̂(B)` (`compensated_integral_sq`) is the `C = D` case of the
full **covariance** of the compensated Poisson random measure:

  `𝔼[Ñ(C)·Ñ(D)] = ν̂(C ∩ D)`   for measurable finite-intensity `C, D`.

`Ñ` is thus an *orthogonal martingale measure* with (deterministic) intensity `ν̂`: increments on
disjoint regions are uncorrelated, and the covariance of general increments is the intensity of their
overlap. The proof decomposes `C = (C∩D) ⊔ (C\D)` and `D = (C∩D) ⊔ (D\C)` into three disjoint pieces
whose counts are independent (the independent-scattering field `indep_of_disjoint_region`); the three
disjoint cross-pairs vanish (`integral_mul_compensated_eq_zero`) and the diagonal `𝔼[Ñ(C∩D)²]` is
`ν̂(C∩D)`.

This covariance is the bilinear core the compensated-integral isometry is built on (the jump analogue
of `WienerIntegralL2.covariance_increment_aux`), and the first rung of the Itô–Lévy integral
*operator* (the CLM over the characterised predictable `L²`).

## Provenance

Built on our own `PoissonRandomMeasure` / `PoissonCompensatedIsometryAdapted` (PRM field shape
consulted from `cgarryZA/LevyStochCalc`, Apache-2.0, cited — a rendering of Applebaum 2009 Def.
2.3.1; the proofs are ours). Reference: Applebaum, *Lévy Processes and Stochastic Calculus*, CUP
2009, Thm 4.2.3.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Weighted future pairings — the bilinear rung

The covariance above is the `φ ≡ 1` case of a **weighted** future pairing
`𝔼[φ · Ñ(C) · Ñ(D)] = 𝔼[φ] · ν̂(C ∩ D)` for `φ` adapted at a time `s` before both `C, D`
(`C, D ⊆ (s, ∞) × E`). It is the jump analogue of `ItoIsometryAdapted.rect_increment_pairing`
(Brownian rectangles — cited, not reused): the past-adapted weight factors out of every future
increment, and the increment covariance supplies `ν̂(C ∩ D)`. From it, splitting a box at the later
of two start times gives the **overlapping-box bilinear pairing** the Itô–Lévy isometry sums over.

All of it rests on the *single-increment* field `indep_of_disjoint_region` — no past-vs-future
`σ`-algebra independence is assumed. Integrability of the triple products is bought by the same
independence (a past-adapted factor is `⟂` any future increment it multiplies). -/


theorem _root_.Prove2MeSourceProof.h_2118dd8af0bc41a167ea34d2 (N : PoissonRandomMeasure P ν)
    {sa ta sb tb : ℝ} (hab : sa ≤ sb)
    {Aa Ab : Set E} (hAa : MeasurableSet Aa) (hAb : MeasurableSet Ab)
    (hAafin : ν Aa ≠ ⊤) (hAbfin : ν Ab ≠ ⊤)
    {φa φb : Ω → ℝ} {Ca Cb : ℝ}
    (hφa : N.AdaptedAt sa φa) (hφb : N.AdaptedAt sb φb)
    (hφaB : ∀ ω, |φa ω| ≤ Ca) (hφbB : ∀ ω, |φb ω| ≤ Cb) :
    ∫ ω, (φa ω * N.compensated (Set.Ioc sa ta ×ˢ Aa) ω)
          * (φb ω * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω) ∂P
      = (∫ ω, φa ω * φb ω ∂P)
          * (referenceIntensity ν ((Set.Ioc sa ta ×ˢ Aa) ∩ (Set.Ioc sb tb ×ˢ Ab))).toReal := by
  -- measurability of the boxes and the past / future half-planes at `sb`
  have hboxams : MeasurableSet (Set.Ioc sa ta ×ˢ Aa) := measurableSet_Ioc.prod hAa
  have hboxbms : MeasurableSet (Set.Ioc sb tb ×ˢ Ab) := measurableSet_Ioc.prod hAb
  have hIicms : MeasurableSet (Set.Iic sb ×ˢ (Set.univ : Set E)) :=
    measurableSet_Iic.prod MeasurableSet.univ
  have hIoims : MeasurableSet (Set.Ioi sb ×ˢ (Set.univ : Set E)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hpastms : MeasurableSet (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) :=
    hboxams.inter hIicms
  have hfutms : MeasurableSet (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) :=
    hboxams.inter hIoims
  -- finiteness (the halves are subsets of `boxa`)
  have hboxafin : MathFin.referenceIntensity ν (Set.Ioc sa ta ×ˢ Aa) ≠ ⊤ :=
    MathFin.referenceIntensity_box_ne_top hAafin
  have hboxbfin : MathFin.referenceIntensity ν (Set.Ioc sb tb ×ˢ Ab) ≠ ⊤ :=
    MathFin.referenceIntensity_box_ne_top hAbfin
  have hpastfin : MathFin.referenceIntensity ν (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hboxafin (measure_mono Set.inter_subset_left)
  have hfutfin : MathFin.referenceIntensity ν (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hboxafin (measure_mono Set.inter_subset_left)
  -- geometry: `boxb ⊆` future, past `⟂` future, past `∪` future `= boxa`, `futPart ∩ boxb = boxa ∩ boxb`
  have hIicIoi : Disjoint (Set.Iic sb ×ˢ (Set.univ : Set E)) (Set.Ioi sb ×ˢ Set.univ) :=
    Set.disjoint_left.mpr fun ⟨x, e⟩ hx hxD =>
      absurd (Set.mem_Iic.mp (Set.mem_prod.mp hx).1)
        (not_le.mpr (Set.mem_Ioi.mp (Set.mem_prod.mp hxD).1))
  have hboxbsub : Set.Ioc sb tb ×ˢ Ab ⊆ Set.Ioi sb ×ˢ Set.univ :=
    Set.prod_mono Set.Ioc_subset_Ioi_self (Set.subset_univ _)
  have hfutsub : Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ) ⊆ Set.Ioi sb ×ˢ Set.univ :=
    Set.inter_subset_right
  have hpastdisjb : Disjoint (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ))
      (Set.Ioc sb tb ×ˢ Ab) :=
    Set.disjoint_of_subset Set.inter_subset_right hboxbsub hIicIoi
  have hdisj_pf : Disjoint (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ))
      (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) :=
    Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right hIicIoi
  have hunion : (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ))
      ∪ (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) = Set.Ioc sa ta ×ˢ Aa := by
    rw [← Set.inter_union_distrib_left, ← Set.union_prod, Set.Iic_union_Ioi,
      Set.univ_prod_univ, Set.inter_univ]
  have hfutinter : (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ∩ (Set.Ioc sb tb ×ˢ Ab)
      = (Set.Ioc sa ta ×ˢ Aa) ∩ (Set.Ioc sb tb ×ˢ Ab) := by
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hboxbsub]
  -- the weight `φa · φb` is adapted at `sb`, bounded, hence integrable
  have hφ : N.AdaptedAt sb (fun ω => φa ω * φb ω) :=
    ((show Measurable[N.pastSigma sa] φa from hφa).mono (pastSigma_mono N hab) le_rfl).mul
      (show Measurable[N.pastSigma sb] φb from hφb)
  have hbound : ∀ ω, ‖φa ω * φb ω‖ ≤ Ca * Cb := fun ω => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hφaB ω) (hφbB ω) (abs_nonneg _) ((abs_nonneg _).trans (hφaB ω))
  have hφint : Integrable (fun ω => φa ω * φb ω) P :=
    (memLp_top_of_bound hφ.measurable.aestronglyMeasurable (Ca * Cb) (ae_of_all _ hbound)).integrable
      le_top
  -- `Ñ(boxa) = Ñ(pastPart) + Ñ(futPart)` a.e.
  have hdecomp : ∀ᵐ ω ∂P, N.compensated (Set.Ioc sa ta ×ˢ Aa) ω
      = N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ω
        + N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ω := by
    have h := MathFin.compensated_add_of_disjoint N hpastms hfutms hdisj_pf hpastfin hfutfin
    rwa [hunion] at h
  -- split the integrand: past term (⟶ 0) + future term (⟶ master pairing)
  have hprod : ∀ᵐ ω ∂P,
      (φa ω * N.compensated (Set.Ioc sa ta ×ˢ Aa) ω)
        * (φb ω * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω)
      = φa ω * φb ω * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ω
          * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω
        + φa ω * φb ω * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ω
          * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω := by
    filter_upwards [hdecomp] with ω hω
    rw [hω]; ring
  rw [integral_congr_ae hprod]
  -- integrabilities: bounded weight × (`L²`-increment) × (`L²`-increment)
  have hint_past : Integrable (fun ω => φa ω * φb ω
      * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ω
      * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω) P :=
    (((_root_.Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hpastms hpastfin).integrable_mul
        (_root_.Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hboxbms hboxbfin)).bdd_mul
        hφ.measurable.aestronglyMeasurable (ae_of_all _ hbound)).congr
      (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring)
  have hint_fut : Integrable (fun ω => φa ω * φb ω
      * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ω
      * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω) P :=
    (((_root_.Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hfutms hfutfin).integrable_mul
        (_root_.Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hboxbms hboxbfin)).bdd_mul
        hφ.measurable.aestronglyMeasurable (ae_of_all _ hbound)).congr
      (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring)
  rw [integral_add hint_past hint_fut]
  -- past term vanishes (weighted past-region factor `⟂` fresh future increment)
  have hXpast : Measurable[N.regionSigma (Set.Ioc sb tb ×ˢ Ab)]
      (fun ω => φa ω * φb ω
        * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ω) :=
    ((show Measurable[N.pastSigma sb] (fun ω => φa ω * φb ω) from hφ).mono
      (pastSigma_le_regionSigma_sub N hboxbsub) le_rfl).mul
      (compensated_measurable_regionSigma N hpastdisjb hpastms)
  rw [_root_.Prove2MeSourceProof.h_8e8c6bf1745159f9e5de9b8d N hboxbms hboxbfin hXpast, zero_add,
    _root_.Prove2MeSourceProof.h_4f9efcc273d3e7aeacb70fad N hfutms hboxbms hfutsub hboxbsub hfutfin hboxbfin hφ hφint,
    hfutinter]
end MathFin


