-- Prove2me | Definitions.Def_SourceProof_4f9efcc273d3e7aeacb70fad
-- name    : SourceProof_4f9efcc273d3e7aeacb70fad
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:57:57.197267+00:00
-- url     : https://prove2.me/theorems/eab2d4b8-cfce-4d0c-9c68-a205896240ec
-- title:
--   LevyStochCalc source module: SourceProof_4f9efcc273d3e7aeacb70fad
-- statement:
--   The original source theorem `MathFin.integral_adapted_bilinear_future` comes from the `MathFin.Foundations.PoissonCompensatedBilinear` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F000
import Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F001

open private adapted_indepFun_compensated_sub compensated_measurable_regionSigma integral_adapted_mul_compensated_sq_sub pastSigma_le_regionSigma_sub from Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F001
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


theorem _root_.Prove2MeSourceProof.h_4f9efcc273d3e7aeacb70fad (N : PoissonRandomMeasure P ν) {s : ℝ}
    {C D : Set (ℝ × E)} (hCms : MeasurableSet C) (hDms : MeasurableSet D)
    (hCsub : C ⊆ Set.Ioi s ×ˢ Set.univ) (hDsub : D ⊆ Set.Ioi s ×ˢ Set.univ)
    (hCfin : referenceIntensity ν C ≠ ⊤) (hDfin : referenceIntensity ν D ≠ ⊤)
    {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ) (hφint : Integrable φ P) :
    ∫ ω, φ ω * N.compensated C ω * N.compensated D ω ∂P
      = (∫ ω, φ ω ∂P) * (referenceIntensity ν (C ∩ D)).toReal := by
  -- the three disjoint pieces, all still strictly after `s`
  have hIms : MeasurableSet (C ∩ D) := hCms.inter hDms
  have hC'ms : MeasurableSet (C \ D) := hCms.diff hDms
  have hD'ms : MeasurableSet (D \ C) := hDms.diff hCms
  have hIsub : C ∩ D ⊆ Set.Ioi s ×ˢ Set.univ := Set.inter_subset_left.trans hCsub
  have hC'sub : C \ D ⊆ Set.Ioi s ×ˢ Set.univ := Set.sdiff_subset.trans hCsub
  have hD'sub : D \ C ⊆ Set.Ioi s ×ˢ Set.univ := Set.sdiff_subset.trans hDsub
  have hIfin : MathFin.referenceIntensity ν (C ∩ D) ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.inter_subset_left)
  have hC'fin : MathFin.referenceIntensity ν (C \ D) ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.sdiff_subset)
  have hD'fin : MathFin.referenceIntensity ν (D \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfin (measure_mono Set.sdiff_subset)
  have hIC' : Disjoint (C ∩ D) (C \ D) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.2
  have hID' : Disjoint (C ∩ D) (D \ C) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.1
  have hC'D' : Disjoint (C \ D) (D \ C) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.1
  -- a.e. decompositions of the two increments
  have hdC : ∀ᵐ ω ∂P, N.compensated C ω
      = N.compensated (C ∩ D) ω + N.compensated (C \ D) ω := by
    have h := MathFin.compensated_add_of_disjoint N hIms hC'ms hIC' hIfin hC'fin
    rwa [Set.inter_union_sdiff] at h
  have hdD : ∀ᵐ ω ∂P, N.compensated D ω
      = N.compensated (C ∩ D) ω + N.compensated (D \ C) ω := by
    have h := MathFin.compensated_add_of_disjoint N hIms hD'ms hID' hIfin hD'fin
    rwa [show (C ∩ D) ∪ (D \ C) = D from by
      rw [Set.inter_comm]; exact Set.inter_union_sdiff D C] at h
  -- reusable measurability / integrability shorthands
  have hφreg : ∀ {q : Set (ℝ × E)}, q ⊆ Set.Ioi s ×ˢ Set.univ → Measurable[N.regionSigma q] φ :=
    fun hq => (show Measurable[N.pastSigma s] φ from hφ).mono
      (pastSigma_le_regionSigma_sub N hq) le_rfl
  have hÑint : ∀ {p : Set (ℝ × E)}, MeasurableSet p → MathFin.referenceIntensity ν p ≠ ⊤ →
      Integrable (N.compensated p) P :=
    fun hp hpf => (_root_.Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hp hpf).integrable (by norm_num)
  have hφÑint : ∀ {p : Set (ℝ × E)}, MeasurableSet p → p ⊆ Set.Ioi s ×ˢ Set.univ →
      MathFin.referenceIntensity ν p ≠ ⊤ → Integrable (fun ω => φ ω * N.compensated p ω) P :=
    fun hp hps hpf =>
      (adapted_indepFun_compensated_sub N hp hps hφ).integrable_mul hφint (hÑint hp hpf)
  -- independence of a weighted disjoint increment from a fresh increment
  have hindep_cross : ∀ {p q : Set (ℝ × E)}, Disjoint p q → MeasurableSet p →
      q ⊆ Set.Ioi s ×ˢ Set.univ → MeasurableSet q →
      IndepFun (fun ω => φ ω * N.compensated p ω) (N.compensated q) P := by
    intro p q hpq hpms hqsub hqms
    have hX : Measurable[N.regionSigma q] (fun ω => φ ω * N.compensated p ω) :=
      (hφreg hqsub).mul (compensated_measurable_regionSigma N hpq hpms)
    have hfield : Indep (N.regionSigma q)
        (MeasurableSpace.comap (fun ω => N.N ω q) inferInstance) P := N.indep_of_disjoint_region hqms
    have hraw : IndepFun (fun ω => φ ω * N.compensated p ω) (fun ω => N.N ω q) P :=
      (IndepFun_iff_Indep _ _ _).mpr
        (indep_of_indep_of_le_left hfield (measurable_iff_comap_le.mp hX))
    have hc := hraw.comp (φ := (id : ℝ → ℝ))
      (ψ := fun x : ℝ≥0∞ => x.toReal - (MathFin.referenceIntensity ν q).toReal) measurable_id (by fun_prop)
    simp only [Function.comp_def, id_eq] at hc
    exact hc
  -- expand the weighted product into diagonal + three cross pieces
  have hprod : ∀ᵐ ω ∂P, φ ω * N.compensated C ω * N.compensated D ω
      = φ ω * (N.compensated (C ∩ D) ω) ^ 2
        + φ ω * N.compensated (C ∩ D) ω * N.compensated (D \ C) ω
        + φ ω * N.compensated (C \ D) ω * N.compensated (C ∩ D) ω
        + φ ω * N.compensated (C \ D) ω * N.compensated (D \ C) ω := by
    filter_upwards [hdC, hdD] with ω hCω hDω
    rw [hCω, hDω]; ring
  rw [integral_congr_ae hprod]
  -- integrabilities of the four pieces
  have hindepI2 := (adapted_indepFun_compensated_sub N hIms hIsub hφ).comp
    (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ => x ^ 2) measurable_id (by fun_prop)
  simp only [Function.comp_def, id_eq] at hindepI2
  have hi1 : Integrable (fun ω => φ ω * (N.compensated (C ∩ D) ω) ^ 2) P :=
    hindepI2.integrable_mul hφint ((_root_.Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hIms hIfin).integrable_sq)
  have hi2 : Integrable
      (fun ω => φ ω * N.compensated (C ∩ D) ω * N.compensated (D \ C) ω) P :=
    (hindep_cross hID' hIms hD'sub hD'ms).integrable_mul
      (hφÑint hIms hIsub hIfin) (hÑint hD'ms hD'fin)
  have hi3 : Integrable
      (fun ω => φ ω * N.compensated (C \ D) ω * N.compensated (C ∩ D) ω) P :=
    (hindep_cross hIC'.symm hC'ms hIsub hIms).integrable_mul
      (hφÑint hC'ms hC'sub hC'fin) (hÑint hIms hIfin)
  have hi4 : Integrable
      (fun ω => φ ω * N.compensated (C \ D) ω * N.compensated (D \ C) ω) P :=
    (hindep_cross hC'D' hC'ms hD'sub hD'ms).integrable_mul
      (hφÑint hC'ms hC'sub hC'fin) (hÑint hD'ms hD'fin)
  have hf12 : Integrable (fun ω => φ ω * (N.compensated (C ∩ D) ω) ^ 2
      + φ ω * N.compensated (C ∩ D) ω * N.compensated (D \ C) ω) P := hi1.add hi2
  have hf123 : Integrable (fun ω => φ ω * (N.compensated (C ∩ D) ω) ^ 2
      + φ ω * N.compensated (C ∩ D) ω * N.compensated (D \ C) ω
      + φ ω * N.compensated (C \ D) ω * N.compensated (C ∩ D) ω) P := hf12.add hi3
  -- the three cross pieces vanish; the diagonal is `𝔼[φ]·ν̂(C∩D)`
  have hX2 : Measurable[N.regionSigma (D \ C)] (fun ω => φ ω * N.compensated (C ∩ D) ω) :=
    (hφreg hD'sub).mul (compensated_measurable_regionSigma N hID' hIms)
  have hX3 : Measurable[N.regionSigma (C ∩ D)] (fun ω => φ ω * N.compensated (C \ D) ω) :=
    (hφreg hIsub).mul (compensated_measurable_regionSigma N hIC'.symm hC'ms)
  have hX4 : Measurable[N.regionSigma (D \ C)] (fun ω => φ ω * N.compensated (C \ D) ω) :=
    (hφreg hD'sub).mul (compensated_measurable_regionSigma N hC'D' hC'ms)
  rw [integral_add hf123 hi4, integral_add hf12 hi3, integral_add hi1 hi2,
    integral_adapted_mul_compensated_sq_sub N hIms hIsub hIfin hφ hφint,
    _root_.Prove2MeSourceProof.h_8e8c6bf1745159f9e5de9b8d N hD'ms hD'fin hX2,
    _root_.Prove2MeSourceProof.h_8e8c6bf1745159f9e5de9b8d N hIms hIfin hX3,
    _root_.Prove2MeSourceProof.h_8e8c6bf1745159f9e5de9b8d N hD'ms hD'fin hX4]
  ring
end MathFin


