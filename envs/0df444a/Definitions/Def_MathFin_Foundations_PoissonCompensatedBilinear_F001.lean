-- Prove2me | Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F001
-- name    : MathFin_Foundations_PoissonCompensatedBilinear_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:34:52.108379+00:00
-- url     : https://prove2.me/theorems/32fad843-2a78-477c-92a4-962c82a3bd48
-- title:
--   Source declarations: MathFin.Foundations.PoissonCompensatedBilinear
-- statement:
--   Source-preserving extracted declarations from MathFin.Foundations.PoissonCompensatedBilinear. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F001
import Definitions.Def_SourceProof_09a1d2ad90db017031836da3

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

/-- The past `σ`-algebra is monotone in time: `pastSigma s ≤ pastSigma s'` for `s ≤ s'`. -/
private lemma pastSigma_mono (N : PoissonRandomMeasure P ν) {s s' : ℝ} (h : s ≤ s') :
    N.pastSigma s ≤ N.pastSigma s' :=
  iSup₂_le fun C hC => le_iSup₂_of_le C
    ⟨hC.1.trans (Set.prod_mono (Set.Iic_subset_Iic.mpr h) le_rfl), hC.2⟩ le_rfl
/-- The past `σ`-algebra at `s` sits inside the disjoint-region `σ`-algebra of any set lying
strictly after `s` (`D ⊆ (s, ∞) × E`) — the generalisation of `pastSigma_le_regionSigma` from a
future box to an arbitrary future set. -/
private lemma pastSigma_le_regionSigma_sub (N : PoissonRandomMeasure P ν) {s : ℝ}
    {D : Set (ℝ × E)} (hD : D ⊆ Set.Ioi s ×ˢ Set.univ) :
    N.pastSigma s ≤ N.regionSigma D := by
  refine iSup₂_le fun C hC => le_iSup₂_of_le C ⟨?_, hC.2⟩ le_rfl
  refine Set.disjoint_of_subset hC.1 hD (Set.disjoint_left.mpr ?_)
  rintro ⟨x, e⟩ hx hxD
  exact absurd (Set.mem_Iic.mp (Set.mem_prod.mp hx).1)
    (not_le.mpr (Set.mem_Ioi.mp (Set.mem_prod.mp hxD).1))
/-- A compensated increment on `p` is measurable for the disjoint-region `σ`-algebra of any set `q`
disjoint from `p`. -/
private lemma compensated_measurable_regionSigma (N : PoissonRandomMeasure P ν)
    {p q : Set (ℝ × E)} (hpq : Disjoint p q) (hpms : MeasurableSet p) :
    Measurable[N.regionSigma q] (N.compensated p) := by
  show Measurable[N.regionSigma q] fun ω => (N.N ω p).toReal - (referenceIntensity ν p).toReal
  have hc : Measurable[N.regionSigma q] fun ω => N.N ω p :=
    (measurable_iff_comap_le.mpr le_rfl).mono (le_iSup₂_of_le p ⟨hpq, hpms⟩ le_rfl) le_rfl
  exact hc.ennreal_toReal.sub measurable_const
/-- **Past-adapted `⟂` future compensated increment (general future set).** For `φ` adapted at `s`
and `D ⊆ (s, ∞) × E`, `φ ⟂ Ñ(D)`. The set-level version of `adapted_indepFun_compensated`. -/
private lemma adapted_indepFun_compensated_sub (N : PoissonRandomMeasure P ν) {s : ℝ}
    {D : Set (ℝ × E)} (hDms : MeasurableSet D) (hDsub : D ⊆ Set.Ioi s ×ˢ Set.univ)
    {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ) :
    IndepFun φ (N.compensated D) P := by
  have hfield : Indep (N.regionSigma D)
      (MeasurableSpace.comap (fun ω => N.N ω D) inferInstance) P :=
    N.indep_of_disjoint_region hDms
  have hφ_le : MeasurableSpace.comap φ inferInstance ≤ N.regionSigma D :=
    le_trans (measurable_iff_comap_le.mp (show Measurable[N.pastSigma s] φ from hφ))
      (pastSigma_le_regionSigma_sub N hDsub)
  have hraw : IndepFun φ (fun ω => N.N ω D) P :=
    (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le_left hfield hφ_le)
  have hcomp := hraw.comp (φ := (id : ℝ → ℝ))
    (ψ := fun x : ℝ≥0∞ => x.toReal - (referenceIntensity ν D).toReal)
    measurable_id (by fun_prop)
  simp only [Function.comp_def, id_eq] at hcomp
  exact hcomp
/-- **Weighted diagonal energy (general future set).** For `φ` adapted at `s`, integrable, and
`D ⊆ (s, ∞) × E`, `𝔼[φ · Ñ(D)²] = 𝔼[φ] · ν̂(D)`: `φ ⟂ Ñ(D)²` and `𝔼[Ñ(D)²] = ν̂(D)`. -/
private lemma integral_adapted_mul_compensated_sq_sub (N : PoissonRandomMeasure P ν) {s : ℝ}
    {D : Set (ℝ × E)} (hDms : MeasurableSet D) (hDsub : D ⊆ Set.Ioi s ×ˢ Set.univ)
    (hDfin : referenceIntensity ν D ≠ ⊤) {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ)
    (hφint : Integrable φ P) :
    ∫ ω, φ ω * (N.compensated D ω) ^ 2 ∂P = (∫ ω, φ ω ∂P) * (referenceIntensity ν D).toReal := by
  have hindep2 := (adapted_indepFun_compensated_sub N hDms hDsub hφ).comp
    (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ => x ^ 2) measurable_id (by fun_prop)
  simp only [Function.comp_def, id_eq] at hindep2
  have hÑsq : Integrable (fun ω => (N.compensated D ω) ^ 2) P :=
    (_root_.Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hDms hDfin).integrable_sq
  rw [hindep2.integral_fun_mul_eq_mul_integral hφint.aestronglyMeasurable
        hÑsq.aestronglyMeasurable, compensated_integral_sq N hDms hDfin]
end MathFin


