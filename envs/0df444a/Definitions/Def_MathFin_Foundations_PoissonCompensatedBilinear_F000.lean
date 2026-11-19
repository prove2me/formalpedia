-- Prove2me | Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F000
-- name    : MathFin_Foundations_PoissonCompensatedBilinear_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:33:47.600349+00:00
-- url     : https://prove2.me/theorems/3099eb0d-31ae-453e-aca0-2d39b95a20b5
-- title:
--   Source declarations: MathFin.Foundations.PoissonCompensatedBilinear
-- statement:
--   Source-preserving extracted declarations from MathFin.Foundations.PoissonCompensatedBilinear. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F001

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

/-- **Counts are a.e. finite** on finite-intensity sets: `N(·, B)` has law `Poisson(ν̂ B)`, which is
supported on `ℕ ⊂ ℝ≥0∞`, so `⊤` is a null value. -/
theorem ae_count_ne_top (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, N.N ω B ≠ ⊤ := by
  rw [ae_iff]
  have hset : {ω | ¬ N.N ω B ≠ ⊤} = (fun ω => N.N ω B) ⁻¹' {⊤} := by
    ext ω; simp [Set.mem_preimage]
  rw [hset, ← Measure.map_apply (N.measurable_eval hB) (measurableSet_singleton ⊤),
    N.poisson_law hB hfin]
  show poissonMeasureENN (referenceIntensity ν B).toNNReal {⊤} = 0
  unfold poissonMeasureENN
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton ⊤),
    show (fun n : ℕ => (n : ℝ≥0∞)) ⁻¹' {(⊤ : ℝ≥0∞)} = ∅ from by
      ext n
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact ENNReal.natCast_ne_top n]
  exact measure_empty
/-- **Additivity of the compensated increment** on disjoint finite-intensity sets:
`Ñ(X ∪ Y) = Ñ(X) + Ñ(Y)` a.e. (count additivity + a.e. finiteness). -/
theorem compensated_add_of_disjoint (N : PoissonRandomMeasure P ν) {X Y : Set (ℝ × E)}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hdisj : Disjoint X Y)
    (hXfin : referenceIntensity ν X ≠ ⊤) (hYfin : referenceIntensity ν Y ≠ ⊤) :
    ∀ᵐ ω ∂P, N.compensated (X ∪ Y) ω = N.compensated X ω + N.compensated Y ω := by
  filter_upwards [ae_count_ne_top N hX hXfin, ae_count_ne_top N hY hYfin] with ω hXω hYω
  simp only [PoissonRandomMeasure.compensated]
  rw [measure_union hdisj hY, ENNReal.toReal_add hXω hYω,
    show referenceIntensity ν (X ∪ Y) = referenceIntensity ν X + referenceIntensity ν Y from
      measure_union hdisj hY, ENNReal.toReal_add hXfin hYfin]
  ring
/-- **Uncorrelated on disjoint regions**: `𝔼[Ñ(X)·Ñ(Y)] = 0` for disjoint measurable `X, Y` (finite
`Y`). `Ñ(X)` lives on the region disjoint from `Y`, so `Ñ(X) ⟂ Ñ(Y)`; `Ñ(Y)` is mean-zero. -/
theorem compensated_mul_compensated_disjoint (N : PoissonRandomMeasure P ν) {X Y : Set (ℝ × E)}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hdisj : Disjoint X Y)
    (hYfin : referenceIntensity ν Y ≠ ⊤) :
    ∫ ω, N.compensated X ω * N.compensated Y ω ∂P = 0 := by
  refine _root_.Prove2MeSourceProof.h_8e8c6bf1745159f9e5de9b8d N hY hYfin ?_
  show Measurable[N.regionSigma Y] fun ω => (N.N ω X).toReal - (referenceIntensity ν X).toReal
  have hc : Measurable[N.regionSigma Y] fun ω => N.N ω X :=
    (measurable_iff_comap_le.mpr le_rfl).mono (le_iSup₂_of_le X ⟨hdisj, hX⟩ le_rfl) le_rfl
  exact hc.ennreal_toReal.sub measurable_const
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

end MathFin


