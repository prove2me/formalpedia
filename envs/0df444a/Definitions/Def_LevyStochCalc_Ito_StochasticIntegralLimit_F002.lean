-- Prove2me | Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F002
-- name    : LevyStochCalc_Ito_StochasticIntegralLimit_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:56:11.284808+00:00
-- url     : https://prove2.me/theorems/d139e7e8-a172-4fd7-a2ee-3d46cfc24986
-- title:
--   Source declarations: LevyStochCalc.Ito.StochasticIntegralLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.StochasticIntegralLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F001
import Definitions.Def_LevyStochCalc_Poisson_SmallJump_F000
import Definitions.Def_SourceProof_6043a31a9e304448bc837b3a
import Definitions.Def_SourceProof_8cda0751354c6a4a5b9ce7f5
import Definitions.Def_SourceProof_9eee3f7abd2657ef6c535363
import Definitions.Def_SourceProof_e6dcd6270ba2ccc8443bc922

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of stochastic integrals along dominated sequences of integrands

A sequence of integrands converging pointwise almost everywhere and dominated by a
square-integrable function converges to its limit in the energy norm, over `P ⊗ ds` for a
Brownian integrand and over `P ⊗ ds ⊗ ν` for a marked one. Through the `L²` isometries of the
Itô and compensated Itô–Lévy integrals this transfers to the integrals themselves: they converge
in `L²`, hence almost surely along a subsequence.

## Main statements

All statements live in the `LevyStochCalc.Ito.IntegralLimit` namespace.

* `tendsto_lintegral_sq_sub_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds`.
* `tendsto_lintegral_sq_sub_mark_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds ⊗ ν`.
* `tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated` and
  `exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated` — the Itô integrals of a
  dominated sequence of integrands converge in `L²`, and almost surely along a strictly monotone
  subsequence.
* `tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated` and
  `exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated` — the same for the
  compensated Itô–Lévy integral.
* `tendsto_lintegral_sq_stochasticIntegral_markCut_compl` and
  `exists_seq_ae_tendsto_stochasticIntegral_markCut_compl` — the compensated Itô–Lévy integrals
  of an integrand cut to the complements of a family of mark sets that eventually misses almost
  every mark converge to the compensated Itô–Lévy integral of the integrand; the suffix
  `_of_antitone` names the same conclusions under an antitone family with null intersection.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.4 (Thm 4.4.7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.IntegralLimit

universe u v

section Basic

variable {α : Type*} [MeasurableSpace α]

end Basic

section Unmarked

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]

end Marked

section Subsequence

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Subsequence

section Brownian

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Brownian.IsBrownianFiltration W ℱ)
  (H : ℕ → Ω → ℝ → ℝ) (H₀ : Ω → ℝ → ℝ) (g : Ω → ℝ → ℝ)
  (hHm : ∀ m, Measurable (Function.uncurry (H m)))
  (hHp : ∀ m, Probability.ProgressivelyMeasurable ℱ (H m))
  (hHq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H m ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hH₀m : Measurable (Function.uncurry H₀))
  (hH₀p : Probability.ProgressivelyMeasurable ℱ H₀)
  (hH₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in
/-- The Itô integrals of a sequence of admissible integrands converging pointwise almost
everywhere and dominated by a square-integrable function converge in `L²`. -/
theorem tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated
    (hgm : Measurable (Function.uncurry g)) {T : ℝ} (hT : 0 < T)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => H m ω s) atTop (𝓝 (H₀ ω s)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ‖H m ω s‖ ≤ g ω s)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Tendsto (fun m => ∫⁻ ω,
        (‖Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (H m) (hHm m) (hHp m) (hHq m) T ω
          - Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₀ hH₀m hH₀p hH₀q T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) :=
  Brownian.Ito.tendsto_lintegral_sq_stochInt_of_tendsto_energy W ℱ hℱ H H₀ hHm hHp hHq
    hH₀m hH₀p hH₀q hT
    (_root_.Prove2MeSourceProof.h_8cda0751354c6a4a5b9ce7f5 hHm hH₀m hgm hpt hdom hg)
include hℱ in
/-- The Itô integrals of a sequence of admissible integrands converging pointwise almost
everywhere and dominated by a square-integrable function converge almost surely along a strictly
monotone subsequence. -/
theorem exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated
    (hgm : Measurable (Function.uncurry g)) {T : ℝ} (hT : 0 < T)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => H m ω s) atTop (𝓝 (H₀ ω s)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ‖H m ω s‖ ≤ g ω s)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i : ℕ, i ≤ k i) ∧ ∀ᵐ ω ∂P, Tendsto
      (fun m => Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (H (k m))
        (hHm (k m)) (hHp (k m)) (hHq (k m)) T ω) atTop
      (𝓝 (Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₀ hH₀m hH₀p hH₀q T ω)) := by
  obtain ⟨ms, hmsge, hms⟩ :=
    _root_.Prove2MeSourceProof.h_e6dcd6270ba2ccc8443bc922 (ι := Unit)
      (fun _ => W) ℱ (fun _ => hℱ) (fun m _ => H m) (fun _ => H₀) (fun m _ => hHm m)
      (fun m _ => hHp m) (fun m _ => hHq m) (fun _ => hH₀m) (fun _ => hH₀p) (fun _ => hH₀q) hT
      fun _ => _root_.Prove2MeSourceProof.h_8cda0751354c6a4a5b9ce7f5 hHm hH₀m hgm hpt hdom hg
  refine _root_.Prove2MeSourceProof.h_9eee3f7abd2657ef6c535363 (P := P)
    (u := fun j ω => Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (H j)
      (hHm j) (hHp j) (hHq j) T ω)
    (v := fun ω => Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₀ hH₀m hH₀p hH₀q T ω)
    hmsge ?_
  filter_upwards [hms] with ω hω
  exact hω ()
end Brownian

section Compensated

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : ℕ → Ω → ℝ → E → ℝ) (φ₀ : Ω → ℝ → E → ℝ) (g : Ω → ℝ → E → ℝ)
  (hφm : ∀ m, Measurable fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2)
  (hφp : ∀ m, Probability.MarkedProgressivelyMeasurable ℱ (φ m))
  (hφq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ m ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hφ₀m : Measurable fun p : Ω × ℝ × E => φ₀ p.1 p.2.1 p.2.2)
  (hφ₀p : Probability.MarkedProgressivelyMeasurable ℱ φ₀)
  (hφ₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- The compensated Itô–Lévy integrals of a sequence of admissible marked integrands converging
pointwise almost everywhere and dominated by a square-integrable function converge in `L²`. -/
theorem tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated
    (hgm : Measurable fun p : Ω × ℝ × E => g p.1 p.2.1 p.2.2) {T : ℝ} (hT : 0 < T)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => φ m ω s e) atTop (𝓝 (φ₀ ω s e)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      ‖φ m ω s e‖ ≤ g ω s e)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Tendsto (fun m => ∫⁻ ω,
        (‖stochasticIntegral N ℱ hℱ (φ m) (hφm m) (hφp m) (hφq m) T ω
          - stochasticIntegral N ℱ hℱ φ₀ hφ₀m hφ₀p hφ₀q T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) :=
  (_root_.Prove2MeSourceProof.h_6043a31a9e304448bc837b3a hφm hφ₀m hgm hpt hdom hg).congr fun m =>
    (itoIsometry_diff_compensated N ℱ hℱ (φ m) φ₀ (hφm m) hφ₀m (hφp m) hφ₀p
      (hφq m) hφ₀q T hT).symm
end Compensated

section MarkCut

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (A : ℕ → Set E) (hA : ∀ m, MeasurableSet (A m))

end MarkCut

end LevyStochCalc.Ito.IntegralLimit


