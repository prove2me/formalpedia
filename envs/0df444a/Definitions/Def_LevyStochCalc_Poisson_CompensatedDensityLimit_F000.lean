-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F000
-- name    : LevyStochCalc_Poisson_CompensatedDensityLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:55:59.209009+00:00
-- url     : https://prove2.me/theorems/a0a3e592-ec1f-420a-ad92-e5255a449ff3
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cross-resolution Cauchy estimate and the `L²` limit

The isometry for the difference of two step integrals at different dyadic resolutions, the
resulting Cauchy estimate for the Euler sums of a bounded predictable integrand, and the limit
in `L²(P)` it produces. Closing bricks on the regularity of monotone `ℝ≥0∞`-valued functions of
time and the right-continuity of the intensity of shrinking time-mark boxes support the path
regularity of that limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The compensated integral of a finite-intensity box is in `L²(P)`. -/
lemma compensated_memLp
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    MeasureTheory.MemLp (fun ω => N.compensated B ω) 2 P := by
  have hmeas : Measurable (fun ω => N.compensated B ω) := by
    change Measurable (fun ω => (N.N ω B).toReal
      - (LevyStochCalc.Poisson.referenceIntensity ν B).toReal)
    exact ((N.measurable_eval hB).ennreal_toReal).sub_const _
  exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr
    (_root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hB hfin)
/-- A bounded measurable factor preserves `L²`-membership. -/
lemma memLp_bdd_mul {P : Measure Ω} {f g : Ω → ℝ} (hf : Measurable f) {M : ℝ}
    (hfb : ∀ ω, |f ω| ≤ M) (hg : MeasureTheory.MemLp g 2 P) :
    MeasureTheory.MemLp (fun ω => f ω * g ω) 2 P := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)).mpr ?_
  refine MeasureTheory.Integrable.mono' (hg.integrable_sq.const_mul (M ^ 2))
    ((hf.aemeasurable.mul hg.aemeasurable).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hfb ω)
  simp only [Pi.mul_apply, Real.norm_eq_abs]
  rw [show (f ω * g ω) ^ 2 = f ω ^ 2 * g ω ^ 2 from by ring, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right
    (by nlinarith [hfb ω, abs_nonneg (f ω), sq_abs (f ω), hM0]) (sq_nonneg _)
/-- The Euler step integral `∑ᵢ∑ₖ ciₖ·Ñ((pᵢ,pᵢ₊₁]×Biₖ)` is in `L²(P)`. -/
lemma eulerStepIntegral_memLp
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ)
    {Ki : Fin N₀ → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hBif : ∀ i k, ν (Bi i k) ≠ ⊤)
    (hcib : ∀ i k, ∃ M, ∀ ω, |ci i k ω| ≤ M) (hcim : ∀ i k, Measurable (ci i k)) :
    MeasureTheory.MemLp (fun ω => ∑ i : Fin N₀, ∑ k₀, ci i k₀ ω
      * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi i k₀) ω) 2 P := by
  have hterm : ∀ (i : Fin N₀) (k₀ : Fin (Ki i)),
      MeasureTheory.MemLp (fun ω => ci i k₀ ω
        * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi i k₀) ω) 2 P := by
    intro i k₀
    obtain ⟨M, hM⟩ := hcib i k₀
    exact memLp_bdd_mul (hcim i k₀) hM
      (compensated_memLp N (measurableSet_Ioc.prod (hBim i k₀))
        (referenceIntensity_Ioc_prod_ne_top (hBif i k₀)))
  exact MeasureTheory.memLp_finsetSum Finset.univ (fun i _ =>
    MeasureTheory.memLp_finsetSum Finset.univ (fun k₀ _ => hterm i k₀))
/-- `∫⁻ ‖g‖₊² = ofReal (∫ g²)` for `g ∈ L²(P)`. -/
lemma lintegral_sq_eq_ofReal_integral {P : Measure Ω} {g : Ω → ℝ}
    (hg : MeasureTheory.MemLp g 2 P) :
    ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (g ω) ^ 2 ∂P) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  refine lintegral_congr (fun ω => ?_)
  rw [show (‖g ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖g ω‖ from (ofReal_norm _).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
/-! ### Path regularity bricks (toward the càdlàg conjunct of #6)

The compensated step integral is càdlàg in `t`: the compensator part is continuous,
and the count part is a Stieltjes function of `t` (monotone, right-continuous with
left limits via measure continuity). These bricks give the right-continuity and
left-limit existence of monotone `ℝ≥0∞`-valued functions, the substrate for the
Doob `L²` càdlàg modification. -/

end LevyStochCalc.Poisson.Compensated


