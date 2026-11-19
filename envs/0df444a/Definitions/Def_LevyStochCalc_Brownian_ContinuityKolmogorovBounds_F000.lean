-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F000
-- name    : LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:13:53.99484+00:00
-- url     : https://prove2.me/theorems/259a6b9f-11cc-487d-bdb5-e44604051163
-- title:
--   Source declarations: LevyStochCalc.Brownian.ContinuityKolmogorovBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ContinuityKolmogorovBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F001
import Definitions.Def_SourceProof_8934056b1c7613716f8c73e6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-sure Hölder bounds from the Kolmogorov condition

The probabilistic half of the Kolmogorov-Chentsov construction. For a process `X` with
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M · edist s t ^ q`, Markov's inequality bounds each
increment tail by `M · edist s t ^ q / lam ^ p`; summing over the `2^n` level-`n` dyadic
intervals of `[0, 1]` makes the bad sets `{|increment| > ((1/2)^α)^n}` summable whenever
`α * p < q - 1`, so Borel-Cantelli gives an almost-sure bound on all small-scale dyadic
increments. Feeding those bounds to the deterministic chaining yields almost-sure local
`α`-Hölder continuity on the dyadics, and the convergence-in-measure form of the same tail
bound identifies the dyadic extension as a modification of `X`
(`kolmogorov_modification_ae_eq`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Markov / Chebyshev bound from the Kolmogorov condition.**

For a process satisfying the Kolmogorov moment condition
`∫⁻ ω, edist (X s ω) (X t ω)^p ∂P ≤ M · edist s t ^ q` and any threshold
`0 < lam < ⊤`,

  `P {ω | lam ≤ edist (X s ω) (X t ω)} ≤ M · edist s t ^ q / lam ^ p`.

This is the per-pair tail bound underlying both the convergence-in-measure
argument (`kolmogorov_modification_ae_eq`) and the per-dyadic-level Borel–
Cantelli step of the continuous-modification construction. -/
lemma kolmogorov_markov_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ≥0∞} (hlam_pos : 0 < lam) (hlam_top : lam ≠ ⊤) :
    P {ω | lam ≤ edist (X s ω) (X t ω)}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / lam ^ p := by
  have hp_pos : 0 < p := hX.p_pos
  -- {lam ≤ edist} = {lam^p ≤ edist^p} since `· ^ p` is strictly monotone.
  have h_set_eq :
      {ω | lam ≤ edist (X s ω) (X t ω)}
        = {ω | lam ^ p ≤ edist (X s ω) (X t ω) ^ p} := by
    ext ω; exact (ENNReal.rpow_le_rpow_iff hp_pos).symm
  have h_edist_aemeas : AEMeasurable
      (fun ω => edist (X s ω) (X t ω) ^ p) P :=
    ((hX.measurable_edist (s := s) (t := t)).pow_const p).aemeasurable
  have h_Kol : ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
      ≤ (M : ℝ≥0∞) * edist s t ^ q := hX.kolmogorovCondition s t
  have h_Markov :
      lam ^ p * P {ω | lam ^ p ≤ edist (X s ω) (X t ω) ^ p}
        ≤ ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P :=
    MeasureTheory.mul_meas_ge_le_lintegral₀ h_edist_aemeas (lam ^ p)
  have h_chain :
      lam ^ p * P {ω | lam ≤ edist (X s ω) (X t ω)}
        ≤ (M : ℝ≥0∞) * edist s t ^ q := by
    rw [h_set_eq]; exact le_trans h_Markov h_Kol
  have hlamp_pos : 0 < lam ^ p := by
    apply ENNReal.rpow_pos_of_nonneg hlam_pos
    exact hp_pos.le
  have hlamp_ne_top : lam ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp_pos.le hlam_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hlamp_pos.ne') (Or.inl hlamp_ne_top),
      mul_comm]
  exact h_chain
/-- Real-threshold form of the tail bound: for `lam > 0`,
`P {ω | lam < |X s ω − X t ω|} ≤ M · edist s t ^ q / (ofReal lam) ^ p`. -/
lemma kolmogorov_real_tail_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    P {ω | lam < |X s ω - X t ω|}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / ENNReal.ofReal lam ^ p := by
  refine le_trans (measure_mono ?_)
    (kolmogorov_markov_bound P X hX s t
      (ENNReal.ofReal_pos.mpr hlam) ENNReal.ofReal_ne_top)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
/-- **Lemma A: per-level bad-set bound.** The union over level-`n` dyadic
intervals in `[0,1]` of the events `{ |increment| > ((1/2)^α)^n }` has measure
`≤ ofReal((M:ℝ)·ρⁿ)` with `ρ = (1/2)^{q−αp−1}`. (Borel–Cantelli summability
follows when `αp < q−1`, i.e. `ρ < 1`.) -/
lemma kc_level_bad_measure
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (n : ℕ) :
    P (⋃ k ∈ Finset.range (2 ^ n),
        {ω | ((1 / 2 : ℝ) ^ α) ^ n
            < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|})
      ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n) := by
  set r : ℝ := (1 / 2 : ℝ) ^ α with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) α
  have hrn0 : 0 < r ^ n := pow_pos hr0 n
  have hhalf_n : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hrnp0 : (0 : ℝ) < (r ^ n) ^ p := Real.rpow_pos_of_pos hrn0 p
  -- Per-interval Markov term, converted to `ofReal`.
  have hterm : ∀ k ∈ Finset.range (2 ^ n),
      P {ω | r ^ n < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|}
        ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ n) ^ q / (r ^ n) ^ p) := by
    intro k _
    have hb := kolmogorov_real_tail_bound P X hX
      (((k : ℝ) + 1) / 2 ^ n) ((k : ℝ) / 2 ^ n) hrn0
    refine le_trans hb (le_of_eq ?_)
    have hedist : edist (((k : ℝ) + 1) / 2 ^ n) ((k : ℝ) / 2 ^ n)
        = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      rw [edist_dist, Real.dist_eq]
      congr 1
      rw [show ((k : ℝ) + 1) / 2 ^ n - (k : ℝ) / 2 ^ n = (1 / 2 : ℝ) ^ n from by
        rw [div_pow, one_pow]; ring]
      exact abs_of_pos hhalf_n
    rw [hedist, ENNReal.ofReal_rpow_of_pos hhalf_n,
        ENNReal.ofReal_rpow_of_pos hrn0, ← ENNReal.ofReal_coe_nnreal (p := M),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos hrnp0]
  refine le_trans (measure_biUnion_finset_le (Finset.range (2 ^ n)) _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      show ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) from by
        rw [← ENNReal.ofReal_natCast]; norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
  refine le_of_eq ?_
  congr 1
  rw [hr_def, show (2 : ℝ) ^ n
        * ((M : ℝ) * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p)
      = (M : ℝ) * ((2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q
          / (((1 / 2 : ℝ) ^ α) ^ n) ^ p) from by ring,
      _root_.Prove2MeSourceProof.h_8934056b1c7613716f8c73e6]
end LevyStochCalc.Brownian.Continuity


