-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001
-- name    : LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:53:15.005621+00:00
-- url     : https://prove2.me/theorems/ef829f01-996c-44db-8acc-b7a55d566f64
-- title:
--   Source declarations: LevyStochCalc.Brownian.ContinuityKolmogorovBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ContinuityKolmogorovBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F000
import Definitions.Def_SourceProof_acac0f8ce0c5f96fd64efb3a

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

/-- **Translation invariance of the Kolmogorov condition.** If `X` satisfies
the Kolmogorov condition, so does the time-shifted process `s ↦ X (s + a)`
(the bound depends only on `edist s t = edist (s+a) (t+a)`). Used to transport
the `[0,1]` construction to every interval `[j, j+1]`. -/
lemma isKolmogorovProcess_comp_add_right
    {P : Measure Ω} (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (a : ℝ) :
    ProbabilityTheory.IsKolmogorovProcess (fun s ω => X (s + a) ω) P p q M where
  measurablePair s t := hX.measurablePair (s + a) (t + a)
  kolmogorovCondition s t := by
    have he : edist s t = edist (s + a) (t + a) := by
      rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
          show (s + a) - (t + a) = s - t from by ring]
    rw [he]
    exact hX.kolmogorovCondition (s + a) (t + a)
  p_pos := hX.p_pos
  q_pos := hX.q_pos
/-- **Lemma B: a.s. dyadic increment bound (Borel–Cantelli).** When
`α·p < q − 1`, almost every path has, for some level `N`, all consecutive
level-`n` dyadic increments in `[0,1]` bounded by `((1/2)^α)^n` for every
`n ≥ N`. This supplies the hypothesis of `dyadic_holder_chaining`. -/
lemma kc_ae_increment_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|
        ≤ ((1 / 2 : ℝ) ^ α) ^ n := by
  set ρ : ℝ := (1 / 2 : ℝ) ^ (q - α * p - 1) with hρ_def
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  set A : ℕ → Set Ω := fun n => ⋃ k ∈ Finset.range (2 ^ n),
      {ω | ((1 / 2 : ℝ) ^ α) ^ n
          < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|} with hA_def
  have hAle : ∀ n, P (A n) ≤ ENNReal.ofReal ((M : ℝ) * ρ ^ n) := fun n =>
    kc_level_bad_measure P X hX n
  have hsummable_real : Summable (fun n => (M : ℝ) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have htsum_ne : (∑' n, P (A n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hAle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable_real]
    exact ENNReal.ofReal_ne_top
  have hlimsup : P (Filter.limsup A Filter.atTop) = 0 :=
    measure_limsup_atTop_eq_zero htsum_ne
  have hae : ∀ᵐ ω ∂P, ω ∉ Filter.limsup A Filter.atTop := by
    rw [ae_iff]; simp only [not_not, Set.setOf_mem_eq]; exact hlimsup
  filter_upwards [hae] with ω hω
  rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently,
      Filter.eventually_atTop] at hω
  obtain ⟨N, hN⟩ := hω
  refine ⟨N, fun n hn k hk0 hk1 => ?_⟩
  have hωn : ω ∉ A n := hN n hn
  rw [hA_def] at hωn
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hωn
  have hk'mem : k.toNat ∈ Finset.range (2 ^ n) := by
    rw [Finset.mem_range]
    have hcast2 : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
    omega
  have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0]
  have hb := hωn k.toNat hk'mem
  rw [hcast] at hb
  exact hb
/-- **Per-interval a.s. Hölder.** For `αp < q − 1`, almost every path is
α-Hölder (at small scales) on the dyadics of every unit interval `[j, j+1]`.
Obtained by transporting `dyadic_holder_chaining` (on `[0,1]`) to `[j,j+1]` via
the time-shifted process `X(·+j)` (translation-invariant Kolmogorov condition),
intersected over the countable family `j : ℤ`. -/
lemma kc_ae_interval_holder
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ j : ℤ, ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧
      ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
        (j : ℝ) ≤ s → s ≤ (j : ℝ) + 1 → (j : ℝ) ≤ t → t ≤ (j : ℝ) + 1 →
        |s - t| ≤ (1 / 2 : ℝ) ^ N → |X s ω - X t ω| ≤ K * |s - t| ^ α := by
  rw [MeasureTheory.ae_all_iff]
  intro j
  have hXj : ProbabilityTheory.IsKolmogorovProcess (fun s ω => X (s + (j : ℝ)) ω) P p q M :=
    isKolmogorovProcess_comp_add_right X hX j
  filter_upwards [kc_ae_increment_bound P (fun s ω => X (s + (j : ℝ)) ω) hXj hαpq] with ω hω
  obtain ⟨N, hN⟩ := hω
  obtain ⟨K, hK0, hKbound⟩ :=
    _root_.Prove2MeSourceProof.h_acac0f8ce0c5f96fd64efb3a (f := fun u => X (u + (j : ℝ)) ω) (α := α) (C := 1) (N := N)
      hα0 (by norm_num) (fun n hn k hk0 hk1 => by
        rw [one_mul]
        simp only [Int.cast_add, Int.cast_one]
        exact hN n hn k hk0 hk1)
  refine ⟨K, N, hK0, fun s hs t ht hjs hsj1 hjt htj1 hst => ?_⟩
  have hu : s - (j : ℝ) ∈ dyadicRationals := sub_intCast_mem_dyadicRationals hs j
  have hv : t - (j : ℝ) ∈ dyadicRationals := sub_intCast_mem_dyadicRationals ht j
  have hKb := hKbound (s - (j : ℝ)) hu (t - (j : ℝ)) hv (by linarith) (by linarith)
    (by linarith) (by linarith)
    (by rw [show s - (j : ℝ) - (t - (j : ℝ)) = s - t from by ring]; exact hst)
  rw [show s - (j : ℝ) + (j : ℝ) = s from by ring,
      show t - (j : ℝ) + (j : ℝ) = t from by ring,
      show s - (j : ℝ) - (t - (j : ℝ)) = s - t from by ring] at hKb
  exact hKb
end LevyStochCalc.Brownian.Continuity


