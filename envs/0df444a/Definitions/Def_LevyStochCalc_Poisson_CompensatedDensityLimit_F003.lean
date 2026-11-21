-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F003
-- name    : LevyStochCalc_Poisson_CompensatedDensityLimit_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:59:40.264198+00:00
-- url     : https://prove2.me/theorems/ff2edd6c-a82d-44f9-9a99-1c7eee8188d2
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

/-! ### Path regularity bricks (toward the càdlàg conjunct of #6)

The compensated step integral is càdlàg in `t`: the compensator part is continuous,
and the count part is a Stieltjes function of `t` (monotone, right-continuous with
left limits via measure continuity). These bricks give the right-continuity and
left-limit existence of monotone `ℝ≥0∞`-valued functions, the substrate for the
Doob `L²` càdlàg modification. -/

/-- **Right-continuity of a monotone `ℝ≥0∞` function from sequential right-continuity.**
If `g` is monotone and `g (t + 1/(n+1)) → g t`, then `g` is right-continuous at `t`. -/
lemma monotone_tendsto_nhdsWithin_Ioi {g : ℝ → ℝ≥0∞} (hg : Monotone g) {t : ℝ}
    (hseq : Filter.Tendsto (fun n : ℕ => g (t + 1 / (n + 1))) Filter.atTop (nhds (g t))) :
    Filter.Tendsto g (nhdsWithin t (Set.Ioi t)) (nhds (g t)) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun s hs => ?_))
    exact hl.trans_le (hg (le_of_lt hs))
  · obtain ⟨N, hN⟩ := (hseq.eventually_lt_const hu).exists
    have hδ : t < t + 1 / ((N : ℝ) + 1) := lt_add_of_pos_right t (by positivity)
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [Iio_mem_nhds hδ] with s hs
    exact (hg (le_of_lt hs)).trans_lt hN
/-- **Left-limit existence for a monotone `ℝ≥0∞` function.** A monotone function has a
left limit at `t`, namely `⨆_{s<t} g s` (no continuity hypothesis needed). -/
lemma monotone_tendsto_nhdsWithin_Iio {g : ℝ → ℝ≥0∞} (hg : Monotone g) (t : ℝ) :
    Filter.Tendsto g (nhdsWithin t (Set.Iio t)) (nhds (⨆ s : {s : ℝ // s < t}, g s.1)) := by
  set L : ℝ≥0∞ := ⨆ s : {s : ℝ // s < t}, g s.1 with hL
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · -- `l < L = ⨆ g s`, so some `s₀ < t` has `l < g s₀`; for `s ∈ (s₀, t)`, `g s ≥ g s₀ > l`.
    rw [hL, lt_iSup_iff] at hl
    obtain ⟨⟨s₀, hs₀t⟩, hs₀⟩ := hl
    refine Filter.eventually_inf_principal.mpr ?_
    filter_upwards [Ioi_mem_nhds hs₀t] with s hs _
    exact hs₀.trans_le (hg (le_of_lt hs))
  · -- `g s ≤ L < u` for all `s < t`.
    refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun s hs => ?_))
    exact lt_of_le_of_lt (le_iSup (fun s : {s : ℝ // s < t} => g s.1) ⟨s, hs⟩) hu
/-- The clamped time-rectangle base `(min a s, min b s]` grows with `s` (for `a ≤ b`):
when `s ≤ a` it is empty, and for `s > a` it is `(a, min b s]`, increasing in `s`. -/
lemma minIoc_subset {a b : ℝ} (hab : a ≤ b) {s s' : ℝ} (hss : s ≤ s') :
    Set.Ioc (min a s) (min b s) ⊆ Set.Ioc (min a s') (min b s') := by
  rintro x ⟨hx1, hx2⟩
  by_cases hsa : s ≤ a
  · rw [min_eq_right hsa] at hx1
    rw [min_eq_right (hsa.trans hab)] at hx2
    exact absurd (hx1.trans_le hx2) (lt_irrefl s)
  · push Not at hsa
    refine ⟨?_, hx2.trans (min_le_min (le_refl b) hss)⟩
    rw [min_eq_left (hsa.le.trans hss)]
    rwa [min_eq_left hsa.le] at hx1
/-- The clamped base `(min a s, min b s]` is always contained in `(a, b]` (for `a ≤ b`). -/
lemma minIoc_subset_Ioc {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Set.Ioc (min a s) (min b s) ⊆ Set.Ioc a b := by
  rintro x ⟨hx1, hx2⟩
  by_cases hsa : s ≤ a
  · rw [min_eq_right hsa] at hx1
    rw [min_eq_right (hsa.trans hab)] at hx2
    exact absurd (hx1.trans_le hx2) (lt_irrefl s)
  · push Not at hsa
    rw [min_eq_left hsa.le] at hx1
    exact ⟨hx1, hx2.trans (min_le_left b s)⟩
/-- **Count-part right-continuity.** For `a ≤ b`, a finite-mass mark set `A`, and a
measure `m` finite on `(a,b]×A`, the clamped count `s ↦ m((min a s, min b s]×A)` is
right-continuous (measure continuity from above along `t + 1/(n+1) ↓ t`). -/
lemma measure_minIoc_prod_rightCont (m : Measure (ℝ × E)) {a b : ℝ} (hab : a ≤ b)
    {A : Set E} (hA : MeasurableSet A) (hfin : m (Set.Ioc a b ×ˢ A) ≠ ⊤) (t : ℝ) :
    Filter.Tendsto (fun s => m (Set.Ioc (min a s) (min b s) ×ˢ A))
      (nhdsWithin t (Set.Ioi t)) (nhds (m (Set.Ioc (min a t) (min b t) ×ˢ A))) := by
  have hgmono : Monotone (fun s => m (Set.Ioc (min a s) (min b s) ×ˢ A)) := fun s s' hss =>
    measure_mono (Set.prod_mono (minIoc_subset hab hss) (le_refl A))
  refine monotone_tendsto_nhdsWithin_Ioi hgmono ?_
  set u : ℕ → ℝ := fun n => t + 1 / ((n : ℝ) + 1) with hu
  have htu : ∀ n, t ≤ u n := fun n => le_add_of_nonneg_right (by positivity)
  have hu_anti : Antitone u := by
    intro n n' hnn
    simp only [hu]
    have h : (1 : ℝ) / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn 1)
    linarith
  have hut : Filter.Tendsto u Filter.atTop (nhds t) := by
    have h0 : Filter.Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (t + 0)) :=
      Filter.Tendsto.const_add t tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hu] using h0
  have hset_anti : Antitone (fun n => Set.Ioc (min a (u n)) (min b (u n)) ×ˢ A) :=
    fun n n' hnn => Set.prod_mono (minIoc_subset hab (hu_anti hnn)) (le_refl A)
  have hInter : ⋂ n, Set.Ioc (min a (u n)) (min b (u n)) ×ˢ A
      = Set.Ioc (min a t) (min b t) ×ˢ A := by
    refine Set.Subset.antisymm (fun x hx => ?_)
      (Set.subset_iInter (fun n => Set.prod_mono (minIoc_subset hab (htu n)) (le_refl A)))
    rw [Set.mem_iInter] at hx
    refine Set.mem_prod.mpr ⟨⟨?_, ?_⟩, (Set.mem_prod.mp (hx 0)).2⟩
    · exact lt_of_le_of_lt (min_le_min (le_refl a) (htu 0)) (Set.mem_prod.mp (hx 0)).1.1
    · exact ge_of_tendsto' (tendsto_const_nhds.min hut)
        (fun n => (Set.mem_prod.mp (hx n)).1.2)
  have hfin0 : m (Set.Ioc (min a (u 0)) (min b (u 0)) ×ˢ A) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono (Set.prod_mono (minIoc_subset_Ioc hab (u 0)) (le_refl
      A)))
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (measurableSet_Ioc.prod hA).nullMeasurableSet) hset_anti ⟨0, hfin0⟩
  rw [hInter] at hlim
  exact hlim
end LevyStochCalc.Poisson.Compensated


