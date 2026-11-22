-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
-- name    : LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:24:16.905457+00:00
-- url     : https://prove2.me/theorems/3ba0f511-34d6-4f30-ad28-e23253dbefad
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaMeasurableShift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaMeasurableShift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGridShiftClosed_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula between two stopping times for a shift known at the earlier time

A random variable known at a stopping time, cut to the event that the time has already occurred by
a deterministic time, is measurable for the σ-algebra at that deterministic time; multiplying by
such a variable therefore preserves progressive measurability of a process that vanishes up to the
stopping time. Reading an integrand along a mark taking finitely many values splits the increment
of the integrand between two ordered stopping times over the values of the mark, so that increment
is progressively measurable as soon as the mark is known at the earlier time. The dyadic lattice
points below a bounded random vector known at the earlier stopping time form such marks and
converge to it, and truncating a random vector on the event that its norm exceeds a level produces
bounded vectors eventually equal to it, so Itô's formula for the increment holds for a shift that
is merely known at the earlier stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stoppingTimeWeight_mul` — a random variable
  known at a stopping time times a progressively measurable process vanishing up to that time is
  progressively measurable.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_of_measurableShift` — the
  increment between two ordered stopping times of an integrand read along a mark taking finitely
  many values and known at the earlier time is progressively measurable.
* `LevyStochCalc.Brownian.Ito.exists_simpleShift_approx_measurableSpace` — a bounded random vector
  known at a stopping time is a pointwise limit of random vectors taking finitely many values and
  known at that stopping time.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_boundedShift` — Itô's formula for the increment of
  a path between two stopping times, for a function translated by a bounded random vector known at
  the earlier time.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_measurableShift` — the same for a function
  translated by a random vector known at the earlier time and subject to no bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Weight

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A random variable known at a stopping time, cut to the event that the time has occurred by a
deterministic time, is measurable for the σ-algebra at that deterministic time. -/
theorem measurable_indicator_le_of_measurableSpace {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) {V : Ω → ℝ}
    (hV : Measurable[hσ.measurableSpace] V) (t : ℝ) :
    Measurable[ℱ t] (Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V) := by
  intro B hB
  have hA : MeasurableSet[ℱ t] {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} := hσ t
  have hVB : MeasurableSet[ℱ t] (V ⁻¹' B ∩ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}) :=
    ((hσ.measurableSet (V ⁻¹' B)).mp (hV hB)).2 t
  by_cases h0 : (0 : ℝ) ∈ B
  · have hset : Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V ⁻¹' B
        = (V ⁻¹' B ∩ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)})
          ∪ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω
      by_cases hω : ω ∈ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}
      · simp [hω]
      · simp [hω, h0]
    rw [hset]
    exact hVB.union hA.compl
  · have hset : Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V ⁻¹' B
        = V ⁻¹' B ∩ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} := by
      ext ω
      by_cases hω : ω ∈ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}
      · simp [hω]
      · simp [hω, h0]
    rw [hset]
    exact hVB
/-- A random variable known at a stopping time, times a progressively measurable process that
vanishes up to that stopping time, is progressively measurable. -/
theorem progressivelyMeasurable_stoppingTimeWeight_mul {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) {V : Ω → ℝ}
    (hV : Measurable[hσ.measurableSpace] V) {D : Ω → ℝ → ℝ}
    (hpD : Probability.ProgressivelyMeasurable ℱ D)
    (hD0 : ∀ (ω : Ω) (s : ℝ), ((s : ℝ) : WithTop ℝ) ≤ σ ω → D ω s = 0) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * D ω s := by
  intro t
  have hVt : Measurable[ℱ t] (Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V) :=
    measurable_indicator_le_of_measurableSpace hσ hV t
  have hDt := hpD t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => V p.1 * D p.1 s) p.2)
      = fun p : Ω × ℝ => Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V p.1
          * (Set.Iic t).indicator (D p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      by_cases hω : p.1 ∈ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}
      · rw [Set.indicator_of_mem hω]
      · have h1 : ((p.2 : ℝ) : WithTop ℝ) ≤ ((t : ℝ) : WithTop ℝ) := by
          exact_mod_cast Set.mem_Iic.mp hp
        have h2 : ((t : ℝ) : WithTop ℝ) ≤ σ p.1 := (not_le.mp hω).le
        rw [Set.indicator_of_notMem hω, zero_mul, hD0 p.1 p.2 (h1.trans h2), mul_zero]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero]
  rw [key]
  letI : MeasurableSpace Ω := ℱ t
  exact ((hVt.comp measurable_fst).stronglyMeasurable).mul hDt
end Weight

section MarkDecomposition

variable {Ω : Type u} {α : Type*}

/-- The increment between two stopping times of an integrand read along a mark taking finitely many
values is the sum, over the values of the mark, of the indicator of the level set of the value
times the increment of the integrand at that value. -/
theorem stopped_sub_eq_sum_indicator {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
    (hcVs : ∀ ω, c ω ∈ Vs) (K : α → Ω → ℝ → ℝ) (Kc : Ω → ℝ → ℝ)
    (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    (fun (ω : Ω) (s : ℝ) => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
      = fun (ω : Ω) (s : ℝ) => ∑ v ∈ Vs, Set.indicator {ω | c ω = v} (fun _ => (1 : ℝ)) ω
          * (Probability.stopped τ (K v) ω s - Probability.stopped σ (K v) ω s) := by
  funext ω s
  have hsum := Finset.sum_eq_single_of_mem (c ω) (hcVs ω)
    (f := fun v => Set.indicator {ω | c ω = v} (fun _ => (1 : ℝ)) ω
      * (Probability.stopped τ (K v) ω s - Probability.stopped σ (K v) ω s))
    (fun v _ hv => by rw [Set.indicator_of_notMem fun hmem => hv hmem.symm, zero_mul])
  rw [hsum, Set.indicator_of_mem (show ω ∈ {ω' | c ω' = c ω} from rfl), one_mul]
  unfold LevyStochCalc.Probability.stopped
  rw [hKc]
end MarkDecomposition

section SimpleMark

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*} [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- The increment between two ordered stopping times of an integrand read along a mark taking
finitely many values and known at the earlier stopping time is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_of_measurableShift
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) {c : Ω → α} (hc : Measurable[hσ.measurableSpace] c)
    {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs)
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s := by
  rw [stopped_sub_eq_sum_indicator hcVs K Kc hKc]
  refine _root_.Prove2MeSourceProof.h_6ecf3972205d198bc7686bf0 ℱ
    (fun (v : α) (ω : Ω) (s : ℝ) => Set.indicator {ω | c ω = v} (fun _ => (1 : ℝ)) ω
      * (Probability.stopped τ (K v) ω s - Probability.stopped σ (K v) ω s))
    (fun v => ?_) Vs
  have hset : MeasurableSet[hσ.measurableSpace] {ω | c ω = v} := hc (measurableSet_singleton v)
  exact progressivelyMeasurable_stoppingTimeWeight_mul hσ (measurable_const.indicator hset)
    (progressivelyMeasurable_stopped_sub hσ hτ (hpK v))
    fun ω s hs => stopped_sub_stopped_eq_zero hστ _ ω hs
end SimpleMark

section TwoPieceMark

variable {Ω : Type u}

/-- The increment between two stopping times of an integrand agreeing with one integrand on a set
and with another off it splits over that set. -/
theorem stopped_sub_eq_indicator_add {σ τ : Ω → WithTop ℝ} {A : Set Ω}
    (K K₀ Kc : Ω → ℝ → ℝ) (hin : ∀ ω ∈ A, ∀ s, Kc ω s = K ω s)
    (hout : ∀ ω ∉ A, ∀ s, Kc ω s = K₀ ω s) :
    (fun (ω : Ω) (s : ℝ) => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
      = fun (ω : Ω) (s : ℝ) => A.indicator (fun _ => (1 : ℝ)) ω
            * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)
          + Aᶜ.indicator (fun _ => (1 : ℝ)) ω
            * (Probability.stopped τ K₀ ω s - Probability.stopped σ K₀ ω s) := by
  funext ω s
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, Set.indicator_of_notMem (by simp [hω]), one_mul, zero_mul,
      add_zero]
    unfold LevyStochCalc.Probability.stopped
    rw [hin ω hω s]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_mem hω, zero_mul, one_mul, zero_add]
    unfold LevyStochCalc.Probability.stopped
    rw [hout ω hω s]
end TwoPieceMark

section Approximation

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A bounded random vector known at a stopping time is the pointwise limit of random vectors
taking finitely many values and known at that stopping time. -/
theorem exists_simpleShift_approx_measurableSpace {n : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → Fin n → ℝ}
    (hc : Measurable[hσ.measurableSpace] c) {M : ℝ} (hcb : ∀ ω, ‖c ω‖ ≤ M) :
    ∃ (cm : ℕ → Ω → Fin n → ℝ) (Vs : ℕ → Finset (Fin n → ℝ)),
      (∀ m, Measurable[hσ.measurableSpace] (cm m)) ∧ (∀ m ω, cm m ω ∈ Vs m) ∧
      ∀ ω, Filter.Tendsto (fun m => cm m ω) Filter.atTop (𝓝 (c ω)) := by
  classical
  have hcoord : ∀ (ω : Ω) (i : Fin n), |c ω i| ≤ M := by
    intro ω i
    calc |c ω i| = ‖c ω i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖c ω‖ := norm_le_pi_norm (c ω) i
      _ ≤ M := hcb ω
  refine ⟨fun m ω => dyadicShift m (c ω), fun m =>
    (Fintype.piFinset fun _ : Fin n =>
        Finset.Icc (-(⌈(2 : ℝ) ^ m * M⌉ + 1)) (⌈(2 : ℝ) ^ m * M⌉ + 1)).image
      fun g : Fin n → ℤ => fun i => (g i : ℝ) / (2 : ℝ) ^ m,
    fun m => _root_.Prove2MeSourceProof.h_37877ecb4860e2a96b519587.comp hc, ?_, ?_⟩
  · intro m ω
    refine Finset.mem_image.mpr ⟨fun i => ⌊(2 : ℝ) ^ m * c ω i⌋, ?_, rfl⟩
    exact Fintype.mem_piFinset.mpr fun i => _root_.Prove2MeSourceProof.h_149ceb509314dcf41ef9a279 m (hcoord ω i)
  · intro ω
    have hhalf : Filter.Tendsto (fun m : ℕ => ((1 : ℝ) / 2) ^ m) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hg : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / 2 ^ m) Filter.atTop (𝓝 0) := by
      simpa [div_pow] using hhalf
    refine tendsto_pi_nhds.2 fun i => ?_
    rw [← tendsto_sub_nhds_zero_iff]
    have hb : ∀ m : ℕ, ‖dyadicShift m (c ω) i - c ω i‖ ≤ 1 / 2 ^ m := by
      intro m
      rw [Real.norm_eq_abs]
      exact abs_dyadicShift_sub_le m (c ω) i
    exact squeeze_zero_norm hb hg
end Approximation

section MeasurableShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end MeasurableShift

end LevyStochCalc.Brownian.Ito


