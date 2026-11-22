-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F003
-- name    : LevyStochCalc_Ito_ItoFormulaGeneralShift_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:07:26.278192+00:00
-- url     : https://prove2.me/theorems/8247f1a0-184f-4c05-abd6-e27ee38244bc
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.ItoFormulaGeneralShift
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.ItoFormulaGeneralShift in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F002
import Definitions.Def_SourceProof_149ceb509314dcf41ef9a279
import Definitions.Def_SourceProof_37877ecb4860e2a96b519587

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for an increment translated by a general random vector

A random vector approached pointwise by random vectors for which Itô's formula between two
stopping times already holds carries the formula itself: the boundary term converges by
continuity of the function, the two Lebesgue terms converge along almost every path by
domination, and the stochastic term converges in `L²` because the energy of the difference of
two increments is at most four times the energy of the difference of the integrands, hence
almost surely along a subsequence common to the finitely many Brownian channels.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_stopped_sub_diff_le` — the energy of the difference of
  the increments of two integrands is at most four times the energy of their difference.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_of_energy` — a path of finite energy is almost
  surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_sum_mul` — the pointwise inner product of two
  families of paths of finite energy is almost surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift` — Itô's formula for the increment
  of a path between two stopping times, for a function translated by a general random vector.
* `LevyStochCalc.Brownian.Ito.dyadicShift` — the dyadic lattice point of a given resolution below
  a vector, coordinate by coordinate.
* `LevyStochCalc.Brownian.Ito.exists_simpleShift_approx` — a bounded random vector known at a
  stopping time is a pointwise limit of finitely valued random vectors known at that time.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section IncrementEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end IncrementEnergy

section WindowIntegrability

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end WindowIntegrability

section GeneralShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end GeneralShift

section DyadicApproximation

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A bounded random vector known at a stopping time in the sense that every Borel condition on
it, intersected with a level set of the time, is known there, is the pointwise limit of random
vectors taking finitely many values and known at that time in the same sense. -/
theorem exists_simpleShift_approx {n : ℕ} {ℱ' : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} {c : Ω → Fin n → ℝ} (hc : Measurable c) {M : ℝ}
    (hcb : ∀ ω i, |c ω i| ≤ M)
    (hcell : ∀ (a : ℝ) (B : Set (Fin n → ℝ)), MeasurableSet B →
      MeasurableSet[ℱ' a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω ∈ B}) :
    ∃ (cm : ℕ → Ω → Fin n → ℝ) (Vs : ℕ → Finset (Fin n → ℝ)),
      (∀ m, Measurable (cm m)) ∧ (∀ m ω, cm m ω ∈ Vs m) ∧
      (∀ (m : ℕ) (a : ℝ) (v : Fin n → ℝ),
        MeasurableSet[ℱ' a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ cm m ω = v}) ∧
      (∀ (m : ℕ) (ω : Ω) (i : Fin n), |cm m ω i - c ω i| ≤ 1 / 2 ^ m) ∧
      ∀ ω, Filter.Tendsto (fun m => cm m ω) Filter.atTop (𝓝 (c ω)) := by
  classical
  refine ⟨fun m ω => dyadicShift m (c ω), fun m =>
    (Fintype.piFinset fun _ : Fin n =>
        Finset.Icc (-(⌈(2 : ℝ) ^ m * M⌉ + 1)) (⌈(2 : ℝ) ^ m * M⌉ + 1)).image
      fun g : Fin n → ℤ => fun i => (g i : ℝ) / (2 : ℝ) ^ m,
    fun m => _root_.Prove2MeSourceProof.h_37877ecb4860e2a96b519587.comp hc, ?_, ?_,
    fun m ω i => abs_dyadicShift_sub_le m (c ω) i, ?_⟩
  · intro m ω
    refine Finset.mem_image.mpr ⟨fun i => ⌊(2 : ℝ) ^ m * c ω i⌋, ?_, rfl⟩
    exact Fintype.mem_piFinset.mpr fun i => _root_.Prove2MeSourceProof.h_149ceb509314dcf41ef9a279 m (hcb ω i)
  · intro m a v
    exact hcell a _ (_root_.Prove2MeSourceProof.h_37877ecb4860e2a96b519587 (measurableSet_singleton v))
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
end DyadicApproximation

end LevyStochCalc.Brownian.Ito


