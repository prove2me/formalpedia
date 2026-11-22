-- Prove2me | Definitions.Def_SourceProof_703991d88a6fb30ce9f631df
-- name    : SourceProof_703991d88a6fb30ce9f631df
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:33:50.825424+00:00
-- url     : https://prove2.me/theorems/a5d56564-e94a-4ac1-b4c8-85e4b41ad8ff
-- title:
--   LevyStochCalc source module: SourceProof_703991d88a6fb30ce9f631df
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_sum_filter_le` comes from the `LevyStochCalc.Ito.AtomJumpRelation` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathDecomposition_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The left-limit jump sum as a step function of the arrival times

Over a window of finite intensity a Poisson random measure is a finite sum of Dirac masses
carried by pairwise distinct times, so the integral of a function against it over an initial
segment of the window is the plain sum of the function's values at the atoms whose time has been
reached. Read at the jump coefficient along the left limits of a path, this writes the
left-limit jump sum over the window as a step function of the arrival times.

## Main statements

* `LevyStochCalc.Poisson.setIntegral_Ioc_prod_eq_sum_filter` — the integral over an initial
  segment of the window is the sum over the atoms whose time has been reached.
* `LevyStochCalc.Poisson.stochasticIntegral_add_setIntegral_sub_eq_pathwise_sub` — the jump side
  of the Itô–Lévy formula at finite activity reads the integrand only at the atoms.
* `LevyStochCalc.Poisson.stochasticIntegral_eq_neg_setIntegral_of_atoms_zero` — an integrand
  vanishing at every atom of the window has compensated integral minus its compensator, on the
  set of sample points where the vanishing holds.
* `LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_sum_filter_le` — the left limit of a step
  function with finitely many steps drops the steps at the point itself.
* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jumpSumLeftAt_eq_sum` — the left-limit
  jump sum over the window is that step function.
* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma` — the increment of a path
  across an arrival time is the jump coefficient at the left limit there.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

section Restriction

variable {E : Type v} [MeasurableSpace E]

end Restriction

section JumpSide

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end JumpSide

end LevyStochCalc.Poisson

namespace LevyStochCalc.Ito.JumpSplitting

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}


theorem _root_.Prove2MeSourceProof.h_703991d88a6fb30ce9f631df {K : ℕ} (θ : Fin K → ℝ) (c : Fin K → ℝ) (b : ℝ) :
    Tendsto (fun t => ∑ j ∈ Finset.univ.filter fun j => θ j ≤ t, c j)
      (𝓝[<] b) (𝓝 (∑ j ∈ Finset.univ.filter fun j => θ j < b, c j)) := by
  classical
  obtain ⟨a, hab, hmax⟩ :
      ∃ a : ℝ, a < b ∧ ∀ j ∈ Finset.univ.filter fun j => θ j < b, θ j ≤ a := by
    set S : Finset ℝ := insert (b - 1) ((Finset.univ.filter fun j => θ j < b).image θ) with hS
    have hne : S.Nonempty := ⟨b - 1, Finset.mem_insert_self _ _⟩
    refine ⟨S.max' hne, ?_, fun j hj => Finset.le_max' _ _ ?_⟩
    · rw [Finset.max'_lt_iff]
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · linarith
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy'
        exact (Finset.mem_filter.mp hk).2
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem θ hj)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    exact le_trans (hmax j (by simp [hj])) ht.1.le
  · intro hj
    exact lt_of_le_of_lt hj ht.2
end LevyStochCalc.Ito.JumpSplitting


