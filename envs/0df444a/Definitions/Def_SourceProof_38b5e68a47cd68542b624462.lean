-- Prove2me | Definitions.Def_SourceProof_38b5e68a47cd68542b624462
-- name    : SourceProof_38b5e68a47cd68542b624462
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:27.422276+00:00
-- url     : https://prove2.me/theorems/48c87665-d93b-4a2b-82b7-e8fb600a0e5f
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUCP_zero_of_diagonal_deviation_bound

import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Simultaneous UCP diagonals on growing horizons

One index is chosen for each pair of convergent rows. Both selected errors vanish
in UCP; the construction does not require a uniform convergence rate across rows.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_38b5e68a47cd68542b624462
    {D : ℕ → ℝ≥0 → Ω → ℝ} {a : ℕ → ℝ} {b : ℕ → ℝ≥0∞}
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hd : ∀ n : ℕ, P {ω | ∃ t ≤ (n : ℝ≥0), a n < ‖D n t ω‖} ≤ b n) :
    TendstoUCP P D atTop 0 := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  simp only [Pi.zero_apply, sub_zero]
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨NT, hNT⟩ := exists_nat_ge T
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (ha.eventually_lt_const hε)
  obtain ⟨NP, hNP⟩ := ENNReal.tendsto_atTop_zero.mp hb η hη
  refine ⟨max NT (max NE NP), fun n hn ↦ ?_⟩
  have hTn : T ≤ (n : ℝ≥0) := hNT.trans (by
    exact_mod_cast (le_max_left NT (max NE NP)).trans hn)
  have hEn := hNE n ((le_max_left NE NP).trans ((le_max_right NT (max NE NP)).trans hn))
  have hPn := hNP n ((le_max_right NE NP).trans ((le_max_right NT (max NE NP)).trans hn))
  apply le_trans ?_ ((hd n).trans hPn)
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  exact ⟨t, ht.trans hTn, hEn.trans hω⟩
end ProbabilityTheory


