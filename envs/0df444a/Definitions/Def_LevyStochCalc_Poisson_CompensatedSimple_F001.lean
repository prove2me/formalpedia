-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F001
-- name    : LevyStochCalc_Poisson_CompensatedSimple_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:23:30.647468+00:00
-- url     : https://prove2.me/theorems/52baf426-f4ef-49df-a0c6-afcb6ed2f11f
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedSimple
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedSimple. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The full rectangles `(t_i, t_{i+1}] × A_i` for `i : Fin φ.N` are pairwise disjoint
(time intervals are disjoint). -/
lemma SimplePredictable.fullRect_disjoint
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) :
    Pairwise (fun i j : Fin φ.N => Disjoint (φ.fullRect i) (φ.fullRect j)) := by
  intro i j hij
  unfold SimplePredictable.fullRect
  rcases lt_or_gt_of_ne hij with h | h
  · have h_succ_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
      φ.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x hx
    obtain ⟨hxi, hxj⟩ := hx
    obtain ⟨hxi_t, _⟩ := Set.mem_prod.mp hxi
    obtain ⟨hxj_t, _⟩ := Set.mem_prod.mp hxj
    obtain ⟨_, hxi_le⟩ := Set.mem_Ioc.mp hxi_t
    obtain ⟨hxj_lt, _⟩ := Set.mem_Ioc.mp hxj_t
    exact absurd (hxi_le.trans h_succ_le) (not_le.mpr hxj_lt)
  · have h_succ_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x hx
    obtain ⟨hxi, hxj⟩ := hx
    obtain ⟨hxi_t, _⟩ := Set.mem_prod.mp hxi
    obtain ⟨hxj_t, _⟩ := Set.mem_prod.mp hxj
    obtain ⟨hxi_lt, _⟩ := Set.mem_Ioc.mp hxi_t
    obtain ⟨_, hxj_le⟩ := Set.mem_Ioc.mp hxj_t
    exact absurd (hxj_le.trans h_succ_le) (not_le.mpr hxi_lt)
end LevyStochCalc.Poisson.Compensated


