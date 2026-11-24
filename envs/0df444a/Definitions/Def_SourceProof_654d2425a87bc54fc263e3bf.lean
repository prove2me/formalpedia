-- Prove2me | Definitions.Def_SourceProof_654d2425a87bc54fc263e3bf
-- name    : SourceProof_654d2425a87bc54fc263e3bf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:30.509111+00:00
-- url     : https://prove2.me/theorems/e7d1c6e1-4c9d-4869-9497-a18db50cd52f
-- title:
--   StochLean source theorem: StochLean.isRightContinuousPath_tprod_Ioc

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_802c352df5798861ebae9666
import Definitions.Def_SourceProof_9121625c995972271da6f2bc
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # One-sided regularity of locally absolutely convergent cumulative products

Closed positive-time products include the jump at the current time; their
strict-left limits are the products on the corresponding open interval.
Zero and negative factors are permitted. Dominated convergence is applied
to deviations from one, not to logarithms of possibly nonpositive factors.
-/

@[expose] public section

open Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_654d2425a87bc54fc263e3bf {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) :
    IsRightContinuousPath (fun t : ℝ≥0 ↦ ∏' s : Ioc 0 t, f s) := by
  intro t
  let T : ℝ≥0 := t + 1
  have htT : t < T := by dsimp only [T]; exact lt_add_one t
  have hlim := tendsto_tprod_one_add_of_dominated_convergence (hs T)
    (fun s : Ioc 0 T ↦ _root_.Prove2MeSourceProof.h_9121625c995972271da6f2bc (s : ℝ≥0) t (f s - 1))
    (Filter.Eventually.of_forall (fun (u : ℝ≥0) (s : Ioc 0 T) ↦ by
      split_ifs <;> simp [abs_nonneg]))
  have he (u : ℝ≥0) : (∏' s : Ioc 0 T, (1 + if (s : ℝ≥0) ≤ u then f s - 1 else 0)) =
      ∏' s : Ioc 0 (min T u), f s := by
    convert _root_.Prove2MeSourceProof.h_802c352df5798861ebae9666 f u T using 1
    apply tprod_congr
    intro s
    split_ifs <;> ring
  simp only [he] at hlim
  rw [min_eq_right htT.le] at hlim
  apply hlim.congr'
  have hu : ∀ᶠ u in 𝓝[≥] t, u < T :=
    (eventually_lt_nhds htT).filter_mono nhdsWithin_le_nhds
  filter_upwards [hu] with u hu
  rw [min_eq_right hu.le]
end StochLean


