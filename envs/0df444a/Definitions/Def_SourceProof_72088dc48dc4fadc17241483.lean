-- Prove2me | Definitions.Def_SourceProof_72088dc48dc4fadc17241483
-- name    : SourceProof_72088dc48dc4fadc17241483
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:39:40.834723+00:00
-- url     : https://prove2.me/theorems/e77d5e1b-2b2c-41d9-9d25-e9887b92d364
-- title:
--   StochLean source theorem: StochLean.tendsto_tprod_Ioc_left

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_518bc9271925c6c9ec0f538d
import Definitions.Def_SourceProof_802c352df5798861ebae9666
import Definitions.Def_SourceProof_e9af2b3ab98e845734fa8674
import Mathlib.Analysis.Normed.Ring.InfiniteProd

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

theorem _root_.Prove2MeSourceProof.h_72088dc48dc4fadc17241483 {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) (t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 ↦ ∏' s : Ioc 0 u, f s) (𝓝[<] t)
      (𝓝 (∏' s : Ioo 0 t, f s)) := by
  let T : ℝ≥0 := t + 1
  have htT : t ≤ T := (lt_add_one t).le
  have hlim := tendsto_tprod_one_add_of_dominated_convergence (hs T)
    (fun s : Ioc 0 T ↦ _root_.Prove2MeSourceProof.h_518bc9271925c6c9ec0f538d (s : ℝ≥0) t (f s - 1))
    (Filter.Eventually.of_forall (fun (u : ℝ≥0) (s : Ioc 0 T) ↦ by
      split_ifs <;> simp [abs_nonneg]))
  have he (u : ℝ≥0) : (∏' s : Ioc 0 T, (1 + if (s : ℝ≥0) ≤ u then f s - 1 else 0)) =
      ∏' s : Ioc 0 (min T u), f s := by
    convert _root_.Prove2MeSourceProof.h_802c352df5798861ebae9666 f u T using 1
    apply tprod_congr
    intro s
    split_ifs <;> ring
  have heleft : (∏' s : Ioc 0 T, (1 + if (s : ℝ≥0) < t then f s - 1 else 0)) =
      ∏' s : Ioo 0 t, f s := by
    convert _root_.Prove2MeSourceProof.h_e9af2b3ab98e845734fa8674 f htT using 1
    apply tprod_congr
    intro s
    split_ifs <;> ring
  simp only [he, heleft] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [min_eq_right ((show u < t from hu).le.trans htT)]
end StochLean


