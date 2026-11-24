-- Prove2me | Definitions.Def_SourceProof_76feef3dc1aabdf57bee683f
-- name    : SourceProof_76feef3dc1aabdf57bee683f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:52.782803+00:00
-- url     : https://prove2.me/theorems/f66e8d93-4d3a-440c-bced-36d1c9410058
-- title:
--   StochLean source theorem: StochLean.eVariationOn_univ_eq_iSup_Icc_nat

import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Variation on the whole nonnegative half-line

The canonical extended variation on the whole half-line is the supremum of
its variations on integer compact intervals. This is purely deterministic:
no path regularity or finiteness assumption is needed, and infinite variation
is retained. The proof uses Mathlib's bounded-interval representation rather
than introducing a second partition or variation definition.
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

namespace StochLean


theorem _root_.Prove2MeSourceProof.h_76feef3dc1aabdf57bee683f {E : Type*} [PseudoEMetricSpace E]
    (x : ℝ≥0 → E) :
    eVariationOn x univ = ⨆ n : ℕ, eVariationOn x (Icc 0 (n : ℝ≥0)) := by
  apply le_antisymm
  · calc
      eVariationOn x univ =
          ⨆ p ∈ {p : ℝ≥0 × ℝ≥0 | p.1 ∈ univ ∧ p.2 ∈ univ ∧ p.1 ≤ p.2},
            eVariationOn x (univ ∩ Icc p.1 p.2) := eVariationOn.eq_biSup_inter_Icc
      _ ≤ ⨆ n : ℕ, eVariationOn x (Icc 0 (n : ℝ≥0)) := by
        refine iSup_le fun p ↦ iSup_le fun _ ↦ ?_
        obtain ⟨n, hn⟩ := exists_nat_ge p.2
        have hs : univ ∩ Icc p.1 p.2 ⊆ Icc 0 (n : ℝ≥0) := by
          rintro t ⟨_, ht⟩
          exact ⟨bot_le, ht.2.trans hn⟩
        exact (eVariationOn.mono x hs).trans
          (le_iSup (fun n : ℕ ↦ eVariationOn x (Icc 0 (n : ℝ≥0))) n)
  · exact iSup_le fun _ ↦ eVariationOn.mono x (subset_univ _)
end StochLean


