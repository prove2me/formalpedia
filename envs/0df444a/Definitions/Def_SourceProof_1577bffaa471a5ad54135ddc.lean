-- Prove2me | Definitions.Def_SourceProof_1577bffaa471a5ad54135ddc
-- name    : SourceProof_1577bffaa471a5ad54135ddc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:47.56825+00:00
-- url     : https://prove2.me/theorems/33b5dec4-ea67-456f-a97d-ac9a31d3e185
-- title:
--   StochLean source theorem: StochLean.eVariationOn_add_le

import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Arithmetic for the canonical bounded-variation predicate -/

@[expose] public section

open Set
open scoped ENNReal

namespace StochLean

variable {α E : Type*} [LinearOrder α] [NormedAddCommGroup E]

theorem _root_.Prove2MeSourceProof.h_1577bffaa471a5ad54135ddc (f g : α → E) (s : Set α) :
    eVariationOn (fun t ↦ f t + g t) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) +
        edist (g (u (i + 1))) (g (u i))) :=
      Finset.sum_le_sum fun _ _ ↦ edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)
end StochLean


