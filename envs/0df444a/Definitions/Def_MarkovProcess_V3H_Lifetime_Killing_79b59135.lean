-- Prove2me | Definitions.Def_MarkovProcess_V3H_Lifetime_Killing_79b59135
-- name    : MarkovProcess_V3H_Lifetime_Killing_79b59135
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:54.029845+00:00
-- url     : https://prove2.me/theorems/ace913d1-e52f-4bf6-afdc-4ce00674d5a5
-- title:
--   MarkovProcess: MarkovProcess_V3H_Lifetime_Killing_79b59135
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic killing of lifetime paths

This file truncates a lifetime path at a deterministic finite time. The coordinate at the
killing time itself is the cemetery state, so this operation is distinct from endpoint-retaining
stopping.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovProcess.LifetimePath

noncomputable section

variable {α : Type*} [TopologicalSpace α]

/-- Kill a lifetime path at the deterministic time `T`. -/
def killAt (T : NNReal) (ω : LifetimePath α) : LifetimePath α where
  lifetime := min ω.lifetime (T : ENNReal)
  livePath := fun t ↦ ω.livePath ⟨t, lt_of_lt_of_le t.property (min_le_left _ _)⟩
  continuous_livePath := by
    apply ω.continuous_livePath.comp
    exact continuous_subtype_val.subtype_mk _

@[simp]
theorem p2m_embedded_36edc09cfee70734 (T : NNReal) (ω : LifetimePath α) :
    (killAt T ω).lifetime = min ω.lifetime (T : ENNReal) :=
  rfl







section Measurable

variable [MeasurableSpace α]



end Measurable

end
end MarkovProcess.LifetimePath


