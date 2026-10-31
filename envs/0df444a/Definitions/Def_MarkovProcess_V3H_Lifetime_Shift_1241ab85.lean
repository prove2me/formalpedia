-- Prove2me | Definitions.Def_MarkovProcess_V3H_Lifetime_Shift_1241ab85
-- name    : MarkovProcess_V3H_Lifetime_Shift_1241ab85
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:58.96539+00:00
-- url     : https://prove2.me/theorems/83791959-e736-47ef-83e4-342538d1cf39
-- title:
--   MarkovProcess: MarkovProcess_V3H_Lifetime_Shift_1241ab85
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
# Deterministic time shifts of lifetime paths

This file shifts a lifetime path forward by a fixed finite time. A shift beyond the original
lifetime produces a path with zero lifetime, hence with cemetery state at every coordinate.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovProcess.LifetimePath

noncomputable section

variable {α : Type*} [TopologicalSpace α]

/-- Shift a lifetime path forward by the deterministic time `S`. -/
def shift (S : NNReal) (ω : LifetimePath α) : LifetimePath α where
  lifetime := ω.lifetime - (S : ENNReal)
  livePath := fun t ↦ ω.livePath ⟨S + t, by
    rw [ENNReal.coe_add, add_comm]
    exact lt_tsub_iff_right.mp t.property⟩
  continuous_livePath := by
    apply ω.continuous_livePath.comp
    exact (continuous_const.add continuous_subtype_val).subtype_mk _















section Measurable

variable [MeasurableSpace α]



end Measurable

end
end MarkovProcess.LifetimePath


