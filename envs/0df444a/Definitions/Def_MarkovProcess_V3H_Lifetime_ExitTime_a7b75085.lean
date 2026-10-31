-- Prove2me | Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
-- name    : MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:49.999817+00:00
-- url     : https://prove2.me/theorems/f67ccd2c-4504-4a61-b1a2-733475f75c26
-- title:
--   MarkovProcess: MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeteryExtension_b0b7bd17
import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
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
# Exit times of lifetime paths

This file defines the first time at which a lifetime path is not a live point of a prescribed
set. Reaching the cemetery state counts as exit. The infimum of the empty set is infinity, so a
path which never exits has infinite exit time.

Only deterministic order properties are proved here. No measurability or stopping-time claim is
made.
-/

open Set
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The first time at which a lifetime path is not a live point of `U`. -/
def exitTime (U : Set alpha) (omega : LifetimePath alpha) : ENNReal :=
  sInf {s : ENNReal | ∃ t : NNReal, s = (t : ENNReal) ∧
    coordinate t omega ∉ Cemetery.alive '' U}







end LifetimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The first time at which an ordinary continuous path leaves `U`. -/
def exitTime (U : Set alpha) (omega : ContinuousPath alpha) : ENNReal :=
  sInf {s : ENNReal | ∃ t : NNReal, s = (t : ENNReal) ∧ omega t ∉ U}

end ContinuousPath

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The lifetime-path exit time of an ordinary continuous path is its ordinary exit time. -/
@[simp]
theorem p2m_embedded_5471974f7a12f116 (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTime U (ofContinuousPath omega) = ContinuousPath.exitTime U omega := by
  apply congrArg sInf
  ext s
  constructor
  · rintro ⟨t, hst, ht⟩
    refine ⟨t, hst, ?_⟩
    intro homega
    apply ht
    exact ⟨omega t, homega, coordinate_ofContinuousPath omega t |>.symm⟩
  · rintro ⟨t, hst, ht⟩
    refine ⟨t, hst, ?_⟩
    rintro ⟨x, hx, hcoordinate⟩
    rw [coordinate_ofContinuousPath] at hcoordinate
    have heq : omega t = x := Sum.inl.inj hcoordinate.symm
    exact ht (heq.symm ▸ hx)



end LifetimePath

end
end MarkovProcess


