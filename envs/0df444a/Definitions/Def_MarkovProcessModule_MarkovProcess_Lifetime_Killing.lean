-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Lifetime_Killing
-- name    : MarkovProcessModule_MarkovProcess_Lifetime_Killing
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:46:59.401626+00:00
-- url     : https://prove2.me/theorems/f543ec0c-1614-4d5d-8fea-68e3fbad9487
-- title:
--   MarkovProcess.Lifetime.Killing
-- statement:
--   # Deterministic killing of lifetime paths
--
--   This file truncates a lifetime path at a deterministic finite time. The coordinate at the
--   killing time itself is the cemetery state, so this operation is distinct from endpoint-retaining
--   stopping.
--
--   Complete pinned Lean module MarkovProcess.Lifetime.Killing by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Lifetime/Killing.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Lifetime_Basic

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
theorem lifetime_killAt (T : NNReal) (ω : LifetimePath α) :
    (killAt T ω).lifetime = min ω.lifetime (T : ENNReal) :=
  rfl

/-- Killing does not change a coordinate strictly before the killing time. -/
theorem coordinate_killAt_of_lt (T t : NNReal) (ω : LifetimePath α)
    (ht : (t : ENNReal) < (T : ENNReal)) :
    coordinate t (killAt T ω) = coordinate t ω := by
  by_cases hω : (t : ENNReal) < ω.lifetime
  · have hk : (t : ENNReal) < min ω.lifetime (T : ENNReal) := lt_min hω ht
    rw [coordinate_of_lt _ _ hk, coordinate_of_lt _ _ hω]
    rfl
  · have hωle : ω.lifetime ≤ (t : ENNReal) := not_lt.mp hω
    rw [coordinate_of_le _ _ hωle]
    apply coordinate_of_le
    exact (min_le_left _ _).trans hωle

/-- At and after the deterministic killing time, the killed coordinate is the cemetery state. -/
@[simp]
theorem coordinate_killAt_of_le (T t : NNReal) (ω : LifetimePath α) (ht : T ≤ t) :
    coordinate t (killAt T ω) = Cemetery.delta := by
  apply coordinate_of_le
  exact (min_le_right _ _).trans (ENNReal.coe_le_coe.mpr ht)

/-- Killing twice is killing once at the earlier of the two deterministic times. -/
theorem killAt_killAt (S T : NNReal) (ω : LifetimePath α) :
    killAt T (killAt S ω) = killAt (min T S) ω := by
  apply ext_coordinate
  · simp only [lifetime_killAt, ENNReal.coe_min]
    rw [min_assoc]
    exact congrArg (min ω.lifetime) (min_comm (S : ENNReal) (T : ENNReal))
  · intro t
    by_cases htT : t < T
    · rw [coordinate_killAt_of_lt T t (killAt S ω) (ENNReal.coe_lt_coe.mpr htT)]
      by_cases htS : t < S
      · rw [coordinate_killAt_of_lt S t ω (ENNReal.coe_lt_coe.mpr htS)]
        rw [coordinate_killAt_of_lt (min T S) t ω]
        exact ENNReal.coe_lt_coe.mpr (lt_min htT htS)
      · rw [coordinate_killAt_of_le S t ω (not_lt.mp htS)]
        rw [coordinate_killAt_of_le (min T S) t ω]
        exact (min_le_right T S).trans (not_lt.mp htS)
    · rw [coordinate_killAt_of_le T t (killAt S ω) (not_lt.mp htT)]
      rw [coordinate_killAt_of_le (min T S) t ω]
      exact (min_le_left T S).trans (not_lt.mp htT)

section Measurable

variable [MeasurableSpace α]

/-- Killing at a fixed deterministic time is measurable for the coordinate-generated
measurable structure on lifetime paths. -/
theorem measurable_killAt (T : NNReal) :
    Measurable (killAt T : LifetimePath α → LifetimePath α) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpace, MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  apply sup_le
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_lifetime.min measurable_const).comap_le
  · rw [iSup_le_iff]
    intro t
    rw [MeasurableSpace.comap_comp]
    by_cases ht : (t : ENNReal) < (T : ENNReal)
    · have hfun : coordinate (α := α) t ∘ killAt T = coordinate t := by
        funext ω
        exact coordinate_killAt_of_lt T t ω ht
      rw [hfun]
      exact (measurable_coordinate t).comap_le
    · have hfun : coordinate (α := α) t ∘ killAt T = fun _ ↦ Cemetery.delta := by
        funext ω
        exact coordinate_killAt_of_le T t ω (ENNReal.coe_le_coe.mp (not_lt.mp ht))
      rw [hfun]
      exact measurable_const.comap_le

end Measurable

end
end MarkovProcess.LifetimePath


