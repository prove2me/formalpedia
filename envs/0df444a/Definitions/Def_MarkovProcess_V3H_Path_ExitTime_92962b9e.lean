-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
-- name    : MarkovProcess_V3H_Path_ExitTime_92962b9e
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:02.589576+00:00
-- url     : https://prove2.me/theorems/3699056c-d0c0-44ec-922e-02fa754203aa
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_ExitTime_92962b9e
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_ClosedSetDetection_642089d8
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times of open sets on continuous-path space

For an open set `U` this file studies `ContinuousPath.exitTime U`, the first time a continuous
path leaves `U`, in the `WithTop`-valued form `ContinuousPath.exitTimeTop U` demanded by
Mathlib's stopping-time convention.  The main consumer facts are: the exit time is a stopping
time for the canonical filtration; it is finite exactly when the path leaves `U` at some time;
at a finite exit time the path sits on the frontier of `U` when it started inside; and its
truncation `exitTimeTrunc U K` at a deterministic horizon is an `NNReal`-valued stopping time,
which is the form the finite-stopping-time API of this library consumes.  The generic time-set
identities `survivalSet_top`, `survivalSet_ne_top`, and `survivalSet` identify the positive real
times below an extended nonnegative horizon.

The route is the closed-set detection of `Path/ClosedSetDetection.lean`: the event
`{exitTime ≤ t}` is the event of hitting the closed set `Uᶜ` by time `t`, because a path that
stays in the open set `U` throughout `[0, t]` stays in it slightly beyond `t`.

This file constructs no probability law and proves no probabilistic statement; in particular it
does not claim that the exit time is almost surely finite for any process.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MarkovProcess

namespace ContinuousPath

noncomputable section

section SurvivalSets







end SurvivalSets

variable {alpha : Type*} [PseudoMetricSpace alpha]

section Order

/-- A time at which the path is outside `U` bounds the exit time from above. -/
theorem exitTime_le_of_notMem (U : Set alpha) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : omega t ∉ U) : exitTime U omega ≤ (t : ℝ≥0∞) := by
  apply sInf_le
  exact ⟨t, rfl, ht⟩

/-- Strictly before the exit time the path is inside `U`. -/
theorem mem_of_lt_exitTime (U : Set alpha) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : (t : ℝ≥0∞) < exitTime U omega) : omega t ∈ U := by
  by_contra htU
  exact absurd (exitTime_le_of_notMem U omega t htU) (not_le_of_gt ht)





/-- For an open set `U`, the exit time is at most `t` exactly when the path meets the closed set
`Uᶜ` at or before time `t`.  The forward direction uses openness of `U`: a path inside `U`
throughout `[0, t]` stays inside `U` for a further positive amount of time, so its exit time is
strictly larger than `t`. -/
theorem p2m_embedded_7694c6643af519a7 (U : Set alpha) (hU : IsOpen U) (t : NNReal)
    (omega : ContinuousPath alpha) :
    exitTime U omega ≤ (t : ℝ≥0∞) ↔ omega ∈ hitsSetBy t Uᶜ := by
  constructor
  · intro hle
    by_contra hnot
    have hall : ∀ s : NNReal, s ≤ t → omega s ∈ U := by
      intro s hs
      by_contra hsU
      exact hnot ⟨⟨s, Set.mem_Iic.mpr hs⟩, hsU⟩
    have hVopen : IsOpen ((omega : NNReal → alpha) ⁻¹' U) := hU.preimage omega.continuous
    have htV : t ∈ (omega : NNReal → alpha) ⁻¹' U := hall t le_rfl
    obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp hVopen t htV
    have hhalf : (0 : ℝ) < delta / 2 := by linarith only [hdelta]
    set d : NNReal := ⟨delta / 2, le_of_lt hhalf⟩ with hd
    have hdpos : 0 < d := NNReal.coe_pos.mp hhalf
    have hmem : ∀ s : NNReal, s < t + d → omega s ∈ U := by
      intro s hs
      by_cases hst : s ≤ t
      · exact hall s hst
      · apply hball
        rw [Metric.mem_ball, NNReal.dist_eq]
        have hts : (t : ℝ) < (s : ℝ) := by exact_mod_cast lt_of_not_ge hst
        have hsd : (s : ℝ) < (t : ℝ) + delta / 2 := by
          have := hs
          rw [← NNReal.coe_lt_coe, NNReal.coe_add] at this
          exact this
        rw [abs_of_pos (by linarith only [hts])]
        linarith only [hsd, hdelta]
    have hge : ((t + d : NNReal) : ℝ≥0∞) ≤ exitTime U omega := by
      rw [exitTime]
      apply le_sInf
      rintro s ⟨u, rfl, hu⟩
      have hnotlt : ¬ u < t + d := fun h ↦ hu (hmem u h)
      exact_mod_cast not_lt.mp hnotlt
    have hlt : (t : ℝ≥0∞) < ((t + d : NNReal) : ℝ≥0∞) := by
      rw [ENNReal.coe_lt_coe]
      exact lt_add_of_pos_right t hdpos
    exact absurd (hlt.trans_le (hge.trans hle)) (lt_irrefl _)
  · rintro ⟨s, hs⟩
    refine le_trans (exitTime_le_of_notMem U omega s hs) ?_
    exact_mod_cast s.property

end Order

section WithTopValue

/-- The exit time of a continuous path from `U`, read in `WithTop ℝ≥0`: this is the same value as
`ContinuousPath.exitTime U`, presented in the type Mathlib's `IsStoppingTime` expects. -/
def exitTimeTop (U : Set alpha) (omega : ContinuousPath alpha) : WithTop NNReal :=
  exitTime U omega



/-- The exit time from `U` truncated at the deterministic horizon `K`: an `NNReal`-valued, hence
finite, time, equal to the exit time when that is at most `K` and to `K` otherwise. -/
def exitTimeTrunc (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) : NNReal :=
  (min (exitTimeTop U omega) (K : WithTop NNReal)).untopA

/-- The truncated exit time, read in `WithTop ℝ≥0`, is the minimum of the exit time and the
horizon. -/
theorem coe_exitTimeTrunc (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    ((exitTimeTrunc U K omega : NNReal) : WithTop NNReal) =
      min (exitTimeTop U omega) (K : WithTop NNReal) := by
  have hne : min (exitTimeTop U omega) (K : WithTop NNReal) ≠ ⊤ := by
    intro htop
    have hle := min_le_right (exitTimeTop U omega) (K : WithTop NNReal)
    rw [htop] at hle
    exact WithTop.coe_ne_top (top_le_iff.mp hle)
  rw [exitTimeTrunc, WithTop.untopA_eq_untop hne, WithTop.coe_untop]



end WithTopValue

section Frontier

/-- The exit position is read at the time `(exitTime U omega).toNNReal`.  The `WithTop.untopD`
spelling of that time, which the `WithTop`-valued stopping-time API produces, is the same
value. -/
@[simp]
theorem p2m_embedded_0ab247f0b7a1e9c3 (U : Set alpha) (omega : ContinuousPath alpha) :
    (exitTime U omega).untopD 0 = (exitTime U omega).toNNReal := rfl



end Frontier

section Stopping

variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- **The exit time from an open set is a stopping time** for the canonical filtration on
continuous paths: the event `{exitTime ≤ t}` is the event of hitting the closed set `Uᶜ` by time
`t`, which is measurable in the canonical filtration at time `t`. -/
theorem isStoppingTime_exitTime (U : Set alpha) (hU : IsOpen U) :
    IsStoppingTime (canonicalFiltration (alpha := alpha)) (exitTimeTop U) := by
  intro t
  have hevent : {omega : ContinuousPath alpha | exitTimeTop U omega ≤ (t : WithTop NNReal)} =
      hitsSetBy t Uᶜ := by
    ext omega
    simp only [Set.mem_ofPred_eq]
    exact _root_.MarkovProcess.ContinuousPath.p2m_embedded_7694c6643af519a7 U hU t omega
  show MeasurableSet[canonicalFiltration (alpha := alpha) t]
    {omega : ContinuousPath alpha | exitTimeTop U omega ≤ (t : WithTop NNReal)}
  rw [hevent]
  exact _root_.MarkovProcess.ContinuousPath.p2m_embedded_edc7c8d8f6c1d830 t Uᶜ hU.isClosed_compl

/-- **The truncated exit time from an open set is a finite stopping time** for the canonical
filtration, in the `NNReal`-valued form consumed by the finite-stopping-time API of this
library. -/
theorem isStoppingTime_exitTimeTrunc (U : Set alpha) (hU : IsOpen U) (K : NNReal) :
    IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ ((exitTimeTrunc U K omega : NNReal) : WithTop NNReal)) := by
  simp only [coe_exitTimeTrunc]
  exact (isStoppingTime_exitTime U hU).min_const K

end Stopping

end

end ContinuousPath

end MarkovProcess


