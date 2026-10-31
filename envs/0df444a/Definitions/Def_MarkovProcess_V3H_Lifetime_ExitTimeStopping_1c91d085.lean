-- Prove2me | Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTimeStopping_1c91d085
-- name    : MarkovProcess_V3H_Lifetime_ExitTimeStopping_1c91d085
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:41.113794+00:00
-- url     : https://prove2.me/theorems/ca108a17-3ded-486b-b6d6-b92ee729bdb1
-- title:
--   MarkovProcess: MarkovProcess_V3H_Lifetime_ExitTimeStopping_1c91d085
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeteryExtension_b0b7bd17
import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
import Definitions.Def_MarkovProcess_V3H_Lifetime_Filtration_a21e5dcd
import Definitions.Def_MarkovProcess_V3H_Path_ClosedSetDetection_642089d8
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
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

/-! # Exit times as stopping times -/

open MeasureTheory Set
open scoped ENNReal

namespace MarkovProcess.LifetimePath

noncomputable section

variable {alpha : Type*} [PseudoMetricSpace alpha]







private def detectionThreshold (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private def liveInfDist (F : Set alpha) : Cemetery alpha → ℝ :=
  Sum.elim (fun x ↦ Metric.infDist x F) (fun _ ↦ 1)

private def DetectsLiveClosedSetBy (t : NNReal) (F : Set alpha)
    (omega : LifetimePath alpha) : Prop :=
  F.Nonempty ∧ ∀ n : ℕ,
    liveInfDist F (coordinate t omega) < detectionThreshold n ∨
      ∃ k : ℕ, DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t ∧
        liveInfDist F
            (coordinate (DenseTime.castOrderEmbedding (DenseTime.enumeration k)) omega) <
          detectionThreshold n



section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]









end Measurable

end
end MarkovProcess.LifetimePath


