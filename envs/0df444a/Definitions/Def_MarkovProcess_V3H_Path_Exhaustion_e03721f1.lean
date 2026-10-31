-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_Exhaustion_e03721f1
-- name    : MarkovProcess_V3H_Path_Exhaustion_e03721f1
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:38:22.394165+00:00
-- url     : https://prove2.me/theorems/8ab869cc-53ce-4723-831a-6ca6d4e033af
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_Exhaustion_e03721f1
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
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
# Exit times along an exhaustion

For an increasing sequence of open sets `U n` covering the state space (an open exhaustion), the
exit time of a continuous path from `U n` tends to infinity: the path restricted to a compact time
interval has compact range, which lies in some `U N`, and the path therefore stays in `U n` on that
interval for every `n ≥ N` (`tendsto_exitTime_atTop`).  Exit times are monotone in the set
(`exitTime_mono`), as are the truncated exit times.

This is the path-space fact behind nonexplosion arguments: no probability law is involved here.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]





/-- An open exhaustion of the state space: an increasing sequence of open sets whose union is the
whole space. -/
structure IsOpenExhaustion (U : ℕ → Set alpha) : Prop where
  /-- Every member is open. -/
  isOpen : ∀ n, IsOpen (U n)
  /-- The sequence is increasing. -/
  monotone : Monotone U
  /-- The sequence covers the state space. -/
  iUnion_eq : ⋃ n, U n = Set.univ











end MarkovProcess.ContinuousPath


