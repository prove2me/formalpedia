-- Prove2me | Definitions.Def_Submission_ThreeSum_StageBounds
-- name    : Submission_ThreeSum_StageBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:11:31.597308+00:00
-- url     : https://prove2.me/theorems/e785c80c-9c62-4511-8aa7-16da05f95896
-- title:
--   Stage Bounds
-- statement:
--   Definitions and structural lemmas for Stage Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean

import Definitions.Def_Submission_ThreeSum_MassScales
set_option autoImplicit false
namespace ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def tableCount (n : ℕ) : ℕ := scheduleCount n * fullOutputs n
def encoderCount (n : ℕ) : ℕ := 2 * bandCount n * scheduleCount n * fullOutputs n
def boxCount (n : ℕ) : ℕ := 3 * bandCount n ^ 2 * scheduleCount n * allPrefixBoxes n
def initialCount (W : ℕ → ℕ) (n : ℕ) : ℕ := W n * queryTerms n 0
def activeCount (H : ℕ → ℕ) (n : ℕ) : ℕ :=
  H n * representationBound n * microPartitions n * allQueryTerms n
def terminalChoices (n : ℕ) : ℕ := 2 ^ residualSize n (terminalDepth n)
def terminalCount (H : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * H n * representationBound n * terminalChoices n
def coreWork (W H : ℕ → ℕ) (n : ℕ) : ℕ :=
  tableCount n + encoderCount n + boxCount n + initialCount W n + activeCount H n + terminalCount H n
def concreteOverhead (C n : ℕ) : ℕ :=
  (localSearch C n + 1) * (primeWindow n + 1) ^ C * polynomialFactor C n
def amplifiedCoreWork (C : ℕ) (W H : ℕ → ℕ) (n : ℕ) : ℕ :=
  concreteOverhead C n * coreWork W H n
noncomputable section
def PowerBound (f : ℕ → ℕ) (a : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d)
namespace PowerBound
end PowerBound
end
end ThreeSum.StageBounds


