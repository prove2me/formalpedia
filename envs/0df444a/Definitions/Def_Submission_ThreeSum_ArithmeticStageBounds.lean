-- Prove2me | Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
-- name    : Submission_ThreeSum_ArithmeticStageBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:50.332717+00:00
-- url     : https://prove2.me/theorems/b8e30e7d-beb4-41e0-8d09-026994fb716c
-- title:
--   Arithmetic Stage Bounds
-- statement:
--   Definitions and structural lemmas for Arithmetic Stage Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ArithmeticStageBounds.lean

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
set_option autoImplicit false
namespace ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000
def maxMod (n : ℕ) : ℕ := radix n * (4*primeWindow n)^2
def bitBudget (k n : ℕ) : ℕ := 2*(k+2)*primeWindow n^2+1
def perTripleBudget (k n : ℕ) : ℕ :=
  10000*(roundedPower (maxMod n) + bandSize n * bitBudget k n + 1)
def arithmeticBudget (C k n : ℕ) : ℕ :=
  concreteOverhead C n * (3*bandCount n^2 * perTripleBudget k n)
def offsetBudget (C n : ℕ) : ℕ :=
  concreteOverhead C n * (2982*roundedPower (radix n))
def normalizationBudget (C n : ℕ) : ℕ := concreteOverhead C n * n
def combinedBudget (C k n : ℕ) : ℕ :=
  workBudget C k n + arithmeticBudget C k n + offsetBudget C n + normalizationBudget C n
noncomputable section
end
end ThreeSum.ArithmeticStageBounds


