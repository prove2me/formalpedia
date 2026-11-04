-- Prove2me | Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
-- name    : Submission_ThreeSum_TernarySolverEndBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:45:03.359163+00:00
-- url     : https://prove2.me/theorems/a84a5d76-04c7-4ff1-a7ef-78a26e980621
-- title:
--   Ternary Solver End Bridge
-- statement:
--   Definitions and structural lemmas for Ternary Solver End Bridge, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
def target : ℚ := 4800698571997281331/2500000000000000000
def targetExponent : ℝ := 4800698571997281331/2500000000000000000
def FastExecution (P : Program) (p κ cutoff : ℕ) (T : ℕ→ ℕ) (need : ℕ→ ℕ→ Need) : Prop :=
  ∀ {lim : Limits} {src n free d : ℕ}, ∀ (x : Fin n→ ℤ) (μ : ℕ→ ℤ),
    cutoff≤ n→ 0<n→ src+n≤ free→ (need n (n^κ)).Ok lim free d→
    Seg μ src (List.ofFn x)→ (∀ i, |x i|≤ ((n^κ:ℕ):ℤ))→
    Meets lim P p d [src,n,free] μ (T n)
      (fun r ν=>(r=0∨r=1) ∧ (r=1↔Coloring.DistinctZeroSum x) ∧ Kept μ ν free)
end ThreeSum.TernarySolverEndBridge


