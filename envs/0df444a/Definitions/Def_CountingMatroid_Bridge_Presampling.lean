-- Prove2me | Definitions.Def_CountingMatroid_Bridge_Presampling
-- name    : CountingMatroid_Bridge_Presampling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T19:27:57.726791+00:00
-- url     : https://prove2.me/theorems/8a2f42ef-56d7-45c8-b487-24baeaf0be90
-- title:
--   Flat-tape replay of the common-base estimator
-- statement:
--   For natural numbers m and w, splitBlocks partitions a Boolean list into m successive blocks using take and drop, each of requested width w. It returns exactly m blocks, allowing short blocks if the input is too short. For a feasibility implementation, input parameters, and two independence oracles, presampledOutcome evaluates the existing charged estimator on these blocks and records its rational answer and its original oracle, abstract-operation, and random-read counters. Out-of-range reads retain the source's false default. This is a mathematical replay function, not a register-machine implementation; its counters exclude the additional work of eagerly generating and storing the tape.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CountingMatroid.Bridge

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations

/-- Divide a flat tape into a fixed number of fixed-width blocks. -/
def splitBlocks (width : ℕ) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | m + 1, bits => bits.take width :: splitBlocks width m (bits.drop width)

/-- Replay exactly the source estimator on a flat, eagerly sampled tape. -/
noncomputable def presampledOutcome (solver : Subroutines.FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (bits : List Bool) : ℚ × ExecutionCost :=
  let run := Program.estimate solver n r o₁ o₂ p
    (blockTape (splitBlocks (blockLength n r p)
      (Program.schedule n p).val.repetitions bits))
  (run.val, ExecutionCost.mk (Subroutines.oracleCalls run)
    (Subroutines.otherSteps run) (run.cost Op.fairBit))

end CountingMatroid.Bridge


