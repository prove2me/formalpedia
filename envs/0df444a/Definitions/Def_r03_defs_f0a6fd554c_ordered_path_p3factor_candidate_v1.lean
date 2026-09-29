-- Prove2me | Definitions.Def_r03_defs_f0a6fd554c_ordered_path_p3factor_candidate_v1
-- name    : r03_defs_f0a6fd554c_ordered_path_p3factor_candidate_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:30.936966+00:00
-- url     : https://prove2.me/theorems/01ac57db-73b6-4033-bee3-c10dcf8466e9
-- title:
--   R03 P3-factor definition module: r03_defs_f0a6fd554c_ordered_path_p3factor_candidate_v1
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp02/ordered_path_p3factor_candidate_v1.lean; source SHA-256 b9ae4a26f4ebca2e93c8715e6533cc5e063ccd65b21f8d69ad461b8287d86b9f; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace R03OrderedPathCandidate

open CubicP3Partition

universe u
variable {V : Type u}

/-- A spanning ordered path, with consecutive vertices joined by graph edges. -/
structure OrderedPath (G : SimpleGraph V) (n : Nat) where
  place : Fin n ≃ V
  edge : ∀ i : Fin (n - 1),
    G.Adj (place ⟨i.val, by omega⟩) (place ⟨i.val + 1, by omega⟩)

/-- The consecutive triple positions in a product of finite types. -/
def idx3 (k : Nat) (i : Fin k) (j : Fin 3) : Fin (k * 3) :=
  ⟨j.val + 3 * i.val, by omega⟩

end R03OrderedPathCandidate


