-- Prove2me | Definitions.Def_DerivativeChainAnalytic_ProjectiveHistories
-- name    : DerivativeChainAnalytic_ProjectiveHistories
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:56:39.378477+00:00
-- url     : https://prove2.me/theorems/3001bd56-62a6-4663-8a35-5ef9aae777bd
-- title:
--   Sign-independent steps and nearest-sign orientations
-- statement:
--   The projective step is min(|y−x|,|y+x|). Recursively orient each next point by the sign nearest the preceding oriented point, choosing the supplied sign in a tie. Define the corresponding finite sequence and the sum of projective steps. These definitions alone do not assert derivative-root compatibility.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/ProjectiveHistories.lean, lines 10-10, SHA-256 d8bed978babcb201b0156f81486332e95189de1f1959868adafc5e0046e25b7a. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/ProjectiveHistories.lean, lines 11-14, SHA-256 d8bed978babcb201b0156f81486332e95189de1f1959868adafc5e0046e25b7a. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/ProjectiveHistories.lean, lines 15-16, SHA-256 d8bed978babcb201b0156f81486332e95189de1f1959868adafc5e0046e25b7a. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/ProjectiveHistories.lean, lines 17-18, SHA-256 d8bed978babcb201b0156f81486332e95189de1f1959868adafc5e0046e25b7a. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
namespace DerivativeChainPhaseLock
noncomputable section

def projectiveStep (x y : ℂ) : ℝ := min ‖y-x‖ ‖y+x‖
def projectiveOrient (x : ℕ → ℂ) : ℕ → ℂ
  | 0 => x 0
  | k+1 => if ‖x (k+1)-projectiveOrient x k‖ ≤ ‖x (k+1)+projectiveOrient x k‖
      then x (k+1) else -x (k+1)
def projectiveHistory (x : ℕ → ℂ) (n : ℕ) : Fin (n+1) → ℂ :=
  fun i => projectiveOrient x i.val
def projectivePathLength (x : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∑ k∈Finset.range n,projectiveStep (x k) (x (k+1))















end
end DerivativeChainPhaseLock


