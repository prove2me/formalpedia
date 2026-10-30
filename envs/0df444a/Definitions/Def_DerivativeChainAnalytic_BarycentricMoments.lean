-- Prove2me | Definitions.Def_DerivativeChainAnalytic_BarycentricMoments
-- name    : DerivativeChainAnalytic_BarycentricMoments
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:55:26.547875+00:00
-- url     : https://prove2.me/theorems/b28fba43-504b-4e87-9b5b-3589db8e93bb
-- title:
--   Weighted appended-edge square energy
-- statement:
--   For the same child-history law and supplied extension coefficients, sum the squared distance from each child-history endpoint to the appended parent root, with coefficients L.weights(i)·α(i,j).
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/BarycentricMoments.lean, lines 11-15, SHA-256 5d92ab8efc8f34b8409a881fc6d74d1443d21307225d5ba5ba3f4088ce963aaf. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainPrivate_foundations
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
universe v
namespace DerivativeChainPhaseLock
noncomputable section

def edgeSquareEnergy {n : ℕ} (a : Fin (n+2) → ℂ) {b : Fin (n+1) → ℂ} {u : ℂ}
    {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw b u κ)
    (α : κ → (fromRoots a).roots.toFinset → ℝ) : ℝ :=
  ∑ ij : κ × (fromRoots a).roots.toFinset, L.weights ij.1*α ij.1 ij.2*
    ‖(ij.2:ℂ)-L.paths ij.1 (Fin.last n)‖^2











end
end DerivativeChainPhaseLock


