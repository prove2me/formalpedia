-- Prove2me | Definitions.Def_DerivativeChainAnalytic_RootProbabilityExtension
-- name    : DerivativeChainAnalytic_RootProbabilityExtension
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:55:55.544192+00:00
-- url     : https://prove2.me/theorems/74dc6895-b136-43d2-bae0-8151086bafc7
-- title:
--   Existing root-probability kernel at history endpoints
-- statement:
--   Given a finite balanced child-history law, evaluate the existing canonical rootProbability of the parent polynomial at each child-history endpoint and each parent root. No new probability-kernel convention is introduced.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/RootProbabilityExtension.lean, lines 11-14, SHA-256 92d0de0dd5da52595a16d6e296fec96efcd94ba9db1b78bac107940cc7800634. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
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
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory
universe v
namespace DerivativeChainPhaseLock
noncomputable section

def rootKernel {n : ℕ} (a : Fin (n+2) → ℂ) {b : Fin (n+1) → ℂ} {u : ℂ}
    {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw b u κ) :
    κ → (fromRoots a).roots.toFinset → ℝ :=
  fun i j => DerivativeChain.rootProbability (fromRoots a) (L.paths i (Fin.last n)) j





end
end DerivativeChainPhaseLock


