-- Prove2me | Definitions.Def_DerivativeChainAnalytic_UniformTransportHistories
-- name    : DerivativeChainAnalytic_UniformTransportHistories
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:57:28.541594+00:00
-- url     : https://prove2.me/theorems/c960b53d-fc3a-4113-bf98-395da0c980c7
-- title:
--   Sum of consecutive uniform transport costs
-- statement:
--   For the supplied finite root arrays, define towerTransportLength as the sum of uniformW1 between consecutive arrays. Polynomial-tower compatibility is a separate hypothesis of later results.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/UniformTransportHistories.lean, lines 14-15, SHA-256 e422d33e090f664c9867aa5960ddb557cc08f17cf1e28844cc0e1c8d136f6d2c. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_UniformWasserstein
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
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
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainFiniteHistory
open DerivativeChainPrefixLaws
namespace DerivativeChainPhaseLock
noncomputable section

def towerTransportLength (r : ComplexRootRows) (n : ℕ) : ℝ :=
  ∑ k : Fin n,uniformW1 (r k.val) (r (k.val+1))





end
end DerivativeChainPhaseLock


