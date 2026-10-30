-- Prove2me | Definitions.Def_DerivativeChainAnalytic_LinearOptimization
-- name    : DerivativeChainAnalytic_LinearOptimization
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:58:55.744106+00:00
-- url     : https://prove2.me/theorems/8ed6d47b-f3be-4ad5-92ed-21c2c868bce1
-- title:
--   Cone of directions nonnegative at zero coordinates
-- statement:
--   For a supplied real vector p, the pointed cone contains exactly the vectors v with v(i)≥0 at every coordinate where p(i)=0.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/LinearOptimization.lean, lines 10-17, SHA-256 a93a5bc3c2a6d0b161fecb6c492d2c52100de7134211d79cef7b9bdeeb6f147c. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
open scoped BigOperators Topology
open Filter
namespace DerivativeChainPrefixLaws
noncomputable section

/-- First-order directions allowed by the zero coordinates of a nonnegative vector. -/
noncomputable def inactiveCone {ι : Type*} (p : ι → ℝ) : PointedCone ℝ (ι → ℝ) where
  carrier := {v | ∀ i,p i=0 → 0 ≤ v i}
  zero_mem' := by intro i hi; exact le_rfl
  add_mem' := by intro v w hv hw i hi; exact add_nonneg (hv i hi) (hw i hi)
  smul_mem' := by
    intro c v hv i hi
    exact mul_nonneg c.property (hv i hi)







end
end DerivativeChainPrefixLaws


