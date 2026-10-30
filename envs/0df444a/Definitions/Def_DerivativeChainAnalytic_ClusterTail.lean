-- Prove2me | Definitions.Def_DerivativeChainAnalytic_ClusterTail
-- name    : DerivativeChainAnalytic_ClusterTail
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T22:47:24.367642+00:00
-- url     : https://prove2.me/theorems/3d56e48b-442b-4012-882d-71a8f6dd2d52
-- title:
--   Root anchor radius from a normalized derivative value
-- statement:
--   Define the degree-m anchor radius at c by |Qₘ(c)|^(1/m), using the real-power convention with inverse of the real cast of m. The definition itself permits every natural m; positivity restrictions belong to each theorem. It is an evaluation-based anchor quantity.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterTail.lean, lines 11-12, SHA-256 1f8def0926d0c974316163c75b78814a53c991a712c49f9ef7f8629386e09304. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Finset Polynomial
namespace DerivativeChainClusterAnchor
noncomputable section

noncomputable def anchorRadius {n : ℕ} (a : Fin n → ℂ) (c : ℂ) (m : ℕ) : ℝ :=
  ‖(ordinaryRow a m).eval c‖^((m:ℝ)⁻¹)















end
end DerivativeChainClusterAnchor


