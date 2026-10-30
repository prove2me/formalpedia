-- Prove2me | Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
-- name    : DerivativeChainAnalytic_ClusterSubsetProduct
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T22:46:54.159731+00:00
-- url     : https://prove2.me/theorems/cfcb06b6-c56c-47fd-b15b-98af262f599d
-- title:
--   Root-slot product and monic normalized derivative rows
-- statement:
--   For a finite list of complex root slots a of length N, define P(X)=∏ᵢ(X−aᵢ), retaining multiplicities, and Qₘ=(m!/N!) P⁽ᴺ⁻ᵐ⁾. These are the source polynomial and its monic normalized derivative rows; the natural-number subtraction convention is the one in the exact Lean definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterSubsetProduct.lean, lines 50-51, SHA-256 a6d05e4fa5d192091e249eddae712315f75cec01915ba331061f322bcc396ae6. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterSubsetProduct.lean, lines 53-54, SHA-256 a6d05e4fa5d192091e249eddae712315f75cec01915ba331061f322bcc396ae6. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
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
set_option maxHeartbeats 1000000
open scoped BigOperators
open Polynomial Finset
namespace DerivativeChainClusterAnchor
noncomputable section

-- Slot indices retain coincident root values as separate factors.
-- The proof extends Mathlib's iterate_derivative_prod_X_sub_C to a noninjective root map.


noncomputable def sourcePolynomial {n : ℕ} (a : Fin n → ℂ) : ℂ[X] :=
  ∏ i, (X-C (a i))

noncomputable def ordinaryRow {n : ℕ} (a : Fin n → ℂ) (m : ℕ) : ℂ[X] :=
  C ((m.factorial:ℂ)/(n.factorial:ℂ)) * derivative^[n-m] (sourcePolynomial a)





end
end DerivativeChainClusterAnchor


