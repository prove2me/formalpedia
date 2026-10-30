-- Prove2me | Definitions.Def_DerivativeChainAnalytic_ExtremalGateExample
-- name    : DerivativeChainAnalytic_ExtremalGateExample
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T22:48:14.538237+00:00
-- url     : https://prove2.me/theorems/798ff8d7-7577-4f65-b999-08e84c3154bc
-- title:
--   Degree-ten radial-prefix example and its real quadratic quotient
-- statement:
--   Define the complex polynomial 3072X¹⁰−1600X⁶+240X²+15i and the real polynomial 64X²−20X+1. Subsequent theorems prove the degree, centroid, exact derivative composition, strict unit-disk root bound, complete-chain estimate and exactly three centered modes.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/extremal/snapshots/radial-prefix-v1/ExtremalGateExample.lean, lines 12-12, SHA-256 625f7b8884b39976e87f03458efad9eb0da74d4c2f7ce720384f4b57a033c69c. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/extremal/snapshots/radial-prefix-v1/ExtremalGateExample.lean, lines 9-10, SHA-256 625f7b8884b39976e87f03458efad9eb0da74d4c2f7ce720384f4b57a033c69c. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint fde5728a069c8d5ad1bf06094368fcdfaefa5af7: submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/POSITIVE_GATE.md, SHA-256 bb50241b080580c05ffd35958aa8bef210234efbb7d16944d0ace8a8895c0765; submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/RESULT.md, SHA-256 41e540e06897511bc15c8d4c580011f42c3d64e65c1169d46028c9bb9d9c9f60.

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation

noncomputable def radialGateExample : Polynomial ℂ :=
  C 3072*X^10-C 1600*X^6+C 240*X^2+C (15*Complex.I)

noncomputable def radialGateQuotient : Polynomial ℝ := C 64*X^2-C 20*X+1

























end DerivativeChainExtremal


