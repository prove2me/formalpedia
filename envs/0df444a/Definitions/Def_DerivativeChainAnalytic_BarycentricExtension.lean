-- Prove2me | Definitions.Def_DerivativeChainAnalytic_BarycentricExtension
-- name    : DerivativeChainAnalytic_BarycentricExtension
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:54:50.618209+00:00
-- url     : https://prove2.me/theorems/77bddf54-e6a4-4227-ab68-160f9b55ad6c
-- title:
--   Weighted parent variance and appended-history square cost
-- statement:
--   For a finite balanced child-history law and an arbitrary supplied extension coefficient array α, define the sum of squared parent-root distances from u and the sum of squared lengths of histories with that parent root appended. Both sums use coefficients L.weights(i)·α(i,j); the definitions themselves impose no additional condition on α.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/BarycentricExtension.lean, lines 14-18, SHA-256 7f59754d742fe35968f59280c833a578eefed8b39f01a074d6f24a5fcb780416. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/BarycentricExtension.lean, lines 20-24, SHA-256 7f59754d742fe35968f59280c833a578eefed8b39f01a074d6f24a5fcb780416. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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

def parentVariance {n : ℕ} (a : Fin (n+2) → ℂ) {b : Fin (n+1) → ℂ} {u : ℂ}
    {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw b u κ)
    (α : κ → (fromRoots a).roots.toFinset → ℝ) : ℝ :=
  ∑ ij : κ × (fromRoots a).roots.toFinset,
    L.weights ij.1*α ij.1 ij.2*‖(ij.2:ℂ)-u‖^2

def parentSquareCost {n : ℕ} (a : Fin (n+2) → ℂ) {b : Fin (n+1) → ℂ} {u : ℂ}
    {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw b u κ)
    (α : κ → (fromRoots a).roots.toFinset → ℝ) : ℝ :=
  ∑ ij : κ × (fromRoots a).roots.toFinset,
    L.weights ij.1*α ij.1 ij.2*chainCost (Fin.snoc (L.paths ij.1) (ij.2:ℂ))^2





end
end DerivativeChainPhaseLock


