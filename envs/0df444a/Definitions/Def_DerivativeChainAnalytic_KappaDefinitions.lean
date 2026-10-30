-- Prove2me | Definitions.Def_DerivativeChainAnalytic_KappaDefinitions
-- name    : DerivativeChainAnalytic_KappaDefinitions
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:58:39.989515+00:00
-- url     : https://prove2.me/theorems/12da8143-c121-4d0b-840b-cfb9b8c4adcd
-- title:
--   Canonical balanced-root variance, κ and Bellman values
-- statement:
--   Balanced root weights are nonnegative, sum to one, and have weighted mean equal to the source centroid. Define their weighted squared distance from that centroid and their weighted squared optimal endpoint cost. The ratio set divides the latter by the former only when the variance is strictly positive; κ is its real infimum. The Bellman value is the real infimum of square cost minus K times variance over all balanced weights, without a positive-variance restriction. These are the source conventions, including the real empty-infimum value zero.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/KappaDefinitions.lean, lines 10-11, SHA-256 50f10408a5067bc9b37033cd80b3e3ea3a2f648628cd8d13ead13960482c32e5. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/KappaDefinitions.lean, lines 13-14, SHA-256 50f10408a5067bc9b37033cd80b3e3ea3a2f648628cd8d13ead13960482c32e5. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/KappaDefinitions.lean, lines 16-17, SHA-256 50f10408a5067bc9b37033cd80b3e3ea3a2f648628cd8d13ead13960482c32e5. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/KappaDefinitions.lean, lines 19-21, SHA-256 50f10408a5067bc9b37033cd80b3e3ea3a2f648628cd8d13ead13960482c32e5. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/KappaDefinitions.lean, lines 23-24, SHA-256 50f10408a5067bc9b37033cd80b3e3ea3a2f648628cd8d13ead13960482c32e5. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/KappaDefinitions.lean, lines 26-28, SHA-256 50f10408a5067bc9b37033cd80b3e3ea3a2f648628cd8d13ead13960482c32e5. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
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
open DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainPrefixLaws
noncomputable section

def BalancedWeights {ι : Type*} [Fintype ι] (a : ι → ℂ) (u : ℂ) (w : ι → ℝ) : Prop :=
  (∀ i,0 ≤ w i) ∧ (∑ i,w i=1) ∧ (∑ i,(w i:ℂ)*a i=u)

noncomputable def rootLawVariance {n : ℕ} (a : Fin (n+1) → ℂ) (w : Fin (n+1) → ℝ) : ℝ :=
  ∑ i,w i*‖a i-complexCentroid a‖^2

noncomputable def rootLawSquareCost {n : ℕ} (a : Fin (n+1) → ℂ) (w : Fin (n+1) → ℝ) : ℝ :=
  ∑ i,w i*(complexEndpointCost a (a i))^2

noncomputable def ratioValues {n : ℕ} (a : Fin (n+1) → ℂ) : Set ℝ :=
  {q | ∃ w : Fin (n+1) → ℝ, BalancedWeights a (complexCentroid a) w ∧
    0 < rootLawVariance a w ∧ q=rootLawSquareCost a w/rootLawVariance a w}

/-- Zero variance is excluded; a collapsed source has the explicit real empty-infimum value zero. -/
noncomputable def kappa {n : ℕ} (a : Fin (n+1) → ℂ) : ℝ := sInf (ratioValues a)

noncomputable def bellmanValue {n : ℕ} (a : Fin (n+1) → ℂ) (K : ℝ) : ℝ :=
  sInf {q | ∃ w : Fin (n+1) → ℝ, BalancedWeights a (complexCentroid a) w ∧
    q=rootLawSquareCost a w-K*rootLawVariance a w}























end
end DerivativeChainPrefixLaws


