-- Prove2me | Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
-- name    : DerivativeChainAnalytic_FiniteBalancedHistoryLaw
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:53:48.480951+00:00
-- url     : https://prove2.me/theorems/ee001c42-9792-4e17-abff-5baec020d635
-- title:
--   Finite balanced laws of actual complete histories
-- statement:
--   A finite probability law consists of nonnegative weights summing to one and actual complete derivative-root chains for a given root array. Every chain starts at the specified point u, and the weighted mean of its final point is u. The bundle also defines the weighted mean squared chain length and the weighted squared final-point distance from u. The original structure and its generated fields are retained exactly.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/FiniteBalancedHistoryLaw.lean, lines 19-21, SHA-256 d10f14356f6ce42b3c48add0198926f01a064a36edc7918e4aa9c63becdd3657. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/FiniteBalancedHistoryLaw.lean, lines 23-25, SHA-256 d10f14356f6ce42b3c48add0198926f01a064a36edc7918e4aa9c63becdd3657. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/FiniteBalancedHistoryLaw.lean, lines 9-17, SHA-256 d10f14356f6ce42b3c48add0198926f01a064a36edc7918e4aa9c63becdd3657. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
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
open scoped BigOperators
open DerivativeChainPrivate
universe v
namespace DerivativeChainFiniteHistory

structure FiniteBalancedHistoryLaw {n : ℕ} (a : Fin (n+1) → ℂ) (u : ℂ)
    (κ : Type v) [Fintype κ] where
  weights : κ → ℝ
  nonneg : ∀ i, 0 ≤ weights i
  total : ∑ i, weights i = 1
  paths : κ → Fin (n+1) → ℂ
  actual : ∀ i, IsChain a (paths i)
  start : ∀ i, paths i 0 = u
  balanced : ∑ i, (weights i : ℂ) * paths i (Fin.last n) = u

noncomputable def FiniteBalancedHistoryLaw.meanSquareCost {n : ℕ} {a : Fin (n+1) → ℂ}
    {u : ℂ} {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw a u κ) : ℝ :=
  ∑ i, L.weights i * chainCost (L.paths i)^2

noncomputable def FiniteBalancedHistoryLaw.endpointVariance {n : ℕ} {a : Fin (n+1) → ℂ}
    {u : ℂ} {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw a u κ) : ℝ :=
  ∑ i, L.weights i * ‖L.paths i (Fin.last n) - u‖^2







end DerivativeChainFiniteHistory


