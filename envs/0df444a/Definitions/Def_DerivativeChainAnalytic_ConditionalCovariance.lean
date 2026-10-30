-- Prove2me | Definitions.Def_DerivativeChainAnalytic_ConditionalCovariance
-- name    : DerivativeChainAnalytic_ConditionalCovariance
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:57:59.866689+00:00
-- url     : https://prove2.me/theorems/2fa35006-ad15-4a81-89a5-8221def336f3
-- title:
--   Planar vectors and weighted second-moment matrices
-- statement:
--   Identify a complex number with its real and imaginary coordinates. Define the weighted matrix sum of outer products of z(i)−u, then apply it to a kernel row about x(i). The supplied reference need not be the mean and the supplied weights need not form a probability law; those hypotheses belong to later theorems.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/ConditionalCovariance.lean, lines 10-10, SHA-256 bd95a5c89932fc1be2c46615ce63470d8ab2bc95fe14447d56cd3446d6f159d7. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/ConditionalCovariance.lean, lines 12-15, SHA-256 bd95a5c89932fc1be2c46615ce63470d8ab2bc95fe14447d56cd3446d6f159d7. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/ConditionalCovariance.lean, lines 17-19, SHA-256 bd95a5c89932fc1be2c46615ce63470d8ab2bc95fe14447d56cd3446d6f159d7. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
set_option maxHeartbeats 1500000
open scoped BigOperators
open Matrix
namespace DerivativeChainPrefixLaws
noncomputable section

noncomputable def planarVector (z : ℂ) : Fin 2 → ℝ := ![z.re,z.im]

/-- Second moment about the supplied reference; it is covariance when that reference is the mean. -/
noncomputable def centeredMomentMatrix {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → ℂ) (u : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ i,w i • vecMulVec (planarVector (z i-u)) (planarVector (z i-u))

noncomputable def conditionalCovariance {ι κ : Type*} [Fintype κ]
    (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ) (i : ι) : Matrix (Fin 2) (Fin 2) ℝ :=
  centeredMomentMatrix (K i) y (x i)















end
end DerivativeChainPrefixLaws


