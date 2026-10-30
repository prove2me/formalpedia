-- Prove2me | Definitions.Def_DerivativeChainAnalytic_WassersteinSufficiency
-- name    : DerivativeChainAnalytic_WassersteinSufficiency
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:59:34.834192+00:00
-- url     : https://prove2.me/theorems/f5d6b6f4-95f1-4aa2-a816-2ef750303502
-- title:
--   Uniform-source variance and endpoint square cost
-- statement:
--   Specialize the canonical weighted-root variance and square endpoint cost to the uniform weights 1/(n+1) on the supplied root array.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/WassersteinSufficiency.lean, lines 13-14, SHA-256 3b7ca058ac2eb652fff15d783c7e54d45d8aa1b2fa2e4758aba92467d178defd. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/WassersteinSufficiency.lean, lines 16-17, SHA-256 3b7ca058ac2eb652fff15d783c7e54d45d8aa1b2fa2e4758aba92467d178defd. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_KappaDefinitions
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
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainFiniteHistory
open DerivativeChainPrefixLaws
namespace DerivativeChainPhaseLock
noncomputable section

def uniformSourceVariance {n : ℕ} (a : Fin (n+1) → ℂ) : ℝ :=
  rootLawVariance a (fun _ => (n+1:ℝ)⁻¹)

def uniformSourceSquareCost {n : ℕ} (a : Fin (n+1) → ℂ) : ℝ :=
  rootLawSquareCost a (fun _ => (n+1:ℝ)⁻¹)













end
end DerivativeChainPhaseLock


