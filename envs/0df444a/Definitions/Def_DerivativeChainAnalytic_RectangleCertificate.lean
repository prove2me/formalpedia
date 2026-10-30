-- Prove2me | Definitions.Def_DerivativeChainAnalytic_RectangleCertificate
-- name    : DerivativeChainAnalytic_RectangleCertificate
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:54:05.893973+00:00
-- url     : https://prove2.me/theorems/cb9202c4-ea6f-4809-bf82-3415f624b3b7
-- title:
--   Fixed rational Bernstein coefficient vector
-- statement:
--   Define the source’s explicit 17-entry rational vector rectangleBernsteinWeights. Positivity and its polynomial identity are separate theorem claims.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/RectangleCertificate.lean, lines 7-7, SHA-256 50f81bd5564a684ccc69de51670ce4776c16d84b5c967527317be4cff5f98d13. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace DerivativeChainPhaseLock

noncomputable def rectangleBernsteinWeights : Fin 17 → ℝ := ![(136161/5000:ℝ), (790443/1250:ℝ), (14143453/2500:ℝ), (7067663/250:ℝ), (91040139/1000:ℝ), (126527539/625:ℝ), (401860261/1250:ℝ), (230283009/625:ℝ), (60288591/200:ℝ), (42276531/250:ℝ), (147756213/2500:ℝ), (13171343/1250:ℝ), (10684441/5000:ℝ), (354456/125:ℝ), (46741/25:ℝ), (2746/5:ℝ), 63]









end DerivativeChainPhaseLock


