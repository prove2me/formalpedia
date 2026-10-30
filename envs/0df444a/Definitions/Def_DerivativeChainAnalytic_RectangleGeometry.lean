-- Prove2me | Definitions.Def_DerivativeChainAnalytic_RectangleGeometry
-- name    : DerivativeChainAnalytic_RectangleGeometry
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:54:20.435445+00:00
-- url     : https://prove2.me/theorems/d223c96e-3f94-4448-b2d2-fe02b77523f8
-- title:
--   Rectangle roots and explicit candidate history arrays
-- statement:
--   Define the four complex points ±x±iy and the four source candidate sequences from zero through the corresponding signed b/√3 and b values to those points. Actual-chain validity is a later theorem with its required hypotheses.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/RectangleGeometry.lean, lines 13-17, SHA-256 3c951a99d41e3720c5be89b18c5fb552a210a6e7344b6e05bf56d3d55c1fe15f. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/RectangleGeometry.lean, lines 9-11, SHA-256 3c951a99d41e3720c5be89b18c5fb552a210a6e7344b6e05bf56d3d55c1fe15f. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
open Polynomial DerivativeChainPrivate
namespace DerivativeChainPhaseLock

noncomputable def rectangleRoots (x y : ℝ) : Fin 4 → ℂ :=
  ![(x:ℂ)+(y:ℂ)*Complex.I,(x:ℂ)-(y:ℂ)*Complex.I,
    -(x:ℂ)+(y:ℂ)*Complex.I,-(x:ℂ)-(y:ℂ)*Complex.I]

noncomputable def rectangleHistory (x y b : ℝ) : Fin 4 → Fin 4 → ℂ :=
  ![![0,((b/Real.sqrt 3:ℝ):ℂ),(b:ℂ),rectangleRoots x y 0],
    ![0,((b/Real.sqrt 3:ℝ):ℂ),(b:ℂ),rectangleRoots x y 1],
    ![0,-((b/Real.sqrt 3:ℝ):ℂ),-(b:ℂ),rectangleRoots x y 2],
    ![0,-((b/Real.sqrt 3:ℝ):ℂ),-(b:ℂ),rectangleRoots x y 3]]















end DerivativeChainPhaseLock


