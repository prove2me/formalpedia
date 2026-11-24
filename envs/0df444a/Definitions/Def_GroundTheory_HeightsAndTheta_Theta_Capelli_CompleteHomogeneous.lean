-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
-- name    : GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:19.471405+00:00
-- url     : https://prove2.me/theorems/c5953ec1-78dc-4292-b244-030a7904a09e
-- title:
--   Complete Homogeneous
-- statement:
--   Definitions and structural lemmas for Complete Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
namespace SymmFun
open MvPolynomial Finset
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
noncomputable def hSeries (x : σ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun b => eval x (hsymm σ ℂ b)
end SymmFun
end GroundTheory.Heights₂.Theta
namespace GroundTheory.Heights₂.Theta
namespace SymmFun
open MvPolynomial Finset
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
end SymmFun
end GroundTheory.Heights₂.Theta


