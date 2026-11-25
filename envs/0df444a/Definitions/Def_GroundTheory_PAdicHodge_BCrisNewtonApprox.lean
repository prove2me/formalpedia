-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
-- name    : GroundTheory_PAdicHodge_BCrisNewtonApprox
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:09.524797+00:00
-- url     : https://prove2.me/theorems/09923b96-18fd-4420-96ef-5cd29625c8ee
-- title:
--   BCris Newton Approx
-- statement:
--   Definitions and structural lemmas for BCris Newton Approx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
namespace WittTilt
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
end WittTilt
end GroundTheory.PAdicHodge


