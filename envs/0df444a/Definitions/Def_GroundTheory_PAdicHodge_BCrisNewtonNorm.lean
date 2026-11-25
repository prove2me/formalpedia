-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
-- name    : GroundTheory_PAdicHodge_BCrisNewtonNorm
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:44.924949+00:00
-- url     : https://prove2.me/theorems/07fe9e2b-4603-4fe6-b367-a578e0048d9d
-- title:
--   BCris Newton Norm
-- statement:
--   Definitions and structural lemmas for BCris Newton Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
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
open _root_.WittVector Laurent
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable (K p) in

def gn (ρ : ℝ) (z : 𝔸) : ℝ := gaussNorm ((teichLift K p).coeffB (toB K p z)) ρ
variable {ρ : ℝ}
variable [CharZero K]
end WittTilt
end GroundTheory.PAdicHodge


