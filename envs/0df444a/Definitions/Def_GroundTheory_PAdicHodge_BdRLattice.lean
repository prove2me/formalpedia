-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
-- name    : GroundTheory_PAdicHodge_BdRLattice
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:52.948866+00:00
-- url     : https://prove2.me/theorems/6780e839-85e9-4e22-b5b5-a02c7ac400f9
-- title:
--   Bd RLattice
-- statement:
--   Definitions and structural lemmas for Bd RLattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
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
open Ideal WittVector IsLocalRing
section Binomial
variable {A : Type*} [CommRing A]
end Binomial
namespace IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
variable {ξ : WittVector p (PreTilt (normInteger K) p)}
end IsPerfectoidField
end GroundTheory.PAdicHodge


