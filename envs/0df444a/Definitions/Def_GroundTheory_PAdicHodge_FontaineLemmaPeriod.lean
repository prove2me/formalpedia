-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod
-- name    : GroundTheory_PAdicHodge_FontaineLemmaPeriod
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:06:38.503807+00:00
-- url     : https://prove2.me/theorems/c612fee8-f6d5-5e48-9c43-552328914c9a
-- title:
--   Fontaine Lemma Period
-- statement:
--   Definitions and structural lemmas for Fontaine Lemma Period, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open _root_.WittVector
namespace ACris
section NumberTheory
variable {p : ℕ} [hp : Fact p.Prime]
end NumberTheory
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
end ACris
end GroundTheory.PAdicHodge


