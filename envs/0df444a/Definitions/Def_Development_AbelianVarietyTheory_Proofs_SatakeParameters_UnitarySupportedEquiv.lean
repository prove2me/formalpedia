-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitarySupportedEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitarySupportedEquiv
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:57:54.205176+00:00
-- url     : https://prove2.me/theorems/cf4e24a9-ff53-40b0-9a6e-7e0478b11862
-- title:
--   Unitary Supported Equiv
-- statement:
--   Definitions and structural lemmas for Unitary Supported Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
namespace GlobalTheory.UnitarySplit
variable {A : Type} [CommRing A] {n : ℕ}
noncomputable def adj (c : A →+* A) (J M : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  J⁻¹ * cT c M * J
end GlobalTheory.UnitarySplit


