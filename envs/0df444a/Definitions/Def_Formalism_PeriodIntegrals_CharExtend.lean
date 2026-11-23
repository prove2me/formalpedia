-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_CharExtend
-- name    : Formalism_PeriodIntegrals_CharExtend
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:24.670433+00:00
-- url     : https://prove2.me/theorems/a128086c-eb45-4d1d-aae0-dc0c004d529a
-- title:
--   Char Extend
-- statement:
--   Definitions and structural lemmas for Char Extend, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/CharExtend.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def CharExtend : Prop :=
  ∀ (G : Type) [CommGroup G] (H : Subgroup G) (χ : H →* ℂˣ), ∃ ψ : G →* ℂˣ, ∀ h : H, ψ (h : G) = χ h
end PI


