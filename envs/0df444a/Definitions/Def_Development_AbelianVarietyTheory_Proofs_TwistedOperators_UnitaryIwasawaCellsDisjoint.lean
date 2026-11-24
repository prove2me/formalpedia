-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCellsDisjoint
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCellsDisjoint
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:28:08.701795+00:00
-- url     : https://prove2.me/theorems/2bf41da5-7570-463d-9c84-afb56ea0e976
-- title:
--   Unitary Iwasawa Cells Disjoint
-- statement:
--   Definitions and structural lemmas for Unitary Iwasawa Cells Disjoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryIwasawaCellsDisjoint.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
namespace GlobalTheory.InertZeta
section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
end
end GlobalTheory.InertZeta


