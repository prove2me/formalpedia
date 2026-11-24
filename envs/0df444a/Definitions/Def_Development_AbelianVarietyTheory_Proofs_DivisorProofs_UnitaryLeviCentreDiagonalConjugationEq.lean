-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviCentreDiagonalConjugationEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviCentreDiagonalConjugationEq
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:09:41.683593+00:00
-- url     : https://prove2.me/theorems/08d54c91-bdef-4099-a027-1129d43c6e46
-- title:
--   Unitary Levi Centre Diagonal Conjugation Eq
-- statement:
--   Definitions and structural lemmas for Unitary Levi Centre Diagonal Conjugation Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryLeviCentreDiagonalConjugationEq.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl.TorusConjProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
end GlobalTheory.SatakeWeyl.TorusConjProof


