-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:02.595254+00:00
-- url     : https://prove2.me/theorems/31738447-9cbb-4adc-b850-c9caf79134b4
-- title:
--   Rel Index Eq Of Surj
-- statement:
--   Definitions and structural lemmas for Rel Index Eq Of Surj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
namespace GlobalTheory.BorelUMod.Cayley
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
def cay (t : L) (u : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L := (1 + t • (u - 1))⁻¹ * (u - 1)
end GlobalTheory.BorelUMod.Cayley


