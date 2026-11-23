-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:24.081668+00:00
-- url     : https://prove2.me/theorems/5751ad4c-fd5d-456e-a450-37863af8a607
-- title:
--   Mem Integers Of Mem Hat O
-- statement:
--   Definitions and structural lemmas for Mem Integers Of Mem Hat O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIntegersOfMemHatO.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.CMVal.Conv
variable {E : Type} [Field E] [NumberField E]
end GlobalTheory.CMVal.Conv


