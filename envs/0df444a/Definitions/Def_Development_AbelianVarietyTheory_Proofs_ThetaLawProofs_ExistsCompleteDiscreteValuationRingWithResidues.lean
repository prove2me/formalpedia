-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:15.59293+00:00
-- url     : https://prove2.me/theorems/9532ecb5-5240-4bd6-b470-4abc421258c6
-- title:
--   Exists Complete Discrete Valuation Ring With Residues
-- statement:
--   Definitions and structural lemmas for Exists Complete Discrete Valuation Ring With Residues, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
namespace GlobalTheory
namespace ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
end ResidueExtension
end GlobalTheory


