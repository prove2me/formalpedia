-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsSymplecticActionOfPeriodLatticeMap
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsSymplecticActionOfPeriodLatticeMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:22.453717+00:00
-- url     : https://prove2.me/theorems/61596e43-683d-47b5-8fb9-aad8a2ff2b29
-- title:
--   Exists Symplectic Action Of Period Lattice Map
-- statement:
--   Definitions and structural lemmas for Exists Symplectic Action Of Period Lattice Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsSymplecticActionOfPeriodLatticeMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SymplecticPeriods
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.SymplecticPeriods


