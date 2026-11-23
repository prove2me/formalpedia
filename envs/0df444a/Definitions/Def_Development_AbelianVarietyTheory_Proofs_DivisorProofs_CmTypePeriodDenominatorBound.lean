-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:24.887796+00:00
-- url     : https://prove2.me/theorems/45922916-1ab5-47f5-809b-b94b8304fa89
-- title:
--   Cm Type Period Denominator Bound
-- statement:
--   Definitions and structural lemmas for Cm Type Period Denominator Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodDenominatorBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
namespace GlobalTheory.PairingBound
section V
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]
end V
end GlobalTheory.PairingBound
namespace GlobalTheory.PairingBound
end GlobalTheory.PairingBound


