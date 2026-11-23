-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralSecond
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralSecond
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:51.584905+00:00
-- url     : https://prove2.me/theorems/77133ac7-3258-4333-85c8-2d8df4fa79e5
-- title:
--   Cm Type Period Integral Second
-- statement:
--   Definitions and structural lemmas for Cm Type Period Integral Second, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralSecond.lean

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
namespace GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
end GlobalTheory.EigenLattice


