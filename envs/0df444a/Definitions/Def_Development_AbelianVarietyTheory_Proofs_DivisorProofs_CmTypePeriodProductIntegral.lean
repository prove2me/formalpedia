-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:59.545743+00:00
-- url     : https://prove2.me/theorems/73ca8b7f-ab6b-457c-b714-14e479ef8c2d
-- title:
--   Cm Type Period Product Integral
-- statement:
--   Definitions and structural lemmas for Cm Type Period Product Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodProductIntegral.lean

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
namespace GlobalTheory.Div.eigen_line_bilinear
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
end SlopeTestRemainingChoices
end GlobalTheory.Div.eigen_line_bilinear


