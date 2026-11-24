-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_StepRatioAbsVwProd
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_StepRatioAbsVwProd
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:24.692172+00:00
-- url     : https://prove2.me/theorems/4a0e36d1-80b7-404a-8a12-8208fafd855c
-- title:
--   Step Ratio Abs Vw Prod
-- statement:
--   Definitions and structural lemmas for Step Ratio Abs Vw Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/StepRatioAbsVwProd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
namespace GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end GlobalTheory.Square


