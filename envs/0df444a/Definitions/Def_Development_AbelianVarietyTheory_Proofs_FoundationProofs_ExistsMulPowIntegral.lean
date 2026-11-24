-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMulPowIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMulPowIntegral
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:43.793008+00:00
-- url     : https://prove2.me/theorems/24a5208c-a481-4468-a6d0-bc7a11cdb34d
-- title:
--   Exists Mul Pow Integral
-- statement:
--   Definitions and structural lemmas for Exists Mul Pow Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMulPowIntegral.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
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
noncomputable section
namespace GlobalTheory.Square.AwayClosure
variable {K : Type} [Field K] [NumberField K]
end GlobalTheory.Square.AwayClosure
namespace GlobalTheory.Square
end GlobalTheory.Square


