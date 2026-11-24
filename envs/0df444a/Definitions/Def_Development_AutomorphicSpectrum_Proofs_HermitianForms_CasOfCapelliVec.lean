-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_CasOfCapelliVec
-- name    : Development_AutomorphicSpectrum_Proofs_HermitianForms_CasOfCapelliVec
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:47.261037+00:00
-- url     : https://prove2.me/theorems/9a34fd66-cc33-464e-995a-dddad7d161f1
-- title:
--   Cas Of Capelli Vec
-- statement:
--   Definitions and structural lemmas for Cas Of Capelli Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/CasOfCapelliVec.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Polynomial
noncomputable def rev {ι : Type} (s : Finset ι) (f : ι → ℂ) : ℂ[X] := ∏ l ∈ s, (1 + C (f l) * X)
end GlobalTheory.CompanionTheory.Inh.CapelliCasimir


