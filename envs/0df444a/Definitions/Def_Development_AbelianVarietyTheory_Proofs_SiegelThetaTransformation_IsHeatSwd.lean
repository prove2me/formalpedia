-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatSwd
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatSwd
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:40:28.488362+00:00
-- url     : https://prove2.me/theorems/9eb3e0fb-1b77-42f8-a8a8-ba534d534b0b
-- title:
--   Is Heat Swd
-- statement:
--   Definitions and structural lemmas for Is Heat Swd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatSwd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThHStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.SwdHeat
open GlobalTheory.SW.EisHeat
section Linear
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
end Linear
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
end GlobalTheory.SW.SwdHeat


