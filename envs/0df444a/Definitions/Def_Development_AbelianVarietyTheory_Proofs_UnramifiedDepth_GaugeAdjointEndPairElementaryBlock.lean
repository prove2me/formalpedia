-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeAdjointEndPairElementaryBlock
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeAdjointEndPairElementaryBlock
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-27T05:55:46.442638+00:00
-- url     : https://prove2.me/theorems/673e4baf-9b7b-5a3f-9491-5f4440cab86a
-- title:
--   Gauge Adjoint End Pair Elementary Block
-- statement:
--   Definitions and structural lemmas for Gauge Adjoint End Pair Elementary Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeAdjointEndPairElementaryBlock.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.RowLaw.EndBlock
open MvPowerSeries
variable {C : Type} [Field C]
section General
variable {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ] (X : RawChart C d I κ)
end General
section Square
variable {dd : ℕ}
variable {d d' : ℕ} {I I' : Fin 2 → Type} (X : RawChart C d I (Fin dd)) (Z : RawChart C d' I' (Fin 2 × Fin dd))
end Square
end GlobalTheory.RowLaw.EndBlock


