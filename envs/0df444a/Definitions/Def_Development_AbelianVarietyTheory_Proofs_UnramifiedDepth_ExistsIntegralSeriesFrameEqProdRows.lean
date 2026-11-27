-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralSeriesFrameEqProdRows
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralSeriesFrameEqProdRows
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-27T06:11:06.72871+00:00
-- url     : https://prove2.me/theorems/33292ec8-cb7b-5953-8a61-be4e22aa70d3
-- title:
--   Exists Integral Series Frame Eq Prod Rows
-- statement:
--   Definitions and structural lemmas for Exists Integral Series Frame Eq Prod Rows, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralSeriesFrameEqProdRows.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeBiadditiveSymmAdjointIntegralEnd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.RowVal.PlaneRead
open MvPowerSeries EndCalc
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}
def expAt (X : RawChart C d I κ) {ω : Type} [Fintype ω] (v : ω → κ → C) : κ → MvPowerSeries ω C :=
  fun x => subst (fun i : κ => ∑ w, v w i • (MvPowerSeries.X w : MvPowerSeries ω C)) (X.ex x)
end GlobalTheory.RowVal.PlaneRead
namespace GlobalTheory.RowVal
open PlaneRead EndCalc
end GlobalTheory.RowVal


