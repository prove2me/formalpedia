-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPureTypicalCurveWithIntegralTangent
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPureTypicalCurveWithIntegralTangent
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-27T06:21:16.7058+00:00
-- url     : https://prove2.me/theorems/6975a7f4-160c-536b-8f93-3b4185703c0f
-- title:
--   Exists Pure Typical Curve With Integral Tangent
-- statement:
--   Definitions and structural lemmas for Exists Pure Typical Curve With Integral Tangent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsPureTypicalCurveWithIntegralTangent.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CurveLogarithmsInvNatCastSmulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowExponentPartMemGaugedCurveLogarithmsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithmsStatement
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
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.RowLaw.PureTypical
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
def emb (X : RawChart C d I κ) (l : ℕ) (g : Fin 2) (b : ℕ → I g → C) (e : ℕ → JJ I g → C) :
    (κ → PowerSeries C) × (JJ I g → PowerSeries C) :=
  (fun i => tyS l fun s => ∑ c, X.u g c i * b s c, fun q => tyS l fun s => e s q)
section Main
variable [NeZero d] {X : RawChart C d I κ} {V : VF C}
end Main
end GlobalTheory.RowLaw.PureTypical
namespace GlobalTheory.RowLaw
end GlobalTheory.RowLaw


