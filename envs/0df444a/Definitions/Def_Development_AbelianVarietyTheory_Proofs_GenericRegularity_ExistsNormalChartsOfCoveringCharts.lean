-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsNormalChartsOfCoveringCharts
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsNormalChartsOfCoveringCharts
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:23:20.070233+00:00
-- url     : https://prove2.me/theorems/6249d14a-2e16-585d-846d-8d88b74619c3
-- title:
--   Exists Normal Charts Of Covering Charts
-- statement:
--   Definitions and structural lemmas for Exists Normal Charts Of Covering Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsNormalChartsOfCoveringCharts.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_NaturalRuleValueBaseChangeOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsMulEqOfSubfieldClosureEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsExtendOfPowDenom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_InjectiveAlgebraMapOfDvrOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsUnramifiedExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.PlaceCompletion
namespace GlobalTheory.Reg.NormalCharts
section Val
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
variable (V K') in

def imageVal : ValuationSubring K' := (valV V (K' := K')).valuationSubring
end Val
section Alg
variable {A : Type} [CommRing A] [IsDomain A]
end Alg
section Chart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} (P : PChart Xo c β)
  {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [IsDomain A]
  [Algebra O A] (io : c.F →+* FractionRing O) (α : P.Ω →+* FractionRing A)
def bdry : Ideal A := Ideal.span {x | ∃ e ∈ P.es, algebraMap A (FractionRing A) x = α e}
variable (hβ : ∀ a, io (β a) ∈ Set.range (algebraMap O (FractionRing O)))
  (hK : ∀ (k : c.F) (a b : O), io k * algebraMap O _ b = algebraMap O _ a →
    α (algebraMap c.F P.Ω k) * algebraMap A _ (algebraMap O A b) = algebraMap A _ (algebraMap O A a))
  (hg : ∀ g ∈ P.gens, α g ∈ Set.range (algebraMap A (FractionRing A)))
end Chart
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
end Main
end GlobalTheory.Reg.NormalCharts
namespace GlobalTheory.Reg
open NormalCharts
end GlobalTheory.Reg


