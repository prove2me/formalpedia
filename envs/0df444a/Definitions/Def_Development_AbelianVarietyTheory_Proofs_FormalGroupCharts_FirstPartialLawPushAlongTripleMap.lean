-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstPartialLawPushAlongTripleMap
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstPartialLawPushAlongTripleMap
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:14.646334+00:00
-- url     : https://prove2.me/theorems/866d4c1d-1f21-4a18-8913-c8de27e39ae4
-- title:
--   First Partial Law Push Along Triple Map
-- statement:
--   Definitions and structural lemmas for First Partial Law Push Along Triple Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstPartialLawPushAlongTripleMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.PushFirstLaw
section Val
variable {X X' Y Z : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι)
def isoVal (ψ : Z ⟶ X') : (Z.presheaf.stalk z)ˣ :=
  gm ψ z ((LB.div (L.pull F) L').U (fun _ => J (ψ ≫ F), J' ψ)) (w.s (fun _ => J (ψ ≫ F), J' ψ))
variable {w z J J'}
end Val
section Cube
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
end Cube
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
end GlobalTheory.PushFirstLaw
namespace GlobalTheory
open PushFirstLaw
end GlobalTheory


