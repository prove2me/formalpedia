-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondPartialLawPushAlongTripleMap
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondPartialLawPushAlongTripleMap
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:20.276293+00:00
-- url     : https://prove2.me/theorems/8897ee1f-8c6e-5f42-8e0b-54e3b378c065
-- title:
--   Second Partial Law Push Along Triple Map
-- statement:
--   Definitions and structural lemmas for Second Partial Law Push Along Triple Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondPartialLawPushAlongTripleMap.lean

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
namespace GlobalTheory.PushSecondLaw
open MvPolynomial (X)
open GlobalTheory.SecondPartialLaw
section Values
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
  {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {ε : K → ℤ} {z : Z} {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι}
end Values
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
end GlobalTheory.PushSecondLaw


