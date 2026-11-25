-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:58:09.149247+00:00
-- url     : https://prove2.me/theorems/d3d64b1c-44bc-5433-86a4-51931e52fccb
-- title:
--   Chart Law Action Eq Transported Of Coord Rel
-- statement:
--   Definitions and structural lemmas for Chart Law Action Eq Transported Of Coord Rel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRel.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
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
namespace GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V] {d : ℕ}
def sub (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m k :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin k × Fin d => a p.1 p.2)
def sub1 (m : ℕ) {n : ℕ} (a : Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m 1 :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d => a p.2)
end GlobalTheory.ChartCmp.CoordLaw


