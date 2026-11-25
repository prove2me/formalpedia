-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TangentDirectionTwoChartsLinearPart
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TangentDirectionTwoChartsLinearPart
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:54.234962+00:00
-- url     : https://prove2.me/theorems/be2a1ad0-ac9b-4722-b50c-8b304f3c14a9
-- title:
--   Tangent Direction Two Charts Linear Part
-- statement:
--   Definitions and structural lemmas for Tangent Direction Two Charts Linear Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TangentDirectionTwoChartsLinearPart.lean

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
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
namespace GlobalTheory.ChartCmp.CoordDir
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
  {t : SAB H (Sp V)} {d : ℕ}
def tanPt (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (g : Fin 1 × Fin d → V) :
    overAt (𝟙 (Sp V)) (DualNumber V) ⟶ t.G :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (tp g) ≫ x 1
variable {κ : Type} [Fintype κ] {G : FGLaw V d} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V}
  {tg : κ → (Sp (DualNumber V) ⟶ t.G.left)} {uv : κ → Fin d → V} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}
end
end GlobalTheory.ChartCmp.CoordDir


