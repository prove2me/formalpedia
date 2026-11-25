-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqBilinearSeriesOfBiadditive
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqBilinearSeriesOfBiadditive
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:17.120584+00:00
-- url     : https://prove2.me/theorems/d6229873-3252-450d-96f5-aef0c9605ceb
-- title:
--   Jet Eq Bilinear Series Of Biadditive
-- statement:
--   Definitions and structural lemmas for Jet Eq Bilinear Series Of Biadditive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesJetEqCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.BilAdd
variable {k : Type} [CommRing k] {d : ℕ}
def degIn (j : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) : ℕ := ∑ i, e (j, i)
end GlobalTheory.ChartCmp.BilAdd


