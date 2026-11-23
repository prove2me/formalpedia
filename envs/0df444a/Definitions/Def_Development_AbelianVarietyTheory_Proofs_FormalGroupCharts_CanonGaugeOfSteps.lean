-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeOfSteps
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeOfSteps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:49.958434+00:00
-- url     : https://prove2.me/theorems/fff2d0ca-abad-4eb3-bf63-edcddf542bb0
-- title:
--   Canon Gauge Of Steps
-- statement:
--   Definitions and structural lemmas for Canon Gauge Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeOfSteps.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.CanonGaugeAssembly
variable {k : Type} [CommRing k] {d : ℕ}
structure Cob {n : ℕ} (c : PS k 2 d → PS k n d) : Prop where
  add : ∀ f g, c (f + g) = c f + c g
  const : ∀ f, constantCoeff f = 0 → constantCoeff (c f) = 0
end GlobalTheory.CanonGaugeAssembly


