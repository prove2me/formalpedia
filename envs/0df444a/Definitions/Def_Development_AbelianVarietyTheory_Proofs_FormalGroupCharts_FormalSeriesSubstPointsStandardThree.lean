-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:52.780674+00:00
-- url     : https://prove2.me/theorems/c2c78102-1219-469d-ac76-cb6e58c0206a
-- title:
--   Formal Series Subst Points Standard Three
-- statement:
--   Definitions and structural lemmas for Formal Series Subst Points Standard Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Sum
namespace GlobalTheory.FormalCocycle
section Tools
variable {k : Type} [CommRing k] {d : ℕ} {μ ν : Type}
def evAt {m : ℕ} (a : Fin m → Fin d → MvPowerSeries μ k) (f : PS k m d) : MvPowerSeries μ k :=
  subst (fun p : Fin m × Fin d => a p.1 p.2) f
def Cen (u : Fin d → MvPowerSeries μ k) : Prop := ∀ i, constantCoeff (u i) = 0
def addAt (F : Fin d → PS k 2 d) (u v : Fin d → MvPowerSeries μ k) :
    Fin d → MvPowerSeries μ k := fun i => evAt ![u, v] (F i)
def mapAt (φ : Pt k 1 d) (u : Fin d → MvPowerSeries μ k) : Fin d → MvPowerSeries μ k :=
  fun i => evAt ![u] (φ i)
end Tools
end GlobalTheory.FormalCocycle


