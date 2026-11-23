-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:27.133751+00:00
-- url     : https://prove2.me/theorems/a33b6837-7c85-47c6-b6da-f03ea54c8019
-- title:
--   Formal Second Point Derivative Second Coordinate
-- statement:
--   Definitions and structural lemmas for Formal Second Point Derivative Second Coordinate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
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
namespace GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}
def dy (v : Fin d → k) (f : PS k 2 d) : PS k 1 d :=
  ∑ i, C (v i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) f)
def lin (v : Fin d → k) (f : PS k 1 d) : k :=
  ∑ i, v i * constantCoeff (pderiv k ((0 : Fin 1), i) f)
section Biadd
variable (F : Fin d → PS k 2 d) (hF : GP F) (g : PS k 2 d)
include hF
end Biadd
def up (a : Pt k 2 d) : Pt k 3 d := evP (n := 3) ![pt k d 0, pt k d 1] a
section Main
variable (F : Fin d → PS k 2 d) (hF : GP F) (g : PS k 2 d)
include hF
end Main
section BaseChange
variable {R : Type} [CommRing R] (φ : R →+* k)
def mapP {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map φ (a i)
end BaseChange
end GlobalTheory.QuadDeriv
namespace GlobalTheory
open QuadDeriv
end GlobalTheory


