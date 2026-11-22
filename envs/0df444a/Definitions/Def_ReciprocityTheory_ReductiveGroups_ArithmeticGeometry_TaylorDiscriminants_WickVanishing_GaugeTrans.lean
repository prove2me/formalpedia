-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:50.580655+00:00
-- url     : https://prove2.me/theorems/8415ba2f-b8de-48ef-a79c-ff54501bd23c
-- title:
--   Gauge Trans
-- statement:
--   Definitions and structural lemmas for Gauge Trans, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
section Exp2
variable (A : Type) [CommRing A] [Algebra ℚ A]
end Exp2
section Ev
variable {k : Type} [CommRing k] {d : ℕ}
def GP {n : ℕ} (a : Pt k n d) : Prop := ∀ i, constantCoeff (a i) = 0
end Ev
section Calc
variable {k : Type} [CommRing k] {d : ℕ}
def evP {m n : ℕ} (V : Fin m → Pt k n d) (a : Pt k m d) : Pt k n d := fun i => ev V (a i)
end Calc
section Calc2
variable {k : Type} [CommRing k] {d : ℕ}
end Calc2
section Main
end Main
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing


