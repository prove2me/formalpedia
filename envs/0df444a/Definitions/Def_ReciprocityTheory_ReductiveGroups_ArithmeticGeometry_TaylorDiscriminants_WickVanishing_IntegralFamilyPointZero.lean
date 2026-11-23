-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:11.573643+00:00
-- url     : https://prove2.me/theorems/53fdffaf-a67b-4021-80b1-da45a9e0052f
-- title:
--   Integral Family Point Zero
-- statement:
--   Definitions and structural lemmas for Integral Family Point Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/IntegralFamilyPointZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
section Int
variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
def Ig (σ : Type) : Subring (MvPowerSeries σ k) := (MvPowerSeries.map (σ := σ) (algebraMap R k)).range
variable {R k}
end Int
section Fam
variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {d : ℕ}
end Fam
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab


