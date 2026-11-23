-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:51.126487+00:00
-- url     : https://prove2.me/theorems/21b17df0-c23b-4eee-ac43-87d566bfc0a4
-- title:
--   Chart Chg Pf TP
-- statement:
--   Definitions and structural lemmas for Chart Chg Pf TP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
namespace ChartChgPfTP
variable {k : Type} [CommRing k]
def OrdGE {σ : Type} (r : ℕ) (g : MvPowerSeries σ k) : Prop := ∀ e : σ →₀ ℕ, e.degree < r → coeff e g = 0
variable {d : ℕ}
section Trans
variable {F : Fin d → PS k 2 d} {φ φi : Pt k 1 d}
end Trans
section Trans2
variable {F : Fin d → PS k 2 d} {φ φi : Pt k 1 d}
end Trans2
section Trans3
variable {F : Fin d → PS k 2 d} {φ φi : Pt k 1 d}
end Trans3
end ChartChgPfTP
end ReciprocityTheory.ChartRestriction.G.TB


