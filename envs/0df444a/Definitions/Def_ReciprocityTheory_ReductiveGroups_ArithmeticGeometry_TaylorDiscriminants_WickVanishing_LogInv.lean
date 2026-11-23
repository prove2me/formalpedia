-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:41.359298+00:00
-- url     : https://prove2.me/theorems/12d129d1-fd58-4bb8-ae97-11d6a400b5eb
-- title:
--   Log Inv
-- statement:
--   Definitions and structural lemmas for Log Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogInv.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
def Jac : Fin d → Fin d → PS k 1 d := fun i b => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F i))
def Ar : Fin d → Fin d → PS k 2 d := fun i b => pderiv k ((1 : Fin 2), b) (G.F i)
section Fams
end Fams
end ReciprocityTheory.ChartRestriction.G.TB.LogPf


