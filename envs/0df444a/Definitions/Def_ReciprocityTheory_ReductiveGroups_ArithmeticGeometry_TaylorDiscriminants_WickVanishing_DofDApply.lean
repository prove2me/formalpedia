-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:40.093002+00:00
-- url     : https://prove2.me/theorems/a9bd4b53-cf11-4928-bad8-6473ca1e0e5a
-- title:
--   Dof DApply
-- statement:
--   Definitions and structural lemmas for Dof DApply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofDApply.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
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
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
def dofCoef (F : Fin d → PS k 2 d) (v : Fin d → k) (j : Fin d) : PS k 1 d :=
  ∑ i : Fin d, C (v i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (F j))
def dofD (F : Fin d → PS k 2 d) (v : Fin d → k) : Derivation k (PS k 1 d) (PS k 1 d) :=
  ∑ j : Fin d, dofCoef F v j • pderiv k ((0 : Fin 1), j)
end ReciprocityTheory.ChartRestriction.G.TB.GE


