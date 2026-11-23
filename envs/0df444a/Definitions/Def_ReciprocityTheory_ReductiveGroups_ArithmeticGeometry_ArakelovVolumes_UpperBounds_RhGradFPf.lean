-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:53.866658+00:00
-- url     : https://prove2.me/theorems/41cf91e9-653a-411f-9d8b-2a902c410b68
-- title:
--   Rh Grad FPf
-- statement:
--   Definitions and structural lemmas for Rh Grad FPf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradFPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
open Filter Topology Set Matrix NumberField ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def eΨ : Fin X.Ψ.card ≃ X.Ψ := X.Ψ.equivFin.symm
def Zmap (z : V (nd X)) : V (nD X.Ψ.card X.p0 (r - X.p0)) :=
  WithLp.toLp 2 fun j => ExF.Zt X z (eΨ X (finProdFinEquiv.symm j).1)
    (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1 (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField
end ReciprocityTheory.ChartRestriction.G.AR.Up


