-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:11.175855+00:00
-- url     : https://prove2.me/theorems/5443b87f-cf38-40f0-a0ca-1c3f9dba45c4
-- title:
--   Prim Uniq St
-- statement:
--   Definitions and structural lemmas for Prim Uniq St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PrimUniqSt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
def PrimUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (wP wP' : PrimTy H Xo), IsPrim wP → IsPrim wP' → wP = wP'
def PrimUniqOfGlobalSt : Prop :=
  GlobalFnsSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l), IsAbelianScheme Xo.univ.t.G →
    ∀ wP wP' : PrimTy H Xo, IsPrim wP → IsPrim wP' → wP = wP'
end Formalism.MainNotions.ModuliIntegralCharts.H1


