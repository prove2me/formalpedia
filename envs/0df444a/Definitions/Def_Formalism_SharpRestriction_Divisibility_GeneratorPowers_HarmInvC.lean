-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvC
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:54.927805+00:00
-- url     : https://prove2.me/theorems/5efd175d-c7ad-4ba4-b5d8-e98d95a78b2c
-- title:
--   Harm Inv C
-- statement:
--   Definitions and structural lemmas for Harm Inv C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvC.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddFin
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
section Col
variable {S : Type} [CommRing S] {n d : ℕ}
def sb (b : Fin n) : Fin 1 × Fin d → MvPowerSeries (Fin n × Fin d) S := fun p => MvPowerSeries.X ((b, p.2))
end Col
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC


