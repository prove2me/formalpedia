-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:46.402812+00:00
-- url     : https://prove2.me/theorems/7fcc8ecb-e083-4255-99e6-c6b47fb948b7
-- title:
--   Harm Inv B
-- statement:
--   Definitions and structural lemmas for Harm Inv B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvB.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
section Log
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB.LogPf
end Log
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
def qT (cc : Fin d → Fin d → S) (u : Lt1 Dw → Fin d → S) (t : Fin 1 × Fin (dL Dw) → S) (i l : Fin d)
    (ℓ ℓ' : Lt1 Dw) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  MvPowerSeries.C (cc i l * u ℓ i * u ℓ' l * t (0, ltIdx Dw ℓ')) *
    (MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ) * MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ'))
def qβ (cc : Fin d → Fin d → S) (u : Lt1 Dw → Fin d → S) (t : Fin 1 × Fin (dL Dw) → S) :
    Matrix (Fin (dL Dw)) (Fin (dL Dw)) S :=
  fun p p' => ∑ i, ∑ l, cc i l * u ((ltIdx Dw).symm p) i * u ((ltIdx Dw).symm p') l * t (0, p')
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB


