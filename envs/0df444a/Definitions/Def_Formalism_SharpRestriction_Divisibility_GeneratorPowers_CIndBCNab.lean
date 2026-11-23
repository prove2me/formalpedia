-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:33.777794+00:00
-- url     : https://prove2.me/theorems/776c614c-0f1e-498b-ab8f-9fdc37bb249a
-- title:
--   CInd BCNab
-- statement:
--   Definitions and structural lemmas for CInd BCNab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {d : ℕ}
variable [Algebra ℚ S] [Algebra ℚ S']
variable {O : Type} [CommRing O] [StarRing O]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CIndBCNab
end Formalism.MainNotions.ModuliIntegralCharts.H1


