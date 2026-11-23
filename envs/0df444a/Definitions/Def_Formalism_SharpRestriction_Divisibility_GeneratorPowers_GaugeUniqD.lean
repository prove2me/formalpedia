-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqD
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:55.669802+00:00
-- url     : https://prove2.me/theorems/1dcaa8aa-acab-401c-88fa-b04e801ab79b
-- title:
--   Gauge Uniq D
-- statement:
--   Definitions and structural lemmas for Gauge Uniq D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqD.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeBeta
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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GaugeR
def gam (A : Type) [CommRing A] : Γ(Sp A, ⊤) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
end GaugeR
end Formalism.MainNotions.ModuliIntegralCharts.H1


