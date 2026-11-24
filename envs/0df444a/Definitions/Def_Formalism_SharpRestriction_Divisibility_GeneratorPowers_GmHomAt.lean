-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:45.550853+00:00
-- url     : https://prove2.me/theorems/3c88ad6f-cb1d-4dde-ad6c-74b75dfc288b
-- title:
--   Gm Hom At
-- statement:
--   Definitions and structural lemmas for Gm Hom At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GmHomAt.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
abbrev σL (C : ChartAt Xo c y) (m : ℕ) : Fin 2 × Fin C.d → MvPolynomial (Fin 1 × Fin C.d) S :=
  fun p => (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn C.d m ![0] (C.B.A.act H.w0 j)] :
    Fin 2 → Fin C.d → MvPolynomial (Fin 1 × Fin C.d) S) p.1 p.2
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI


