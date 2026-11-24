-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhTwoValHolds
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhTwoValHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:20.492874+00:00
-- url     : https://prove2.me/theorems/9da46601-3ca4-488d-adab-e66cbe1ca777
-- title:
--   Ph Two Val Holds
-- statement:
--   Definitions and structural lemmas for Ph Two Val Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhTwoValHolds.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
abbrev P3 (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (u0 u1 u2 : 𝓞 E) :
    Fin 3 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun k => φa c φ (![u0, u1, u2] k)
abbrev σ2 (C : ChartAt Xo c y) (a b : Fin 3) : Fin 2 × Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S :=
  fun p => (![fun j => MvPolynomial.X (a, j), fun j => MvPolynomial.X (b, j)] :
    Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2
abbrev σS (C : ChartAt Xo c y) (m : ℕ) : Fin 2 × Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S :=
  fun p => (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] :
    Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
attribute [local instance] Over.cartesianMonoidalCategory
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ


