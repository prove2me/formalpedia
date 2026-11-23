-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:34:34.655717+00:00
-- url     : https://prove2.me/theorems/055ee7e8-6c54-4889-9cad-ff19c3ac9a17
-- title:
--   Th Expr Uniq Of Chart Indep2
-- statement:
--   Definitions and structural lemmas for Th Expr Uniq Of Chart Indep2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ThExprUniqOfChartIndep2.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndSt
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
def ChartIndepSt2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S),
    (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) →
    (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      chartVal C k f P = chartVal C' k f' P
end Formalism.MainNotions.ModuliIntegralCharts.H1


