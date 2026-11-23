-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:34.276707+00:00
-- url     : https://prove2.me/theorems/d3b2938b-37fc-4522-9983-4b7759f4d27a
-- title:
--   Germ Fun
-- statement:
--   Definitions and structural lemmas for Germ Fun, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFun.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
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
def IsGermFunStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (d : ℕ) (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTy y d x m)
    (wP : PrimTy H Xo) (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f f' : MvPowerSeries (Fin 1 × Fin d) S),
    IsGerm y d x act e wP k F f → IsGerm y d x act e wP k F f' → f = f'
end Formalism.MainNotions.ModuliIntegralCharts.H1


