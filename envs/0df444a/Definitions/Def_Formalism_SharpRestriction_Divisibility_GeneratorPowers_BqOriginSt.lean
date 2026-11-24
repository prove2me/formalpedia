-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BqOriginSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_BqOriginSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:54.923079+00:00
-- url     : https://prove2.me/theorems/a60086f8-d65a-4735-9d90-e2b2dbca953b
-- title:
--   Bq Origin St
-- statement:
--   Definitions and structural lemmas for Bq Origin St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/BqOriginSt.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ESecToUnit
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
def BqOriginSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (a : 𝓞 E)
      (wLa : ExpGC.AdTy Xo a), ExpGD.AdRel C a wLa → ∀ (wLb : ExpGC.AdTy Xo (H.bar a)), ExpGD.AdRel C (H.bar a) wLb →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (overAt y.x S).left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J →
        val (ExpGC.Bq C.wP a wLa wLb) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J *
          val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J ^ (3 : ℤ) = 1
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO


