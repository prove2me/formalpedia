-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqH
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:41:18.234809+00:00
-- url     : https://prove2.me/theorems/0f7acf70-d74b-4d0a-87a2-f0288c3bfaa8
-- title:
--   Gauge Uniq H
-- statement:
--   Definitions and structural lemmas for Gauge Uniq H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqH.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniq
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
def CocId {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) (e : ∀ m, ExpFr y x m) (a : 𝓞 E)
    (β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε)) : Prop :=
  ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eAt y x e m (1 + a * H.bar a))
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left)
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eAt y x e m a) 2)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (e m) (eAt y x e m (a * H.bar a)))))
def CommonCocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)
    (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G), IsExpChart y x →
    ∀ e e' : ∀ m, ExpFr y x m, IsExpGauge y x e → IsExpGauge y x e' →
    ∀ a : 𝓞 E, ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
        (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
      CocId y x e a β ∧ CocId y x e' a β
end Formalism.MainNotions.ModuliIntegralCharts.H1


