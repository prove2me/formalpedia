-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:21.773948+00:00
-- url     : https://prove2.me/theorems/6b1ebb57-586e-4e86-8059-b7e30aa9adfa
-- title:
--   Cocycle Product Three
-- statement:
--   Definitions and structural lemmas for Cocycle Product Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
abbrev AdTy (Xo : Moduli Dw l) (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L
    (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)])
      (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))
abbrev wPc (wP : PrimTy H Xo) (c : 𝓞 E) :=
  LB.pullGen Xo.univ.t.PP.L _ _ wP (Xo.univ.t.act.act c).left
abbrev cubAt (p q r : Xo.univ.t.G ⟶ Xo.univ.t.G) :=
  LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift p (lift q r)).left
def Bq (wP : PrimTy H Xo) (a : 𝓞 E) (wLa : AdTy Xo a) (wLb : AdTy Xo (H.bar a)) :=
  let A := Xo.univ.t.act.act
  let b := a * H.bar a
  LB.mulGen Xo.univ.t.PP.L _ _ _ _
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (wPc wP (1 + b))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP a))
          (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP a))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ wP)
        (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP b))))
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (cubAt (A 1) (A b) (A ((1 + b) * H.w0)))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (cubAt (A H.w0) (A (b * H.w0)) (A 1))
          (cubAt (A H.w0) (A (b * H.w0)) (A b))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wLa (lift (A 1) (A (a * H.w0))).left)
        (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wLb (lift (A a) (A H.w0)).left))))
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC


