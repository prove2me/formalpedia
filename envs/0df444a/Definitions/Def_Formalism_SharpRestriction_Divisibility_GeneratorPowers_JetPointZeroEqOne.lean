-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:17.560055+00:00
-- url     : https://prove2.me/theorems/32a65ca8-6a2c-4476-a2f7-e1dd3bb46612
-- title:
--   Jet Point Zero Eq One
-- statement:
--   Definitions and structural lemmas for Jet Point Zero Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetPointZeroEqOne.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
def AdRel (C : ChartAt Xo c y) (a : 𝓞 E) (wL : ExpGC.AdTy Xo a) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ, (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (C.B.ad a) ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left)
        (pe y C.d C.x C.e m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGen _ _ (unitΓ u)
        (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)]))
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD


