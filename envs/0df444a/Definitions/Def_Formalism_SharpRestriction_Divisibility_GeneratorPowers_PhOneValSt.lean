-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:09.693624+00:00
-- url     : https://prove2.me/theorems/8da8287f-31c7-422e-b197-1dab6e668573
-- title:
--   Ph One Val St
-- statement:
--   Definitions and structural lemmas for Ph One Val St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhOneValSt.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
def PhOneValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
    ∀ (m : ℕ) (u0 u1 u2 : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
      (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J →
      ∃ w : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
        (w : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (atP ![φa c φ u0, φa c φ u1, φa c φ u2] C.B.ph1) ∧
        val (ExpGC.cubAt (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2)) (xExp y C φ m).left z J =
          gm (𝟙 _) z ⊤ (unitΓ w) * (val (C.e m) (ptm C ![φa c φ (u0 + u1), φa c φ u2] m).left z J *
            (val (C.e m) (ptm C ![φa c φ u0, φa c φ u2] m).left z J)⁻¹ *
            (val (C.e m) (ptm C ![φa c φ u1, φa c φ u2] m).left z J)⁻¹)
def PhTwoValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
    ∀ (m : ℕ) (u0 u1 u2 : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
      (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J →
      ∃ w : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
        (w : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (atP ![φa c φ u0, φa c φ u1, φa c φ u2] C.B.ph2) ∧
        val (ExpGC.cubAt (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2) (Xo.univ.t.act.act u0)) (xExp y C φ m).left z J =
          gm (𝟙 _) z ⊤ (unitΓ w) * (val (C.e m) (ptm C ![φa c φ u0, φa c φ (u1 + u2)] m).left z J *
            (val (C.e m) (ptm C ![φa c φ u0, φa c φ u1] m).left z J)⁻¹ *
            (val (C.e m) (ptm C ![φa c φ u0, φa c φ u2] m).left z J)⁻¹)
def AdValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
    (∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) →
    ∀ (a' : 𝓞 E) (wL : ExpGC.AdTy Xo a'), ExpGD.AdRel C a' wL →
    ∀ (m : ℕ) (u0 u1 : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
      (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J →
      ∃ w : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
        (w : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (atP ![φa c φ u0, φa c φ u1] (C.B.ad a')) ∧
        val (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1)).left)
            (xExp y C φ m).left z J =
          gm (𝟙 _) z ⊤ (unitΓ w) * (val (C.e m) (ptm C ![φa c φ u0, φa c φ (H.bar a' * u1)] m).left z J *
            (val (C.e m) (ptm C ![φa c φ (a' * u0), φa c φ u1] m).left z J)⁻¹)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ


