-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:23.001059+00:00
-- url     : https://prove2.me/theorems/3912d23e-6d58-429b-82fe-0d93c8b6fed1
-- title:
--   Germ Cut
-- statement:
--   Definitions and structural lemmas for Germ Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermCut.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
attribute [local instance] Over.cartesianMonoidalCategory
section Rel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
def FrTrunc (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, LB.Gen.Corr t.PP.L _ _ _ _
    (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)]) (cε 2) (e (m + 1))
      (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
    (e m)
def FrAxes (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
          (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S)
            p.1 p.2)).left)
      (LB.oneGen t.PP.L) ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
          (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S)
            p.1 p.2)).left)
      (LB.oneGen t.PP.L)
def Rig0G (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) :
    Prop :=
  LB.Gen.Corr t.PP.L _ _ _ _
    (LB.pullGen t.PP.L _ _ (eLG t x0 d x act e wP 0) (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left)
    (rigT t.G t.PP.L t.PP.rig (overAt x0 S) 1)
end Rel
section Ids
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O]
structure AxesOK (ph1 ph2 : PS R 3 d) (sy : PS R 2 d) (ad : O → PS R 2 d) : Prop where
  cocycleLeft_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph1 = 1
  cocycleRight_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph2 = 1
  cocycleRight_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph2 = 1
  cocycleRight_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph2 = 1
  symmetry_zero_fst : ev (n := 1) ![0, pt R d 0] sy = 1
  symmetry_zero_snd : ev (n := 1) ![pt R d 0, 0] sy = 1
  ad_c : ∀ a, MvPowerSeries.constantCoeff (ad a) = 1
structure FBRest [StarRing O] (G : FGLaw R d) (A : Germ.OAct O G) (ph1 ph2 : PS R 3 d) (sy : PS R 2 d)
    (ad : O → PS R 2 d) : Prop where
  adjoint_zero_fst : ∀ a, ev (n := 1) ![0, pt R d 0] (ad a) = 1
  adjoint_zero_snd : ∀ a, ev (n := 1) ![pt R d 0, 0] (ad a) = 1

  cocycleLeft_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph1 =
      ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph1 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph1

  cocycleLeft_comm : ev (n := 3) ![pt R d 1, pt R d 0, pt R d 2] ph1 = ph1

  cocycleRight_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph2 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph2

  cocycleRight_comm : ev (n := 3) ![pt R d 0, pt R d 2, pt R d 1] ph2 = ph2

  interchange :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph1 * ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 * ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph1

  sy_inv : sy * ev (n := 2) ![pt R d 1, pt R d 0] sy = 1

  sy_law :
    ph2 * ev (n := 3) ![pt R d 0, pt R d 1] sy * ev (n := 3) ![pt R d 0, pt R d 2] sy =
      ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] sy * ev (n := 3) ![pt R d 1, pt R d 2, pt R d 0] ph1

  adjoint_compat_left : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), comp1 (A.act a) (pt R d 1), pt R d 2] ph1 *
        ev (n := 3) ![G.add (pt R d 0) (pt R d 1), pt R d 2] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 2] (ad a) * ev (n := 3) ![pt R d 1, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, pt R d 1, comp1 (A.act (star a)) (pt R d 2)] ph1

  adjoint_compat_right : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), pt R d 1, pt R d 2] ph2 *
        ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 1] (ad a) * ev (n := 3) ![pt R d 0, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1),
          comp1 (A.act (star a)) (pt R d 2)] ph2
  ad_one : ad 1 = 1

  ad_mul : ∀ a b : O, ad (a * b) =
    ev (n := 2) ![comp1 (A.act b) (pt R d 0), pt R d 1] (ad a) *
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] (ad b)

  ad_add : ∀ a b : O,
    ev (n := 2) ![comp1 (A.act a) (pt R d 0), comp1 (A.act b) (pt R d 0), pt R d 1] ph1 * ad (a + b) =
      ad a * ad b *
        ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1), comp1 (A.act (star b)) (pt R d 1)] ph2

  ad_sy : ∀ a : O,
    ad a * ev (n := 2) ![pt R d 1, pt R d 0] (ad (star a)) *
        ev (n := 2) ![comp1 (A.act a) (pt R d 0), pt R d 1] sy =
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] sy
def mkFB [StarRing O] (G : FGLaw R d) (A : Germ.OAct O G) (ph1 ph2 : PS R 3 d) (sy : PS R 2 d)
    (ad : O → PS R 2 d) (ha : AxesOK ph1 ph2 sy ad) (hr : FBRest G A ph1 ph2 sy ad) : Germ.FB R d O :=
  { G := G, A := A, ph1 := ph1, ph2 := ph2, sy := sy, ad := ad,
    cocycleLeft_zero_fst := ha.cocycleLeft_zero_fst, cocycleLeft_zero_snd := ha.cocycleLeft_zero_snd, cocycleLeft_zero_thd := ha.cocycleLeft_zero_thd,
    cocycleRight_zero_fst := ha.cocycleRight_zero_fst, cocycleRight_zero_snd := ha.cocycleRight_zero_snd, cocycleRight_zero_thd := ha.cocycleRight_zero_thd,
    symmetry_zero_fst := ha.symmetry_zero_fst, symmetry_zero_snd := ha.symmetry_zero_snd, adjoint_zero_fst := hr.adjoint_zero_fst, adjoint_zero_snd := hr.adjoint_zero_snd,
    cocycleLeft_assoc := hr.cocycleLeft_assoc, cocycleLeft_comm := hr.cocycleLeft_comm, cocycleRight_assoc := hr.cocycleRight_assoc, cocycleRight_comm := hr.cocycleRight_comm,
    interchange := hr.interchange, sy_inv := hr.sy_inv, sy_law := hr.sy_law, adjoint_compat_left := hr.adjoint_compat_left,
    adjoint_compat_right := hr.adjoint_compat_right, ad_one := hr.ad_one, ad_mul := hr.ad_mul, ad_add := hr.ad_add, ad_sy := hr.ad_sy }
end Ids
def ChartDataSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (y : FrPt Xo c K),
    ∃ (d : ℕ) (G : Germ.FGLaw K d) (A : Germ.OAct (𝓞 E) G) (uvec : Lt1 Dw → Fin d → K)
      (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G), IsChart y d G.F A.act uvec x
def FrameSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0)
    (S : Type) [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G)
    (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G), IsChartG t x0 d G.F A.act tg uvec x →
    ∃ (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d),
      IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e ∧ IsPrimG t wP ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e ∧
        (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) ∧ Rig0G t x0 d x A.act e wP
def FBIdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0),
    (∀ n, Function.Bijective (ReciprocityTheory.ChartRestriction.G.Out.powObj t.G n).hom.appTop.hom) → ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G)
    (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (e : ∀ m, FrTyG t x0 d x m) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d)
    (ad : 𝓞 E → PS S 2 d), IsChartG t x0 d G.F A.act tg uvec x →
    IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e → FrAxes t x0 d x e → (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) →
      AxesOK ph1 ph2 sy ad ∧ FBRest G A ph1 ph2 sy ad
def GermSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0)
    (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d)
    (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t), IsChartG t x0 d F act tg uvec x →
    IsFrameG t x0 d x F act ph1 ph2 sy ad e → IsPrimG t wP → FrTrunc t x0 d x e →
    ∀ (k : ℕ) (Fs : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))), ∃ f, IsGermG t x0 d x act e wP k Fs f
end Formalism.MainNotions.ModuliIntegralCharts.H1


