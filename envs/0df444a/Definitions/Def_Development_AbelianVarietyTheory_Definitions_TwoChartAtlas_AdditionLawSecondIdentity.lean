-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
-- name    : Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:39:32.761863+00:00
-- url     : https://prove2.me/theorems/d410b16d-f4ed-42f8-9e07-ad15cbd75fbd
-- title:
--   Addition Law Second Identity
-- statement:
--   Definitions and structural lemmas for Addition Law Second Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwoChartAtlas/AdditionLawSecondIdentity.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_Comp1Scalar
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChartCmp
section Series
variable {R : Type} [CommRing R]
def JEq {σ : Type} (m : ℕ) (f g : MvPowerSeries σ R) : Prop :=
  ∀ e : σ →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g
structure JRel {d : ℕ} {O : Type} [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d) : Prop where
  inv : IsInvPair φ φi
  unit : IsUnit (MvPowerSeries.constantCoeff ε)
  law : ∀ i, B'.G.F i = transF B.G.F φ φi i
  act : ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)
  ph1 : JEq m (B'.ph1 * ev (n := 3) ![addOf B'.G.F (pt R (n := 3) d 0) (pt R (n := 3) d 1), pt R (n := 3) d 2] ε)
    (ev (n := 3) ![comp1 φ (pt R (n := 3) d 0), comp1 φ (pt R (n := 3) d 1), comp1 φ (pt R (n := 3) d 2)] B.ph1 *
      (ev (n := 3) ![pt R (n := 3) d 0, pt R (n := 3) d 2] ε * ev (n := 3) ![pt R (n := 3) d 1, pt R (n := 3) d 2] ε))
  ph2 : JEq m (B'.ph2 * ev (n := 3) ![pt R (n := 3) d 0, addOf B'.G.F (pt R (n := 3) d 1) (pt R (n := 3) d 2)] ε)
    (ev (n := 3) ![comp1 φ (pt R (n := 3) d 0), comp1 φ (pt R (n := 3) d 1), comp1 φ (pt R (n := 3) d 2)] B.ph2 *
      (ev (n := 3) ![pt R (n := 3) d 0, pt R (n := 3) d 1] ε * ev (n := 3) ![pt R (n := 3) d 0, pt R (n := 3) d 2] ε))
  sy : JEq m (B'.sy * ε)
    (ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] B.sy * ev (n := 2) ![pt R (n := 2) d 1, pt R (n := 2) d 0] ε)
  ad : ∀ a, JEq m (B'.ad a * ev (n := 2) ![pt R (n := 2) d 0, comp1 (B'.A.act (star a)) (pt R (n := 2) d 1)] ε)
    (ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] (B.ad a) *
      ev (n := 2) ![comp1 (B'.A.act a) (pt R (n := 2) d 0), pt R (n := 2) d 1] ε)
structure Biadd {d : ℕ} {O : Type} [CommRing O] [StarRing O] (m : ℕ) (B : FB R d O) (k : Type) [CommRing k] [Algebra R k]
    (g : PS k 2 d) : Prop where
  ax0 : JEq m (ev (n := 1) ![0, pt k (n := 1) d 0] g) 0
  ax1 : JEq m (ev (n := 1) ![pt k (n := 1) d 0, 0] g) 0
  add1 : JEq m (ev (n := 3) ![addOf (B.FK k) (pt k (n := 3) d 0) (pt k (n := 3) d 1), pt k (n := 3) d 2] g)
    (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] g)
  add2 : JEq m (ev (n := 3) ![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k (n := 3) d 2)] g)
    (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] g + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g)
  sym : JEq m (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] g) g
  bal : ∀ a : O, JEq m (ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k (n := 2) d 1] g)
    (ev (n := 2) ![pt k (n := 2) d 0, comp1 (B.actK k (star a)) (pt k (n := 2) d 1)] g)
def bilSer {d n : ℕ} (β : Matrix (Fin d) (Fin d) R) (x z : Pt R n d) : PS R n d :=
  ∑ i, ∑ j, MvPowerSeries.C (β i j) * (x i * z j)
end Series
section Bundles
def Carries {X X' Y : Scheme.{0}} {L' : LB X'} (L : LB X) (F : X' ⟶ X) (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) : Prop :=
  LB.Gen.Maps (LB.linCombIso w φ ε) g (flatGen L F φ ε g')
end Bundles
section Geo
variable {V : Type} [CommRing V]
def CoordRel {G : Over (Sp V)} {d : ℕ} (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (φ : Pt V 1 d) : Prop :=
  ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) ≫ x m
def dirs {G : Over (Sp V)} {d : ℕ} (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) : Fin d → (Sp (DualNumber V) ⟶ G.left) :=
  fun j => (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ x 1).left
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def FrRel (t : SAB H (Sp V)) {d : ℕ} (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m)
    (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ : Pt V 1 d) (m : ℕ) (ε : PS V 2 d) : Prop :=
  ∃ u : (Jet V (Fin 2 × Fin d) m)ˣ, (u : Jet V (Fin 2 × Fin d) m) = psJet m ε ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (e' m)
      (scaleGenG t _ _ (unitΓ u) (peG t (𝟙 (Sp V)) d x e m ![fun j => psIn d m ![0] (φ j), fun j => psIn d m ![1] (φ j)]))
def PushFr {t t' : SAB H (Sp V)} (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) {d : ℕ}
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m) : Prop :=
  ∀ m, (e' m).IsGen ∧ ∃ c : LB.Gen (LB.LinComb t'.PP.L
      (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) (cε 2)),
    c.IsGen ∧ LB.Gen.Corr t'.PP.L _ _ _ _ c (e' m) ∧
      Carries t'.PP.L n.φ w (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)]) (cε 2) (e m) c
def CubIso {t t' : SAB H (Sp V)} (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) : Prop :=
  w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (thφ t.G (x3 t.G)) thε) t.cub.t (n.cm.thetaPull t'.PP.L t'.cub.t)
end Geo
section Families
open MvPolynomial (X C)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
def FamPh1 (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (ph1 : MvPowerSeries (Fin 3 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
def FamPh2 (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (ph2 : MvPowerSeries (Fin 3 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
def FamSy (sy : MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (e m)
      (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))
def FamAd (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
      LB.Gen.Corr t.PP.L _ _ _ _
        (LB.mulGen t.PP.L _ _ _ _
          (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
          (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
        (scaleGenG t _ _ (unitΓ u)
          (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))
end Families
section Depth
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def nuAlg (Dw : Datum H) [StarRing (𝓞 E)] (T : CDVR) {d : ℕ} (B : FB T.V d (𝓞 E)) (h : PS T.Fr 2 d) (u : Lt1 Dw → Fin d → T.Fr)
    (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  ⨅ (P : MvPolynomial (LtN Dw n) T.Fr) (_ : P ∈ FFV (Dw := Dw) T a n) (f : PS T.V n d),
    nval T.V e (nabValN B T.Fr h H.w0 k (MvPowerSeries.map (algebraMap T.V T.Fr) f) (fun ℓ => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P)
end Depth
end GlobalTheory.ChartCmp
end
noncomputable section
namespace GlobalTheory.ChartCmp.Inh
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.AdditiveBiext
abbrev addInt : FB ℤ 1 ℤ := additiveFB ℤ 1
def refl1 : Pt ℤ 1 1 := fun i => C (-1) * X ((0 : Fin 1), i)
def xz : PS ℤ 2 1 := X ((0 : Fin 2), (0 : Fin 1)) * X ((1 : Fin 2), (0 : Fin 1))
section Depth
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
end Depth
end GlobalTheory.ChartCmp.Inh


