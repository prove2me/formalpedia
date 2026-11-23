-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_ArcFramePointTruncation
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_ArcFramePointTruncation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:37.699904+00:00
-- url     : https://prove2.me/theorems/7543d4b7-ff1a-45a8-8505-608fd27d5eee
-- title:
--   Arc Frame Point Truncation
-- statement:
--   Definitions and structural lemmas for Arc Frame Point Truncation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/ArcFramePointTruncation.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Theorems.Thm_Formalism_L2_Pj_OverLa_bc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (dualMap FrPt Gx PPx IsCombAt embK)
open scoped CategoryTheory.Obj
section Bundles
variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
def GenThrough (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    Prop :=
  (∀ k, φ' k ≫ F = h ≫ φ k) ∧ PMaps w φ' φ ε a t h
def SecThrough (w : LB.Iso L' (L.pull F)) (s : L.Sec) (s' : L'.Sec) : Prop :=
  ∀ (j : L.ι) (k : L'.ι) (V : X'.Opens) (h₁ : V ≤ F ⁻¹ᵁ L.U j) (h₂ : V ≤ (LB.div (L.pull F) L').U (fun _ => j, k))
    (h₃ : V ≤ L'.U k), (F.appLE _ _ h₁).hom (s.f j) = resG _ h₂ (w.s (fun _ => j, k)).val * resG _ h₃ (s'.f k)
end Bundles
section Tangent
variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}
abbrev EpsPt (D₀ : Out.DegPre A) : Type := Out.GtPt D₀ (epsR A)
def IsTanGt (ν : EpsPt D₀) : Prop :=
  IsTangent ν.b ∧ ∀ x, LB.Gen.Corr D₀.P.L _ _ _ _
    (LB.pullGen D₀.P.L _ _ (ν.s x) (spMap (TrivSqZeroExt.fstHom A A A).toRingHom)) (LB.oneGen D₀.P.L)
def IsSmulGt (r : A) (ν ν' : EpsPt D₀) : Prop := Out.GtPt.IsPull (spMap (epsMul r)) ν ν'
def IsCombGt {m : ℕ} (ν : Fin m → EpsPt D₀) (r : Fin m → A) (ω : EpsPt D₀) : Prop :=
  ∃ (u : Fin m → EpsPt D₀) (s : Fin (m + 1) → EpsPt D₀), (∀ i, IsSmulGt (r i) (ν i) (u i)) ∧ (s 0).IsZero ∧
    (∀ i : Fin m, Out.GtPt.IsAdd (s i.castSucc) (u i) (s i.succ)) ∧ s (Fin.last m) = ω
def ActGt {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (oa : D₀.OAct O) {T : Over (Sp A)} (a : O)
    (g g' : Out.GtPt D₀ T) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D₀.P.L (Out.rosatiφ D₀.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε), u.IsGen →
      LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (Out.zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
      ∀ x, LB.Gen.Corr D₀.P.L _ _ _ _
        (LB.mulGen D₀.P.L _ _ _ _ (g.s (star a • x))
          (LB.pullGen D₀.P.L _ _ u (lift (Out.DegPre.cT D₀ T x) g.b).left)) (g'.s x)
def IsEigGt {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (oa : D₀.OAct O) (t : O →+* A) (ν : EpsPt D₀) : Prop :=
  ∀ a : O, ∃ ν' : EpsPt D₀, IsSmulGt (t a) ν ν' ∧ ActGt oa a ν ν'
def IsEigBasisGt {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (oa : D₀.OAct O) (t : O →+* A) {m : ℕ}
    (ν : Fin m → EpsPt D₀) : Prop :=
  (∀ i, IsTanGt (ν i)) ∧ (∀ i, IsEigGt oa t (ν i)) ∧
    ∀ ω : EpsPt D₀, IsTanGt ω → IsEigGt oa t ω → ∃! r : Fin m → A, IsCombGt ν r ω
def IsMulSec (r : A) (th th' : D₀.P.L.Sec) : Prop :=
  ∀ j, th'.f j = constFn D₀.P.A.hom (D₀.P.L.U j) r * th.f j
def FibrewiseNe (th : D₀.P.L.Sec) : Prop :=
  ∀ s : Sp A, ∃ x : D₀.P.A.left, D₀.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th
def IsGenSec (th : D₀.P.L.Sec) : Prop := ∀ th' : D₀.P.L.Sec, ∃! r : A, IsMulSec r th th'
end Tangent
section BaseChange
variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {g : A →+* A'}
  {D₀ : Out.DegPre A} {D₁ : Out.DegPre A'}
abbrev prOf (pd : Out.IsPullDeg g D₀ D₁) : D₁.P.A.left ⟶ D₀.P.A.left :=
  pd.e.hom.left ≫ pullback.fst D₀.P.A.hom (Out.specOf g)
def LetterBC (pd : Out.IsPullDeg g D₀ D₁) (ν : EpsPt D₀) (ν' : EpsPt D₁) : Prop :=
  ν'.b.left ≫ prOf pd = spMap (dualMap g) ≫ ν.b.left ∧
    ∀ x, GenThrough pd.w Out.DegPre.gtε (ν'.s x) (ν.s (pd.xe x)) (spMap (dualMap g))
def SecBC (pd : Out.IsPullDeg g D₀ D₁) (th : D₀.P.L.Sec) (th' : D₁.P.L.Sec) : Prop := SecThrough pd.w th th'
def fracMap (g : A →+* A') (hg : Function.Injective g) : FractionRing A →+* FractionRing A' :=
  IsFractionRing.lift (g := (algebraMap A' (FractionRing A')).comp g) ((IsFractionRing.injective A' _).comp hg)
def QkBC (pd : Out.IsPullDeg g D₀ D₁) (hg : Function.Injective g) {k : ℕ} (p : Out.QkPt D₀ (FractionRing A) k)
    (p' : Out.QkPt D₁ (FractionRing A') k) : Prop :=
  ∃ q : Out.QkPt D₁ (FractionRing A') k, pd.xe q.y = p.y ∧
    q.g.b.left ≫ prOf pd = spMap (fracMap g hg) ≫ p.g.b.left ∧
    (∀ x, GenThrough pd.w Out.DegPre.gtε (q.g.s x) (p.g.s (pd.xe x)) (spMap (fracMap g hg))) ∧
    Out.QkPt.Equiv D₁ (FractionRing A') q p'
end BaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
section Inputs
variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {b : O →+* A} {b' : O →+* A'}
def IsLetters (a : ArcIn D l β A b) (io : c.F →+* FractionRing A)
    (ν : ∀ τ : E →+* ℂ, Fin (D.mult τ) → EpsPt a.D₀) : Prop :=
  letI := H.starRing
  io.comp β = (algebraMap A (FractionRing A)).comp b ∧
    ∀ τ, ∃ t : 𝓞 E →+* A, (algebraMap A (FractionRing A)).comp t = io.comp (embK c τ) ∧ IsEigBasisGt a.oa t (ν τ)
def InputBC (g : A →+* A') (a : ArcIn D l β A b) (a' : ArcIn D l β A' b') (pd : Out.IsPullDeg g a.D₀ a'.D₀) : Prop :=
  letI := H.starRing
  b' = g.comp b ∧ (∀ (r : 𝓞 E) x, pd.xe (r • x) = r • pd.xe x) ∧
    (∀ r : 𝓞 E, (a'.oa.onB.act r).left ≫ prOf pd = prOf pd ≫ (a.oa.onB.act r).left) ∧
    (∀ x z, a'.be x z = a.be (pd.xe x) (pd.xe z)) ∧
    ∃ hg : Function.Injective g, (∀ v, QkBC pd hg (a.etaA v) (a'.etaA v)) ∧
      ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), QkBC pd hg (a.eta v) (a'.eta v)
abbrev Wit (Y : Model Xo c β) (a : ArcIn D l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) :=
  ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := A)) PowerSeries.X χ
variable {Y : Model Xo c β}
def WitBC (g : A →+* A') {a : ArcIn D l β A b} {a' : ArcIn D l β A' b'} (pd : Out.IsPullDeg g a.D₀ a'.D₀)
    {χ : Sp (PowerSeries A) ⟶ Y.X} {χ' : Sp (PowerSeries A') ⟶ Y.X} (W : Wit Y a χ) (W' : Wit Y a' χ') : Prop :=
  InputBC g a a' pd ∧ χ' = spMap (PowerSeries.map g) ≫ χ ∧
    ∃ (hD : Out.IsPullDeg (PowerSeries.map g) W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (Out.specOf (PowerSeries.map g))).obj W.t.G),
      IsMonHom bc.hom ∧ Out.IsPullUnif (PowerSeries.map g) hD bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (PowerSeries.map g))) ≫ W.m.φ ∧
      W'.φ ≫ prOf pd = prOf hD ≫ W.φ ∧ (∀ x, hD.xe (W'.e x) = W.e (pd.xe x)) ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ W'.P.D.toPre.P.A.left) (z : Z) (j : a.D₀.P.L.ι) (i : W.P.D.toPre.P.L.ι)
        (i' : a'.D₀.P.L.ι) (k : W'.P.D.toPre.P.L.ι), (f ≫ prOf hD ≫ W.φ) z ∈ a.D₀.P.L.U j →
        (f ≫ prOf hD) z ∈ W.P.D.toPre.P.L.U i → (f ≫ W'.φ) z ∈ a'.D₀.P.L.U i' → f z ∈ W'.P.D.toPre.P.L.U k →
        gw W.w (f ≫ prOf hD) z j i * gw hD.w f z i k = gw pd.w (f ≫ W'.φ) z j i' * gw W'.w f z i' k
variable {a : ArcIn D l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}
abbrev Trunc (A : Type) [CommRing A] (n : ℕ) : Type :=
  PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1)
def LieId (W : Wit Y a χ) (ν : EpsPt a.D₀) (v : epsR (PowerSeries A) ⟶ W.t.G) : Prop :=
  IsTanGt ν ∧ ∀ n : ℕ, ∃ vn : Sp (DualNumber (Trunc A n)) ⟶
      (Out.thickObj (PowerSeries A) (Ideal.span {PowerSeries.X}) n W.t.G).left,
    vn ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left = spMap (dualMap (Ideal.Quotient.mk _)) ≫ v.left ∧
    vn ≫ (W.P.U.gt n).pG.left ≫ W.φ = spMap (dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))) ≫ ν.b.left ∧
    ∀ x, GenThrough W.w Out.Oinvε (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn)
      (show LB.Gen (LB.LinComb a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR A) ν.b x) Out.Oinvε) from ν.s x)
      (spMap (dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))))
def ThetaId (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) : Prop :=
  ∃ fam : ∀ x, W.P.D.toPre.SecB 1 x, (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 (show _ from σ) fam) ∧
    ∀ (j : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι) (V : W.P.D.toPre.P.A.left.Opens)
      (h₁ : V ≤ LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j)
      (h₂ : V ≤ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀),
      LB.Coh W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j →
      (W.φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (W.w.s (fun _ => j₀, j 1)).val * resG _ h₁ ((fam 0).f j)
variable {S : Type} [CommRing S] [Algebra c.F S]
def PointAlong (Y : Model Xo c β) (χ : Sp (PowerSeries A) ⟶ Y.X) (ρ : PowerSeries A →+* S) (x : Sp S ⟶ Xo.X)
    (yF : Sp S ⟶ Xo.XF c) : Prop :=
  yF ≫ pullback.fst _ _ = x ∧ yF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) ∧ yF ≫ Y.j = spMap ρ ≫ χ
def VecAlong (W : Wit Y a χ) (ρ : PowerSeries A →+* S) (yF : Sp S ⟶ Xo.XF c) (ν : EpsPt a.D₀)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ (v : epsR (PowerSeries A) ⟶ W.t.G) (uF : Sp (DualNumber S) ⟶ Y.oF.t.G.left), LieId W ν v ∧
    uF ≫ Y.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ yF ∧ uF ≫ Y.m0.toSABMap.φ = u ∧
    uF ≫ Y.m.φ = spMap (dualMap ρ) ≫ v.left ≫ W.m.φ
def ThetaAlong (W : Wit Y a χ) (ρ : PowerSeries A →+* S) {x : Sp S ⟶ Xo.X} (yF : Sp S ⟶ Xo.XF c)
    (th : a.D₀.P.L.Sec) (s : LB.Sec (PPx x)) : Prop :=
  ∃ (σ : Out.H0 W.P.U.LG.L 1) (g₁ : Gx x ⟶ Y.oF.t.G.left) (g₂ : Gx x ⟶ W.t.G.left)
    (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ))
    (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)),
    ThetaId W th σ ∧
    g₁ ≫ Y.m0.toSABMap.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
    g₁ ≫ Y.oF.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ yF ∧
    g₂ ≫ W.m.φ = g₁ ≫ Y.m.φ ∧ g₂ ≫ W.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ spMap ρ ∧
    IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ ∧ IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ ∧
    IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ ∧
    ∀ (j : Y.t.PP.L.ι) (k : W.P.U.LG.L.ι) (k₁ : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι) (V : (Gx x).Opens)
      (h₀ : V ≤ g₁ ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k₁))
      (h₁ : V ≤ g₁ ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k₁))
      (h₂ : V ≤ g₂ ⁻¹ᵁ (LB.div (Y.t.PP.L.pull W.m.φ) W.P.U.LG.L).U (fun _ => j, k))
      (h₃ : V ≤ g₂ ⁻¹ᵁ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k))
      (h₄ : V ≤ (PPx x).U (fun _ => j₀)),
      (g₁.appLE _ _ h₁).hom (w₁.s (fun _ => j, k₁)).val * resG _ h₄ (s.f (fun _ => j₀)) =
        (g₁.appLE _ _ h₀).hom (w₀.s (fun _ => j₀, k₁)).val * (g₂.appLE _ _ h₂).hom (w₂.s (fun _ => j, k)).val *
          (g₂.appLE _ _ h₃).hom (σ.f (fun _ => k))
def IsArcFrPt (W : Wit Y a χ) (ν : ∀ τ : E →+* ℂ, Fin (D.mult τ) → EpsPt a.D₀) (th : a.D₀.P.L.Sec)
    (ρ : PowerSeries A →+* S) (y : FrPt Xo c S) : Prop :=
  ∃ yF : Sp S ⟶ Xo.XF c, PointAlong Y χ ρ y.x yF ∧ (∀ τ i, VecAlong W ρ yF (ν τ i) (y.u τ i)) ∧
    ThetaAlong W ρ yF th y.s
def IsArcFrPtIn (W : Wit Y a χ) (ν : ∀ τ : E →+* ℂ, Fin (D.mult τ) → EpsPt a.D₀) (th : a.D₀.P.L.Sec)
    (ρ : PowerSeries A →+* S) (ξ : ∀ τ : E →+* ℂ, Fin (D.mult τ) → Fin (D.mult τ) → S) (y : FrPt Xo c S) : Prop :=
  ∃ yF : Sp S ⟶ Xo.XF c, PointAlong Y χ ρ y.x yF ∧
    (∃ u : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
      (∀ τ k, VecAlong W ρ yF (ν τ k) (u τ k)) ∧ ∀ τ i, IsCombAt y.x (u τ) (ξ τ i) (y.u τ i)) ∧
    ThetaAlong W ρ yF th y.s
end Inputs
example {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A} (ν : Fin 0 → EpsPt D₀) (r : Fin 0 → A) (ω : EpsPt D₀) :
    IsCombGt ν r ω ↔ ω.IsZero :=
  ⟨fun ⟨_, _, _, h₀, _, h⟩ => h ▸ h₀, fun h => ⟨Fin.elim0, fun _ => ω, fun i => i.elim0, h, fun i => i.elim0, rfl⟩⟩
example {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A} (th : D₀.P.L.Sec) : IsMulSec 1 th th := fun j => by
  simp [constFn]
end GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints


