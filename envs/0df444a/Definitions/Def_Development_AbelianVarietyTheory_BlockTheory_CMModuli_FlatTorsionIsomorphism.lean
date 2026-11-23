-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:55.652011+00:00
-- url     : https://prove2.me/theorems/14ad5608-eb67-4db5-a322-b08545efd751
-- title:
--   Flat Torsion Isomorphism
-- statement:
--   Definitions and structural lemmas for Flat Torsion Isomorphism, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/FlatTorsionIsomorphism.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
section Data
variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}
structure GtTors (D : Out.DegPre R) (k : ℕ) (T : Over (Sp R)) where

  g : Out.GtPt D T

  tors : ∃ z : Out.GtPt D T, Out.GtPt.IsNsmul k g z ∧ z.IsZero
def GtSmul {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) {T : Over (Sp R)} (a : O)
    (g g' : Out.GtPt D T) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (Out.rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (Out.zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
          (LB.pullGen D.P.L _ _ u (lift (Out.DegPre.cT D T χ) g.b).left)) (g'.s χ)
def unitGen {X Y : Scheme.{0}} (L : LB X) (c : Γ(Y, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top c
def TorusValue {T : Over (Sp R)} (g : Out.GtPt D T) (χ : D.X) (c : Γ(T.left, ⊤)ˣ) : Prop :=
  g.b = Out.DegPre.zeroT D T ∧ LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (unitGen D.P.L c)
def CoordOf {I : Ideal R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (gc : Out.GtCoord I D e G)
    {T : Over (Sp (R ⧸ I ^ (e + 1)))} (x : T ⟶ Out.thickObj R I e G)
    (g : Out.GtPt D ((Over.map (Out.thick R I e)).obj T)) : Prop :=
  g.b = (Over.map (Out.thick R I e)).map x ≫ gc.pG ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.pullGen D.P.L _ _ (gc.t χ) x.left)
def torsScheme {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ) : Over S :=
  pullback ((𝟙 G : G ⟶ G) ^ k) η[G]
abbrev resι {S : Scheme.{0}} {T : Over S} (V : T.left.Opens) : Out.overRes V ⟶ T := Out.overResι V
end Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
section Unif
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}
structure FinitePart (P : PELUnif I t) (k : ℕ) where

  h : ∀ T : Over (Sp R), GtTors P.D.toPre k T → (T ⟶ t.G)
  tors : ∀ T g, h T g ^ k = 1
  pull : ∀ (T T' : Over (Sp R)) (φ : T' ⟶ T) (g : GtTors P.D.toPre k T) (g' : GtTors P.D.toPre k T'),
    Out.GtPt.IsPull φ.left g.g g'.g → h T' g' = φ ≫ h T g
  add : ∀ T (g g' g'' : GtTors P.D.toPre k T), Out.GtPt.IsAdd g.g g'.g g''.g → h T g'' = h T g * h T g'
  lin : letI := H.starRing
    ∀ T (a : 𝓞 E) (g g' : GtTors P.D.toPre k T), GtSmul P.oD a g.g g'.g → h T g' = h T g ≫ t.act.act a
  inj : ∀ T, Function.Injective (h T)
  onto : ∀ T : Over (Sp R), IsFinite T.hom → ∀ x : T ⟶ t.G, x ^ k = 1 → ∃ g, h T g = x
  red : ∀ (e : ℕ) (T : Over (Sp (R ⧸ I ^ (e + 1)))) (x : T ⟶ Out.thickObj R I e t.G)
    (g : GtTors P.D.toPre k ((Over.map (Out.thick R I e)).obj T)), CoordOf (P.U.gt e) x g.g →
    h _ g = (Over.map (Out.thick R I e)).map x ≫ Out.fstG I e t.G
structure FlatIso (P : PELUnif I t) {W : (Sp R).Opens} (ψW : Out.PsiOn P.D.toPre W) (k : ℕ) (φ : FinitePart P k) where
  finite : IsFinite ((torsScheme t.G k).hom ∣_ W)
  flat : Flat ((torsScheme t.G k).hom ∣_ W)

  f : ∀ T : Over W.toScheme, Out.QkPtW P.D.toPre W ψW k T → (Out.overW W T ⟶ t.G)
  tors : ∀ T p, f T p ^ k = 1
  pull : ∀ (T T' : Over W.toScheme) (m : T' ⟶ T) (p : Out.QkPtW P.D.toPre W ψW k T)
    (p' : Out.QkPtW P.D.toPre W ψW k T'), Out.QkPtW.IsPull m p p' → f T' p' = (Over.map W.ι).map m ≫ f T p
  add : ∀ T (p p' p'' : Out.QkPtW P.D.toPre W ψW k T), Out.QkPtW.IsAdd p p' p'' → f T p'' = f T p * f T p'
  lin : letI := H.starRing
    ∀ T (a : 𝓞 E) (p p' : Out.QkPtW P.D.toPre W ψW k T), p'.y = a • p.y → GtSmul P.oD a p.g p'.g →
      f T p' = f T p ≫ t.act.act a
  inj : ∀ T : Over W.toScheme, Nonempty T.left → ∀ p p' : Out.QkPtW P.D.toPre W ψW k T,
    f T p = f T p' ↔ Out.QkPtW.Equiv p p'
  onto : ∀ (T : Over W.toScheme) (x : Out.overW W T ⟶ t.G), x ^ k = 1 → ∀ s : T.left,
    ∃ V : T.left.Opens, s ∈ V ∧ ∃ p : Out.QkPtW P.D.toPre W ψW k (Out.overRes V),
      f _ p = (Over.map W.ι).map (resι V) ≫ x
  generic : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Over W.toScheme) (s : Sp F ⟶ T.left)
    (p : Out.QkPtW P.D.toPre W ψW k T) (p' : Out.QkPt P.D.toPre F k) (x : Out.TFK (R := R) F ⟶ P.A.A),
    Out.QkPtW.IsPullF F s p p' →
    x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R) = s ≫ (f T p).left → P.ToA F k p' x
  onGt : ∀ (T : Over W.toScheme) (p : Out.QkPtW P.D.toPre W ψW k T) (g : GtTors P.D.toPre k (Out.overW W T)),
    p.y = 0 → g.g = p.g → f T p = φ.h _ g
  onY : ∀ (T : Over W.toScheme) (p p' : Out.QkPtW P.D.toPre W ψW k T) (c : Γ((Out.overW W T).left, ⊤)ˣ),
    p.y = 0 → TorusValue p.g p'.y c → Out.WeilIs t.G t.PP.L k (f T p) (f T p') c
def FlatForm (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  letI := H.starRing
  ∃ ψW : Out.PsiOn P.D.toPre W,
    (∃ io : P.D.toPre.X → Out.GtPt P.D.toPre (Out.overW W (Over.mk (𝟙 W.toScheme))),
      (∀ y, Out.GtPt.IsIotaW ψW y (io y)) ∧ (∀ y y', Out.GtPt.IsAdd (io y) (io y') (io (y + y'))) ∧
      ∀ (a : 𝓞 E) y, GtSmul P.oD a (io y) (io (a • y))) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ φ : FinitePart P k, Nonempty (FlatIso P ψW k φ)
structure IsPowTriple {S : Scheme.{0}} (t' t : SAB H S) (j : ℕ) where

  pw : Out.IsPowGrp t'.G t.G j
  act : ∀ a i, t'.act.act a ≫ pw.pr i = pw.pr i ≫ t.act.act a

  w : LB.Iso t'.PP.L (Out.boxLB t.PP.L pw.pr)
  w_gen : w.IsGen
  w_rig : ∃ b : LB.Gen (LB.LinComb t.PP.L (K := Fin j) (fun i => eSec t'.G ≫ (pw.pr i).left) (fun _ => 1)),
    Out.GeneratorPullback.MapsAt t.PP.L t'.PP.L (fun i => (pw.pr i).left) w (eSec t'.G) 1 t'.PP.rig b ∧
    LB.Gen.Corr t.PP.L _ _ _ _ b
      (Out.GeneratorPullback.finProdGen t.PP.L (J := Fin j) (fun _ _ => eSec t.G) (fun _ _ => 1) (fun _ => t.PP.rig))
def IsPowUnif {t' : SAB H (Sp R)} {j : ℕ} (pt : IsPowTriple t' t j) (P' : PELUnif I t') (P : PELUnif I t) : Prop :=
  letI := H.starRing
  ∃ (pD : Out.IsPowDeg P'.D.toPre P.D.toPre j) (pA : Out.IsPowPolAV P'.A P.A j),
    Nonempty (Out.UnifPowOf3 pD pA pt.pw P'.U P.U) ∧
    (∀ (a : 𝓞 E) x i, pD.xe (a • x) i = a • pD.xe x i) ∧
    (∀ a i, P'.oD.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧
    ∀ a i, P'.oA.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a
def Conclusion (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  (∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R))) ∧ P.TorsionIso ∧ FlatForm P W
def Products (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  ∀ j : ℕ, (∃ t' : SAB H (Sp R), Nonempty (IsPowTriple t' t j)) ∧
    ∀ (t' : SAB H (Sp R)) (pt : IsPowTriple t' t j), ∃ P' : PELUnif I t', IsPowUnif pt P' P ∧ Conclusion P' W
end Unif
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def TorsionAndProducts (Y : Model Xo c β) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R →
    IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty →
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField R)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)) →
      ∃ W : (Sp R).Opens, (W : Set (Sp R)) = ξ ⁻¹' abLocus Y.t.G ∧
        ∃ P : PELUnif (IsLocalRing.maximalIdeal R) t, Conclusion P W ∧ Products P W
example (Y : Model Xo c β) (h : TorsionAndProducts Y) : Y.N3 := by
  intro R _ _ _ _ h1 h2 h3 ξ t m hne hs
  obtain ⟨W, hW, P, hP, -⟩ := h R h1 h2 h3 ξ t m hne hs
  exact ⟨P, hW ▸ hP.1, hP.2.1⟩
end GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism


