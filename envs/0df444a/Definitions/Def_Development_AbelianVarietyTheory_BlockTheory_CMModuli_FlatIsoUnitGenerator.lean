-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:55.101548+00:00
-- url     : https://prove2.me/theorems/32ab74c3-1e7c-459d-9be4-6d8650cd6da9
-- title:
--   Flat Iso Unit Generator
-- statement:
--   Definitions and structural lemmas for Flat Iso Unit Generator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/FlatIsoUnitGenerator.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
section Points
variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}
def GtTors (k : ℕ) {T : Over (Sp R)} (g : Out.GtPt D T) : Prop :=
  ∃ h : Out.GtPt D T, Out.GtPt.IsNsmul k g h ∧ h.IsZero
def GtActT {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O) {T : Over (Sp R)}
    (g g' : Out.GtPt D T) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (Out.rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (Out.zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
          (LB.pullGen D.P.L _ _ u (lift (Out.DegPre.cT D T χ) g.b).left)) (g'.s χ)
def unitGen {X Y : Scheme.{0}} (L : LB X) (z : Γ(Y, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top z
def TorusVal {T : Over (Sp R)} (g : Out.GtPt D T) (χ : D.X) (z : Γ(T.left, ⊤)ˣ) : Prop :=
  g.b = Out.DegPre.zeroT D T ∧ LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (unitGen D.P.L z)
end Points
section Formal
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
  {A : Out.PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
def FormalEq (U : Out.UnifPre I D A G) {T : Over (Sp R)} (x : T ⟶ G) (g : Out.GtPt D.toPre T) : Prop :=
  ∀ e : ℕ,
    (Out.fstG I e T).left ≫ g.b.left =
        ((Over.pullback (Out.thick R I e)).map x).left ≫ (U.gt e).pG.left ∧
      ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _
        (LB.pullGen D.toPre.P.L _ _ (g.s χ) (Out.fstG I e T).left)
        (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (Out.thick R I e)).map x).left)
structure IsFinitePart (U : Out.UnifPre I D A G) (k : ℕ) (N : Over (Sp R)) (g₀ : Out.GtPt D.toPre N)
    (x₀ : N ⟶ G) : Prop where
  finite : IsFinite N.hom
  flat : Flat N.hom
  gt_tors : GtTors k g₀
  gt_univ : ∀ (T : Over (Sp R)) (g : Out.GtPt D.toPre T), GtTors k g →
    ∃! h : T ⟶ N, Out.GtPt.IsPull h.left g₀ g
  g_tors : x₀ ^ k = 1
  g_mono : Mono x₀
  g_univ : ∀ T : Over (Sp R), IsFinite T.hom → ∀ x : T ⟶ G, x ^ k = 1 → ∃ h : T ⟶ N, h ≫ x₀ = x
  formal : FormalEq U x₀ g₀
end Formal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
section Flat
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}
def TorsFiniteFlat (G : Over (Sp R)) [GrpObj G] (W : (Sp R).Opens) (k : ℕ) : Prop :=
  ∃ (N : Over W.toScheme) (n : Out.overW W N ⟶ G), IsFinite N.hom ∧ Flat N.hom ∧ n ^ k = 1 ∧
    ∀ (T : Over W.toScheme) (x : Out.overW W T ⟶ G), x ^ k = 1 →
      ∃! h : T ⟶ N, (Over.map W.ι).map h ≫ n = x
structure IsFlatIso (P : PELUnif I t) {W : (Sp R).Opens} (ψW : Out.PsiOn P.D.toPre W) (k : ℕ)
    (f : ∀ T : Over W.toScheme, Out.QkPtW P.D.toPre W ψW k T → (Out.overW W T ⟶ t.G)) : Prop where
  tors : ∀ T p, f T p ^ k = 1
  natural : ∀ (T T' : Over W.toScheme) (h : T' ⟶ T) p p', Out.QkPtW.IsPull h p p' →
    f T' p' = (Over.map W.ι).map h ≫ f T p
  add : ∀ T p p' p'', Out.QkPtW.IsAdd p p' p'' → f T p'' = f T p * f T p'
  lin : letI := H.starRing
    ∀ (a : 𝓞 E) T (p p' : Out.QkPtW P.D.toPre W ψW k T), p'.y = a • p.y → GtActT P.oD a p.g p'.g →
      f T p' = f T p ≫ t.act.act a
  inj : ∀ T : Over W.toScheme, Nonempty T.left → ∀ p p', f T p = f T p' ↔ Out.QkPtW.Equiv p p'
  surj : ∀ (T : Over W.toScheme) (x : Out.overW W T ⟶ t.G), x ^ k = 1 → ∀ s : T.left,
    ∃ V : T.left.Opens, s ∈ V ∧ ∃ p, f (Out.overRes V) p = (Over.map W.ι).map (Out.overResι V) ≫ x
  generic : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Over W.toScheme) (x : Sp F ⟶ T.left),
    x ≫ (Out.overW W T).hom = Out.jFK (R := R) F ≫ Out.jK R →
    ∀ p (q : Out.QkPt P.D.toPre F k), Out.QkPtW.IsPullF F x p q →
      ∀ a : Out.TFK (R := R) F ⟶ P.A.A,
        a.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R) = x ≫ (f T p).left → P.ToA F k q a
  onGt : ∃ (N : Over (Sp R)) (g₀ : Out.GtPt P.D.toPre N) (x₀ : N ⟶ t.G),
    IsFinitePart P.U.toUnifPre k N g₀ x₀ ∧
    ∀ (T : Over W.toScheme) (h : Out.overW W T ⟶ N) (p : Out.QkPtW P.D.toPre W ψW k T), p.y = 0 →
      Out.GtPt.IsPull h.left g₀ p.g → f T p = h ≫ x₀
  onY : ∀ (T : Over W.toScheme) (p p' : Out.QkPtW P.D.toPre W ψW k T) (z : Γ((Out.overW W T).left, ⊤)ˣ),
    p.y = 0 → TorusVal p.g p'.y z → Out.WeilIs t.G t.PP.L (k : ℤ) (f T p) (f T p') z
def FlatTorsion (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  ∃ ψW : Out.PsiOn P.D.toPre W,
    (∀ y, ∃ g : Out.GtPt P.D.toPre (Out.overW W (𝟙_ (Over W.toScheme))), Out.GtPt.IsIotaW ψW y g) ∧
    ∀ k : ℕ, 1 ≤ k → TorsFiniteFlat t.G W k ∧ ∃ f, IsFlatIso P ψW k f
def Concl (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  (∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R))) ∧ P.TorsionIso ∧ FlatTorsion P W
def IsPowOf {t' : SAB H (Sp R)} (P' : PELUnif I t') (P : PELUnif I t) (j : ℕ) : Prop :=
  letI := H.starRing
  ∃ (pG : Out.IsPowGrp t'.G t.G j) (pD : Out.IsPowDeg P'.D.toPre P.D.toPre j) (pA : Out.IsPowPolAV P'.A P.A j),
    Nonempty (Out.UnifPowOf3 pD pA pG P'.U P.U) ∧
    (∀ a i, t'.act.act a ≫ pG.pr i = pG.pr i ≫ t.act.act a) ∧
    (∀ a i, P'.oA.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) ∧
    (∀ a i, P'.oD.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧
    ∀ (a : 𝓞 E) x i, pD.xe (a • x) i = a • pD.xe x i
def Products (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  ∀ j : ℕ, ∃ (t' : SAB H (Sp R)) (P' : PELUnif I t'), IsPowOf P' P j ∧ Concl P' W
end Flat
def FullOut {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (U : Set (Sp R)) : Prop :=
  ∃ (W : (Sp R).Opens) (P : PELUnif (IsLocalRing.maximalIdeal R) t),
    (W : Set (Sp R)) = U ∧ Concl P W ∧ Products P W
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def ModelFull (Y : Model Xo c β) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R →
    IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty →
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField R)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)) →
      FullOut t (ξ ⁻¹' abLocus Y.t.G)
end GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator


