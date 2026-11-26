-- Prove2me | Definitions.Def_AlgebraicGeometry_EtalePullbackGermNaturality
-- name    : AlgebraicGeometry_EtalePullbackGermNaturality
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T07:39:53.723913+00:00
-- url     : https://prove2.me/theorems/e85389f6-bc13-5feb-8f3b-10d01e9a3141
-- title:
--   Naturality of étale restriction on strict local section germs
-- statement:
--   Comparison of inverse images along a cartesian square is compatible with evaluation at a lift of a geometric point.
-- source:
--   Stacks Project, Section 59.83, https://stacks.math.columbia.edu/tag/03SB.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms
import Definitions.Def_AlgebraicGeometry_FreeEtaleChartSheaves
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Tactic.FinCases

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etalePullbackGermNaturalityHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etalePullbackGermNaturalityHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etalePullbackGermNaturalityEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso pullbackConstantIso)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtalePullbackComposition
  (pullbackCompIso restrictGlobalSections_app_eq restrictGlobalSections_comp)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtalePrimeTorsionComparison (restrict)


namespace PhilipponEtaleCohomologyRestrictionComp

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Z₀ := AddCommGrpCat.of (ULift.{u} ℤ)
private abbrev C (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj Z₀

private def constAdj (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⊣ globalSections X :=
  constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
    (IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) (Scheme.Etale.mk (𝟙 X)) Over.mkIdTerminal)

private abbrev constMap {X Y : Scheme.{u}} (f : Y ⟶ X) :
    C Y ⟶ (pullbackSheaves f).obj (C X) :=
  (pullbackConstantIso f).inv.app Z₀

private theorem homEquiv_constMap {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Ab X) (a : C X ⟶ F) :
    (constAdj Y).homEquiv Z₀ _ (constMap f ≫ (pullbackSheaves f).map a) =
      (constAdj X).homEquiv Z₀ F a ≫ (restrictGlobalSections f).app F := by
  let L := pullbackSheaves f
  let adj := pullbackAdjunction f
  let d := ((constAdj X).comp adj).ofNatIsoRight (globalSectionsIso f)
  have hl : adj.homEquiv _ _ (L.map a) = a ≫ adj.unit.app F := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality a).symm
  have hc : (constAdj Y).homEquiv Z₀ (L.obj (C X)) (constMap f) = d.unit.app Z₀ :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (constAdj Y) d Z₀
  calc
    _ = d.homEquiv Z₀ _ (L.map a) := by
      rw [Adjunction.homEquiv_naturality_right, hc, Adjunction.homEquiv_unit]
    _ = _ := by
      dsimp only [d]
      rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
      change (constAdj X).homEquiv Z₀ _ (adj.homEquiv _ _ (L.map a)) ≫
        (globalSectionsIso f).hom.app (L.obj F) = _
      rw [hl, Adjunction.homEquiv_naturality_right, restrictGlobalSections_app_eq, Category.assoc]

private theorem constMap_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    constMap g ≫ (pullbackSheaves g).map (constMap f) ≫
      (pullbackCompIso f g).hom.app (C X) = constMap (g ≫ f) := by
  let a := (constAdj X).homEquiv Z₀ (C X) (𝟙 (C X))
  let d := (pullbackCompIso f g).hom.app (C X)
  have hc {P Q : Scheme.{u}} (h : Q ⟶ P) :
      (constAdj Q).homEquiv Z₀ _ (constMap h) =
        (constAdj P).homEquiv Z₀ (C P) (𝟙 (C P)) ≫ (restrictGlobalSections h).app (C P) := by
    have hh := homEquiv_constMap h (C P) (𝟙 (C P))
    rw [(pullbackSheaves h).map_id (C P), Category.comp_id] at hh
    exact hh
  apply ((constAdj Z).homEquiv Z₀ _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right, homEquiv_constMap,
    hc f, hc (g ≫ f)]
  change (a ≫ (restrictGlobalSections f).app (C X) ≫
    (restrictGlobalSections g).app ((pullbackSheaves f).obj (C X))) ≫
      (globalSections Z).map d = a ≫ (restrictGlobalSections (g ≫ f)).app (C X)
  simp only [Category.assoc, d, restrictGlobalSections_comp]

/-- The constant integer sheaf comparisons compose along inverse images. -/
theorem pullbackConstantIso_inv_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (pullbackConstantIso g).inv.app Z₀ ≫
        (pullbackSheaves g).map ((pullbackConstantIso f).inv.app Z₀) ≫
        (pullbackCompIso f g).hom.app (C X) =
      (pullbackConstantIso (g ≫ f)).inv.app Z₀ :=
  constMap_comp f g

end PhilipponEtaleCohomologyRestrictionComp

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackComposition (pullbackCompIso pullbackCompIso_over_hom restrictDirectImage)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtalePullbackSquareUnits

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

section Adjunctions

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {L : A ⥤ B} {R : B ⥤ A} {M : A ⥤ C} {S : C ⥤ A}
  {N : C ⥤ D} {T : D ⥤ C} {Q : B ⥤ D} {V : D ⥤ B}
  (a : M ⊣ S) (b : N ⊣ T) (c : L ⊣ R) (d : Q ⊣ V)
  (e : V ⋙ R ≅ T ⋙ S)

private theorem base_change_naturality {F G : B} (g : F ⟶ G) :
    M.map (R.map g) ≫ (a.homEquiv _ _).symm (R.map (d.unit.app G) ≫ e.hom.app (Q.obj G)) =
      (a.homEquiv _ _).symm (R.map (d.unit.app F) ≫ e.hom.app (Q.obj F)) ≫ T.map (Q.map g) := by
  apply (a.homEquiv (R.obj F) (T.obj (Q.obj G))).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Functor.id_obj, Equiv.apply_symm_apply]
  have h : R.map (V.map (Q.map g)) ≫ e.hom.app (Q.obj G) =
    e.hom.app (Q.obj F) ≫ S.map (T.map (Q.map g)) := e.hom.naturality (Q.map g)
  have hUnit : g ≫ d.unit.app G = d.unit.app F ≫ V.map (Q.map g) := d.unit.naturality g
  change R.map g ≫ R.map (d.unit.app G) ≫ e.hom.app (Q.obj G) =
    (R.map (d.unit.app F) ≫ e.hom.app (Q.obj F)) ≫ S.map (T.map (Q.map g))
  rw [Category.assoc, ← h, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, hUnit]

end Adjunctions

section OverComposite

variable {X P Z W : Scheme.{u}} (p : P ⟶ X) (i : Z ⟶ X) (j : W ⟶ P) (r : W ⟶ Z)
    (ρ : W ⟶ X) (hp : j ≫ p = ρ) (hi : r ≫ i = ρ)

private def pushforwardSquareIsoOver :
    pushforward r ⋙ pushforward i ≅ pushforward j ⋙ pushforward p :=
  (pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)) ≪≫
    (pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)).symm

/-- Ordinary base change is natural in the coefficients. -/
@[reassoc]
theorem restrictionBaseChangeOver_naturality {B C : Ab Z} (a : B ⟶ C) :
    (pullbackSheaves p).map ((pushforward i).map a) ≫
      restrictionBaseChangeOver p i j r ρ hp hi C =
    restrictionBaseChangeOver p i j r ρ hp hi B ≫
      (pushforward j).map ((pullbackSheaves r).map a) := by
  exact base_change_naturality (pullbackAdjunction p) (pullbackAdjunction r)
    (pushforwardSquareIsoOver p i j r ρ hp hi) a

end OverComposite
end PhilipponEtalePullbackSquareUnits

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleCohomologyUnits

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev H (X : Scheme.{u}) (q : ℕ) := Sheaf.functorH X.smallEtaleTopology q
private abbrev Z := AddCommGrpCat.of (ULift.{u} ℤ)
private abbrev C (X : Scheme.{u}) := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj Z

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

def directImageConstant : C X ⟶ (pushforward p).obj (C Y) :=
  (pullbackAdjunction p).homEquiv _ _ ((pullbackConstantIso p).hom.app Z)

variable [PreservesFiniteColimits (pushforward p)]

theorem bijective_toDirectImage (F : Ab Y) (q : ℕ) : Function.Bijective (toDirectImage p F q) := by
  apply PhilipponExtComparison.comparison_bijective
  intro G
  let L := pullbackAdjunction p
  let e := (pullbackConstantIso p).app Z
  let h := L.homEquiv (C X) G
  have hEq : (fun a : C Y ⟶ G => directImageConstant p ≫ (pushforward p).map a) =
      h ∘ fun a : C Y ⟶ G => e.hom ≫ a := by
    funext a
    exact (L.homEquiv_naturality_right e.hom a).symm
  change Function.Bijective (fun a : C Y ⟶ G => directImageConstant p ≫ (pushforward p).map a)
  rw [hEq]
  exact h.bijective.comp ((Iso.homCongr e (Iso.refl G)).symm.bijective)

end PhilipponEtaleCohomologyUnits

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms
open PhilipponEtalePullbackComposition (pullbackCompIso unit_comp)
open PhilipponEtalePullbackSquareUnits
  (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


namespace PhilipponEtaleBaseChangeGerms

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

set_option maxHeartbeats 900000 in
/-- Transposing the ordinary base-change map gives the pushed-forward
unit, after identifying the two direct images along the common map. -/
private theorem unit_restrictionBaseChangeOver {X P Z W : Scheme.{u}}
    (p : P ⟶ X) (i : Z ⟶ X) (j : W ⟶ P) (r : W ⟶ Z)
    (ρ : W ⟶ X) (hp : j ≫ p = ρ) (hi : r ≫ i = ρ) (B : Ab Z) :
    (pullbackAdjunction p).unit.app ((pushforward i).obj B) ≫
      (pushforward p).map (restrictionBaseChangeOver p i j r ρ hp hi B) ≫
      (pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)).hom.app
        ((pullbackSheaves r).obj B) =
    (pushforward i).map ((pullbackAdjunction r).unit.app B) ≫
      (pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)).hom.app
        ((pullbackSheaves r).obj B) := by
  let adj := pullbackAdjunction p
  let C := restrictionBaseChangeOver p i j r ρ hp hi B
  let P := pullbackSheaves r
  let e := pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)
  let f := pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)
  have h : adj.homEquiv _ _ C =
      (pushforward i).map ((pullbackAdjunction r).unit.app B) ≫
        (f ≪≫ e.symm).hom.app (P.obj B) := Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  change adj.unit.app _ ≫ (pushforward p).map C ≫ e.hom.app (P.obj B) = _
  rw [← Category.assoc, h]
  simp only [P, f, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

variable {K : Type u} [Field K] [IsSepClosed K]

private abbrev stalk {X : Scheme.{u}} (s : Spec (.of K) ⟶ X) :=
  (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

@[reassoc]
theorem evalAtLiftOver_naturality {X Y : Scheme.{u}} (p : Y ⟶ X) (v : Spec (.of K) ⟶ Y)
    (s : Spec (.of K) ⟶ X) (h : v ≫ p = s) {F G : Ab Y} (a : F ⟶ G) :
    (stalk s).map ((pushforward p).map a) ≫ evalAtLiftOver p v s h G =
      evalAtLiftOver p v s h F ≫ (stalk v).map a := by
  subst s
  simpa only [evalAtLiftOver, eqToHom_refl, Category.id_comp] using evalAtLift_naturality p v a

@[reassoc]
theorem evalAtLiftOver_comp_via {X Y Z : Scheme.{u}} (p : Y ⟶ X) (d : Z ⟶ Y)
    (ρ : Z ⟶ X) (hp : d ≫ p = ρ) (v : Spec (.of K) ⟶ Z)
    (s : Spec (.of K) ⟶ X) (h : v ≫ ρ = s) (F : Ab Z) :
    (stalk s).map ((pushforwardCompIso p d ≪≫ eqToIso (congrArg pushforward hp)).hom.app F) ≫
      evalAtLiftOver ρ v s h F =
    evalAtLiftOver p (v ≫ d) s ((Category.assoc _ _ _).trans
      ((congrArg (v ≫ ·) hp).trans h)) ((pushforward d).obj F) ≫ evalAtLift d v F := by
  subst ρ
  simpa only [eqToIso_refl, Iso.trans_refl] using evalAtLiftOver_comp p d v s
    ((Category.assoc _ _ _).trans h) F

set_option maxHeartbeats 900000 in
/-- On geometric stalks the ordinary base-change map preserves evaluation
at a geometric lift in the commutative square. -/
theorem evalAtLift_baseChangeOver {X S Y W : Scheme.{u}}
    (p : S ⟶ X) (i : Y ⟶ X) (j : W ⟶ S) (r : W ⟶ Y)
    (ρ : W ⟶ X) (hp : j ≫ p = ρ) (hi : r ≫ i = ρ)
    (v : Spec (.of K) ⟶ W) (F : Ab Y) :
    (stalk (v ≫ j)).map (restrictionBaseChangeOver p i j r ρ hp hi F) ≫
        evalAtLift j v ((pullbackSheaves r).obj F) ≫ (stalkPullbackIso r v).hom.app F =
      (stalkPullbackIso p (v ≫ j)).hom.app ((pushforward i).obj F) ≫
        evalAtLiftOver i (v ≫ r) ((v ≫ j) ≫ p) (by simp only [Category.assoc, hi, hp]) F := by
  let t := v ≫ j
  let s := t ≫ p
  let A := (pullbackSheaves r).obj F
  let G := (pushforward i).obj F
  let H := (pushforward j).obj A
  let δ := restrictionBaseChangeOver p i j r ρ hp hi F
  let α := (pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)).hom.app A
  let β := (pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)).hom.app A
  let eb := stalkPullbackIso p t
  let er := stalkPullbackIso r v
  let ηp := (pullbackAdjunction p).unit.app G
  let ηr := (pullbackAdjunction r).unit.app F
  have hv : v ≫ ρ = s := by simp only [s, t, Category.assoc, hp]
  have hr : (v ≫ r) ≫ i = s := by simp only [s, t, Category.assoc, hp, hi]
  have hU : (stalk s).map ηp ≫ evalAtLift p t ((pullbackSheaves p).obj G) = eb.inv.app G := by
    apply (cancel_mono (eb.hom.app G)).mp
    simp only [Category.assoc]
    exact (evalAtLift_unit p t G).trans (Iso.inv_hom_id_app eb G).symm
  have hLeft : (stalk s).map α ≫ evalAtLiftOver ρ v s hv A =
      evalAtLift p t H ≫ evalAtLift j v A := by
    simpa only [α, evalAtLiftOver, eqToHom_refl, Category.id_comp] using
      evalAtLiftOver_comp_via p j ρ hp v s hv A
  have hRight : (stalk s).map β ≫ evalAtLiftOver ρ v s hv A =
      evalAtLiftOver i (v ≫ r) s hr ((pushforward r).obj A) ≫ evalAtLift r v A :=
    evalAtLiftOver_comp_via i r ρ hi v s hv A
  change (stalk t).map δ ≫ evalAtLift j v A ≫ er.hom.app F =
    eb.hom.app G ≫ evalAtLiftOver i (v ≫ r) s hr F
  apply (cancel_epi (eb.inv.app G)).mp
  rw [Iso.inv_hom_id_app_assoc]
  calc
    _ = (stalk s).map ηp ≫ evalAtLift p t ((pullbackSheaves p).obj G) ≫
        (stalk t).map δ ≫ evalAtLift j v A ≫ er.hom.app F := by rw [← hU, Category.assoc]
    _ = (stalk s).map (ηp ≫ (pushforward p).map δ ≫ α) ≫
        evalAtLiftOver ρ v s hv A ≫ er.hom.app F := by
      have hNat : (stalk s).map ((pushforward p).map δ) ≫ evalAtLift p t H =
          evalAtLift p t ((pullbackSheaves p).obj G) ≫ (stalk t).map δ :=
        evalAtLift_naturality p t δ
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hNat, reassoc_of% hLeft]
    _ = (stalk s).map ((pushforward i).map ηr) ≫
        evalAtLiftOver i (v ≫ r) s hr ((pushforward r).obj A) ≫ evalAtLift r v A ≫ er.hom.app F := by
      rw [show ηp ≫ (pushforward p).map δ ≫ α = (pushforward i).map ηr ≫ β from
        unit_restrictionBaseChangeOver p i j r ρ hp hi F]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hRight]
    _ = _ := by
      have hNat : (stalk s).map ((pushforward i).map ηr) ≫
          evalAtLiftOver i (v ≫ r) s hr ((pushforward r).obj A) =
          evalAtLiftOver i (v ≫ r) s hr F ≫ (stalk (v ≫ r)).map ηr :=
        evalAtLiftOver_naturality i (v ≫ r) s hr ηr
      rw [reassoc_of% hNat, evalAtLift_unit r v F, Category.comp_id]

set_option maxHeartbeats 900000 in
/-- The inverse-image comparison for a composite gives the successive
inverse-image comparisons on stalks. -/
theorem stalkPullbackIso_hom_comp {X Y Z : Scheme.{u}} (p : Y ⟶ X) (d : Z ⟶ Y)
    (v : Spec (.of K) ⟶ Z) (F : Ab X) :
    (stalk v).map ((pullbackCompIso p d).hom.app F) ≫
      (stalkPullbackIso (d ≫ p) v).hom.app F ≫
      eqToHom (congrArg (fun x => (stalk x).obj F) (Category.assoc v d p).symm) =
    (stalkPullbackIso d v).hom.app ((pullbackSheaves p).obj F) ≫
      (stalkPullbackIso p (v ≫ d)).hom.app F := by
  let s := (v ≫ d) ≫ p
  let t := v ≫ d
  let A := (pullbackSheaves p).obj F
  let B := (pullbackSheaves d).obj A
  let H := (pullbackSheaves (d ≫ p)).obj F
  let ηp := (pullbackAdjunction p).unit.app F
  let ηd := (pullbackAdjunction d).unit.app A
  let e := stalkPullbackIso p t
  let e' := stalkPullbackIso d v
  let β := (pullbackCompIso p d).hom.app F
  let hs : v ≫ (d ≫ p) = s := (Category.assoc v d p).symm
  let l := (stalkPullbackIso (d ≫ p) v).hom.app F ≫
    eqToHom (congrArg (fun x => (stalk x).obj F) hs)
  have h₁ : (stalk s).map ηp ≫ evalAtLift p t A = e.inv.app F := by
    apply (cancel_mono (e.hom.app F)).mp
    simp only [Category.assoc]
    exact (evalAtLift_unit p t F).trans (Iso.inv_hom_id_app e F).symm
  have h₂ : (stalk t).map ηd ≫ evalAtLift d v B = e'.inv.app A := by
    apply (cancel_mono (e'.hom.app A)).mp
    simp only [Category.assoc]
    exact (evalAtLift_unit d v A).trans (Iso.inv_hom_id_app e' A).symm
  have hc := evalAtLiftOver_comp p d v s rfl B
  simp only [evalAtLiftOver, eqToHom_refl, Category.id_comp] at hc
  have hc' : (stalk s).map ((pushforwardCompIso p d).hom.app B) ≫
      evalAtLiftOver (d ≫ p) v s hs B =
      evalAtLift p t ((pushforward d).obj B) ≫ evalAtLift d v B := hc
  change (stalk v).map β ≫ l = e'.hom.app A ≫ e.hom.app F
  apply (cancel_epi (e.inv.app F ≫ e'.inv.app A)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  calc
    _ = (stalk s).map ηp ≫ evalAtLift p t A ≫ (stalk t).map ηd ≫ evalAtLift d v B ≫
        (stalk v).map β ≫ l := by simp only [← reassoc_of% h₁, ← reassoc_of% h₂]
    _ = (stalk s).map (ηp ≫ (pushforward p).map ηd ≫ (pushforwardCompIso p d).hom.app B ≫
          (pushforward (d ≫ p)).map β) ≫ evalAtLiftOver (d ≫ p) v s hs H ≫ l := by
      simp only [Functor.map_comp, Category.assoc]
      have hNat : (stalk s).map ((pushforward (d ≫ p)).map β) ≫ evalAtLiftOver (d ≫ p) v s hs H =
          evalAtLiftOver (d ≫ p) v s hs B ≫ (stalk v).map β :=
        evalAtLiftOver_naturality (d ≫ p) v s hs β
      have hNat' : (stalk s).map ((pushforward p).map ηd) ≫ evalAtLift p t ((pushforward d).obj B) =
          evalAtLift p t A ≫ (stalk t).map ηd := evalAtLift_naturality p t ηd
      rw [reassoc_of% hNat, reassoc_of% hc', reassoc_of% hNat']
    _ = _ := by
      rw [show ηp ≫ (pushforward p).map ηd ≫ (pushforwardCompIso p d).hom.app B ≫
          (pushforward (d ≫ p)).map β = (pullbackAdjunction (d ≫ p)).unit.app F from unit_comp p d F]
      exact evalAtLiftOver_unit (d ≫ p) v s hs F

end PhilipponEtaleBaseChangeGerms

end


