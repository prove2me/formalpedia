-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleDirectImageSectionGerms
-- name    : AlgebraicGeometry_EtaleDirectImageSectionGerms
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T23:49:00.289432+00:00
-- url     : https://prove2.me/theorems/ce54dcf0-f9fb-4223-ba58-08e66149869c
-- title:
--   Germ maps for étale direct images
-- statement:
--   Evaluation of direct-image germs and transport of geometric points over field extensions.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (pointFiberIso stalkPullbackIso stalkPullbackIso_germ)


namespace PhilipponEtaleDirectImageGerms

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y : Scheme.{u}} (p : Y ⟶ X) {K : Type u} [Field K] [IsSepClosed K]
  (r : Spec (.of K) ⟶ Y)

private abbrev basePoint := Scheme.pointSmallEtale (r ≫ p)
private abbrev liftPoint := Scheme.pointSmallEtale r

/-- The stalk of the direct image maps to the stalk of the original
sheaf at any lift of its geometric point. -/
def evalAtLift (F : Ab Y) :
    (basePoint p r).sheafFiber.obj ((pushforward p).obj F) ⟶ (liftPoint r).sheafFiber.obj F :=
  (stalkPullbackIso p r).inv.app ((pushforward p).obj F) ≫
    (liftPoint r).sheafFiber.map ((pullbackAdjunction p).counit.app F)

/-- Evaluation at a lift of a specified base geometric point. -/
def evalAtLiftOver (s : Spec (.of K) ⟶ X) (h : r ≫ p = s) (F : Ab Y) :
    (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward p).obj F) ⟶
      (liftPoint r).sheafFiber.obj F :=
  eqToHom (congrArg (fun a => (Scheme.pointSmallEtale a).sheafFiber.obj ((pushforward p).obj F))
    h.symm) ≫ evalAtLift p r F

/-- Evaluation at a lift commutes with changing the coefficient sheaf. -/
theorem evalAtLift_naturality {F G : Ab Y} (a : F ⟶ G) :
    (basePoint p r).sheafFiber.map ((pushforward p).map a) ≫ evalAtLift p r G =
      evalAtLift p r F ≫ (liftPoint r).sheafFiber.map a := by
  let e := stalkPullbackIso p r
  let Q := (liftPoint r).sheafFiber (A := AddCommGrpCat.{u})
  let R := pushforward p
  let L := pullbackSheaves p
  let ε := (pullbackAdjunction p).counit
  have he : (basePoint p r).sheafFiber.map (R.map a) ≫ e.inv.app (R.obj G) =
      e.inv.app (R.obj F) ≫ Q.map (L.map (R.map a)) := e.inv.naturality (R.map a)
  have hε : L.map (R.map a) ≫ ε.app G = ε.app F ≫ a := ε.naturality a
  change _ ≫ e.inv.app (R.obj G) ≫ Q.map (ε.app G) =
    (e.inv.app (R.obj F) ≫ Q.map (ε.app F)) ≫ Q.map a
  rw [← Category.assoc, he, Category.assoc, Category.assoc,
    ← Q.map_comp, ← Q.map_comp, hε]

set_option maxRecDepth 4096 in
/-- On a representative of a direct-image germ, evaluation uses the
point on the pulled-back chart. -/
theorem evalAtLift_germ (F : Ab Y) (W : X.Etale)
    (t : (liftPoint r).fiber.obj ((baseChange p).obj W)) :
    (basePoint p r).toPresheafFiber W ((pointFiberIso p r).hom.app W t)
        ((pushforward p).obj F).obj ≫ evalAtLift p r F =
      (liftPoint r).toPresheafFiber ((baseChange p).obj W) t F.obj := by
  let Q := liftPoint r
  let R := pushforward p
  let L := pullbackSheaves p
  let a := pullbackAdjunction p
  let ε := a.counit.app F
  let V := (baseChange p).obj W
  let η : (R.obj F).obj.obj (op W) ⟶ (L.obj (R.obj F)).obj.obj (op V) :=
    (a.unit.app (R.obj F)).hom.app (op W)
  let e := stalkPullbackIso p r
  have h := stalkPullbackIso_germ p r (R.obj F) W t
  have hε : η ≫ ε.hom.app (op V) = 𝟙 (F.obj.obj (op V)) :=
    congrArg (fun α : R.obj F ⟶ R.obj F => α.hom.app (op W)) (a.right_triangle_components F)
  change _ ≫ e.inv.app (R.obj F) ≫ Q.sheafFiber.map ε = _
  rw [← h]
  simp only [Category.assoc]
  change η ≫ Q.toPresheafFiber V t (L.obj (R.obj F)).obj ≫
    e.hom.app (R.obj F) ≫ e.inv.app (R.obj F) ≫ Q.presheafFiber.map ε.hom = _
  rw [Iso.hom_inv_id_app_assoc, Q.toPresheafFiber_naturality, ← Category.assoc, hε]
  exact Category.id_comp (Q.toPresheafFiber V t F.obj)

/-- Evaluation on a germ remains the same when the base point is given
by an equality with the image of the lifted point. -/
theorem evalAtLift_germ_of_eq {s : Spec (.of K) ⟶ X} (h : r ≫ p = s) (F : Ab Y)
    (W : X.Etale) (w : (Scheme.pointSmallEtale s).fiber.obj W)
    (t : (liftPoint r).fiber.obj ((baseChange p).obj W))
    (ht : t.left ≫ pullback.fst W.hom p = w.left) :
    (Scheme.pointSmallEtale s).toPresheafFiber W w ((pushforward p).obj F).obj ≫
      eqToHom (congrArg (fun a => (Scheme.pointSmallEtale a).sheafFiber.obj ((pushforward p).obj F))
        h.symm) ≫ evalAtLift p r F =
      (liftPoint r).toPresheafFiber ((baseChange p).obj W) t F.obj := by
  subst s
  have hw : (pointFiberIso p r).hom.app W t = w := Over.OverMorphism.ext ht
  rw [eqToHom_refl, Category.id_comp, ← hw]
  exact evalAtLift_germ p r F W t

/-- The direct-image unit is the identity on each lifted stalk after
identifying that stalk with the stalk on the base. -/
theorem evalAtLift_unit (F : Ab X) :
    (basePoint p r).sheafFiber.map ((pullbackAdjunction p).unit.app F) ≫
      evalAtLift p r ((pullbackSheaves p).obj F) ≫ (stalkPullbackIso p r).hom.app F =
        𝟙 ((basePoint p r).sheafFiber.obj F) := by
  let Q := (liftPoint r).sheafFiber (A := AddCommGrpCat.{u})
  let L := pullbackSheaves p
  let a := pullbackAdjunction p
  let e := stalkPullbackIso p r
  have h : (basePoint p r).sheafFiber.map (a.unit.app F) ≫
      e.inv.app ((pushforward p).obj (L.obj F)) = e.inv.app F ≫ Q.map (L.map (a.unit.app F)) :=
    e.inv.naturality (a.unit.app F)
  have hTriangle : L.map (a.unit.app F) ≫ a.counit.app (L.obj F) = 𝟙 (L.obj F) :=
    a.left_triangle_components F
  change (basePoint p r).sheafFiber.map (a.unit.app F) ≫ e.inv.app ((pushforward p).obj (L.obj F)) ≫
    Q.map (a.counit.app (L.obj F)) ≫ e.hom.app F = _
  rw [← Category.assoc, h, Category.assoc, ← Category.assoc
    (Q.map (L.map (a.unit.app F))), ← CategoryTheory.Functor.map_comp,
    hTriangle, Q.map_id (L.obj F)]
  exact (congrArg (e.inv.app F ≫ ·) (Category.id_comp (e.hom.app F))).trans (Iso.inv_hom_id_app e F)

/-- Transporting the lifted germ to the specified base stalk sends the
unit of pullback to the identity. -/
theorem evalAtLiftOver_unit (s : Spec (.of K) ⟶ X) (h : r ≫ p = s) (F : Ab X) :
    (Scheme.pointSmallEtale s).sheafFiber.map ((pullbackAdjunction p).unit.app F) ≫
      evalAtLiftOver p r s h ((pullbackSheaves p).obj F) ≫ (stalkPullbackIso p r).hom.app F ≫
      eqToHom (congrArg (fun a => (Scheme.pointSmallEtale a).sheafFiber.obj F) h) =
        𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj F) := by
  subst s
  simpa only [evalAtLiftOver, eqToHom_refl, Category.id_comp, Category.comp_id] using
    evalAtLift_unit p r F

set_option maxRecDepth 4096 in
/-- Evaluation at a lift along a composite is successive evaluation at
the two geometric lifts. -/
theorem evalAtLiftOver_comp {Z : Scheme.{u}} (d : Z ⟶ Y) (v : Spec (.of K) ⟶ Z)
    (s : Spec (.of K) ⟶ X) (h : (v ≫ d) ≫ p = s) (F : Ab Z) :
    (Scheme.pointSmallEtale s).sheafFiber.map ((pushforwardCompIso p d).hom.app F) ≫
      evalAtLiftOver (d ≫ p) v s ((Category.assoc _ _ _).symm.trans h) F =
    evalAtLiftOver p (v ≫ d) s h ((pushforward d).obj F) ≫ evalAtLift d v F := by
  let S := Scheme.pointSmallEtale s
  let Q := Scheme.pointSmallEtale v
  let G := (pushforward p).obj ((pushforward d).obj F)
  let H := (pushforward (d ≫ p)).obj F
  let α : G ⟶ H := (pushforwardCompIso p d).hom.app F
  let hv : v ≫ (d ≫ p) = s := (Category.assoc _ _ _).symm.trans h
  let ε := evalAtLiftOver (d ≫ p) v s hv F
  apply (S.isColimitPresheafFiberCocone G.obj).hom_ext
  intro i
  let W := i.unop.fst
  let w := i.unop.snd
  let a := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) d p).hom.app W
  let u : Q.fiber.obj ((baseChange (d ≫ p)).obj W) :=
    Over.homMk (pullback.lift w.left v ((Over.w w).trans hv.symm)) (pullback.lift_snd ..)
  have hu : u.left ≫ pullback.fst W.hom (d ≫ p) = w.left := pullback.lift_fst ..
  let u' := Q.fiber.map a u
  let w' := (pointFiberIso d v).hom.app ((baseChange p).obj W) u'
  have ha : a.left ≫ pullback.fst (pullback.snd W.hom p) d ≫ pullback.fst W.hom p =
      pullback.fst W.hom (d ≫ p) :=
    MorphismProperty.Over.pullbackComp_left_fst_fst (P := @Etale) (Q := ⊤) d p W
  have hw' : w'.left ≫ pullback.fst W.hom p = w.left := by
    change ((u.left ≫ a.left) ≫ pullback.fst (pullback.snd W.hom p) d) ≫
      pullback.fst W.hom p = w.left
    rw [Category.assoc, Category.assoc, ha, hu]
  have hα : S.toPresheafFiber W w G.obj ≫ S.presheafFiber.map α.hom =
      F.obj.map a.op ≫ S.toPresheafFiber W w H.obj :=
    S.toPresheafFiber_naturality α.hom W w
  have h₁ := evalAtLift_germ_of_eq (d ≫ p) v hv F W w u hu
  have h₂ : S.toPresheafFiber W w G.obj ≫
      evalAtLiftOver p (v ≫ d) s h ((pushforward d).obj F) =
      (Scheme.pointSmallEtale (v ≫ d)).toPresheafFiber
        ((baseChange p).obj W) w' ((pushforward d).obj F).obj :=
    evalAtLift_germ_of_eq p (v ≫ d) h ((pushforward d).obj F) W w w' hw'
  have h₃ := evalAtLift_germ d v F ((baseChange p).obj W) u'
  calc
    _ = F.obj.map a.op ≫ S.toPresheafFiber W w H.obj ≫ ε := (reassoc_of% hα) ε
    _ = F.obj.map a.op ≫ Q.toPresheafFiber ((baseChange (d ≫ p)).obj W) u F.obj :=
      congrArg (F.obj.map a.op ≫ ·) h₁
    _ = Q.toPresheafFiber ((baseChange d).obj ((baseChange p).obj W)) u' F.obj :=
      Q.toPresheafFiber_w a u F.obj
    _ = _ := h₃.symm.trans ((reassoc_of% h₂) (evalAtLift d v F)).symm

end PhilipponEtaleDirectImageGerms

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms
open PhilipponEtalePullbackComposition (pullbackCompIso restrictDirectImage unit_restrictDirectImage)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


namespace PhilipponEtaleDescentCofaces

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K] (p : Y ⟶ X)

private abbrev stalk {T : Scheme.{u}} (s : Spec (.of K) ⟶ T) :=
  (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

private def liftIso (r : Spec (.of K) ⟶ Y) (s : Spec (.of K) ⟶ X) (h : r ≫ p = s) (F : Ab X) :
    (stalk r).obj ((pullbackSheaves p).obj F) ≅ (stalk s).obj F :=
  (stalkPullbackIso p r).app F ≪≫ eqToIso (congrArg (fun z => (stalk z).obj F) h)

/-- Evaluate the direct-image stalk at a lift and identify the resulting
stalk of the coefficient pullback with the base stalk. -/
def transportedLiftEvaluation (r : Spec (.of K) ⟶ Y) (s : Spec (.of K) ⟶ X)
    (h : r ≫ p = s) (F : Ab X) :
    (stalk s).obj ((pushforward p).obj ((pullbackSheaves p).obj F)) ⟶ (stalk s).obj F :=
  evalAtLiftOver p r s h ((pullbackSheaves p).obj F) ≫ (liftIso p r s h F).hom

theorem unit_evaluation (r : Spec (.of K) ⟶ Y) (s : Spec (.of K) ⟶ X)
    (h : r ≫ p = s) (F : Ab X) :
    (stalk s).map ((pullbackAdjunction p).unit.app F) ≫ transportedLiftEvaluation p r s h F =
      𝟙 ((stalk s).obj F) := by
  simp only [transportedLiftEvaluation, liftIso, Iso.trans_hom, eqToIso.hom]
  exact evalAtLiftOver_unit p r s h F

theorem evalAtLiftOver_eq_of_transported_eq (r : Spec (.of K) ⟶ Y) (s : Spec (.of K) ⟶ X)
    (h : r ≫ p = s) (F : Ab X)
    {a b : (stalk s).obj ((pushforward p).obj ((pullbackSheaves p).obj F))}
    (hab : transportedLiftEvaluation p r s h F a = transportedLiftEvaluation p r s h F b) :
    evalAtLiftOver p r s h ((pullbackSheaves p).obj F) a =
      evalAtLiftOver p r s h ((pullbackSheaves p).obj F) b :=
  (ConcreteCategory.bijective_of_isIso (liftIso p r s h F).hom).1 hab

@[reassoc]
private theorem evalAtLiftOver_naturality {F G : Ab Y} (a : F ⟶ G)
    (r : Spec (.of K) ⟶ Y) (s : Spec (.of K) ⟶ X) (h : r ≫ p = s) :
    (stalk s).map ((pushforward p).map a) ≫ evalAtLiftOver p r s h G =
      evalAtLiftOver p r s h F ≫ (stalk r).map a := by
  subst s
  simpa only [evalAtLiftOver, eqToHom_refl, Category.id_comp] using evalAtLift_naturality p r a

set_option maxRecDepth 4096 in
/-- Restricting a direct-image germ along a map over the base evaluates
at the image of the lifted geometric point. -/
theorem restrict_evaluation {Z : Scheme.{u}} (d : Z ⟶ Y) (ρ : Z ⟶ X) (hd : d ≫ p = ρ)
    (v : Spec (.of K) ⟶ Z) (s : Spec (.of K) ⟶ X) (h : (v ≫ d) ≫ p = s)
    (hρ : v ≫ ρ = s) (F : Ab X) :
    (stalk s).map (restrictDirectImage p d ρ hd F) ≫ transportedLiftEvaluation ρ v s hρ F =
      transportedLiftEvaluation p (v ≫ d) s h F := by
  subst ρ
  let A := (pullbackSheaves p).obj F
  let B := (pullbackSheaves d).obj A
  let H := (pullbackSheaves (d ≫ p)).obj F
  let α : A ⟶ (pushforward d).obj B := (pullbackAdjunction d).unit.app A
  let β : B ⟶ H := (pullbackCompIso p d).hom.app F
  let μ := (liftIso (d ≫ p) v s hρ F).hom
  let S := stalk s
  let e := evalAtLiftOver p (v ≫ d) s h A
  let c := (stalk (v ≫ d)).map α ≫ evalAtLift d v B ≫ (stalk v).map β ≫ μ
  let δ := restrictDirectImage p d (d ≫ p) rfl F
  have hδ : δ = (pushforward p).map α ≫ (pushforwardCompIso p d).hom.app B ≫
      (pushforward (d ≫ p)).map β := by
    simp only [δ, restrictDirectImage, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
    rfl
  have hf : S.map δ ≫ transportedLiftEvaluation (d ≫ p) v s hρ F = e ≫ c := by
    rw [hδ, S.map_comp, S.map_comp]
    simp only [transportedLiftEvaluation, Category.assoc]
    change S.map ((pushforward p).map α) ≫ S.map ((pushforwardCompIso p d).hom.app B) ≫
      S.map ((pushforward (d ≫ p)).map β) ≫ evalAtLiftOver (d ≫ p) v s hρ H ≫ μ = _
    rw [evalAtLiftOver_naturality_assoc (d ≫ p) β v s hρ,
      reassoc_of% (evalAtLiftOver_comp p d v s h B),
      evalAtLiftOver_naturality_assoc p α (v ≫ d) s h]
  let k := S.map ((pullbackAdjunction p).unit.app F) ≫ e
  let i := liftIso p (v ≫ d) s h F
  have hk : k ≫ i.hom = 𝟙 _ := by
    exact (Category.assoc _ _ _).trans (unit_evaluation p (v ≫ d) s h F)
  have hk' : k = i.inv := (cancel_mono i.hom).mp (hk.trans i.inv_hom_id.symm)
  have : Epi k := by rw [hk']; infer_instance
  have hc : c = i.hom := (cancel_epi k).mp (by
    calc
      k ≫ c = S.map ((pullbackAdjunction p).unit.app F) ≫ S.map δ ≫
          transportedLiftEvaluation (d ≫ p) v s hρ F := by
        change (S.map ((pullbackAdjunction p).unit.app F) ≫ e) ≫ c = _
        rw [Category.assoc, hf]
      _ = 𝟙 _ := by
        rw [← S.map_comp_assoc, unit_restrictDirectImage]
        exact unit_evaluation (d ≫ p) v s hρ F
      _ = k ≫ i.hom := hk.symm)
  exact hf.trans (congrArg (e ≫ ·) hc)

theorem restrict_evaluation_of_eq {Z : Scheme.{u}} (d : Z ⟶ Y) (ρ : Z ⟶ X) (hd : d ≫ p = ρ)
    (v : Spec (.of K) ⟶ Z) (r : Spec (.of K) ⟶ Y) (s : Spec (.of K) ⟶ X) (hv : v ≫ d = r)
    (hr : r ≫ p = s) (hρ : v ≫ ρ = s) (F : Ab X) :
    (stalk s).map (restrictDirectImage p d ρ hd F) ≫ transportedLiftEvaluation ρ v s hρ F =
      transportedLiftEvaluation p r s hr F := by
  subst r
  exact restrict_evaluation p d ρ hd v s hr hρ F

end PhilipponEtaleDescentCofaces

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponEtaleGeometricFieldExtension

universe u

/-- An extended-field point of an étale chart descends to the original
separably closed field if its image in the base scheme does. -/
theorem exists_descent_of_etale_point {X U : Scheme.{u}} (g : U ⟶ X) [Etale g]
    {K L : Type u} [Field K] [IsSepClosed K] [Field L]
    (s : Spec (.of K) ⟶ X) (a : Spec (.of L) ⟶ Spec (.of K))
    (t : Spec (.of L) ⟶ U) (ht : t ≫ g = a ≫ s) :
    ∃ r : Spec (.of K) ⟶ U, r ≫ g = s ∧ a ≫ r = t := by
  let q := pullback.snd g s
  let z := pullback.lift t a ht
  have : Etale q := inferInstanceAs (Etale (pullback.snd g s))
  obtain ⟨v, hv, hs⟩ := Scheme.exists_fac_of_etale_of_isSepClosed q (𝟙 _) (z default)
    (Subsingleton.elim _ _)
  have : Etale (v ≫ q) := hv ▸ inferInstance
  have : Etale v := Etale.of_comp v q
  have : Mono v := mono_of_mono_fac hv
  have : IsOpenImmersion v := IsOpenImmersion.of_flat_of_mono v
  have hZ : Set.range z ⊆ Set.range v := by
    rintro _ ⟨x, rfl⟩
    exact ⟨default, hs.trans (congrArg z (Subsingleton.elim _ _))⟩
  let b := IsOpenImmersion.lift v z hZ
  have hb : b ≫ v = z := IsOpenImmersion.lift_fac _ _ _
  have he : b = a := by
    have hz : z ≫ q = a := pullback.lift_snd _ _ _
    rw [← hb, Category.assoc, hv, Category.comp_id] at hz
    exact hz
  refine ⟨v ≫ pullback.fst g s, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ s) hv).trans (Category.id_comp s)
  · rw [← he, ← Category.assoc, hb]
    exact pullback.lift_fst _ _ _

end PhilipponEtaleGeometricFieldExtension

end

end


