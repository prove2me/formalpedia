-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitUniversalProperty
-- name    : AlgebraicGeometry_EtaleAffineLimitUniversalProperty
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T07:16:59.501963+00:00
-- url     : https://prove2.me/theorems/dd19dcae-c544-4809-85c0-5324de3f36e4
-- title:
--   Universal property of the étale limit sheaf on affine schemes
-- statement:
--   A map out of the limit sheaf is determined by compatible maps on the stages. Restriction to the affine étale basis and extension from that basis give the bijection.
-- source:
--   Stacks Project, Lemmas 59.51.4, 59.73.2 and 59.74.4, https://stacks.math.columbia.edu/tag/03Q5.

import Definitions.Def_AlgebraicGeometry_EtalePullbackSystemComparisons

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages chart flatten fst_ext flatten_fst)
open PhilipponEtaleTotalStageSite (StageChart toLimit atStage atStage_toLimit toLimit_map_fst)
open PhilipponEtaleSystemPresheaf
  (presheaf map_atStage cartesianMap map_cartesian intoBaseChange factor_through_cartesian)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConeSystem (extended)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleLimitTestMaps (stageMap)


namespace PhilipponEtaleLimitTestMapConstruction

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D)
  (F : System (directImages D)) (H : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})
  (v : ∀ i, F.obj i ⟶ (pushforward (c.π.app i)).obj H)

private abbrev compare {i j : I} (a : i ⟶ j) :=
  (directImages (extended c)).composition (WithInitial.homTo i) (WithInitial.incl.map a)

private def app (A : StageChart D) : (presheaf F).obj (op A) ⟶ H.obj.obj (op ((toLimit c).obj A)) :=
  (v A.index).hom.app (op A.etale)

private theorem app_natural_stage {i : I} {U V : (D.obj i).Etale} (a : U ⟶ V) :
    (presheaf F).map ((atStage i).map a).op ≫ app c F H v ⟨i, U⟩ =
      app c F H v ⟨i, V⟩ ≫ H.obj.map ((toLimit c).map ((atStage i).map a)).op := by
  let e := atStage_toLimit c i
  have h := e.hom.naturality a
  change (toLimit c).map ((atStage i).map a) ≫ 𝟙 _ =
    𝟙 _ ≫ (baseChange (c.π.app i)).map a at h
  rw [Category.comp_id, Category.id_comp] at h
  rw [map_atStage, h]
  exact (v i).hom.naturality a.op

private theorem app_natural_cartesian
    (hv : ∀ {i j : I} (a : i ⟶ j),
      v j ≫ (compare c a).hom.app H = F.map a ≫ ((directImages D).functor a).map (v i))
    {i : I} (A : StageChart D) (a : i ⟶ A.index) :
    (presheaf F).map (cartesianMap A a).op ≫ app c F H v ⟨i, (chart D a).obj A.etale⟩ =
      app c F H v A ≫ H.obj.map ((toLimit c).map (cartesianMap A a)).op := by
  let b := (flatten (extended c) (WithInitial.homTo i) (WithInitial.incl.map a)).hom.app A.etale
  have hb : (toLimit c).map (cartesianMap A a) = b := by
    apply fst_ext (extended c) (WithInitial.homTo A.index) A.etale
    exact (toLimit_map_fst c (cartesianMap A a)).trans
      (flatten_fst (extended c) (WithInitial.homTo i) (WithInitial.incl.map a) A.etale).symm
  rw [map_cartesian, hb]
  exact (congrArg (fun m => m.hom.app (op A.etale)) (hv a)).symm

/-- Compatible maps at the stages assemble into a natural family of
section maps to the test sheaf on the cone point. -/
def ofStageMaps (hv : ∀ {i j : I} (a : i ⟶ j),
    v j ≫ (compare c a).hom.app H = F.map a ≫ ((directImages D).functor a).map (v i)) :
    presheaf F ⟶ (toLimit c).op ⋙ H.obj where
  app A := app c F H v A.unop
  naturality {A B} f := by
    let g := f.unop
    let a := (atStage (D := D) B.unop.index).map (intoBaseChange g)
    let b := cartesianMap A.unop g.indexMap
    have h : a ≫ b = g := factor_through_cartesian g
    change (presheaf F).map g.op ≫ app c F H v B.unop =
      app c F H v A.unop ≫ H.obj.map ((toLimit c).map g).op
    rw [← h, op_comp, (presheaf F).map_comp, (toLimit c).map_comp, op_comp,
      H.obj.map_comp, Category.assoc, app_natural_stage, ← Category.assoc,
      app_natural_cartesian c F H v hv, Category.assoc]

/-- Evaluating the assembled map at a stage recovers the original map. -/
theorem stageMap_ofStageMaps (hv : ∀ {i j : I} (a : i ⟶ j),
    v j ≫ (compare c a).hom.app H = F.map a ≫ ((directImages D).functor a).map (v i))
    (i : I) : stageMap c F H (ofStageMaps c F H v hv) i = v i := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rfl

end PhilipponEtaleLimitTestMapConstruction

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (StageChart toLimit)
open PhilipponEtaleSystemPresheaf (presheaf)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affineColimit affinePresheaf)
open PhilipponEtaleLimitSheaf (limitSheaf topology restriction restrictionIso)
open PhilipponEtaleLimitCanonical (naturalMap fromStage)
open PhilipponEtaleLimitTestMaps (stageMap)
open PhilipponEtaleLimitTestMapConstruction (ofStageMaps stageMap_ofStageMaps)
open PhilipponEtaleConeSystem (extended)
open PhilipponEtaleClosedPushforward (pushforward)


namespace PhilipponEtaleLimitUniversalProperty

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (F : System (directImages D))

private abbrev J := c.pt.smallEtaleTopology
private abbrev G := (affineCharts c.pt).ι
private abbrev L := (toLimit c).op

private def d (U : (affineCharts c.pt).FullSubcategoryᵒᵖ) :=
  affineColimit c hc F U.unop

private abbrev affineLimit : Sheaf (topology c) AddCommGrpCat.{u} :=
  ⟨affinePresheaf c hc F, PhilipponEtaleLimitSheaf.isSheaf c hc F⟩

variable (H : Sheaf (J c) AddCommGrpCat.{u})

private def kanEquiv :=
  PhilipponRestrictedKan.homEquiv (L c) (presheaf F) (G c).op (d c hc F)
    (PhilipponDenseSheafKan.isPointwiseRightKanExtension (G c) (J c) H)

/-- Maps of the limit sheaf to a test sheaf are the compatible families
of maps on the total stage site. -/
def homEquiv :
    (limitSheaf c hc F ⟶ H) ≃ (presheaf F ⟶ (L c) ⋙ H.obj) :=
  (restriction c).asEquivalence.fullyFaithfulFunctor.homEquiv.trans
    (((restrictionIso c hc F).homCongr (Iso.refl _)).trans
      (((fullyFaithfulSheafToPresheaf (topology c) AddCommGrpCat.{u}).homEquiv
        (X := affineLimit c hc F) (Y := (restriction c).obj H)).trans
        (kanEquiv c hc F H)))

private theorem homEquiv_symm_fac (η : presheaf F ⟶ (L c) ⋙ H.obj) :
    naturalMap c hc F ≫ Functor.whiskerLeft (L c) ((homEquiv c hc F H).symm η).hom = η := by
  let q := (homEquiv c hc F H).symm η
  let A := affineLimit c hc F
  let U := (restriction c).obj H
  let θ : A ⟶ U := ⟨(kanEquiv c hc F H).symm η⟩
  have hθ : (restriction c).map q = (restrictionIso c hc F).hom ≫ θ := by
    change (restriction c).map ((restriction c).asEquivalence.fullyFaithfulFunctor.preimage
      (((restrictionIso c hc F).hom ≫ θ) ≫ 𝟙 _)) = _
    rw [Functor.FullyFaithful.map_preimage, Category.comp_id]
  have h₁ : (kanEquiv c hc F (limitSheaf c hc F)).symm (naturalMap c hc F) =
      (restrictionIso c hc F).inv.hom :=
    (kanEquiv c hc F (limitSheaf c hc F)).symm_apply_apply _
  apply (kanEquiv c hc F H).symm.injective
  change PhilipponRestrictedKan.descend (L c) (presheaf F) (G c).op (d c hc F)
    (naturalMap c hc F ≫ Functor.whiskerLeft (L c) q.hom) = _
  rw [PhilipponRestrictedKan.descend_postcompose]
  change (kanEquiv c hc F (limitSheaf c hc F)).symm (naturalMap c hc F) ≫
    ((restriction c).map q).hom = _
  rw [h₁, hθ]
  exact congrArg (fun m => m.hom) ((restrictionIso c hc F).inv_hom_id_assoc θ)

/-- The universal comparison is composition with the canonical maps
from the stages. -/
theorem homEquiv_apply (q : limitSheaf c hc F ⟶ H) :
    homEquiv c hc F H q = naturalMap c hc F ≫ Functor.whiskerLeft (L c) q.hom := by
  let e := homEquiv c hc F H
  have h := homEquiv_symm_fac c hc F H (e q)
  rw [e.symm_apply_apply] at h
  exact h.symm

theorem stageMap_homEquiv (q : limitSheaf c hc F ⟶ H) (i : I) :
    stageMap c F H (homEquiv c hc F H q) i =
      fromStage c hc F i ≫ (pushforward (c.π.app i)).map q := by
  rw [homEquiv_apply]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

/-- A map out of the limit sheaf is determined by all its restrictions
to stages. -/
theorem hom_ext {p q : limitSheaf c hc F ⟶ H}
    (h : ∀ i, fromStage c hc F i ≫ (pushforward (c.π.app i)).map p =
      fromStage c hc F i ≫ (pushforward (c.π.app i)).map q) : p = q := by
  apply (homEquiv c hc F H).injective
  apply PhilipponEtaleLimitTestMaps.ext
  intro i
  rw [stageMap_homEquiv, stageMap_homEquiv, h i]

private abbrev compare {i j : I} (a : i ⟶ j) :=
  (directImages (extended c)).composition (WithInitial.homTo i) (WithInitial.incl.map a)

/-- A compatible family of maps of stage coefficients induces a map
out of the limit sheaf. -/
def desc (v : ∀ i, F.obj i ⟶ (pushforward (c.π.app i)).obj H)
    (hv : ∀ {i j : I} (a : i ⟶ j),
      v j ≫ (compare c a).hom.app H = F.map a ≫ ((directImages D).functor a).map (v i)) :
    limitSheaf c hc F ⟶ H :=
  (homEquiv c hc F H).symm (ofStageMaps c F H v hv)

/-- The map constructed from compatible stages has the prescribed
restriction at each stage. -/
@[reassoc]
theorem desc_fac (v : ∀ i, F.obj i ⟶ (pushforward (c.π.app i)).obj H)
    (hv : ∀ {i j : I} (a : i ⟶ j),
      v j ≫ (compare c a).hom.app H = F.map a ≫ ((directImages D).functor a).map (v i))
    (i : I) :
    fromStage c hc F i ≫ (pushforward (c.π.app i)).map (desc c hc F H v hv) = v i := by
  rw [← stageMap_homEquiv, desc, Equiv.apply_symm_apply]
  exact stageMap_ofStageMaps c F H v hv i

end PhilipponEtaleLimitUniversalProperty

end

end


