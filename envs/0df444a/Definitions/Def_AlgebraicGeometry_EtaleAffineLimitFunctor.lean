-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitFunctor
-- name    : AlgebraicGeometry_EtaleAffineLimitFunctor
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T05:04:15.906271+00:00
-- url     : https://prove2.me/theorems/8bd259fb-c1f1-547f-80ca-adb6841f5f35
-- title:
--   The limit functor and exactness for compatible étale sheaves
-- statement:
--   The construction of the limit sheaf is functorial. The image condition for an exact sequence can be checked locally at a stage, which shows that the limit functor preserves sequences that are exact at every stage.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitSheaf
import Definitions.Def_AlgebraicGeometry_EtaleModeledCech
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponRestrictedKan

variable {A B C W : Type*} [Category* A] [Category* B] [Category* C] [Category* W]
  (L : A ⥤ B) (F : A ⥤ W) (G : C ⥤ B)
  (d : ∀ c : C, ColimitCocone (CostructuredArrow.proj L (G.obj c) ⋙ F))

section Map

variable {F' : A ⥤ W}
  (d' : ∀ c : C, ColimitCocone (CostructuredArrow.proj L (G.obj c) ⋙ F'))
  (η : F ⟶ F')

private def coconeMap (x : C) : Cocone (CostructuredArrow.proj L (G.obj x) ⋙ F) :=
  (Cocone.precompose (Functor.whiskerLeft (CostructuredArrow.proj L (G.obj x)) η)).obj
    (d' x).cocone

/-- A map of the original diagrams induces a map between their restricted
pointwise colimits. -/
def mapRestricted : restrictedColimit L F G d ⟶ restrictedColimit L F' G d' where
  app x := (d x).isColimit.desc (coconeMap L F G d' η x)
  naturality {x y} f := (d x).isColimit.hom_ext fun j => by
    rw [ι_map_assoc, (d y).isColimit.fac, ← Category.assoc, (d x).isColimit.fac]
    change η.app j.left ≫ (d' y).cocone.ι.app ((CostructuredArrow.map (G.map f)).obj j) =
      (η.app j.left ≫ (d' x).cocone.ι.app j) ≫ (restrictedColimit L F' G d').map f
    rw [Category.assoc, ι_map]

@[reassoc]
theorem ι_mapRestricted (x : C) (j : CostructuredArrow L (G.obj x)) :
    (d x).cocone.ι.app j ≫ (mapRestricted L F G d d' η).app x =
      η.app j.left ≫ (d' x).cocone.ι.app j :=
  (d x).isColimit.fac (coconeMap L F G d' η x) j

end Map
end PhilipponRestrictedKan

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponCompatibleSystemCokernel (Hom comp_app zero_app)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (toLimit)
open PhilipponEtaleSystemPresheaf (presheaf presheafMap)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affineColimit affinePresheaf)
open PhilipponEtaleLimitSheaf (topology restriction)


namespace PhilipponEtaleLimitFunctor

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) {F H : System (directImages D)}

private abbrev L := (toLimit c).op
private abbrev G := (affineCharts c.pt).ι.op

/-- Maps of compatible systems act on the section colimits on affine charts. -/
def affineMap (η : Hom F H) : affinePresheaf c hc F ⟶ affinePresheaf c hc H :=
  PhilipponRestrictedKan.mapRestricted (L c) (presheaf F) (G c)
    (fun U => affineColimit c hc F U.unop) (fun U => affineColimit c hc H U.unop) (presheafMap η)

@[reassoc]
theorem ι_affineMap (η : Hom F H) (U : (affineCharts c.pt).FullSubcategory)
    (j : CostructuredArrow (L c) (op U.obj)) :
    (affineColimit c hc F U).cocone.ι.app j ≫ (affineMap c hc η).app (op U) =
      (presheafMap η).app j.left ≫ (affineColimit c hc H U).cocone.ι.app j :=
  PhilipponRestrictedKan.ι_mapRestricted (L c) (presheaf F) (G c)
    (fun T => affineColimit c hc F T.unop) (fun T => affineColimit c hc H T.unop)
    (presheafMap η) (op U) j

/-- The colimits of compatible systems, as sheaves on the affine charts. -/
def affineFunctor : System (directImages D) ⥤ Sheaf (topology c) AddCommGrpCat.{u} where
  obj F := ⟨affinePresheaf c hc F, PhilipponEtaleLimitSheaf.isSheaf c hc F⟩
  map η := ⟨affineMap c hc η⟩
  map_id F := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (affineMap c hc (𝟙 F)).app (op U.unop) = 𝟙 _
    apply (affineColimit c hc F U.unop).isColimit.hom_ext
    intro j
    rw [ι_affineMap]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  map_comp {F H P} f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (affineMap c hc (f ≫ g)).app (op U.unop) =
      (affineMap c hc f).app (op U.unop) ≫ (affineMap c hc g).app (op U.unop)
    apply (affineColimit c hc F U.unop).isColimit.hom_ext
    intro j
    rw [ι_affineMap, ι_affineMap_assoc, ι_affineMap, ← Category.assoc]
    rfl

instance : (affineFunctor c hc).PreservesZeroMorphisms where
  map_zero F H := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (affineMap c hc (0 : F ⟶ H)).app (op U.unop) = 0
    apply (affineColimit c hc F U.unop).isColimit.hom_ext
    intro j
    rw [ι_affineMap, comp_zero]
    change (0 : (presheaf F).obj j.left ⟶ (presheaf H).obj j.left) ≫ _ = _
    exact zero_comp

/-- The limit sheaf construction on compatible systems. -/
def limitFunctor : System (directImages D) ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u} :=
  affineFunctor c hc ⋙ (restriction c).asEquivalence.inverse

instance : (limitFunctor c hc).PreservesZeroMorphisms := by
  let e := (restriction c).asEquivalence
  let : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  change (affineFunctor c hc ⋙ e.inverse).PreservesZeroMorphisms
  infer_instance

end PhilipponEtaleLimitFunctor

end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace PhilipponFilteredCohomologyDetection

universe u

/-- An element whose image in a filtered colimit of abelian groups is zero
has zero image along a transition map. -/
theorem exists_map_eq_zero {I : Type u} [Category.{u} I] [IsFiltered I]
    (D : I ⥤ AddCommGrpCat.{u}) {c : Cocone D} (hc : IsColimit c)
    {i : I} (x : D.obj i) (hx : c.ι.app i x = 0) :
    ∃ (j : I) (f : i ⟶ j), D.map f x = 0 := by
  let U := forget AddCommGrpCat.{u}
  let c' := U.mapCocone c
  have hc' : IsColimit c' := isColimitOfPreserves U hc
  have he : c'.ι.app i x = c'.ι.app i (0 : D.obj i) :=
    hx.trans (map_zero (c.ι.app i).hom).symm
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' x (0 : D.obj i)).mp he
  exact ⟨j, f, hf.trans (map_zero (D.map f).hom)⟩

end PhilipponFilteredCohomologyDetection

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponCompatibleSystemCokernel (Hom)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (toLimit)
open PhilipponEtaleLimitChartIndex (fromStages fromStages_final)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affineColimit affinePresheaf AffineModel)
open PhilipponEtaleLimitFunctor (affineMap ι_affineMap affineFunctor limitFunctor)
open PhilipponEtaleLimitSheaf (topology restriction)
open PhilipponEtaleSystemPresheaf (presheaf presheafMap presheafFunctor)


namespace PhilipponEtaleLimitRepresentatives

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}
  (c : Cone D) (U : (affineCharts c.pt).FullSubcategory) (M : AffineModel c U.obj)

/-- Refine a model of an affine chart through the stages, with the
canonical isomorphisms of the resulting limit charts. -/
def modelIndices : (Over M.chart.index)ᵒᵖ ⥤ CostructuredArrow (toLimit c).op (op U.obj) :=
  fromStages c M.chart ⋙ (CostructuredArrow.mapIso M.comparison.op).functor

instance (j : (Over M.chart.index)ᵒᵖ) : IsIso ((modelIndices c U M).obj j).hom := by
  change IsIso ((PhilipponEtaleChartLimitDiagram.toLimitIso M.chart c j.unop).inv.op ≫
    M.comparison.hom.op)
  infer_instance

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)] (hc : IsLimit c)

include hc in
theorem modelIndices_final : (modelIndices c U M).Final := by
  let : IsAffine M.chart.etale.left := M.affine
  let : (fromStages c M.chart).Final := fromStages_final c M.chart hc
  change (fromStages c M.chart ⋙ (CostructuredArrow.mapIso M.comparison.op).functor).Final
  infer_instance

variable (F : System (directImages D))

/-- The filtered section diagram of a model for a fixed affine chart. -/
abbrev modelDiagram :=
  modelIndices c U M ⋙ CostructuredArrow.proj (toLimit c).op (op U.obj) ⋙ presheaf F

/-- The limit sections as a cocone on the filtered diagram of a model. -/
def modelCocone : Cocone (modelDiagram c U M F) :=
  (affineColimit c hc F U).cocone.whisker (modelIndices c U M)

/-- Sections of the limit sheaf on an affine chart are computed by each model. -/
def modelCoconeIsColimit : IsColimit (modelCocone c U M hc F) := by
  let : (modelIndices c U M).Final := modelIndices_final c U M hc
  exact (Functor.Final.isColimitWhiskerEquiv (modelIndices c U M) _).symm
    (affineColimit c hc F U).isColimit

variable {c U M F} in
/-- A section of the affine limit sheaf is represented by a section at
some stage of any model of the chart. -/
theorem exists_rep (hc : IsLimit c) (y : (affinePresheaf c hc F).obj (op U)) :
    ∃ j x, (modelCocone c U M hc F).ι.app j x = y := by
  let V := forget AddCommGrpCat.{u}
  let d := modelCocone c U M hc F
  let h : IsColimit (V.mapCocone d) :=
    isColimitOfPreserves V (modelCoconeIsColimit c U M hc F)
  exact Types.jointly_surjective_of_isColimit h y

variable {F}

/-- Maps of the limit sheaves take a representative to the same-stage
image of that representative. -/
theorem map_rep {H : System (directImages D)} (f : Hom F H)
    (j : (Over M.chart.index)ᵒᵖ) (x : (modelDiagram c U M F).obj j) :
    (affineMap c hc f).app (op U) ((modelCocone c U M hc F).ι.app j x) =
      (modelCocone c U M hc H).ι.app j ((presheafMap f).app ((modelIndices c U M).obj j).left x) :=
  congrArg (fun (m : (modelDiagram c U M F).obj j ⟶ (affinePresheaf c hc H).obj (op U)) => m x)
    (ι_affineMap c hc f U ((modelIndices c U M).obj j))

/-- A section killed by a compatible map is represented at some stage
by a section in the kernel at that stage. -/
theorem exists_rep_in_kernel {H : System (directImages D)} (f : Hom F H)
    (x : (affinePresheaf c hc F).obj (op U))
    (hx : (affineMap c hc f).app (op U) x = 0) :
    ∃ j y, (modelCocone c U M hc F).ι.app j y = x ∧
      (presheafMap f).app ((modelIndices c U M).obj j).left y = 0 := by
  obtain ⟨j, y, hy⟩ := exists_rep (M := M) hc x
  have h₀ := ((map_rep c U M hc f j y).symm.trans (congrArg _ hy)).trans hx
  obtain ⟨k, a, ha⟩ := PhilipponFilteredCohomologyDetection.exists_map_eq_zero
    (modelDiagram c U M H) (modelCoconeIsColimit c U M hc H) _ h₀
  let A := modelDiagram c U M F
  let B := modelDiagram c U M H
  let φ : A ⟶ B := Functor.whiskerLeft
    (modelIndices c U M ⋙ CostructuredArrow.proj (toLimit c).op (op U.obj)) (presheafMap f)
  have hn : φ.app k (A.map a y) = B.map a (φ.app j y) :=
    NatTrans.naturality_apply φ a y
  refine ⟨k, A.map a y, ?_, hn.trans ha⟩
  exact (congrArg (fun (m : A.obj j ⟶ (modelCocone c U M hc F).pt) => m y)
    ((modelCocone c U M hc F).w a)).trans hy

/-- Stagewise monomorphisms induce sectionwise monomorphisms on all
affine limit charts. -/
theorem affineMap_injective {H : System (directImages D)} (f : Hom F H)
    (hf : ∀ i, Mono (f.app i)) :
    Function.Injective ((affineMap c hc f).app (op U)) := by
  let : IsAffine U.obj.left := U.property
  let M := (PhilipponEtaleLimitAffinePresheaf.exists_affineModel c hc U.obj).some
  apply (injective_iff_map_eq_zero ((affineMap c hc f).app (op U)).hom).mpr
  intro x hx
  obtain ⟨j, y, hy, hfy⟩ := exists_rep_in_kernel c U M hc f x hx
  let A := ((modelIndices c U M).obj j).left.unop
  let : Mono (f.app A.index) := hf A.index
  let : Mono (f.app A.index).hom :=
    (sheafToPresheaf (D.obj A.index).smallEtaleTopology AddCommGrpCat.{u}).map_mono (f.app A.index)
  have hm : Mono ((f.app A.index).hom.app (op A.etale)) := inferInstance
  have hz : y = 0 := (AddCommGrpCat.mono_iff_injective _).mp hm (hfy.trans (map_zero _).symm)
  rw [← hy, hz, map_zero]

/-- The filtered section diagram, functorially in the system of sheaves. -/
def modelFunctor : System (directImages D) ⥤ (Over M.chart.index)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  presheafFunctor ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (modelIndices c U M ⋙ CostructuredArrow.proj (toLimit c).op (op U.obj))

instance : (modelFunctor c U M).PreservesZeroMorphisms := by
  delta modelFunctor
  infer_instance

/-- The colimit formula for sections is natural in the system. -/
def modelSectionsIso :
    modelFunctor c U M ⋙ colim ≅
      affineFunctor c hc ⋙ (sheafSections (topology c) AddCommGrpCat.{u}).obj (op U) := by
  let A := modelFunctor c U M
  let C (H : System (directImages D)) := modelCocone c U M hc H
  let e (H : System (directImages D)) :=
    (colimit.isColimit (A.obj H)).coconePointUniqueUpToIso (modelCoconeIsColimit c U M hc H)
  refine NatIso.ofComponents e ?_
  intro P Q f
  change colimMap (A.map f) ≫ (e Q).hom = (e P).hom ≫ (affineMap c hc f).app (op U)
  apply colimit.hom_ext
  intro j
  change colimit.ι (A.obj P) j ≫ colimMap (A.map f) ≫ (e Q).hom =
    colimit.ι (A.obj P) j ≫ (e P).hom ≫ (affineMap c hc f).app (op U)
  have hP : colimit.ι (A.obj P) j ≫ (e P).hom = (C P).ι.app j :=
    (colimit.isColimit (A.obj P)).fac (C P) j
  have hQ : colimit.ι (A.obj Q) j ≫ (e Q).hom = (C Q).ι.app j :=
    (colimit.isColimit (A.obj Q)).fac (C Q) j
  rw [ι_colimMap_assoc, hQ, ← Category.assoc, hP]
  exact (ι_affineMap c hc f U ((modelIndices c U M).obj j)).symm

/-- The colimit formula holds as sections of the full limit sheaf. -/
def modelLimitSectionsIso :
    modelFunctor c U M ⋙ colim ≅
      limitFunctor c hc ⋙ (sheafSections c.pt.smallEtaleTopology AddCommGrpCat.{u}).obj (op U.obj) :=
  modelSectionsIso c U M hc ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (affineFunctor c hc) (restriction c).asEquivalence.counitIso.symm)
      ((sheafSections (topology c) AddCommGrpCat.{u}).obj (op U))

end PhilipponEtaleLimitRepresentatives

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponCompatibleSystemCokernel (Hom)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (StageChart atStage toLimit atStage_toLimit_eq)
open PhilipponEtaleSystemPresheaf (presheaf presheafMap map_atStage)
open PhilipponEtaleBaseChangeComparison (baseChange coverPreserving)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affineColimit affinePresheaf affinePresheaf_ι_map)
open PhilipponEtaleLimitSheaf (topology)
open PhilipponEtaleLimitFunctor (affineMap ι_affineMap)
open PhilipponEtaleAffineSectionColimit (pullbackAffine)


namespace PhilipponEtaleLimitLocalImage

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
  {F H : System (directImages D)} (f : Hom F H)
  {U : (affineCharts c.pt).FullSubcategory}
  (j : CostructuredArrow (toLimit c).op (op U.obj)) [IsIso j.hom]

variable {c} in
private abbrev A := j.left.unop

private def comparison : U.obj ≅ (toLimit c).obj (A j) := asIso j.hom.unop

private abbrev K := atStage (D := D) (A j).index ⋙ toLimit c

private def refines (V : (affineCharts (D.obj (A j).index)).FullSubcategory)
    (a : V.obj ⟶ (A j).etale) :
    (pullbackAffine (A j).index c hc).obj V ⟶ U :=
  ObjectProperty.homMk ((K c j).map a ≫ (comparison c j).inv)

private theorem mem_image_of_stage {V : (affineCharts (D.obj (A j).index)).FullSubcategory}
    (a : V.obj ⟶ (A j).etale) (y : (presheaf H).obj j.left)
    (hy : Presheaf.imageSieve (f.app (A j).index).hom y a) :
    Presheaf.imageSieve (affineMap c hc f) ((affineColimit c hc H U).cocone.ι.app j y)
      (refines c hc j V a) := by
  obtain ⟨z, hz⟩ := hy
  let W := (pullbackAffine (A j).index c hc).obj V
  let w := refines c hc j V a
  let L := (toLimit c).op
  let B := ((atStage (A j).index).obj V.obj : StageChart D)
  let b : B ⟶ A j := (atStage (A j).index).map a
  let k : CostructuredArrow L (op W.obj) := CostructuredArrow.mk (𝟙 (op ((toLimit c).obj B)))
  let l := (CostructuredArrow.map w.hom.op).obj j
  let m : l ⟶ k := CostructuredArrow.homMk b.op (by
    apply Quiver.Hom.unop_inj
    change 𝟙 _ ≫ (K c j).map a = ((K c j).map a ≫ (comparison c j).inv) ≫ (comparison c j).hom
    rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  refine ⟨(affineColimit c hc F W).cocone.ι.app k z, ?_⟩
  have h₀ := congrArg
    (fun (g : (presheaf F).obj (op B) ⟶ (affinePresheaf c hc H).obj (op W)) => g z)
      (ι_affineMap c hc f W k)
  have h₁ := congrArg
    (fun (g : (presheaf H).obj j.left ⟶ (affinePresheaf c hc H).obj (op W)) => g y)
      ((affineColimit c hc H W).cocone.w m)
  have h₂ := congrArg
    (fun (g : (presheaf H).obj j.left ⟶ (affinePresheaf c hc H).obj (op W)) => g y)
      (affinePresheaf_ι_map c hc H w j)
  simp only [ConcreteCategory.comp_apply] at h₀ h₁ h₂
  change (affineMap c hc f).app (op W) ((affineColimit c hc F W).cocone.ι.app k z) =
    (affinePresheaf c hc H).map w.op ((affineColimit c hc H U).cocone.ι.app j y)
  let V_H := (H.obj (A j).index).obj.obj (op V.obj)
  let Q : V_H ⟶ (affinePresheaf c hc H).obj (op W) := (affineColimit c hc H W).cocone.ι.app k
  have hh := congrArg (fun (u : V_H) => Q u) hz
  have hs := congrArg (fun (p : (presheaf H).obj j.left ⟶ V_H) => Q (p y)) (map_atStage H a)
  exact h₀.trans (hh.trans (hs.symm.trans (h₁.trans h₂.symm)))

/-- Local preimages at a stage give local preimages on an isomorphic
affine chart of the limit. -/
theorem imageSieve_mem_of_rep (y : (presheaf H).obj j.left)
    (hy : Presheaf.imageSieve (f.app (A j).index).hom y ∈ (D.obj (A j).index).smallEtaleTopology (A j).etale)
    (hA : IsAffine (A j).etale.left) :
    Presheaf.imageSieve (affineMap c hc f) ((affineColimit c hc H U).cocone.ι.app j y) ∈
      topology c U := by
  let J := (D.obj (A j).index).smallEtaleTopology
  let G₀ := (affineCharts (D.obj (A j).index)).ι
  let A₀ : (affineCharts (D.obj (A j).index)).FullSubcategory := ⟨(A j).etale, hA⟩
  let T : Sieve (G₀.obj A₀) := Presheaf.imageSieve (f.app (A j).index).hom y
  let T₀ : Sieve A₀ := Sieve.functorPullback G₀ (X := A₀) T
  have hT : T₀.functorPushforward G₀ ∈ J (G₀.obj A₀) :=
    Functor.IsCoverDense.functorPullback_pushforward_covering (G := G₀) (X := A₀) ⟨T, hy⟩
  let r := c.π.app (A j).index
  have hK : (T₀.functorPushforward G₀).functorPushforward (K c j) ∈
      c.pt.smallEtaleTopology ((K c j).obj (A j).etale) := by
    rw [show K c j = baseChange r from atStage_toLimit_eq c _]
    exact (coverPreserving r).cover_preserve hT
  let a (t : T₀.arrows.category) := refines c hc j t.obj.left t.obj.hom.hom
  let R := Sieve.ofArrows (fun t : T₀.arrows.category => (pullbackAffine (A j).index c hc).obj t.obj.left) a
  have hR : R ∈ topology c U := by
    let G := (affineCharts c.pt).ι
    apply (G.mem_inducedTopology_iff_of_isCoverDense _ _).mpr
    rw [Sieve.functorPushforward_ofArrows]
    rw [← Sieve.ofArrows_category T₀, Sieve.functorPushforward_ofArrows,
      Sieve.functorPushforward_ofArrows] at hK
    apply c.pt.smallEtaleTopology.superset_covering _
      (c.pt.smallEtaleTopology.pullback_stable (comparison c j).hom hK)
    rintro B b ⟨Q, g, _, ⟨t⟩, ht⟩
    refine ⟨_, g, _, ⟨t⟩, ?_⟩
    have he := congrArg (· ≫ (comparison c j).inv) ht
    change (g ≫ (K c j).map t.obj.hom.hom) ≫ (comparison c j).inv =
      (b ≫ (comparison c j).hom) ≫ (comparison c j).inv at he
    change g ≫ (K c j).map t.obj.hom.hom ≫ (comparison c j).inv = b
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he
  refine (topology c).superset_covering ?_ hR
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨t⟩
  exact mem_image_of_stage c hc f j _ y t.property

end PhilipponEtaleLimitLocalImage

end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite

namespace PhilipponTorsorSectionExactness
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]

def evaluation (U : Cᵒᵖ) : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U

end PhilipponTorsorSectionExactness

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponCompatibleSystemCokernel (Hom)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleSystemPresheaf (presheafMap)
open PhilipponEtaleLimitAffinePresheaf (affineCharts exists_affineModel)
open PhilipponEtaleLimitSheaf (topology)
open PhilipponEtaleLimitFunctor (affineFunctor limitFunctor)
open PhilipponEtaleLimitRepresentatives (modelIndices modelCocone exists_rep_in_kernel affineMap_injective)
open PhilipponEtaleLimitLocalImage (imageSieve_mem_of_rep)


namespace PhilipponEtaleLimitExactness

universe u v w

section SheafKernels

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]
  (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))

private theorem injective_iCycles (V : C) :
    Function.Injective (S.iCycles.hom.app (op V)) := by
  let E : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
    PhilipponTorsorSectionExactness.evaluation (J := J) (op V)
  let : PreservesLimits E := inferInstanceAs (PreservesLimits
    (sheafToPresheaf J AddCommGrpCat.{w} ⋙ (CategoryTheory.evaluation _ _).obj (op V)))
  exact (AddCommGrpCat.mono_iff_injective _).mp (E.map_mono S.iCycles)

private theorem imageSieve_cycles {U : C} (x : S.cycles.obj.obj (op U)) :
    Presheaf.imageSieve S.toCycles.hom x =
      Presheaf.imageSieve S.f.hom (S.iCycles.hom.app (op U) x) := by
  ext V a
  have ha (y : S.X₁.obj.obj (op V)) :
      S.f.hom.app (op V) y = S.iCycles.hom.app (op V) (S.toCycles.hom.app (op V) y) :=
    congrArg (fun (f : S.X₁ ⟶ S.X₂) => f.hom.app (op V) y) S.toCycles_i.symm
  have hn := NatTrans.naturality_apply S.iCycles.hom a.op x
  change (∃ y, S.toCycles.hom.app (op V) y = S.cycles.obj.map a.op x) ↔
    ∃ y, S.f.hom.app (op V) y = S.X₂.obj.map a.op (S.iCycles.hom.app (op U) x)
  simp only [ha, ← hn, (injective_iCycles S V).eq_iff]

private theorem exists_cycle_section {U : C} (x : S.X₂.obj.obj (op U))
    (hx : S.g.hom.app (op U) x = 0) :
    ∃ y, S.iCycles.hom.app (op U) y = x := by
  let E : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
    PhilipponTorsorSectionExactness.evaluation (J := J) (op U)
  let : PreservesLimits E := inferInstanceAs (PreservesLimits
    (sheafToPresheaf J AddCommGrpCat.{w} ⋙ (CategoryTheory.evaluation _ _).obj (op U)))
  let : E.PreservesZeroMorphisms := inferInstanceAs
    ((sheafToPresheaf J AddCommGrpCat.{w} ⋙ (CategoryTheory.evaluation _ _).obj (op U)).PreservesZeroMorphisms)
  let T := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hT : T.Exact := T.exact_of_f_is_kernel S.cyclesIsKernel
  have h := (ShortComplex.ab_exact_iff_function_exact (T.map E)).mp
    (hT.map_of_mono_of_preservesKernel E inferInstance inferInstance)
  exact (h x).mp hx

variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

private theorem imageSieve_mem_of_exact [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hS : S.Exact) {U : C}
    (x : S.X₂.obj.obj (op U)) (hx : S.g.hom.app (op U) x = 0) :
    Presheaf.imageSieve S.f.hom x ∈ J U := by
  obtain ⟨z, rfl⟩ := exists_cycle_section S x hx
  rw [← imageSieve_cycles S z]
  let : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} S.toCycles).mpr hS.epi_toCycles
  exact Presheaf.imageSieve_mem J S.toCycles.hom z

private theorem exact_of_local_image
    (h : ∀ (U : C) (x : S.X₂.obj.obj (op U)), S.g.hom.app (op U) x = 0 →
      Presheaf.imageSieve S.f.hom x ∈ J U) :
    S.Exact := by
  apply (ShortComplex.exact_iff_epi_toCycles S).mpr
  let : Sheaf.IsLocallySurjective S.toCycles := ⟨fun {U} x => by
    rw [imageSieve_cycles]
    exact h U _ (congrArg (fun (f : S.cycles ⟶ S.X₃) => f.hom.app (op U) x) S.iCycles_g)⟩
  infer_instance

end SheafKernels

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}

/-- Evaluation of a compatible system at one stage. -/
def atStageSheaf (i : I) :
    System (directImages D) ⥤ Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u} where
  obj F := F.obj i
  map f := f.app i

instance (i : I) : (atStageSheaf (D := D) i).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)

/-- A pointwise monomorphism survives the limit construction. -/
theorem mono_affineMap {F G : System (directImages D)} (f : F ⟶ G)
    (hf : ∀ i, Mono (f.app i)) : Mono ((affineFunctor c hc).map f) := by
  apply Sheaf.mono_of_injective
  intro U
  exact affineMap_injective c U.unop hc f hf

/-- A pointwise monomorphism survives the full limit construction. -/
theorem mono_limitMap {F G : System (directImages D)} (f : F ⟶ G)
    (hf : ∀ i, Mono (f.app i)) : Mono ((limitFunctor c hc).map f) := by
  let : Mono ((affineFunctor c hc).map f) := mono_affineMap c hc f hf
  exact (PhilipponEtaleLimitSheaf.restriction c).asEquivalence.inverse.map_mono _

/-- A short complex exact at every stage remains exact after taking the
limit sheaves on the affine site. -/
theorem exact_affine (S : ShortComplex (System (directImages D)))
    (hS : ∀ i, (S.map (atStageSheaf i)).Exact) :
    (S.map (affineFunctor c hc)).Exact := by
  apply exact_of_local_image
  intro U x hx
  let : IsAffine U.obj.left := U.property
  let M := (exists_affineModel c hc U.obj).some
  obtain ⟨k, y, hy, hk⟩ := exists_rep_in_kernel c U M hc S.g x hx
  let j := (modelIndices c U M).obj k
  let A := j.left.unop
  let : IsAffine A.etale.left :=
    @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine (D.obj k.unop.left)
      M.chart.etale.left (D.obj M.chart.index)
      (D.map k.unop.hom) M.chart.etale.hom inferInstance M.affine inferInstance
  have hloc := imageSieve_mem_of_exact (S.map (atStageSheaf A.index)) (hS A.index) y hk
  rw [← hy]
  exact imageSieve_mem_of_rep c hc S.f j y hloc inferInstance

/-- The full limit sheaf construction preserves stagewise exactness. -/
theorem exact_limit (S : ShortComplex (System (directImages D)))
    (hS : ∀ i, (S.map (atStageSheaf i)).Exact) :
    (S.map (limitFunctor c hc)).Exact := by
  let e := (PhilipponEtaleLimitSheaf.restriction c).asEquivalence
  let : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  exact (exact_affine c hc S hS).map e.inverse

end PhilipponEtaleLimitExactness

end

end


