-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitSectionMaps
-- name    : AlgebraicGeometry_EtaleAffineLimitSectionMaps
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T06:36:10.976609+00:00
-- url     : https://prove2.me/theorems/c944a946-71fe-459c-9813-ddddc7162b35
-- title:
--   Stage maps on global sections of compatible étale sheaves
-- statement:
--   Under the identification of degree-zero cohomology with global sections, the maps in the section colimit are the cohomological transition maps.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitBoundaryMaps
import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitGlobalSections

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso terminalComparison)
open PhilipponEtaleDirectImageSystem (directImages chart)
open PhilipponEtaleTotalStageSite (StageChart StageHom atStage)
open PhilipponEtaleChartLimitDiagram (stageCharts)
open PhilipponEtaleSystemPresheaf (presheaf map_atStage map_cartesian cartesianMap)
open PhilipponEtaleLimitGlobalSections (sectionsDiagram evalIso)
open PhilipponEtaleModeledSections (reversedBaseChangeIso)
open PhilipponEtaleStageCohomology (transitionMap)


namespace PhilipponEtaleGlobalSectionTransitions

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (i : I)
  (F : System (directImages D))

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private abbrev A (D : I ⥤ Scheme.{u}) (i : I) : StageChart D := ⟨i, terminal (D.obj i)⟩

private def chartIso (D : I ⥤ Scheme.{u}) (j : Over i) :
    ((stageCharts (A D i)).obj j).etale ≅ terminal (D.obj j.left) :=
  (reversedBaseChangeIso (D.map j.hom)).app (terminal (D.obj i)) ≪≫ terminalComparison (D.map j.hom)

omit [IsCofiltered I] [∀ i, IsAffine (D.obj i)] in
private theorem chartMap_eq {j k : Over i} (a : j ⟶ k) :
    (stageCharts (A D i)).map a ≫ (atStage (D := D) k.left).map (chartIso i D k).hom =
      (atStage (D := D) j.left).map ((chartIso i D j).hom ≫ (terminalComparison (D.map a.left)).inv) ≫
        cartesianMap (A D k.left) a.left := by
  let l := (stageCharts (A D i)).map a ≫ (atStage (D := D) k.left).map (chartIso i D k).hom
  let r := (atStage (D := D) j.left).map ((chartIso i D j).hom ≫ (terminalComparison (D.map a.left)).inv) ≫
    cartesianMap (A D k.left) a.left
  have h : l.indexMap = r.indexMap := (Category.comp_id _).trans (Category.id_comp _).symm
  apply StageHom.ext h
  have hl := l.over
  have hr := r.over
  change l.left ≫ 𝟙 _ = _ at hl
  change r.left ≫ 𝟙 _ = _ at hr
  rw [Category.comp_id, h] at hl
  rw [Category.comp_id] at hr
  exact hl.trans hr.symm

private theorem map_commuting_square {C B : Type*} [Category* C] [Category* B]
    (P : Cᵒᵖ ⥤ B) {U V W Z : C} (a : U ⟶ V) (b : V ⟶ Z)
    (r : U ⟶ W) (s : W ⟶ Z) (h : a ≫ b = r ≫ s) :
    P.map b.op ≫ P.map a.op = P.map s.op ≫ P.map r.op := by
  rw [← P.map_comp, ← op_comp, h, op_comp, P.map_comp]

/-- The stages in the global-sections colimit have transition maps
given by evaluating the coefficient system's sheaf maps. -/
theorem eval_transition {j k : Over i} (a : j ⟶ k) :
    ((sectionsDiagram c hc i).obj F).map a.op ≫ ((evalIso c hc i (op j)).app F).hom =
      ((evalIso c hc i (op k)).app F).hom ≫
        (globalSections (D.obj k.left)).map (transitionMap a.left F) ≫
        (globalSectionsIso (D.map a.left)).hom.app (F.obj j.left) := by
  let P := presheaf F
  let b := D.map a.left
  let V := terminal (D.obj k.left)
  let e₀ := (F.obj k.left).obj.mapIso (chartIso i D k).symm.op
  let e₁ := (F.obj j.left).obj.mapIso (chartIso i D j).symm.op
  let m := (transitionMap a.left F).hom.app (op V)
  let n := (F.obj j.left).obj.map (terminalComparison b).inv.op
  let u := (stageCharts (A D i)).map a
  let v := (atStage (D := D) k.left).map (chartIso i D k).hom
  let s := (atStage (D := D) j.left).map ((chartIso i D j).hom ≫ (terminalComparison b).inv)
  let t := cartesianMap (A D k.left) a.left
  have huv : u ≫ v = s ≫ t := chartMap_eq i a
  have hv : P.map v.op = e₀.inv := map_atStage F (chartIso i D k).hom
  have hs : P.map s.op = n ≫ e₁.inv := by
    refine (map_atStage F ((chartIso i D j).hom ≫ (terminalComparison b).inv)).trans ?_
    exact (F.obj j.left).obj.map_comp (terminalComparison b).inv.op (chartIso i D j).hom.op
  have ht : P.map t.op = m := map_cartesian F (A D k.left) a.left
  have h := map_commuting_square P u v s t huv
  rw [hv, hs, ht] at h
  change P.map u.op ≫ e₁.hom = e₀.hom ≫ m ≫ n
  calc
    _ = e₀.hom ≫ (e₀.inv ≫ P.map u.op) ≫ e₁.hom := by
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = _ := by
      rw [h]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end PhilipponEtaleGlobalSectionTransitions

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitSheaf (limitSheaf)
open PhilipponEtaleLimitCanonical (fromStage restrictCoefficients)
open PhilipponEtaleLimitCohomologyTransport (stageRestriction)
open PhilipponEtaleLimitSectionProjections (stageSections)
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleCohomologyRestrictionComp (sectionsEquiv sectionsEquiv_restrict)
open PhilipponEtalePullbackComposition (restrictGlobalSections_app_eq)

namespace PhilipponEtaleLimitSectionsCohomology

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (F : System (directImages D))

/-- In degree zero the canonical cohomology restriction agrees with
the map on global sections. -/
theorem sectionsEquiv_stageRestriction (i : I) (x : (F.obj i).H 0) :
    sectionsEquiv (limitSheaf c hc F) (stageRestriction c hc F i 0 x) =
      stageSections c hc F i (sectionsEquiv (F.obj i) x) := by
  let f : c.pt ⟶ D.obj i := c.π.app i
  let M := F.obj i
  let N := limitSheaf c hc F
  let m : (pullbackSheaves f).obj M ⟶ N := restrictCoefficients c hc F i
  let e := pullbackAdjunction f
  have hm : e.unit.app M ≫ (pushforward f).map m = fromStage c hc F i :=
    (e.homEquiv_unit M N m).symm.trans ((e.homEquiv M N).apply_symm_apply _)
  change sectionsEquiv N (Sheaf.H.map m 0 (restrict f M 0 x)) = _
  rw [← Sheaf.H.equiv₀_naturality, sectionsEquiv_restrict f M x, restrictGlobalSections_app_eq]
  have h := (globalSectionsIso f).hom.naturality m
  change ((globalSections (D.obj i)).map ((pullbackAdjunction f).unit.app M) ≫
      (globalSectionsIso f).hom.app ((pullbackSheaves f).obj M) ≫
      (globalSections c.pt).map m) (sectionsEquiv M x) = _
  rw [← h, Functor.comp_map, ← Functor.map_comp_assoc, hm]
  rfl

end PhilipponEtaleLimitSectionsCohomology

end

end


