-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_of_affine_limit
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T05:26:24.585557+00:00
-- url     : https://prove2.me/submissions/26957367-1106-48c5-afd5-c11e007b9a56

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitResolution

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (StageChart toLimit)
open PhilipponEtaleSystemPresheaf (presheaf)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleConeSystem (extended restrict projectionMap)
open PhilipponEtalePullbackSystem (toBase pullbackSystem)
open PhilipponEtaleLimitTestMaps (stageMap)


namespace PhilipponEtaleLimitBaseMaps

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} {X : Scheme.{u}}

/-- A compatible map from the entire inverse cone to a fixed scheme. -/
structure OverBase (c : Cone D) (X : Scheme.{u}) where
  stage (i : I) : D.obj i ⟶ X
  point : c.pt ⟶ X
  stage_w {i j : I} (a : i ⟶ j) : D.map a ≫ stage j = stage i
  point_w (i : I) : c.π.app i ≫ stage i = point

variable (B : OverBase c X)

private def coneMap : ∀ j : WithInitial I, (extended c).obj j ⟶ X
  | WithInitial.of i => B.stage i
  | WithInitial.star => B.point

private theorem coneMap_w (i j : WithInitial I) (a : i ⟶ j) :
    (extended c).map a ≫ coneMap B j = coneMap B i := by
  cases i <;> cases j
  · exact B.stage_w (WithInitial.down a)
  · exact (WithInitial.false_of_to_star a).elim
  · exact B.point_w _
  · exact Category.id_comp _

private abbrev toBaseDiagram := PhilipponEtalePullbackSystem.extended (extended c) (coneMap B) (coneMap_w B)

/-- Pull a sheaf on the base to every object of the inverse cone. -/
def coneSystem (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    System (directImages (extended c)) :=
  pullbackSystem (extended c) (coneMap B) (coneMap_w B) F

private abbrev atStageBase {i j : I} (a : i ⟶ j) :
    pushforward (B.stage i) ≅ (directImages D).functor a ⋙ pushforward (B.stage j) :=
  toBase (extended c) (coneMap B) (coneMap_w B) (WithInitial.incl.map a)

private abbrev atPointBase (i : I) :
    pushforward B.point ≅ pushforward (c.π.app i) ⋙ pushforward (B.stage i) :=
  toBase (extended c) (coneMap B) (coneMap_w B) (WithInitial.homTo i)

private abbrev imageComposition {i j : I} (a : i ⟶ j) :
    pushforward (c.π.app j) ≅ pushforward (c.π.app i) ⋙ (directImages D).functor a :=
  (directImages (extended c)).composition (WithInitial.homTo i) (WithInitial.incl.map a)

private theorem base_assoc {i j : I} (a : i ⟶ j)
    (H : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) :
    (atPointBase B j).hom.app H ≫ (pushforward (B.stage j)).map ((imageComposition a).hom.app H) =
      (atPointBase B i).hom.app H ≫ (atStageBase B a).hom.app ((pushforward (c.π.app i)).obj H) := by
  let R := directImages (toBaseDiagram B)
  let k := WithTerminal.incl.map (WithInitial.homTo i)
  let a' := WithTerminal.incl.map (WithInitial.incl.map a)
  let q := WithTerminal.homFrom (WithInitial.of j)
  have h := R.comp_assoc k a' q H
  simp only [eqToHom_refl, Category.id_comp] at h
  exact h

variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
  (H : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})
  (η : presheaf (restrict c (coneSystem B F)) ⟶ (toLimit c).op ⋙ H.obj)

/-- Compare a stage map with the adjoint of the desired map from the
inverse image on the limit. -/
def compareAt (i : I) : F ⟶ (pushforward B.point).obj H :=
  (pullbackAdjunction (B.stage i)).unit.app F ≫
    (pushforward (B.stage i)).map (stageMap c _ H η i) ≫ (atPointBase B i).inv.app H

/-- The adjoint of a natural map is independent of transitions between
the stages. -/
theorem compareAt_eq {i j : I} (a : i ⟶ j) :
    compareAt B F H η j = compareAt B F H η i := by
  let e₁ := atPointBase B j
  let e₂ := atPointBase B i
  let e₃ := atStageBase B a
  let r := imageComposition (c := c) a
  let L₁ := pushforward (B.stage j)
  let L₂ := pushforward (B.stage i)
  let A := (directImages D).functor a
  let α := fun k => stageMap c (restrict c (coneSystem B F)) H η k
  let u := fun k => (pullbackAdjunction (B.stage k)).unit.app F
  let z := e₁.hom.app H ≫ L₁.map (r.hom.app H)
  have hz : z = e₂.hom.app H ≫ e₃.hom.app ((pushforward (c.π.app i)).obj H) :=
    base_assoc B a H
  let : IsIso z := inferInstance
  apply (cancel_mono z).mp
  have h₁ : compareAt B F H η j ≫ z = u j ≫ L₁.map (α j ≫ r.hom.app H) := by
    change (u j ≫ L₁.map (α j) ≫ e₁.inv.app H) ≫ e₁.hom.app H ≫ L₁.map (r.hom.app H) = _
    rw [L₁.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have h₂ : compareAt B F H η i ≫ z =
      u i ≫ L₂.map (α i) ≫ e₃.hom.app ((pushforward (c.π.app i)).obj H) := by
    rw [hz]
    change (u i ≫ L₂.map (α i) ≫ e₂.inv.app H) ≫
      e₂.hom.app H ≫ e₃.hom.app ((pushforward (c.π.app i)).obj H) = _
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  let m := (restrict c (coneSystem B F)).map a
  have hn : α j ≫ r.hom.app H = m ≫ A.map (α i) :=
    PhilipponEtaleLimitTestMaps.naturality c _ H η a
  have hu : u j ≫ L₁.map m = u i ≫ e₃.hom.app ((restrict c (coneSystem B F)).obj i) :=
    PhilipponEtalePullbackSystem.system_unit (extended c) (coneMap B) (coneMap_w B) F (WithInitial.incl.map a)
  have hnat : L₂.map (α i) ≫ e₃.hom.app ((pushforward (c.π.app i)).obj H) =
      e₃.hom.app ((restrict c (coneSystem B F)).obj i) ≫ L₁.map (A.map (α i)) :=
    e₃.hom.naturality (α i)
  rw [h₁, h₂, hn, L₁.map_comp, ← Category.assoc, hu, Category.assoc, hnat]

/-- Restriction to the stages of a map from the inverse image on the limit. -/
def project (q : (pullbackSheaves B.point).obj F ⟶ H) :
    presheaf (restrict c (coneSystem B F)) ⟶ (toLimit c).op ⋙ H.obj :=
  projectionMap c (coneSystem B F) ≫ Functor.whiskerLeft (toLimit c).op q.hom

private theorem stage_project (q : (pullbackSheaves B.point).obj F ⟶ H) (i : I) :
    stageMap c _ H (project B F H q) i =
      (coneSystem B F).map (WithInitial.homTo i) ≫ (pushforward (c.π.app i)).map q := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change (projectionMap c (coneSystem B F)).app (op (⟨i, V.unop⟩ : StageChart D)) ≫
      q.hom.app _ = _
  rw [PhilipponEtaleConeSystem.projectionMap_app]
  rfl

private theorem compare_project (q : (pullbackSheaves B.point).obj F ⟶ H) (i : I) :
    compareAt B F H (project B F H q) i = (pullbackAdjunction B.point).homEquiv F H q := by
  let e := atPointBase B i
  let A := (pullbackSheaves B.point).obj F
  let L := pushforward (B.stage i)
  let P := pushforward (c.π.app i)
  let u₀ := (pullbackAdjunction B.point).unit.app F
  let u := (pullbackAdjunction (B.stage i)).unit.app F
  let m := (coneSystem B F).map (WithInitial.homTo i)
  have hu : u ≫ L.map m = u₀ ≫ e.hom.app A :=
    PhilipponEtalePullbackSystem.system_unit (extended c) (coneMap B) (coneMap_w B) F (WithInitial.homTo i)
  have hn : e.hom.app A ≫ L.map (P.map q) = (pushforward B.point).map q ≫ e.hom.app H :=
    (e.hom.naturality q).symm
  have he : e.hom.app A ≫ L.map (P.map q) ≫ e.inv.app H = (pushforward B.point).map q := by
    rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  unfold compareAt
  rw [stage_project]
  change u ≫ L.map (m ≫ P.map q) ≫ e.inv.app H = _
  rw [L.map_comp, ← Category.assoc, ← Category.assoc, hu]
  simp only [Category.assoc, he, Adjunction.homEquiv_unit]
  rfl

private theorem stageMap_eq_of_compare {ζ : presheaf (restrict c (coneSystem B F)) ⟶ (toLimit c).op ⋙ H.obj}
    (i : I) (h : compareAt B F H η i = compareAt B F H ζ i) :
    stageMap c _ H η i = stageMap c _ H ζ i := by
  apply ((pullbackAdjunction (B.stage i)).homEquiv F ((pushforward (c.π.app i)).obj H)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply (cancel_mono ((atPointBase B i).inv.app H)).mp
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

/-- Maps from the inverse image on the cone point are exactly the natural
maps from the inverse images at the stages. -/
theorem project_bijective [IsCofiltered I] : Function.Bijective (project B F H) := by
  let i := (IsCofiltered.nonempty (C := I)).some
  let adj := pullbackAdjunction B.point
  constructor
  · intro q q' h
    apply (adj.homEquiv F H).injective
    exact (compare_project B F H q i).symm.trans <|
      (congrArg (fun ζ => compareAt B F H ζ i) h).trans (compare_project B F H q' i)
  · intro ζ
    let q := (adj.homEquiv F H).symm (compareAt B F H ζ i)
    refine ⟨q, PhilipponEtaleLimitTestMaps.ext c _ H _ fun j => ?_⟩
    apply stageMap_eq_of_compare B F H _ j
    have h := compare_project B F H q j
    change compareAt B F H (project B F H q) j = (adj.homEquiv F H) q at h
    rw [h, Equiv.apply_symm_apply]
    exact (compareAt_eq B F H ζ (IsCofiltered.minToLeft i j)).trans
      (compareAt_eq B F H ζ (IsCofiltered.minToRight i j)).symm

end PhilipponEtaleLimitBaseMaps

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleTotalStageSite (toLimit)
open PhilipponEtaleSystemPresheaf (presheaf)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleConeSystem (restrict projectionMap)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affineColimit affinePresheaf)
open PhilipponEtaleLimitBaseMaps (OverBase coneSystem project project_bijective)
open PhilipponEtaleLimitSheaf (limitSheaf topology restriction restrictionIso)


namespace PhilipponEtaleLimitFixedCoefficient

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] {c : Cone D} (hc : IsLimit c) {X : Scheme.{u}}
  (B : OverBase c X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

private abbrev S := restrict c (coneSystem B F)
private abbrev G := (affineCharts c.pt).ι
private abbrev A := (pullbackSheaves B.point).obj F

private def cocone (U : (affineCharts c.pt).FullSubcategoryᵒᵖ) :=
  affineColimit c hc (S B F) U.unop

private abbrev affineLimit : Sheaf (topology c) AddCommGrpCat.{u} :=
  ⟨affinePresheaf c hc (S B F), PhilipponEtaleLimitSheaf.isSheaf c hc (S B F)⟩

private def comparison : limitSheaf c hc (S B F) ⟶ A B F :=
  (restriction c).preimage ((restrictionIso c hc (S B F)).hom ≫
    ⟨PhilipponRestrictedKan.descend (toLimit c).op (presheaf (S B F)) G.op
      (cocone hc B F) (projectionMap c (coneSystem B F))⟩)

private def homEquiv (H : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) :
    (limitSheaf c hc (S B F) ⟶ H) ≃ (presheaf (S B F) ⟶ (toLimit c).op ⋙ H.obj) :=
  (restriction c).asEquivalence.fullyFaithfulFunctor.homEquiv.trans
    (((restrictionIso c hc (S B F)).homCongr (Iso.refl _)).trans
      (((fullyFaithfulSheafToPresheaf (topology c) AddCommGrpCat.{u}).homEquiv
        (X := affineLimit hc B F) (Y := (restriction c).obj H)).trans
        (PhilipponRestrictedKan.homEquiv (toLimit c).op (presheaf (S B F)) G.op (cocone hc B F)
          (PhilipponDenseSheafKan.isPointwiseRightKanExtension G c.pt.smallEtaleTopology H))))

private theorem comparison_comp (H : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) (q : A B F ⟶ H) :
    comparison hc B F ≫ q = (homEquiv hc B F H).symm (project B F H q) := by
  apply (restriction c).map_injective
  rw [(restriction c).map_comp]
  let d : affineLimit hc B F ⟶ (restriction c).obj H :=
    ⟨PhilipponRestrictedKan.descend (toLimit c).op (presheaf (S B F)) G.op (cocone hc B F)
      (project B F H q)⟩
  have hd : (restriction c).map ((homEquiv hc B F H).symm (project B F H q)) =
      (restrictionIso c hc (S B F)).hom ≫ d := by
    change (restriction c).map ((restriction c).asEquivalence.fullyFaithfulFunctor.preimage
      (((restrictionIso c hc (S B F)).hom ≫ d) ≫ 𝟙 _)) = _
    rw [Functor.FullyFaithful.map_preimage, Category.comp_id]
  rw [hd]
  change (restriction c).map (comparison hc B F) ≫ (restriction c).map q =
    (restrictionIso c hc (S B F)).hom ≫ d
  rw [comparison, (restriction c).map_preimage, Category.assoc]
  congr 1
  apply Sheaf.hom_ext
  exact (PhilipponRestrictedKan.descend_postcompose (toLimit c).op (presheaf (S B F)) G.op
    (cocone hc B F) q.hom (projectionMap c (coneSystem B F))).symm

/-- For coefficients pulled back from a fixed base, the limit sheaf is
the inverse image of the original coefficient on the limit scheme. -/
def limitIso : limitSheaf c hc (S B F) ≅ (pullbackSheaves B.point).obj F := by
  let q := comparison hc B F
  have hq : IsIso q := by
    apply isIso_of_coyoneda_map_bijective q
    intro H
    have h : (fun f : A B F ⟶ H => q ≫ f) =
        (homEquiv hc B F H).symm ∘ project B F H :=
      funext (comparison_comp hc B F H)
    rw [h]
    exact (homEquiv hc B F H).symm.bijective.comp (project_bijective B F H)
  exact asIso q

end PhilipponEtaleLimitFixedCoefficient

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleConeSystem (restrict)
open PhilipponEtaleLimitBaseMaps (OverBase coneSystem)
open PhilipponEtaleLimitFixedCoefficient (limitIso)


namespace PhilipponEtaleLimitVanishing

universe u

/-- If the pulled-back coefficients have zero cohomology at every affine
stage, the corresponding cohomology vanishes at the inverse limit. -/
theorem subsingleton_of_affine_limit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (g : D ⟶ (Functor.const I).obj X) (f : c.pt ⟶ X)
    (hf : ∀ i, c.π.app i ≫ g.app i = f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    (h : ∀ i, Subsingleton (((pullbackSheaves (g.app i)).obj F).H q)) :
    Subsingleton (((pullbackSheaves f).obj F).H q) := by
  let B : OverBase c X := ⟨g.app, f, fun a => by
    have h₀ := g.naturality a
    change _ = g.app _ ≫ 𝟙 X at h₀
    exact h₀.trans (Category.comp_id _), hf⟩
  let S := restrict c (coneSystem B F)
  let R := Sheaf.functorH c.pt.smallEtaleTopology q
  let : Subsingleton (R.obj (PhilipponEtaleLimitSheaf.limitSheaf c hc S)) :=
    PhilipponEtaleLimitCohomology.subsingleton_H_all c hc S q h
  let e := R.mapIso (limitIso hc B F)
  exact e.addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end PhilipponEtaleLimitVanishing

end

section

open PhilipponEtaleSmallSite (pullbackSheaves)

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (g : D ⟶ (Functor.const I).obj X) (f : c.pt ⟶ X)
    (hf : ∀ i, c.π.app i ≫ g.app i = f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    (∀ i, Subsingleton (((pullbackSheaves (g.app i)).obj F).H q)) →
      Subsingleton (((pullbackSheaves f).obj F).H q) := by
  exact PhilipponEtaleLimitVanishing.subsingleton_of_affine_limit
    D c hc g f hf F q

end

end
