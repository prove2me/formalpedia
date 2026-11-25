-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitCoefficientMaps
-- name    : AlgebraicGeometry_EtaleAffineLimitCoefficientMaps
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T05:42:44.607387+00:00
-- url     : https://prove2.me/theorems/9050054b-6bf6-4ec7-b73b-f03d12aa1d6a
-- title:
--   Canonical maps of étale coefficients from an affine stage to the limit
-- statement:
--   The natural maps into the limit sheaf are functorial in the coefficient system. For a system of pullbacks from a fixed scheme these maps agree with the projection maps for the inverse image on the limit.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitFunctor

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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponCompatibleSystemCokernel (Hom)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (StageChart toLimit)
open PhilipponEtaleSystemPresheaf (presheaf presheafMap)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affineColimit)
open PhilipponEtaleLimitSheaf (limitSheaf restrictionIso restriction)
open PhilipponEtaleLimitFunctor (affineFunctor limitFunctor ι_affineMap)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleLimitTestMaps (stageMap)


namespace PhilipponEtaleLimitCanonical

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (F : System (directImages D))

private abbrev J := c.pt.smallEtaleTopology
private abbrev G := (affineCharts c.pt).ι
private abbrev L := (toLimit c).op

private def d (U : (affineCharts c.pt).FullSubcategoryᵒᵖ) :=
  affineColimit c hc F U.unop

/-- The stage presheaf has a canonical map into the restrictions of the
limit sheaf. -/
def naturalMap : presheaf F ⟶ (L c) ⋙ (limitSheaf c hc F).obj :=
  PhilipponRestrictedKan.ascend (L c) (presheaf F) (G c).op (d c hc F)
    (PhilipponDenseSheafKan.isPointwiseRightKanExtension (G c) (J c) (limitSheaf c hc F))
    (restrictionIso c hc F).inv.hom

/-- On affine charts the canonical map is the corresponding colimit
injection followed by the restriction comparison. -/
@[reassoc]
theorem naturalMap_affine (U : (affineCharts c.pt).FullSubcategory)
    (j : CostructuredArrow (L c) (op U.obj)) :
    (naturalMap c hc F).app j.left ≫ (limitSheaf c hc F).obj.map j.hom =
      (affineColimit c hc F U).cocone.ι.app j ≫ (restrictionIso c hc F).inv.hom.app (op U) := by
  let b : StructuredArrow ((L c).obj j.left) (G c).op := StructuredArrow.mk j.hom
  have h := PhilipponRestrictedKan.ascend_map (L c) (presheaf F) (G c).op (d c hc F)
    (PhilipponDenseSheafKan.isPointwiseRightKanExtension (G c) (J c) (limitSheaf c hc F))
    (restrictionIso c hc F).inv.hom j.left b
  let P (k : CostructuredArrow (L c) (op U.obj)) :=
    (naturalMap c hc F).app k.left ≫ (limitSheaf c hc F).obj.map k.hom =
      (affineColimit c hc F U).cocone.ι.app k ≫ (restrictionIso c hc F).inv.hom.app (op U)
  exact (congrArg P (CostructuredArrow.eq_mk j)).mpr h

/-- The canonical coefficient map from a stage into the direct image of
the limit sheaf. -/
def fromStage (i : I) :
    F.obj i ⟶ (pushforward (c.π.app i)).obj (limitSheaf c hc F) :=
  stageMap c F (limitSheaf c hc F) (naturalMap c hc F) i

/-- The canonical comparison commutes with maps of coefficient systems. -/
theorem naturalMap_naturality {H : System (directImages D)} (η : F ⟶ H) :
    presheafMap η ≫ naturalMap c hc H =
      naturalMap c hc F ≫ Functor.whiskerLeft (L c) ((limitFunctor c hc).map η).hom := by
  let Q := limitSheaf c hc H
  let h := PhilipponDenseSheafKan.isPointwiseRightKanExtension (G c) (J c) Q
  let B := PhilipponRestrictedKan.homEquiv (L c) (presheaf F) (G c).op (d c hc F) h
  let q := (limitFunctor c hc).map η
  apply B.symm.injective
  apply NatTrans.ext
  funext T
  apply (affineColimit c hc F T.unop).isColimit.hom_ext
  intro j
  change (d c hc F T).cocone.ι.app j ≫
      (PhilipponRestrictedKan.descend (L c) (presheaf F) (G c).op (d c hc F)
        (presheafMap η ≫ naturalMap c hc H)).app T =
    (d c hc F T).cocone.ι.app j ≫
      (PhilipponRestrictedKan.descend (L c) (presheaf F) (G c).op (d c hc F)
        (naturalMap c hc F ≫ Functor.whiskerLeft (L c) q.hom)).app T
  have hl := PhilipponRestrictedKan.ι_descend (L c) (presheaf F) (G c).op (d c hc F)
    (presheafMap η ≫ naturalMap c hc H) T j
  have hr := PhilipponRestrictedKan.ι_descend (L c) (presheaf F) (G c).op (d c hc F)
    (naturalMap c hc F ≫ Functor.whiskerLeft (L c) q.hom) T j
  refine hl.trans (Eq.trans ?_ hr.symm)
  change ((presheafMap η).app j.left ≫ (naturalMap c hc H).app j.left) ≫ Q.obj.map j.hom =
    ((naturalMap c hc F).app j.left ≫ q.hom.app ((L c).obj j.left)) ≫ Q.obj.map j.hom
  have hw : q.hom.app ((L c).obj j.left) ≫ Q.obj.map j.hom =
      (limitSheaf c hc F).obj.map j.hom ≫ q.hom.app (op T.unop.obj) :=
    (q.hom.naturality j.hom).symm
  rw [Category.assoc, naturalMap_affine, Category.assoc, hw, ← Category.assoc,
    naturalMap_affine_assoc, ← Category.assoc, ← ι_affineMap]
  have he := (restriction c).asEquivalence.counitIso.inv.naturality ((affineFunctor c hc).map η)
  have he' := congrArg (fun m => m.hom.app T) he
  change (PhilipponEtaleLimitFunctor.affineMap c hc η).app T ≫
      (restrictionIso c hc H).inv.hom.app T =
    (restrictionIso c hc F).inv.hom.app T ≫ q.hom.app (op T.unop.obj) at he'
  simp only [Category.assoc, he']

/-- Canonical coefficient maps commute with taking a map of systems. -/
theorem fromStage_naturality {H : System (directImages D)} (η : F ⟶ H) (i : I) :
    η.app i ≫ fromStage c hc H i =
      fromStage c hc F i ≫ (pushforward (c.π.app i)).map ((limitFunctor c hc).map η) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact congrArg (fun α => α.app (op (⟨i, V.unop⟩ : StageChart D)))
    (naturalMap_naturality c hc F η)

/-- The coefficient restriction after pulling back from a stage to the limit. -/
def restrictCoefficients (i : I) :
    (pullbackSheaves (c.π.app i)).obj (F.obj i) ⟶ limitSheaf c hc F :=
  ((pullbackAdjunction (c.π.app i)).homEquiv _ _).symm (fromStage c hc F i)

/-- Pullback coefficient restrictions are natural in the system. -/
theorem restrictCoefficients_naturality {H : System (directImages D)} (η : F ⟶ H) (i : I) :
    (pullbackSheaves (c.π.app i)).map (η.app i) ≫ restrictCoefficients c hc H i =
      restrictCoefficients c hc F i ≫ (limitFunctor c hc).map η := by
  let a := pullbackAdjunction (c.π.app i)
  change (pullbackSheaves (c.π.app i)).map (η.app i) ≫
      (a.homEquiv _ _).symm (fromStage c hc H i) =
    (a.homEquiv _ _).symm (fromStage c hc F i) ≫ (limitFunctor c hc).map η
  rw [← a.homEquiv_naturality_left_symm, fromStage_naturality, a.homEquiv_naturality_right_symm]

end PhilipponEtaleLimitCanonical

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleConeSystem (restrict projectionMap projectionMap_app)
open PhilipponEtaleLimitBaseMaps (OverBase coneSystem)
open PhilipponEtaleLimitFixedCoefficient (limitIso)
open PhilipponEtaleLimitCanonical (naturalMap fromStage)
open PhilipponEtaleLimitSheaf (limitSheaf restriction restrictionIso)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affineColimit)
open PhilipponEtaleTotalStageSite (StageChart toLimit)
open PhilipponEtaleSystemPresheaf (presheaf)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleClosedPushforward (pushforward)


namespace PhilipponEtaleLimitFixedComparison

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] {c : Cone D} (hc : IsLimit c) {X : Scheme.{u}}
  (B : OverBase c X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

private abbrev S := restrict c (coneSystem B F)
private abbrev L := (toLimit c).op
private abbrev G := (affineCharts c.pt).ι
private abbrev A := (pullbackSheaves B.point).obj F
private def d (U : (affineCharts c.pt).FullSubcategoryᵒᵖ) :=
  affineColimit c hc (S B F) U.unop

/-- Under the identification with the inverse image on the limit, the
canonical family of maps is the projection family of the cone. -/
theorem naturalMap_comp :
    naturalMap c hc (S B F) ≫ Functor.whiskerLeft (L (c := c)) (limitIso hc B F).hom.hom =
      projectionMap c (coneSystem B F) := by
  let η := projectionMap c (coneSystem B F)
  let q := (limitIso hc B F).hom
  let d' := d hc B F
  let e (P : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) :=
    PhilipponRestrictedKan.homEquiv (L (c := c)) (presheaf (S B F)) G.op d'
      (PhilipponDenseSheafKan.isPointwiseRightKanExtension G c.pt.smallEtaleTopology P)
  have h₁ : (e (limitSheaf c hc (S B F))).symm (naturalMap c hc (S B F)) =
      (restrictionIso c hc (S B F)).inv.hom :=
    (e (limitSheaf c hc (S B F))).symm_apply_apply _
  let θ : ⟨PhilipponEtaleLimitAffinePresheaf.affinePresheaf c hc (S B F),
      PhilipponEtaleLimitSheaf.isSheaf c hc (S B F)⟩ ⟶ (restriction c).obj (A B F) :=
    ⟨(e (A B F)).symm η⟩
  have h₂ : (restriction c).map q = (restrictionIso c hc (S B F)).hom ≫ θ := by
    change (restriction c).map ((restriction c).preimage _) = _
    rw [(restriction c).map_preimage]
    rfl
  apply (e (A B F)).symm.injective
  change PhilipponRestrictedKan.descend (L (c := c)) (presheaf (S B F)) G.op d'
    (naturalMap c hc (S B F) ≫ Functor.whiskerLeft (L (c := c)) q.hom) = _
  rw [PhilipponRestrictedKan.descend_postcompose]
  change (e (limitSheaf c hc (S B F))).symm (naturalMap c hc (S B F)) ≫
    ((restriction c).map q).hom = _
  rw [h₁, h₂]
  exact congrArg (fun m => m.hom) ((restrictionIso c hc (S B F)).inv_hom_id_assoc θ)

/-- At a stage the adjoint canonical comparison is the map supplied by
the fixed-base coefficient system on the cone. -/
theorem fromStage_comp (i : I) :
    fromStage c hc (S B F) i ≫ (pushforward (c.π.app i)).map (limitIso hc B F).hom =
      (coneSystem B F).map (WithInitial.homTo i) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let T : StageChart D := ⟨i, V.unop⟩
  exact (congrArg (fun α => α.app (op T)) (naturalMap_comp hc B F)).trans
    (projectionMap_app c (coneSystem B F) T)

end PhilipponEtaleLimitFixedComparison

end

end


