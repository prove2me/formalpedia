-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleConstantDiagramSheafColimit
-- name    : AlgebraicGeometry_EtaleConstantDiagramSheafColimit
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T07:52:39.175565+00:00
-- url     : https://prove2.me/theorems/46475eaf-0a21-5778-a651-a25ce3c86ab1
-- title:
--   An étale limit sheaf over a constant scheme is a filtered sheaf colimit
-- statement:
--   For a filtered diagram of sheaves on a fixed affine scheme, the étale limit sheaf has the universal property of the filtered colimit, with the ordinary stage injections.
-- source:
--   Stacks Project, Lemmas 59.51.4, 59.73.2 and 59.74.4, https://stacks.math.columbia.edu/tag/03Q5.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitUniversalProperty
import Definitions.Def_AlgebraicGeometry_EtalePullbackSystemComparisons

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 650000

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageSystem (directImages)


namespace PhilipponEtaleConstantDiagramSystem

universe u

variable {I : Type u} [Category.{u} I] (X : Scheme.{u})

private abbrev Ab := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev D := (Functor.const I).obj X
private abbrev P := pushforward (𝟙 X)

/-- Direct image along any arrow of the constant scheme diagram
identifies with the identity functor. -/
def unit (i : I) : P X ≅ 𝟭 (Ab X) :=
  (directImages (D (I := I) X)).identity i

theorem unit_eq (i j : I) : unit X i = unit X j := rfl

theorem comparison_hom {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (F : Ab X) :
    ((directImages (D (I := I) X)).composition a b).hom.app F =
      (unit X k).inv.app ((P X).obj F) := by
  let R := directImages (D (I := I) X)
  let e : P X ≅ P X ⋙ P X := R.composition a b
  let e' : P X ≅ P X ⋙ P X := R.composition (𝟙 k) (𝟙 k)
  have h : e = e' :=
    (PhilipponEtaleDirectImageComposition.composition_eq (D (I := I) X) a b).trans
      (PhilipponEtaleDirectImageComposition.composition_eq (D (I := I) X) (𝟙 k) (𝟙 k)).symm
  change e.hom.app F = _
  rw [h]
  apply (cancel_mono ((unit X k).hom.app ((P X).obj F))).mp
  have hu : e'.hom.app F ≫ (unit X k).hom.app ((P X).obj F) = 𝟙 _ :=
    (R.comp_identity (𝟙 k) F).trans (eqToHom_refl _ _)
  exact hu.trans (Iso.inv_hom_id_app (unit X k) ((P X).obj F)).symm

/-- A filtered diagram of sheaves on a fixed scheme is a compatible
system on the constant cofiltered scheme diagram. -/
def ofSheafDiagram (F : Iᵒᵖ ⥤ Ab X) : System (directImages (D (I := I) X)) where
  obj i := F.obj (op i)
  map {i j} a := F.map a.op ≫ (unit X i).inv.app (F.obj (op i))
  map_identity i := by
    change (F.map (𝟙 i).op ≫ (unit X i).inv.app (F.obj (op i))) ≫ (unit X i).hom.app _ = _
    rw [op_id, F.map_id, Category.id_comp, Iso.inv_hom_id_app]
    rfl
  map_composition {i j k} a b := by
    let V := F.obj (op i)
    let W := F.obj (op j)
    let e := unit X j
    let h := (unit X i).inv.app V
    have hc : ((directImages (D (I := I) X)).composition a b).hom.app V = e.inv.app ((P X).obj V) :=
      (comparison_hom X a b V).trans (congrArg (fun z => z.inv.app ((P X).obj V)) (unit_eq X k j))
    have hn : e.inv.app W ≫ (P X).map (F.map a.op ≫ h) =
      (F.map a.op ≫ h) ≫ e.inv.app ((P X).obj V) := (e.inv.naturality _).symm
    change (F.map (a ≫ b).op ≫ h) ≫ ((directImages (D (I := I) X)).composition a b).hom.app V =
      (F.map b.op ≫ e.inv.app W) ≫ (P X).map (F.map a.op ≫ h)
    simp only [hc, Category.assoc, hn, op_comp, F.map_comp]

end PhilipponEtaleConstantDiagramSystem

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleConeSystem (extended)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleDirectImageComposition (composition_eq)
open PhilipponEtaleConstantDiagramSystem (ofSheafDiagram unit unit_eq comparison_hom)
open PhilipponEtaleLimitCanonical (naturalMap fromStage restrictCoefficients)
open PhilipponEtaleLimitSheaf (limitSheaf)
open PhilipponEtaleLimitUniversalProperty (desc desc_fac)


namespace PhilipponEtaleConstantDiagramColimit

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (X : Scheme.{u}) [IsAffine X]

private abbrev Ab := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev D := (Functor.const I).obj X
private abbrev P := pushforward (𝟙 X)

local instance : ∀ i, IsAffine (((Functor.const I).obj X).obj i) :=
  fun _ => inferInstanceAs (IsAffine X)

/-- For an affine scheme the constant diagram has the scheme itself
as its inverse limit. -/
def coneIsLimit : IsLimit (constCone I X) := by
  let : IsConnected I := IsCofiltered.isConnected I
  exact isLimitConstCone I X

private theorem coneComparison {i j : I} (a : i ⟶ j) (H : Ab X) :
    ((directImages (extended (constCone I X))).composition
      (WithInitial.homTo i) (WithInitial.incl.map a)).hom.app H =
      (unit X i).inv.app ((P X).obj H) := by
  let e : P X ≅ P X ⋙ P X := (directImages (extended (constCone I X))).composition
    (WithInitial.homTo i) (WithInitial.incl.map a)
  let e' : P X ≅ P X ⋙ P X := (directImages (D (I := I) X)).composition a (𝟙 j)
  have h : e = e' :=
    (composition_eq (extended (constCone I X)) (WithInitial.homTo i) (WithInitial.incl.map a)).trans
      (composition_eq (D (I := I) X) a (𝟙 j)).symm
  change e.hom.app H = _
  rw [h]
  exact (comparison_hom X a (𝟙 j) H).trans
    (congrArg (fun z => z.inv.app ((P X).obj H)) (unit_eq X j i))

variable (F : Iᵒᵖ ⥤ Ab X)

/-- The limit sheaf built from the compatible system on the constant
scheme diagram. -/
abbrev limitCoefficients : Ab X := limitSheaf (constCone I X) (coneIsLimit X) (ofSheafDiagram X F)

private def stage (i : I) : F.obj (op i) ⟶ (P X).obj (limitCoefficients X F) :=
  fromStage (constCone I X) (coneIsLimit X) (ofSheafDiagram X F) i

private theorem stage_transition {i j : I} (a : i ⟶ j) :
    F.map a.op ≫ stage X F i = stage X F j := by
  let c := constCone I X
  let h := coneIsLimit (I := I) X
  let S := ofSheafDiagram X F
  let H := limitCoefficients X F
  let e := unit X i
  let p := (P X).obj H
  have w := PhilipponEtaleLimitTestMaps.naturality c S H (naturalMap c h S) a
  change stage X F j ≫ ((directImages (extended c)).composition
    (WithInitial.homTo i) (WithInitial.incl.map a)).hom.app H =
    (F.map a.op ≫ e.inv.app (F.obj (op i))) ≫ (P X).map (stage X F i) at w
  have he : ((directImages (extended c)).composition
    (WithInitial.homTo i) (WithInitial.incl.map a)).hom.app H = e.inv.app p :=
    coneComparison X a H
  have hn : e.inv.app (F.obj (op i)) ≫ (P X).map (stage X F i) =
      stage X F i ≫ e.inv.app p := (e.inv.naturality (stage X F i)).symm
  rw [he, Category.assoc, hn, ← Category.assoc] at w
  exact ((cancel_mono (e.inv.app p)).mp w).symm

/-- The compatible map of coefficients on a constant scheme diagram
gives an ordinary cocone of sheaves. -/
def cocone : Cocone F where
  pt := limitCoefficients X F
  ι :=
    { app := fun i => stage X F i.unop ≫ (unit X i.unop).hom.app (limitCoefficients X F)
      naturality := by
        intro i j a
        have h : F.map a ≫ stage X F j.unop = stage X F i.unop :=
          stage_transition X F a.unop
        change F.map a ≫ stage X F j.unop ≫ (unit X j.unop).hom.app _ =
          (stage X F i.unop ≫ (unit X i.unop).hom.app _) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, ← unit_eq X j.unop i.unop, h] }

private def stageTarget (d : Cocone F) (i : I) : F.obj (op i) ⟶ (P X).obj d.pt :=
  d.ι.app (op i) ≫ (unit X i).inv.app d.pt

private theorem stageTarget_compatible (d : Cocone F) {i j : I} (a : i ⟶ j) :
    stageTarget X F d j ≫
      ((directImages (extended (constCone I X))).composition
        (WithInitial.homTo i) (WithInitial.incl.map a)).hom.app d.pt =
      (ofSheafDiagram X F).map a ≫ (P X).map (stageTarget X F d i) := by
  let e := unit X i
  have h₀ : ((directImages (extended (constCone I X))).composition
      (WithInitial.homTo i) (WithInitial.incl.map a)).hom.app d.pt =
      e.inv.app ((P X).obj d.pt) := coneComparison X a d.pt
  have h₁ : e.inv.app (F.obj (op i)) ≫ (P X).map (stageTarget X F d i) =
      stageTarget X F d i ≫ e.inv.app ((P X).obj d.pt) :=
    (e.inv.naturality (stageTarget X F d i)).symm
  have h₂ : F.map a.op ≫ stageTarget X F d i = stageTarget X F d j := by
    change F.map a.op ≫ d.ι.app (op i) ≫ (unit X i).inv.app d.pt =
      d.ι.app (op j) ≫ (unit X j).inv.app d.pt
    rw [← Category.assoc, d.w, unit_eq X j i]
  change stageTarget X F d j ≫ _ = (F.map a.op ≫ e.inv.app (F.obj (op i))) ≫
    (P X).map (stageTarget X F d i)
  rw [h₀, Category.assoc, h₁, ← Category.assoc, h₂]

private def descend (d : Cocone F) : limitCoefficients X F ⟶ d.pt :=
  desc (constCone I X) (coneIsLimit X) (ofSheafDiagram X F) d.pt
    (stageTarget X F d) (stageTarget_compatible X F d)

private theorem descend_fac (d : Cocone F) (i : Iᵒᵖ) :
    (cocone X F).ι.app i ≫ descend X F d = d.ι.app i := by
  let e := unit X i.unop
  let m := descend X F d
  have hn : (P X).map m ≫ e.hom.app d.pt =
      e.hom.app (limitCoefficients X F) ≫ m := (e.hom.naturality m)
  have hm : stage X F i.unop ≫ (P X).map m = stageTarget X F d i.unop :=
    desc_fac _ _ _ _ _ _ _
  change (stage X F i.unop ≫ e.hom.app (limitCoefficients X F)) ≫ m = _
  rw [Category.assoc, ← hn, ← Category.assoc, hm]
  change (d.ι.app i ≫ e.inv.app d.pt) ≫ e.hom.app d.pt = d.ι.app i
  rw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The limit-coefficient construction on a constant scheme diagram
computes the colimit in the category of étale sheaves. -/
def isColimitCocone : IsColimit (cocone X F) where
  desc := descend X F
  fac := descend_fac X F
  uniq d m hm := by
    apply PhilipponEtaleLimitUniversalProperty.hom_ext (constCone I X) (coneIsLimit X)
      (ofSheafDiagram X F) d.pt
    intro i
    let e := unit X i
    have hn : (P X).map m ≫ e.hom.app d.pt = e.hom.app (limitCoefficients X F) ≫ m :=
      e.hom.naturality m
    have hh : (P X).map (descend X F d) ≫ e.hom.app d.pt =
        e.hom.app (limitCoefficients X F) ≫ descend X F d :=
      e.hom.naturality (descend X F d)
    change stage X F i ≫ (P X).map m = stage X F i ≫ (P X).map (descend X F d)
    apply (cancel_mono (e.hom.app d.pt)).mp
    rw [Category.assoc, Category.assoc, hn, hh]
    change ((cocone X F).ι.app (op i) ≫ m) = ((cocone X F).ι.app (op i) ≫ descend X F d)
    exact (hm (op i)).trans (descend_fac X F d (op i)).symm

/-- The coefficient map out of the identity inverse image factors
through the ordinary colimit injection. -/
theorem restrictCoefficients_eq (i : I) :
    restrictCoefficients (constCone I X) (coneIsLimit X) (ofSheafDiagram X F) i =
      ((pullbackAdjunction (𝟙 X)).homEquiv (F.obj (op i)) (F.obj (op i))).symm
        ((unit X i).inv.app (F.obj (op i))) ≫ (cocone X F).ι.app (op i) := by
  let e := unit X i
  let a := pullbackAdjunction (𝟙 X)
  let t := (cocone X F).ι.app (op i)
  let H := F.obj (op i)
  have hn : e.inv.app H ≫ (P X).map t = t ≫ e.inv.app (limitCoefficients X F) :=
    (e.inv.naturality t).symm
  change (a.homEquiv H _).symm (stage X F i) = (a.homEquiv H H).symm (e.inv.app H) ≫ t
  rw [← a.homEquiv_naturality_right_symm, hn]
  congr 1
  change stage X F i = (stage X F i ≫ e.hom.app _) ≫ e.inv.app _
  rw [Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

end PhilipponEtaleConstantDiagramColimit

end

end


