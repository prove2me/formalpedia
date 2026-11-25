-- Prove2me | Definitions.Def_AlgebraicGeometry_EtalePullbackSystemComparisons
-- name    : AlgebraicGeometry_EtalePullbackSystemComparisons
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T06:28:02.886678+00:00
-- url     : https://prove2.me/theorems/ef5cf0ee-61b2-4745-a656-7a896d73c97c
-- title:
--   Inverse-image comparisons for compatible systems pulled back from a fixed scheme
-- statement:
--   The adjoint of a transition map of the system is the canonical composition comparison for inverse images, obtained from the unit identities.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitCoefficientMaps
import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestrictionComposition

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageSystem (directImages)


namespace PhilipponEtaleDirectImageComposition

universe u

private def compositionOver {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (ρ : Z ⟶ X) (h : ρ = g ≫ f) :
    pushforward ρ ≅ pushforward g ⋙ pushforward f :=
  (Functor.sheafPushforwardContinuousComp'
    (F := baseChange f) (G := baseChange g) (FG := baseChange ρ)
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f ρ h).symm
    AddCommGrpCat.{u} X.smallEtaleTopology Y.smallEtaleTopology Z.smallEtaleTopology).symm

private theorem compositionOver_eq {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (ρ : Z ⟶ X) (h : ρ = g ≫ f) :
    compositionOver f g ρ h = eqToIso (congrArg pushforward h) ≪≫ (pushforwardCompIso f g).symm := by
  subst ρ
  simp only [congrArg, eqToIso_refl, Iso.refl_trans]
  rfl

/-- The direct-image system's comparison is ordinary composition of
direct images, transported across the diagram's composition law. -/
theorem composition_eq {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    (directImages D).composition a b =
      eqToIso (congrArg pushforward (D.map_comp a b)) ≪≫ (pushforwardCompIso (D.map b) (D.map a)).symm :=
  compositionOver_eq (D.map b) (D.map a) (D.map (a ≫ b)) (D.map_comp a b)

end PhilipponEtaleDirectImageComposition

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleCohomologyAlong (pullbackComposition)
open PhilipponEtalePullbackComposition (pullbackCompIso_over_hom)
open PhilipponEtalePullbackSystem (extended pullbackSystem toBase system_unit)
open PhilipponEtaleDirectImageComposition (composition_eq)
open PhilipponEtaleDirectImageSystem (directImages)


namespace PhilipponEtalePullbackSystemComparison

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) {X : Scheme.{u}}
  (p : ∀ i, D.obj i ⟶ X) (hp : ∀ (i j : I) (a : i ⟶ j), D.map a ≫ p j = p i)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {i j : I} (a : i ⟶ j)

private theorem toBase_symm :
    (toBase D p hp a).symm =
      pushforwardCompIso (p j) (D.map a) ≪≫ eqToIso (congrArg pushforward (hp i j a)) := by
  change ((directImages (extended D p hp)).composition (WithTerminal.incl.map a)
    (WithTerminal.homFrom j)).symm = _
  rw [composition_eq, Iso.trans_symm]
  change pushforwardCompIso (p j) (D.map a) ≪≫
    (eqToIso (congrArg pushforward (hp i j a).symm)).symm = _
  congr 1

/-- The transition between pullbacks of a fixed sheaf is adjoint to
the canonical comparison for the composite inverse image. -/
theorem adjoint_transition :
    ((pullbackAdjunction (D.map a)).homEquiv ((pullbackSheaves (p j)).obj F)
      ((pullbackSheaves (p i)).obj F)).symm ((pullbackSystem D p hp F).map a) =
        (pullbackComposition (p j) (D.map a) (p i) (hp i j a)).hom.app F := by
  let M := (pullbackSheaves (p j)).obj F
  let N := (pullbackSheaves (p i)).obj F
  let ai := pullbackAdjunction (p i)
  let aj := pullbackAdjunction (p j)
  let aa := pullbackAdjunction (D.map a)
  let e := pushforwardCompIso (p j) (D.map a) ≪≫ eqToIso (congrArg pushforward (hp i j a))
  let adj := (aj.comp aa).ofNatIsoRight e
  let m : M ⟶ (pushforward (D.map a)).obj N := (pullbackSystem D p hp F).map a
  let b := (aa.homEquiv M N).symm m
  have hu : aj.unit.app F ≫ (pushforward (p j)).map m ≫ e.hom.app N = ai.unit.app F := by
    let v : pushforward (p i) ≅ pushforward (D.map a) ⋙ pushforward (p j) := toBase D p hp a
    have h : aj.unit.app F ≫ (pushforward (p j)).map m = ai.unit.app F ≫ v.hom.app N :=
      system_unit D p hp F a
    have he : e = v.symm := (toBase_symm D p hp a).symm
    rw [he]
    change aj.unit.app F ≫ (pushforward (p j)).map m ≫ v.inv.app N = ai.unit.app F
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id (ai.unit.app F)
  have he : (adj.leftAdjointUniq ai).hom.app F =
      (pullbackComposition (p j) (D.map a) (p i) (hp i j a)).hom.app F :=
    pullbackCompIso_over_hom (p j) (D.map a) (p i) (hp i j a) F
  change b = (pullbackComposition (p j) (D.map a) (p i) (hp i j a)).hom.app F
  rw [← he]
  apply (adj.homEquiv F N).injective
  have ha : adj.homEquiv F N ((adj.leftAdjointUniq ai).hom.app F) = ai.unit.app F :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app adj ai F
  rw [ha]
  change ((aj.comp aa).ofNatIsoRight e).homEquiv F N b = _
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change aj.homEquiv F _ (aa.homEquiv M N b) ≫ e.hom.app N = _
  rw [show aa.homEquiv M N b = m from (aa.homEquiv M N).apply_symm_apply _, aj.homEquiv_unit, Category.assoc]
  exact hu

end PhilipponEtalePullbackSystemComparison

end

end


