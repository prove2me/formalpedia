-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleRefinedSectionTransport
-- name    : AlgebraicGeometry_EtaleRefinedSectionTransport
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T23:40:18.140792+00:00
-- url     : https://prove2.me/theorems/016dd46c-4f60-4dfa-8402-ad056422faae
-- title:
--   Transport of étale section lifts along pullback
-- statement:
--   Comparison of a section lifted along a base-changed closed immersion with the two direct-image restrictions.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts

noncomputable section

section

section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackComposition (restrictDirectImage)
open PhilipponEtalePullbackSquareUnits (pulledImageComparisonOver pulledImageComparison_unit)
open PhilipponEtaleSectionFiniteRefinement
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleRefinedSectionLifts

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

variable {X Z P : Scheme.{u}} (i : Z ⟶ X) (p : P ⟶ X) (F : Ab X)

private abbrev j := pullback.fst p i
private abbrev r := pullback.snd p i
private abbrev composite := j i p ≫ p

private theorem r_comp : r i p ≫ i = composite i p := pullback.condition.symm

private abbrev image (i : Z ⟶ X) (F : Ab X) : Ab X :=
  (pushforward i).obj ((pullbackSheaves i).obj F)

private abbrev η (i : Z ⟶ X) (F : Ab X) : F ⟶ image i F :=
  (pullbackAdjunction i).unit.app F

private def comparison :
    (pullbackSheaves p).obj (image i F) ⟶ image (j i p) ((pullbackSheaves p).obj F) :=
  pulledImageComparisonOver p i (j i p) (r i p) (composite i p) rfl (r_comp i p) F

private theorem unit_comparison :
    (pullbackSheaves p).map (η i F) ≫ comparison i p F =
      η (j i p) ((pullbackSheaves p).obj F) :=
  pulledImageComparison_unit p i (j i p) (r i p) (composite i p) rfl (r_comp i p) F

/-- The pulled section on the closed subset of the new base, expressed
on the direct image of the inverse-image sheaf. -/
def pullClosedSection :
    (image i F).obj.obj (op (terminal X)) ⟶
      (image (j i p) ((pullbackSheaves p).obj F)).obj.obj (op (terminal P)) :=
  pullSectionAlong p (V := terminal X) p (Category.comp_id p) (image i F) ≫
    (comparison i p F).hom.app (op (terminal P))

set_option maxRecDepth 4096 in
/-- The section-lifting equation on the base-changed closed subset
identifies the restrictions of the two direct-image sections. -/
theorem directImage_eq_of_lift
    (a : (globalSections X).obj (image i F)) (b : (globalSections P).obj ((pullbackSheaves p).obj F))
    (hb : (η (j i p) ((pullbackSheaves p).obj F)).hom.app (op (terminal P)) b =
      pullClosedSection i p F a) :
    (globalSections X).map (restrictDirectImage p (j i p) (composite i p) rfl F)
        ((globalSectionsIso p).inv.app ((pullbackSheaves p).obj F) b) =
      (globalSections X).map (restrictDirectImage i (r i p) (composite i p) (r_comp i p) F) a := by
  unfold pullClosedSection at hb
  rw [pullSectionAlong_terminal] at hb
  exact PhilipponEtaleSectionComparison.restrictDirectImage_eq_of_lift p i (j i p) (r i p)
    (composite i p) rfl (r_comp i p) F a b hb

/-- Use the direct-image lifting equality on a pullback square whose
projections are treated as variables. -/
theorem closedLift_induction [Surjective p]
    (a : (globalSections X).obj (image i F)) (b : (globalSections P).obj ((pullbackSheaves p).obj F))
    (hb : (η (j i p) ((pullbackSheaves p).obj F)).hom.app (op (terminal P)) b =
      pullClosedSection i p F a) {T : Prop}
    (use : ∀ {A : Scheme.{u}} (u : A ⟶ P) (v : A ⟶ Z) (σ : A ⟶ X)
      (hu : u ≫ p = σ) (hv : v ≫ i = σ), IsPullback u v p i → Surjective v →
      (globalSections X).map (restrictDirectImage p u σ hu F)
          ((globalSectionsIso p).inv.app ((pullbackSheaves p).obj F) b) =
        (globalSections X).map (restrictDirectImage i v σ hv F) a → T) : T :=
  use (j i p) (r i p) (composite i p) rfl (r_comp i p) (IsPullback.of_hasPullback p i)
    (inferInstanceAs (Surjective (pullback.snd p i))) (directImage_eq_of_lift i p F a b hb)

private theorem pullClosedSection_restrict (V : P.Etale) (k : V ⟶ terminal P) :
    pullClosedSection i p F ≫ (image (j i p) ((pullbackSheaves p).obj F)).obj.map k.op =
      pullSectionAlongChart (U := terminal X) (A := V) p (image i F) (V.hom ≫ p)
        (Category.comp_id _) ≫ (comparison i p F).hom.app (op V) := by
  have hk : k.left = V.hom := (Category.comp_id _).symm.trans (MorphismProperty.Over.w k)
  unfold pullClosedSection pullSectionAlong
  rw [Category.assoc, ← (comparison i p F).hom.naturality k.op, ← Category.assoc,
    pullSectionAlongChart_restrict]
  congr 1
  exact pullSectionAlongChart_congr (U := terminal X) (A := V) p (image i F)
    (congrArg (· ≫ p) hk) _ _

/-- Pulling an étale lift across the finite-cover chart produces a lift
of the pulled closed-subscheme section there. -/
theorem pull_lift_restricts {U : X.Etale} {V : P.Etale}
    (g : U ⟶ terminal X) (k : V ⟶ terminal P) (l : V.left ⟶ U.left)
    (hl : l ≫ U.hom = V.hom ≫ p)
    (a : ↥((image i F).obj.obj (op (terminal X)))) (b : ↥(F.obj.obj (op U)))
    (h : (η i F).hom.app (op U) b = (image i F).obj.map g.op a) :
    (η (j i p) ((pullbackSheaves p).obj F)).hom.app (op V)
        (pullSectionAlongChart p F l hl b) =
      (image (j i p) ((pullbackSheaves p).obj F)).obj.map k.op (pullClosedSection i p F a) := by
  let v := pullSectionAlongChart p (image i F) l hl
  let d := (comparison i p F).hom.app (op V)
  have hUnit := congrArg (fun m => m.hom.app (op V)) (unit_comparison i p F)
  have h1 :
      pullSectionAlongChart p F l hl ≫ (η (j i p) ((pullbackSheaves p).obj F)).hom.app (op V) =
      (η i F).hom.app (op U) ≫ v ≫ d := by
    refine Eq.trans (congrArg (fun m => pullSectionAlongChart p F l hl ≫ m) hUnit.symm) ?_
    change pullSectionAlongChart p F l hl ≫ ((pullbackSheaves p).map (η i F)).hom.app (op V) ≫ d =
      (η i F).hom.app (op U) ≫ v ≫ d
    rw [← Category.assoc, ← pullSectionAlongChart_naturality, Category.assoc]
  have hg : g.left = U.hom := (Category.comp_id _).symm.trans (MorphismProperty.Over.w g)
  have h2 : (image i F).obj.map g.op ≫ v =
      pullSectionAlongChart (U := terminal X) (A := V) p (image i F) (V.hom ≫ p)
        (Category.comp_id _) := by
    change (image i F).obj.map g.op ≫ pullSectionAlongChart p (image i F) l hl = _
    rw [pullSectionAlongChart_comp]
    have he : l ≫ g.left = V.hom ≫ p := (congrArg (l ≫ ·) hg).trans hl
    exact pullSectionAlongChart_congr (U := terminal X) (A := V) p (image i F) he _ _
  calc
    _ = (v ≫ d) ((η i F).hom.app (op U) b) := ConcreteCategory.congr_hom h1 b
    _ = ((image i F).obj.map g.op ≫ v ≫ d) a := by rw [h]; rfl
    _ = _ := by
      rw [← Category.assoc, h2, ← pullClosedSection_restrict i p F V k]
      rfl

end PhilipponEtaleRefinedSectionLifts

end

end


