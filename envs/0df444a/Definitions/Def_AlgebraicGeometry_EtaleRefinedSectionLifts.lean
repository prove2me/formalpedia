-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleRefinedSectionLifts
-- name    : AlgebraicGeometry_EtaleRefinedSectionLifts
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T23:41:59.978962+00:00
-- url     : https://prove2.me/theorems/d48b84c2-3215-4c5f-87f9-7a38b92b4272
-- title:
--   Étale section lifts on a finite surjective refinement
-- statement:
--   Comparison and gluing of lifts on a finite cover refined by open subschemes.

import Definitions.Def_AlgebraicGeometry_EtaleRefinedSectionTransport
import Definitions.Def_AlgebraicGeometry_EtaleZariskiSectionGluing

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
open PhilipponEtaleZariskiSections (exists_global_lift_of_open_lifts openToTerminal)
open PhilipponZariskiTorsorCoordinates (opensToEtale)


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

/-- For any section on the closed subset, there is a finite
surjective cover on which the pulled-back section has Zariski-local lifts. -/
theorem exists_finite_cover_with_zariski_lifts [IsClosedImmersion i] [SpectralSpace X]
    (a : ↥((image i F).obj.obj (op (terminal X)))) :
    ∃ (P : Scheme.{u}) (p : P ⟶ X), IsFinite p ∧ Surjective p ∧
      ∀ x : P, ∃ (U : P.Opens) (_ : x ∈ U)
        (b : ↥(((pullbackSheaves p).obj F).obj.obj (op ((opensToEtale P).obj U)))),
        (η (j i p) ((pullbackSheaves p).obj F)).hom.app (op ((opensToEtale P).obj U)) b =
          (image (j i p) ((pullbackSheaves p).obj F)).obj.map (openToTerminal U).op
            (pullClosedSection i p F a) := by
  have : SpectralSpace (terminal X).left := inferInstanceAs (SpectralSpace X)
  obtain ⟨I, _, V, g, b, P, p, hp, hs, hL, hA⟩ :=
    exists_finite_refinement_of_lifts i (U := terminal X) F a
  refine ⟨P, p, hp, hs, fun x => ?_⟩
  obtain ⟨s, W, k, hk, hx, l, hl⟩ := hA x
  let U := k.opensRange
  let e := IsOpenImmersion.isoOfRangeEq U.ι k (by rw [Scheme.Opens.range_ι]; rfl)
  have he : e.hom ≫ k = U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hg : (g s).left = (V s).hom := (Category.comp_id _).symm.trans (MorphismProperty.Over.w (g s))
  let m := e.hom ≫ l
  have hm : m ≫ (V s).hom = U.ι ≫ p := by
    change (e.hom ≫ l) ≫ (V s).hom = _
    rw [Category.assoc, ← hg, hl, ← Category.assoc, he]
  let c := pullSectionAlongChart (A := (opensToEtale P).obj U) p F m hm (b s)
  exact ⟨U, hx, c, pull_lift_restricts i p F (g s) (openToTerminal U) m hm a (b s) (hL s)⟩

/-- If the inverse image of the closed set meets each point closure on
finite covers in a connected nonempty set, the lift over a finite cover
can be taken globally. -/
theorem exists_global_lift_on_finite_cover [IsClosedImmersion i] [SpectralSpace X]
    (hConn : ∀ {P : Scheme.{u}} (p : P ⟶ X), IsFinite p → Surjective p →
      ∀ x : P, IsConnected (Set.range (j i p) ∩ closure ({x} : Set P)))
    (a : ↥((image i F).obj.obj (op (terminal X)))) :
    ∃ (P : Scheme.{u}) (p : P ⟶ X), IsFinite p ∧ Surjective p ∧
      ∃ b : ↥(((pullbackSheaves p).obj F).obj.obj (op (terminal P))),
        (η (j i p) ((pullbackSheaves p).obj F)).hom.app (op (terminal P)) b =
          pullClosedSection i p F a := by
  obtain ⟨P, p, hp, hs, hL⟩ := exists_finite_cover_with_zariski_lifts i F a
  let _ : IsFinite p := hp
  let _ : SpectralSpace P :=
    { toCompactSpace := (quasiCompact_iff_compactSpace p).mp inferInstance
      toQuasiSeparatedSpace := quasiSeparatedSpace_of_quasiSeparated p }
  exact ⟨P, p, hp, hs, exists_global_lift_of_open_lifts (j i p) ((pullbackSheaves p).obj F)
    (hConn p hp hs) (pullClosedSection i p F a) (fun x _ => hL x)⟩

end PhilipponEtaleRefinedSectionLifts

end

end


