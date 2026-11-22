-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleClosedLiftDescent
-- name    : AlgebraicGeometry_EtaleClosedLiftDescent
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T06:00:12.451821+00:00
-- url     : https://prove2.me/theorems/193f2b4e-b121-4850-8fe7-43fdb79dfb6e
-- title:
--   Descent of a finite-cover lift of a closed-fiber section
-- statement:
--   A lift agreeing on the finite overlap descends to the original scheme and recovers the given closed-fiber section.

import Definitions.Def_AlgebraicGeometry_EtaleClosedOverlapComparison
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionEqualizer

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDescentCofaces (evalAtLiftOver_eq_of_transported_eq)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap)
open PhilipponEtalePullbackComposition (restrictDirectImage unit_restrictDirectImage
  restrictDirectImage_sections_injective restrictGlobalSections_injective_of_surjective)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleRestrictionTransitivity (EvaluationsSeparate)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStrictHenselization (toBase)
open PhilipponFiniteEtaleDescent (HasClosedStrictLocalComponents exists_section_of_agreement)


namespace PhilipponEtaleClosedLiftDescent

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev image {X Y : Scheme.{u}} (p : Y ⟶ X) (F : Ab X) :=
  (pushforward p).obj ((pullbackSheaves p).obj F)
private abbrev η {X Y : Scheme.{u}} (p : Y ⟶ X) (F : Ab X) :=
  (pullbackAdjunction p).unit.app F
private abbrev Sections (X : Scheme.{u}) := globalSections X

private theorem separation_of_closed_components {X W : Scheme.{u}} (τ : W ⟶ X) [IsFinite τ]
    (hSplit : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) τ))
    (F : Ab X) : EvaluationsSeparate τ F := by
  intro x a b hab
  obtain ⟨I, B, hB, hH, hSep, c, hc⟩ := hSplit x
  let _ : ∀ i, CommRing (B i) := hB
  let _ : ∀ i, HenselianLocalRing (B i) := hH
  let _ : ∀ i, IsSepClosed (IsLocalRing.ResidueField (B i)) := hSep
  let s := algebraicallyClosedGeometricMap x
  apply PhilipponFiniteStalkEvaluation.ext_of_evaluations_equal s τ B c hc ((pullbackSheaves τ).obj F)
  intro v hv
  exact evalAtLiftOver_eq_of_transported_eq τ v s hv F (hab v hv)

set_option maxRecDepth 4096 in
/-- A lift on a finite cover descends, provided restriction to the closed
overlap is injective and the cover remains surjective over the closed subset. -/
theorem exists_preimage_of_closed_lift
    {X Y Z Q A B : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Surjective p] (i : Z ⟶ X)
    (d₁ d₂ : Q ⟶ Y) (ρ : Q ⟶ X) (hsq : IsPullback d₁ d₂ p p)
    (h₁ : d₁ ≫ p = ρ) (h₂ : d₂ ≫ p = ρ)
    (u : A ⟶ Y) (v : A ⟶ Z) [Surjective v] (hUV : IsPullback u v p i)
    (σ : A ⟶ X) (hu : u ≫ p = σ) (hv : v ≫ i = σ)
    (j : B ⟶ Q) (r : B ⟶ Z) (τ : B ⟶ X) [IsFinite τ] (hj : j ≫ ρ = τ) (hr : r ≫ i = τ)
    (hSplitP : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p))
    (hSplitT : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) τ))
    (F : Ab X) (b : (Sections X).obj (image p F)) (a : (Sections X).obj (image i F))
    (hInj : Function.Injective ((restrictGlobalSections j).app ((pullbackSheaves ρ).obj F)))
    (hLift : (Sections X).map (restrictDirectImage p u σ hu F) b =
      (Sections X).map (restrictDirectImage i v σ hv F) a) :
    ∃ c : (Sections X).obj F, (Sections X).map (η i F) c = a := by
  let Γ := Sections X
  have hSep := separation_of_closed_components τ hSplitT F
  have hClosed (d : Q ⟶ Y) (hd : d ≫ p = ρ) :
      Γ.map (restrictDirectImage ρ j τ hj F) (Γ.map (restrictDirectImage p d ρ hd F) b) =
        Γ.map (restrictDirectImage i r τ hr F) a := by
    have hFactor : (j ≫ d) ≫ p = r ≫ i := by rw [Category.assoc, hd, hj, hr]
    obtain ⟨m, hm₁, hm₂⟩ := hUV.exists_lift (j ≫ d) r hFactor
    have hm : m ≫ σ = τ := by rw [← hv, ← Category.assoc, hm₂, hr]
    exact PhilipponEtaleClosedOverlap.restrict_to_closed_overlap p i d ρ hd u v σ hu hv
      j r m τ hj hr hm hm₁.symm hm₂ F hSep b a hLift
  have hAgree : Γ.map (restrictDirectImage p d₁ ρ h₁ F) b =
      Γ.map (restrictDirectImage p d₂ ρ h₂ F) b :=
    restrictDirectImage_sections_injective ρ j τ hj F hInj
      ((hClosed d₁ h₁).trans (hClosed d₂ h₂).symm)
  obtain ⟨c, hc⟩ := exists_section_of_agreement p d₁ d₂ ρ h₁ h₂ hsq hSplitP F b hAgree
  refine ⟨c, ?_⟩
  apply restrictDirectImage_sections_injective i v σ hv F
    (restrictGlobalSections_injective_of_surjective v ((pullbackSheaves i).obj F))
  have hUnit (k : Y ⟶ X) (l : A ⟶ Y) (h : l ≫ k = σ) :
      Γ.map (η k F) ≫ Γ.map (restrictDirectImage k l σ h F) = Γ.map (η σ F) := by
    rw [← Γ.map_comp, unit_restrictDirectImage]
  have hUnit' : Γ.map (η i F) ≫ Γ.map (restrictDirectImage i v σ hv F) = Γ.map (η σ F) := by
    rw [← Γ.map_comp, unit_restrictDirectImage]
  calc
    Γ.map (restrictDirectImage i v σ hv F) (Γ.map (η i F) c) = Γ.map (η σ F) c :=
      ConcreteCategory.congr_hom hUnit' c
    _ = Γ.map (restrictDirectImage p u σ hu F) (Γ.map (η p F) c) :=
      (ConcreteCategory.congr_hom (hUnit p u hu) c).symm
    _ = Γ.map (restrictDirectImage p u σ hu F) b := congrArg (Γ.map _) hc
    _ = _ := hLift

end PhilipponEtaleClosedLiftDescent

end

end


