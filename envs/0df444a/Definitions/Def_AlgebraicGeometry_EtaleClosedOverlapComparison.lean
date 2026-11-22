-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleClosedOverlapComparison
-- name    : AlgebraicGeometry_EtaleClosedOverlapComparison
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T05:56:59.290169+00:00
-- url     : https://prove2.me/theorems/22b5547a-68d1-4fe1-9b9d-f040ee026917
-- title:
--   Restriction on a closed fiber of a finite overlap
-- statement:
--   The restriction of a lift to the closed overlap agrees with the original closed-fiber section there.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteRestrictionTransitivity

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackComposition (restrictDirectImage)
open PhilipponEtaleRestrictionTransitivity (EvaluationsSeparate restrictDirectImage_comp)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleClosedOverlap

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev image {X Y : Scheme.{u}} (p : Y ⟶ X) (F : Ab X) :=
  (pushforward p).obj ((pullbackSheaves p).obj F)

private theorem restrict_congr {X Y W : Scheme.{u}} (p : Y ⟶ X) (τ : W ⟶ X)
    {k l : W ⟶ Y} (h : k = l) (hk : k ≫ p = τ) (hl : l ≫ p = τ) (F : Ab X) :
    restrictDirectImage p k τ hk F = restrictDirectImage p l τ hl F := by
  subst l
  rfl

set_option maxRecDepth 4096 in
/-- The lift on the cover restricts on a closed overlap to the
restriction of the original closed-subscheme section. -/
theorem restrict_to_closed_overlap
    {X Y Z Q A B : Scheme.{u}} (p : Y ⟶ X) (i : Z ⟶ X)
    (d : Q ⟶ Y) (ρ : Q ⟶ X) (hd : d ≫ p = ρ)
    (u : A ⟶ Y) (v : A ⟶ Z) (σ : A ⟶ X) (hu : u ≫ p = σ) (hv : v ≫ i = σ)
    (j : B ⟶ Q) (r : B ⟶ Z) (m : B ⟶ A) (τ : B ⟶ X)
    (hj : j ≫ ρ = τ) (hr : r ≫ i = τ) (hm : m ≫ σ = τ)
    (hY : j ≫ d = m ≫ u) (hZ : m ≫ v = r)
    (F : Ab X) (hSep : EvaluationsSeparate τ F)
    (b : (globalSections X).obj (image p F)) (a : (globalSections X).obj (image i F))
    (hb : (globalSections X).map (restrictDirectImage p u σ hu F) b =
      (globalSections X).map (restrictDirectImage i v σ hv F) a) :
    (globalSections X).map (restrictDirectImage ρ j τ hj F)
      ((globalSections X).map (restrictDirectImage p d ρ hd F) b) =
    (globalSections X).map (restrictDirectImage i r τ hr F) a := by
  let Γ := globalSections X
  let D := restrictDirectImage p d ρ hd F
  let J := restrictDirectImage ρ j τ hj F
  let U := restrictDirectImage p u σ hu F
  let V := restrictDirectImage i v σ hv F
  let M := restrictDirectImage σ m τ hm F
  let R := restrictDirectImage i r τ hr F
  have h₁ : (j ≫ d) ≫ p = τ := by rw [Category.assoc, hd, hj]
  have h₂ : (m ≫ u) ≫ p = τ := by rw [Category.assoc, hu, hm]
  have h₃ : (m ≫ v) ≫ i = τ := by rw [hZ, hr]
  have hDJ : D ≫ J = U ≫ M :=
    (restrictDirectImage_comp p d ρ hd j τ hj h₁ F hSep).trans
      ((restrict_congr p τ hY h₁ h₂ F).trans
        (restrictDirectImage_comp p u σ hu m τ hm h₂ F hSep).symm)
  have hVR : V ≫ M = R :=
    (restrictDirectImage_comp i v σ hv m τ hm h₃ F hSep).trans
      (restrict_congr i τ hZ h₃ hr F)
  calc
    Γ.map J (Γ.map D b) = (Γ.map (D ≫ J)) b :=
      (ConcreteCategory.congr_hom (Γ.map_comp D J) b).symm
    _ = (Γ.map (U ≫ M)) b := congrArg (fun t => (Γ.map t) b) hDJ
    _ = Γ.map M (Γ.map U b) := ConcreteCategory.congr_hom (Γ.map_comp U M) b
    _ = Γ.map M (Γ.map V a) := congrArg (Γ.map M) hb
    _ = (Γ.map (V ≫ M)) a := (ConcreteCategory.congr_hom (Γ.map_comp V M) a).symm
    _ = Γ.map R a := congrArg (fun t => Γ.map t a) hVR

end PhilipponEtaleClosedOverlap

end

end


