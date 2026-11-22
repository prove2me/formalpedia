-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionDescent
-- name    : AlgebraicGeometry_EtaleFiniteSectionDescent
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T06:03:45.903917+00:00
-- url     : https://prove2.me/theorems/cf42a2f2-a0f0-4f8a-9182-c8a5ee7a099b
-- title:
--   Descent of étale sections along finite covers
-- statement:
--   Degree-zero comparison for proper closed fibers using a finite cover and its overlap.

import Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
import Definitions.Def_AlgebraicGeometry_EtaleClosedLiftDescent

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleClosedFiberSections (FiniteCoverLifts closedFiberι exists_closedFiber_lift_on_finite_cover)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap)
open PhilipponEtalePullbackComposition (restrictGlobalSections_app_eq)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStrictHenselization (toBase)
open PhilipponFiniteEtaleDescent (HasClosedStrictLocalComponents)


namespace PhilipponEtaleClosedFiberDegreeZero

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (.of R)) [IsProper f]

private abbrev residue := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

omit [IsProper f] in
private theorem closedFiber_closedImmersion : IsClosedImmersion (closedFiberι f) := by
  let : IsClosedImmersion (residue (R := R)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (IsLocalRing.residue R))
      IsLocalRing.residue_surjective
  exact inferInstanceAs (IsClosedImmersion (pullback.snd (residue (R := R)) f))

/-- The unit on global sections is injective for closed-fiber restriction. -/
theorem unitSections_injective (F : Ab Y) :
    Function.Injective ((globalSections Y).map ((pullbackAdjunction (closedFiberι f)).unit.app F)) := by
  intro a b hab
  apply PhilipponEtaleClosedFiberSections.restrictGlobalSections_app_injective f F
  let i := closedFiberι f
  have h := restrictGlobalSections_app_eq i F
  exact (ConcreteCategory.congr_hom h a).trans
    ((congrArg ((globalSectionsIso i).hom.app ((pullbackSheaves i).obj F)) hab).trans
      (ConcreteCategory.congr_hom h b).symm)

/-- The double overlap of a finite cover is again finite over the base. -/
theorem exists_finite_overlap {P X : Scheme.{u}} (p : P ⟶ X) [IsFinite p] :
    ∃ (Q : Scheme.{u}) (d₁ d₂ : Q ⟶ P) (ρ : Q ⟶ X),
      IsFinite ρ ∧ IsPullback d₁ d₂ p p ∧ d₁ ≫ p = ρ ∧ d₂ ≫ p = ρ := by
  let d := pullback.fst p p
  exact ⟨pullback p p, d, pullback.snd p p, d ≫ p,
    inferInstanceAs (IsFinite (pullback.fst p p ≫ p)), IsPullback.of_hasPullback p p,
    rfl, pullback.condition.symm⟩

/-- On a finite overlap, restriction to the inverse image of the closed fiber is injective. -/
theorem exists_closed_overlap {Q : Scheme.{u}} (ρ : Q ⟶ Y) [IsFinite ρ] (G : Ab Q) :
    ∃ (B : Scheme.{u}) (j : B ⟶ Q) (r : B ⟶ pullback (residue (R := R)) f) (τ : B ⟶ Y),
      IsFinite τ ∧ j ≫ ρ = τ ∧ r ≫ closedFiberι f = τ ∧
        Function.Injective ((restrictGlobalSections j).app G) := by
  let i := closedFiberι f
  let : IsClosedImmersion i := closedFiber_closedImmersion f
  let j := pullback.fst ρ i
  refine ⟨pullback ρ i, j, pullback.snd ρ i, j ≫ ρ,
    inferInstanceAs (IsFinite (pullback.fst ρ i ≫ ρ)), rfl, pullback.condition.symm, ?_⟩
  exact PhilipponEtaleClosedFiberSections.restrictGlobalSections_app_injective_on_baseChange f ρ G

set_option maxRecDepth 4096 in
private theorem descend_lift {X P Z Q B : Scheme.{u}} (p : P ⟶ X) [IsFinite p] [Surjective p]
    (i : Z ⟶ X) (d₁ d₂ : Q ⟶ P) (ρ : Q ⟶ X) (hsq : IsPullback d₁ d₂ p p)
    (h₁ : d₁ ≫ p = ρ) (h₂ : d₂ ≫ p = ρ)
    (j : B ⟶ Q) (r : B ⟶ Z) (τ : B ⟶ X) [IsFinite τ]
    (hj : j ≫ ρ = τ) (hr : r ≫ i = τ)
    (hSplitP : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p))
    (hSplitT : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) τ))
    (F : Ab X) (a : (globalSections X).obj ((pushforward i).obj ((pullbackSheaves i).obj F)))
    (b : (globalSections P).obj ((pullbackSheaves p).obj F))
    (hInj : Function.Injective ((restrictGlobalSections j).app ((pullbackSheaves ρ).obj F)))
    (hb : ((pullbackAdjunction (pullback.fst p i)).unit.app ((pullbackSheaves p).obj F)).hom.app
      (op (Scheme.Etale.mk (𝟙 P))) b = PhilipponEtaleRefinedSectionLifts.pullClosedSection i p F a) :
    ∃ c : (globalSections X).obj F, (globalSections X).map ((pullbackAdjunction i).unit.app F) c = a := by
  refine PhilipponEtaleRefinedSectionLifts.closedLift_induction i p F a b hb ?_
  intro A u v σ hu hv hUV hSurj hAgree
  let : Surjective v := hSurj
  exact PhilipponEtaleClosedLiftDescent.exists_preimage_of_closed_lift p i d₁ d₂ ρ hsq h₁ h₂
    u v hUV σ hu hv j r τ hj hr hSplitP hSplitT F
    ((globalSectionsIso p).inv.app ((pullbackSheaves p).obj F) b) a hInj hAgree

private def FiniteOverlapInjection {X Z : Scheme.{u}} (i : Z ⟶ X) : Prop :=
  ∀ {Q : Scheme.{u}} (ρ : Q ⟶ X) [IsFinite ρ] (G : Ab Q),
    ∃ (B : Scheme.{u}) (j : B ⟶ Q) (r : B ⟶ Z) (τ : B ⟶ X),
      IsFinite τ ∧ j ≫ ρ = τ ∧ r ≫ i = τ ∧
        Function.Injective ((restrictGlobalSections j).app G)

set_option maxRecDepth 4096 in
private theorem unitSections_surjective_of_lifts {X Z : Scheme.{u}} (i : Z ⟶ X) (F : Ab X)
    (hLifts : FiniteCoverLifts i F) (hOverlap : FiniteOverlapInjection i)
    (hSplit : ∀ {P : Scheme.{u}} (p : P ⟶ X) [IsFinite p], ∀ x : X,
      HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p)) :
    Function.Surjective ((globalSections X).map ((pullbackAdjunction i).unit.app F)) := by
  intro a
  obtain ⟨P, p, hp, hs, b, hb⟩ := hLifts a
  let : IsFinite p := hp
  let : Surjective p := hs
  obtain ⟨Q, d₁, d₂, ρ, hFinite, hsq, h₁, h₂⟩ := exists_finite_overlap p
  let : IsFinite ρ := hFinite
  obtain ⟨B, j, r, τ, hFinite', hj, hr, hInj⟩ := hOverlap ρ ((pullbackSheaves ρ).obj F)
  let : IsFinite τ := hFinite'
  exact descend_lift p i d₁ d₂ ρ hsq h₁ h₂ j r τ hj hr (hSplit p) (hSplit τ) F a b hInj hb

private theorem closedFiber_finiteOverlapInjection : FiniteOverlapInjection (closedFiberι f) := by
  intro Q ρ hFinite G
  exact exists_closed_overlap f ρ G

private theorem unitSections_iso_of_lifts {X Z : Scheme.{u}} (i : Z ⟶ X) (F : Ab X)
    (hInj : Function.Injective ((globalSections X).map ((pullbackAdjunction i).unit.app F)))
    (hLifts : FiniteCoverLifts i F) (hOverlap : FiniteOverlapInjection i)
    (hSplit : ∀ {P : Scheme.{u}} (p : P ⟶ X) [IsFinite p], ∀ x : X,
      HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p)) :
    IsIso ((globalSections X).map ((pullbackAdjunction i).unit.app F)) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨hInj, unitSections_surjective_of_lifts i F hLifts hOverlap hSplit⟩

set_option maxRecDepth 4096 in
/-- The closed-fiber comparison in degree zero follows from connectedness
of the closed fibers of preconnected proper schemes and decomposition of
finite strict-local pullbacks. -/
theorem isIso_unitSections_of_connectedness
    (hFiber : ∀ {V : Scheme.{u}} (g : V ⟶ Spec (.of R)) [IsProper g] [PreconnectedSpace V],
      _root_.IsPreconnected (g ⁻¹' {IsLocalRing.closedPoint R}))
    (hSplit : ∀ {V : Scheme.{u}} (g : V ⟶ Y) [IsFinite g], ∀ y : Y,
      HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap y)) g))
    (F : Ab Y) :
    IsIso ((globalSections Y).map ((pullbackAdjunction (closedFiberι f)).unit.app F)) :=
  unitSections_iso_of_lifts (closedFiberι f) F (unitSections_injective f F)
    (exists_closedFiber_lift_on_finite_cover f F hFiber) (closedFiber_finiteOverlapInjection f) hSplit

end PhilipponEtaleClosedFiberDegreeZero

end

end


