-- Prove2me | solution 1 for AlgebraicGeometry.exists_admissible_flattening_of_affine_open_immersion
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-18T17:41:44.305195+00:00
-- url     : https://prove2.me/submissions/637f175d-3e4a-4049-8480-8490916bb3af

import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_MvPolynomial_CrossingResolution
import Definitions.Def_OAIQ068A013
import Definitions.Def_OAIQ068A020
import Mathlib

universe u v

/- PhilipponNativeBlowupIdealBridge -/
section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory


namespace PhilipponNativeBlowupIdealBridge

theorem nonZeroDivisors_map_equiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) {r : R} (hr : r ∈ nonZeroDivisors R) : e r ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_left]
  intro s hs
  apply e.symm.injective
  rw [map_zero]
  apply mem_nonZeroDivisors_iff_left.mp hr
  simpa only [map_mul, map_zero, e.symm_apply_apply] using congrArg e.symm hs

/-- The registered Rees-blowup predicate is exactly invertibility of
the actual native pulled-back ideal. This comparison preserves universe u. -/
theorem invertible_iff {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    OAI.PiExponentSeshadri.Geometry.InvertiblePullbackIdeal I f ↔ (I.comap f).IsInvertible := by
  rw [OAI.PiExponentSeshadri.InvertibleLocal.invertible_iff_local_equations]
  constructor
  · intro h y
    obtain ⟨U, hy, r, hr, hgen⟩ := h y
    have hreg : U.1.topIso.hom r ∈ nonZeroDivisors Γ(Y, U) :=
      nonZeroDivisors_map_equiv U.1.topIso.commRingCatIsoToRingEquiv
        (isRegular_iff_mem_nonZeroDivisors.mp hr)
    have hbase : (I.comap f).ideal U = Ideal.span {U.1.topIso.hom r} := by
      have hm := congrArg (Ideal.map U.1.topIso.hom.hom) hgen
      rw [OAI.PiExponentSeshadri.IdealPullback.comap_ι_top, Ideal.map_map,
        Ideal.map_span, Set.image_singleton] at hm
      change Ideal.map (U.1.topIso.inv ≫ U.1.topIso.hom).hom ((I.comap f).ideal U) = _ at hm
      simpa only [Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id] using hm
    refine ⟨U, 1, by simpa using hy, ?_⟩
    have hW : Y.affineBasicOpen (U := U) (1 : Γ(Y, U)) = U :=
      Subtype.ext (Y.basicOpen_one)
    rw [hW]
    exact ⟨_, hreg, hbase⟩
  · intro h y
    obtain ⟨U, s, hy, r, hr, hgen⟩ := h y
    let V := Y.affineBasicOpen s
    refine ⟨V, hy, V.1.topIso.inv r, ?_, ?_⟩
    · apply isRegular_iff_mem_nonZeroDivisors.mpr
      exact nonZeroDivisors_map_equiv V.1.topIso.symm.commRingCatIsoToRingEquiv hr
    · rw [OAI.PiExponentSeshadri.IdealPullback.comap_ι_top]
      erw [hgen, Ideal.map_span, Set.image_singleton]

end PhilipponNativeBlowupIdealBridge

end
end

/- PhilipponAffineBlowupUniversal -/
section

/-!
Universe-polymorphic form of the affine universal-property proof in the
public OAIQ068A020 definition bundle. Reuses its graded Rees construction,
principal maps and uniqueness calculation in their original universes.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.PiExponentSeshadri
open OAI.PiExponentSeshadri.Geometry OAI.PiExponentSeshadri.ReesGrading
open OAI.PiExponentSeshadri.SpecMaps


namespace PhilipponAffineBlowupUniversal

variable {R : Type u} [CommRing R] (I : Ideal R)

lemma specIdeal_coordinate {Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ Spec (CommRingCat.of R)) :
    ((IdealPullback.specIdeal I).comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      I.map (coordinate f).hom := by
  rw [IdealPullback.comap_top, IdealPullback.specIdeal_top, Ideal.map_map]
  rfl

lemma invertible_unique {Y : Scheme.{u}} (g h : Y ⟶ affineBlowup I)
    (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) : g = h := by
  apply Scheme.hom_ext_of_forall g h
  intro y
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  refine ⟨U.1, hyU, ?_⟩
  apply principal_unique I (U.1.ι ≫ g) (U.1.ι ≫ h) (U.1.ι ≫ f)
    (by rw [Category.assoc, hg]) (by rw [Category.assoc, hh]) r _ hr
  rwa [← Scheme.IdealSheafData.comap_comp, specIdeal_coordinate] at hIr

lemma local_lift {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ h : U.toScheme ⟶ affineBlowup I,
      h ≫ projection I = U.ι ≫ f := by
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  rw [← Scheme.IdealSheafData.comap_comp, specIdeal_coordinate] at hIr
  refine ⟨U.1, hyU, principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ f)).hom r hIr hr, ?_⟩
  rw [principalScheme_projection]
  exact factor (U.1.ι ≫ f)

theorem universal {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) :
    ∃! h : Y ⟶ affineBlowup I, h ≫ projection I = f := by
  classical
  choose U hyU g hg using local_lift I f hf
  let C : Y.OpenCover := {
    I₀ := Y
    X y := (U y).toScheme
    f y := (U y).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun y => ⟨y, ?_⟩, inferInstance⟩
      simpa using hyU y }
  have hcompat (x y : C.I₀) : pullback.fst (C.f x) (C.f y) ≫ g x =
      pullback.snd (C.f x) (C.f y) ≫ g y := by
    let j := pullback.fst (C.f x) (C.f y) ≫ C.f x
    apply invertible_unique I _ _ (j ≫ f)
    · rw [Category.assoc, hg x]
      rfl
    · rw [Category.assoc, hg y]
      exact (pullback.condition_assoc f).symm
    · exact InvertibleLocal.invertible_restrict (IdealPullback.specIdeal I) f hf j
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro y
    rw [← Category.assoc, C.ι_glueMorphisms]
    exact hg y
  · intro h hh
    exact invertible_unique I h _ f hh (by
      apply C.hom_ext
      intro y
      rw [← Category.assoc, C.ι_glueMorphisms]
      exact hg y) hf

theorem existsUnique_lift {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : ((IdealPullback.specIdeal I).comap f).IsInvertible) :
    ∃! h : Y ⟶ affineBlowup I, h ≫ projection I = f :=
  universal I f ((PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mpr hf)

end PhilipponAffineBlowupUniversal

end
end

/- PhilipponAffineBlowupCenter -/
section

/-! Universe-polymorphic exceptional ideal and affine blowup, following
the verified public OAIQ068A020 construction. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory
open OAI.PiExponentSeshadri
open OAI.PiExponentSeshadri.Geometry OAI.PiExponentSeshadri.ReesGrading


namespace PhilipponAffineBlowupCenter

variable {R : Type u} [CommRing R] (I : Ideal R)

def lineBundle : Geometry.LineBundle (affineBlowup I) :=
  Geometry.idealLineBundle (exceptionalIdeal I) (chartCover I) (chartEquation I)
    (exceptional_chart I) (chartEquation_regular I)

def inclusion : (lineBundle I).sheaf ⟶ Geometry.structureSheaf (affineBlowup I) :=
  IdealModule.closedInclusion (exceptionalIdeal I)

instance inclusion_mono : Mono (inclusion I) := by
  exact inferInstanceAs (Mono (IdealModule.inclusion (exceptionalIdeal I).subschemeι))

theorem presents : Geometry.PresentsPullbackIdeal (IdealPullback.specIdeal I)
    (projection I) (lineBundle I) (inclusion I) := by
  refine ⟨inclusion_mono I, fun U V e => ?_⟩
  change ((IdealModule.closedInclusion (exceptionalIdeal I)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal (IdealPullback.specIdeal I) (projection I) U V e

theorem invertible : Geometry.InvertiblePullbackIdeal (IdealPullback.specIdeal I) (projection I) :=
  ⟨lineBundle I, inclusion I, presents I⟩

theorem nativeInvertible :
    ((IdealPullback.specIdeal I).comap (projection I)).IsInvertible :=
  (PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mp (invertible I)

theorem isBlowup : Geometry.IsBlowup (IdealPullback.specIdeal I) (projection I) :=
  ⟨invertible I, fun _ f hf => PhilipponAffineBlowupUniversal.universal I f hf⟩

end PhilipponAffineBlowupCenter

namespace PhilipponAffineBlowup

variable {X : Scheme.{u}} [IsAffine X]

lemma specIdeal_comap_toSpec (I : X.IdealSheafData) :
    (IdealPullback.specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comap X.toSpecΓ = I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [IdealPullback.comap_top, IdealPullback.specIdeal_top, Scheme.toSpecΓ_appTop, Ideal.map_map]
  change Ideal.map ((Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom.comp
    (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom) _ = _
  simp only [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

lemma comap_isoSpec_inv (I : X.IdealSheafData) :
    I.comap X.isoSpec.inv = IdealPullback.specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩) := by
  conv_lhs => rw [← specIdeal_comap_toSpec I]
  rw [← Scheme.IdealSheafData.comap_comp]
  change (IdealPullback.specIdeal _).comap (X.isoSpec.inv ≫ X.isoSpec.hom) = _
  rw [Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

abbrev scheme (I : X.IdealSheafData) : Scheme.{u} :=
  ReesGrading.affineBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)

def projection (I : X.IdealSheafData) : scheme I ⟶ X :=
  ReesGrading.projection (I.ideal ⟨⊤, isAffineOpen_top X⟩) ≫ X.isoSpec.inv

theorem isBlowup (I : X.IdealSheafData) : Geometry.IsBlowup I (projection I) :=
  (PhilipponAffineBlowupCenter.isBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)).postIso
    X.isoSpec.symm I (comap_isoSpec_inv I)

theorem nativeInvertible (I : X.IdealSheafData) : (I.comap (projection I)).IsInvertible :=
  (PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mp (isBlowup I).1

instance projection_proper [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    IsProper (projection I) := by
  letI : IsNoetherianRing Γ(X, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  unfold projection
  infer_instance

end PhilipponAffineBlowup

end
end

/- PhilipponBlowup -/
section

/-!
Adapted from the verified public OAIQ068A020 definition bundle (Apache-2.0).
The relative gluing and its universal property are kept in universe u.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.PiExponentSeshadri
open OAI.PiExponentSeshadri.Geometry


namespace PhilipponBlowup

variable {X : Scheme.{u}}

abbrev baseCover (_I : X.IdealSheafData) : X.OpenCover :=
  Scheme.AffineZariskiSite.directedCover X

local instance localAffine (U : X.AffineZariskiSite) : IsAffine U.toOpens.toScheme := U.2

abbrev localCentre (I : X.IdealSheafData) (U : X.AffineZariskiSite) :
    U.toOpens.toScheme.IdealSheafData := I.comap U.toOpens.ι

lemma centre_transition (I : X.IdealSheafData) {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    (localCentre I V).comap ((baseCover I).trans h) = localCentre I U := by
  rw [localCentre, ← Scheme.IdealSheafData.comap_comp]
  change I.comap ((baseCover I).trans h ≫ (baseCover I).f V) = _
  rw [Scheme.Cover.trans_map]

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.PiExponentSeshadri.Geometry
variable {X : Scheme.{u}} (I : X.IdealSheafData)

abbrev localScheme (U : X.AffineZariskiSite) : Scheme.{u} :=
  PhilipponAffineBlowup.scheme (localCentre I U)

abbrev localProjection (U : X.AffineZariskiSite) : localScheme I U ⟶ U.toOpens.toScheme :=
  PhilipponAffineBlowup.projection (localCentre I U)

lemma local_isBlowup (U : X.AffineZariskiSite) :
    IsBlowup (localCentre I U) (localProjection I U) :=
  PhilipponAffineBlowup.isBlowup (localCentre I U)

lemma local_invertible {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    InvertiblePullbackIdeal (localCentre I V)
      (localProjection I U ≫ (baseCover I).trans h) := by
  apply (InvertibleLocal.invertible_congr (I' := localCentre I U)
    (f' := localProjection I U) ?_).mpr (local_isBlowup I U).1
  rw [Scheme.IdealSheafData.comap_comp, centre_transition]

def transition {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    localScheme I U ⟶ localScheme I V :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose

@[reassoc (attr := simp)]
lemma transition_projection {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    transition I h ≫ localProjection I V = localProjection I U ≫ (baseCover I).trans h :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose_spec.1

lemma transition_id (U : X.AffineZariskiSite) : transition I (𝟙 U) = 𝟙 (localScheme I U) := by
  apply (local_isBlowup I U).hom_ext (localProjection I U) (local_isBlowup I U).1
  · rw [transition_projection, Scheme.Cover.trans_id (baseCover I) U, Category.comp_id]
  · simp

lemma transition_comp {U V W : X.AffineZariskiSite} (h : U ⟶ V) (k : V ⟶ W) :
    transition I (h ≫ k) = transition I h ≫ transition I k := by
  apply (local_isBlowup I W).hom_ext _ (local_invertible I (h ≫ k))
  · exact transition_projection I (h ≫ k)
  · rw [Category.assoc, transition_projection, ← Category.assoc, transition_projection,
      Category.assoc, Scheme.Cover.trans_comp (baseCover I) h k]

def diagram : X.AffineZariskiSite ⥤ Scheme.{u} where
  obj := localScheme I
  map := transition I
  map_id := transition_id I
  map_comp := transition_comp I

def diagramMap : diagram I ⟶ (baseCover I).functorOfLocallyDirected where
  app := localProjection I
  naturality _ _ h := transition_projection I h

lemma diagramMap_equifibered : (diagramMap I).Equifibered := by
  intro U V h
  apply IsPullback.flip
  change IsPullback (localProjection I U) (transition I h)
    ((baseCover I).trans h) (localProjection I V)
  apply (local_isBlowup I V).baseChangeSquare ((baseCover I).trans h)
    (localProjection I U)
  · rw [centre_transition]
    exact local_isBlowup I U
  · exact transition_projection I h

def gluing : (baseCover I).RelativeGluingData where
  functor := diagram I
  natTrans := diagramMap I
  equifibered := diagramMap_equifibered I

abbrev scheme : Scheme.{u} := (gluing I).glued
abbrev projection : scheme I ⟶ X := (gluing I).toBase
abbrev cover : (scheme I).OpenCover := (gluing I).cover

@[reassoc (attr := simp)]
lemma cover_projection (U : X.AffineZariskiSite) :
    (cover I).f U ≫ projection I = localProjection I U ≫ U.toOpens.ι :=
  (gluing I).ι_toBase U

lemma local_pullback (U : X.AffineZariskiSite) :
    IsPullback (localProjection I U) ((cover I).f U) U.toOpens.ι (projection I) :=
  (gluing I).isPullback_natTrans_ι_toBase U

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.PiExponentSeshadri.Geometry
variable {X : Scheme.{u}} (I : X.IdealSheafData)

lemma projection_invertible : InvertiblePullbackIdeal I (projection I) := by
  apply InvertibleLocal.invertible_of_cover I (projection I) (cover I)
  intro U
  erw [cover_projection]
  apply (InvertibleLocal.invertible_congr
    (Scheme.IdealSheafData.comap_comp I (localProjection I U) U.toOpens.ι)).mpr
  exact (local_isBlowup I U).1

lemma test_invertible {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (U : X.AffineZariskiSite) :
    InvertiblePullbackIdeal (localCentre I U) (pullback.snd f U.toOpens.ι) := by
  apply (InvertibleLocal.invertible_congr (I' := I)
    (f' := pullback.fst f U.toOpens.ι ≫ f) ?_).mpr
  · exact InvertibleLocal.invertible_restrict_general I f hf (pullback.fst f U.toOpens.ι)
  · change ((I.comap U.toOpens.ι).comap (pullback.snd f U.toOpens.ι)) = _
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition]

lemma hom_ext {Y : Scheme.{u}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f)
    (g h : Y ⟶ scheme I) (hg : g ≫ projection I = f) (hh : h ≫ projection I = f) : g = h := by
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  apply C.hom_ext
  intro U
  let s := pullback.snd f U.toOpens.ι
  let t := pullback.fst f U.toOpens.ι
  have eg : s ≫ U.toOpens.ι = (t ≫ g) ≫ projection I := by
    rw [Category.assoc, hg]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  have eh : s ≫ U.toOpens.ι = (t ≫ h) ≫ projection I := by
    rw [Category.assoc, hh]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  let g' := (local_pullback I U).lift s (t ≫ g) eg
  let h' := (local_pullback I U).lift s (t ≫ h) eh
  have he : g' = h' := (local_isBlowup I U).hom_ext s (test_invertible I f hf U)
    ((local_pullback I U).lift_fst _ _ _) ((local_pullback I U).lift_fst _ _ _)
  have he' := congrArg (fun k : C.X U ⟶ localScheme I U => k ≫ (cover I).f U) he
  change t ≫ g = t ≫ h
  exact ((local_pullback I U).lift_snd s (t ≫ g) eg).symm.trans
    (he'.trans ((local_pullback I U).lift_snd s (t ≫ h) eh))

theorem universal {Y : Scheme.{u}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f) :
    ∃! h : Y ⟶ scheme I, h ≫ projection I = f := by
  classical
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  let l (U : X.AffineZariskiSite) : C.X U ⟶ localScheme I U :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose
  have hl (U : X.AffineZariskiSite) : l U ≫ localProjection I U = pullback.snd f U.toOpens.ι :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose_spec.1
  let g (U : C.I₀) : C.X U ⟶ scheme I := l U ≫ (cover I).f U
  have hg (U : C.I₀) : g U ≫ projection I = C.f U ≫ f := by
    dsimp only [g]
    exact (Category.assoc (l U) ((cover I).f U) (projection I)).trans
      ((congrArg (fun q : localScheme I U ⟶ X => l U ≫ q)
        (cover_projection I U)).trans
        ((Category.assoc (l U) (localProjection I U) U.toOpens.ι).symm.trans
          ((congrArg (fun q : C.X U ⟶ U.toOpens.toScheme => q ≫ U.toOpens.ι)
            (hl U)).trans (pullback.condition (f := f) (g := U.toOpens.ι)).symm)))
  have hcompat (U V : C.I₀) : pullback.fst (C.f U) (C.f V) ≫ g U =
      pullback.snd (C.f U) (C.f V) ≫ g V := by
    let j := pullback.fst (C.f U) (C.f V) ≫ C.f U
    apply hom_ext I (j ≫ f)
    · exact InvertibleLocal.invertible_restrict_general I f hf j
    · rw [Category.assoc, hg]
      rfl
    · rw [Category.assoc, hg]
      exact (pullback.condition_assoc f).symm
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U
  · intro h hh
    apply hom_ext I f hf h _ hh
    apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U

theorem isBlowup : IsBlowup I (projection I) :=
  ⟨projection_invertible I, fun _ f hf => universal I f hf⟩


theorem nativeInvertible : (I.comap (projection I)).IsInvertible :=
  (PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mp (projection_invertible I)

theorem existsUnique_lift {Y : Scheme.{u}} (f : Y ⟶ X) (hf : (I.comap f).IsInvertible) :
    ∃! h : Y ⟶ scheme I, h ≫ projection I = f :=
  universal I f ((PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mpr hf)

instance projection_proper [IsLocallyNoetherian X] : IsProper (projection I) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (baseCover I)
  intro U
  let he := (local_pullback I U).flip.isoPullback
  have hh : he.hom ≫ pullback.snd (projection I) U.toOpens.ι = localProjection I U :=
    (local_pullback I U).flip.isoPullback_hom_snd
  have h : IsProper (localProjection I U) := by infer_instance
  rw [← hh] at h
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsProper) he.hom _).mp h

instance source_isLocallyNoetherian [IsLocallyNoetherian X] : IsLocallyNoetherian (scheme I) :=
  LocallyOfFiniteType.isLocallyNoetherian (projection I)

end PhilipponBlowup

end
end

/- PhilipponBlowupSupport -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponentSeshadri

namespace PhilipponBlowupSupport

lemma support_specIdeal {R : Type u} [CommRing R] (I : Ideal R) :
    ((IdealPullback.specIdeal I).support : Set (Spec (.of R))) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [IdealPullback.specIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop,
    Spec_zeroLocus, ← Ideal.coe_comap]
  rw [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)]

lemma affine_preimage_support {X : Scheme.{u}} [IsAffine X]
    (K I : X.IdealSheafData) :
    (PhilipponAffineBlowup.projection K) ⁻¹' (I.support : Set X) =
      (ReesGrading.projection (K.ideal ⟨⊤, isAffineOpen_top X⟩)) ⁻¹'
        PrimeSpectrum.zeroLocus (I.ideal ⟨⊤, isAffineOpen_top X⟩ : Set Γ(X, ⊤)) := by
  have hs : X.isoSpec.inv ⁻¹' (I.support : Set X) =
      PrimeSpectrum.zeroLocus (I.ideal ⟨⊤, isAffineOpen_top X⟩ : Set Γ(X, ⊤)) := by
    rw [← support_specIdeal, ← PhilipponAffineBlowup.comap_isoSpec_inv]
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  change (X.isoSpec.inv ∘ ReesGrading.projection (K.ideal ⟨⊤, isAffineOpen_top X⟩)) ⁻¹' _ = _
  rw [Set.preimage_comp, hs]

lemma affine_preimage_difference {X : Scheme.{u}} [IsAffine X]
    (K I : X.IdealSheafData) :
    (PhilipponAffineBlowup.projection K) ⁻¹' Set.diff (I.support : Set X) K.support =
      (ReesGrading.projection (K.ideal ⟨⊤, isAffineOpen_top X⟩)) ⁻¹'
        Set.diff
          (PrimeSpectrum.zeroLocus (I.ideal ⟨⊤, isAffineOpen_top X⟩ : Set Γ(X, ⊤)))
          (PrimeSpectrum.zeroLocus (K.ideal ⟨⊤, isAffineOpen_top X⟩ : Set Γ(X, ⊤))) := by
  change Set.diff ((PhilipponAffineBlowup.projection K) ⁻¹' (I.support : Set X))
      ((PhilipponAffineBlowup.projection K) ⁻¹' (K.support : Set X)) = _
  rw [affine_preimage_support, affine_preimage_support]
  rfl

/-- Actual strict-transform supports restrict to an open chart by the
original comparison square and the original restricted ideals. -/
lemma strict_preimage {B L X U : Scheme.{u}} (π : B ⟶ X) (q : L ⟶ U)
    (i : L ⟶ B) [IsOpenImmersion i] (j : U ⟶ X) (h : i ≫ π = q ≫ j)
    (I K : X.IdealSheafData) :
    i ⁻¹' closure (π ⁻¹' Set.diff (I.support : Set X) K.support) =
      closure (q ⁻¹' Set.diff ((I.comap j).support : Set U) (K.comap j).support) := by
  rw [i.isOpenMap.preimage_closure_eq_closure_preimage i.continuous]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_diff, Scheme.IdealSheafData.support_comap,
    Closeds.coe_preimage]
  change (π (i x) ∈ I.support ∧ π (i x) ∉ K.support) ↔
    (j (q x) ∈ I.support ∧ j (q x) ∉ K.support)
  have hx : π (i x) = j (q x) :=
    congrArg (fun f : L ⟶ X => f x) h
  rw [hx]

end PhilipponBlowupSupport

end
end

/- PhilipponIdealStalkComparison -/
section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite


namespace PhilipponIdealStalkComparison

variable {X : Scheme.{u}}

lemma map_germ_of_le (I : X.IdealSheafData) {U V : X.affineOpens}
    (h : (U : X.Opens) ≤ V) (x : X) (hx : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ V x (h hx)).hom (I.ideal V) =
      Ideal.map (X.presheaf.germ U x hx).hom (I.ideal U) := by
  rw [← I.map_ideal h, Ideal.map_map, ← CommRingCat.hom_comp]
  have hg : X.presheaf.map (homOfLE h).op ≫ X.presheaf.germ U x hx =
      X.presheaf.germ V x (h hx) :=
    X.presheaf.germ_res' (homOfLE h).op x hx
  exact congrArg (fun f : Γ(X, V) ⟶ X.presheaf.stalk x =>
    Ideal.map f.hom (I.ideal V)) hg.symm

/-- The native stalk ideal of a quasi-coherent ideal datum is independent
of the affine neighborhood used to compute it. -/
theorem map_germ_eq (I : X.IdealSheafData) (U V : X.affineOpens)
    (x : X) (hxU : x ∈ (U : X.Opens)) (hxV : x ∈ (V : X.Opens)) :
    Ideal.map (X.presheaf.germ U x hxU).hom (I.ideal U) =
      Ideal.map (X.presheaf.germ V x hxV).hom (I.ideal V) := by
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ ((U : X.Opens) ⊓ V) from ⟨hxU, hxV⟩)
  let A : X.affineOpens := ⟨W, hW⟩
  have hAU : (A : X.Opens) ≤ U := fun z hz => (hWV hz).1
  have hAV : (A : X.Opens) ≤ V := fun z hz => (hWV hz).2
  exact (map_germ_of_le I hAU x hxW).trans (map_germ_of_le I hAV x hxW).symm

end PhilipponIdealStalkComparison

end
end

/- PhilipponSpecIdealCoordinates -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open OAI.PiExponentSeshadri

namespace PhilipponSpecIdealCoordinates

/-- The structural map on the coordinate ring of an affine chart. -/
def coordinates {R : CommRingCat.{u}} {X : Scheme.{u}} (g : X ⟶ Spec R)
    (V : X.affineOpens) : R ⟶ Γ(X, V) :=
  (Scheme.ΓSpecIso R).inv ≫ g.appLE ⊤ V.1 (by simp)

theorem map_coordinates {R : CommRingCat.{u}} {X : Scheme.{u}} (g : X ⟶ Spec R)
    (V : X.affineOpens) :
    Spec.map (coordinates g V) = V.2.fromSpec ≫ g := by
  rw [coordinates, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
    ← IsAffineOpen.fromSpec_top (X := Spec R)]
  exact IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) V.2 _

/-- Taking an ideal from the affine base and restricting it to a
chart is extension along the structural coordinate map. -/
theorem ideal_comap {R : CommRingCat.{u}} {X : Scheme.{u}} (g : X ⟶ Spec R)
    (V : X.affineOpens) (J : Ideal R) :
    ((IdealPullback.specIdeal J).comap g).ideal V = J.map (coordinates g V).hom := by
  rw [IdealPullback.comap_ideal _ g V ⟨⊤, isAffineOpen_top _⟩ (by simp),
    IdealPullback.specIdeal_top, Ideal.map_map]
  rfl

theorem specIdeal_mono {R : Type u} [CommRing R] {I J : Ideal R} (h : I ≤ J) :
    IdealPullback.specIdeal I ≤ IdealPullback.specIdeal J := by
  apply Scheme.IdealSheafData.le_of_isAffine
  rw [IdealPullback.specIdeal_top, IdealPullback.specIdeal_top]
  exact Ideal.map_mono h

theorem specIdeal_mul {R : Type u} [CommRing R] (I J : Ideal R) :
    IdealPullback.specIdeal (I * J) = IdealPullback.specIdeal I * IdealPullback.specIdeal J := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  change (IdealPullback.specIdeal (I * J)).ideal ⟨⊤, isAffineOpen_top _⟩ =
    (IdealPullback.specIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩ *
      (IdealPullback.specIdeal J).ideal ⟨⊤, isAffineOpen_top _⟩
  simp only [IdealPullback.specIdeal_top, Ideal.map_mul]

theorem coordinates_germ {R : CommRingCat.{u}} {X : Scheme.{u}}
    (g : X ⟶ Spec R) (V : X.affineOpens) (x : X) (hx : x ∈ V.1) :
    coordinates g V ≫ X.presheaf.germ V.1 x hx = Spec.preimage (X.fromSpecStalk x ≫ g) := by
  apply Spec.map_injective
  rw [Spec.map_comp, map_coordinates, Spec.map_preimage, ← Category.assoc,
    ← V.2.fromSpecStalk_eq_fromSpecStalk hx]
  rfl

/-- Coordinate extension of a base ideal along the chart and then to
a stalk of another scheme agrees with direct extension to the stalk. -/
theorem map_ideal_to_stalk {R : CommRingCat.{u}} {X Y : Scheme.{u}}
    (g : Y ⟶ Spec R) (h : X ⟶ Y) (V : Y.affineOpens) (x : X) (hx : h x ∈ V.1)
    (J : Ideal R) :
    (J.map (coordinates g V).hom).map
          ((Y.presheaf.germ V.1 (h x) hx) ≫ h.stalkMap x).hom =
      J.map (Spec.preimage (X.fromSpecStalk x ≫ h ≫ g)).hom := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Category.assoc, coordinates_germ]
  congr 1
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage,
    Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, Spec.map_preimage]

theorem coordinates_res {R : CommRingCat.{u}} {X : Scheme.{u}} (g : X ⟶ Spec R)
    (V W : X.affineOpens) (h : V.1 ≤ W.1) :
    coordinates g W ≫ X.presheaf.map (homOfLE h).op = coordinates g V := by
  simp only [coordinates, Category.assoc, Scheme.Hom.appLE_map]

theorem ideal_germ {R : CommRingCat.{u}} {X : Scheme.{u}}
    (g : X ⟶ Spec R) (V : X.affineOpens) (x : X) (hx : x ∈ V.1) (J : Ideal R) :
    (((IdealPullback.specIdeal J).comap g).ideal V).map (X.presheaf.germ V.1 x hx).hom =
      J.map (Spec.preimage (X.fromSpecStalk x ≫ g)).hom := by
  rw [ideal_comap, Ideal.map_map, ← CommRingCat.hom_comp, coordinates_germ]

end PhilipponSpecIdealCoordinates

end
end

/- PhilipponAdmissibleDenominators -/
section

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponAdmissibleDenominators

variable {R B : Type*} [CommRing R] [CommRing B] {ι : Type*}

/-- The common denominator ideal for the selected generators of an
affine algebra. -/
def denominators (f : R →+* B) (b : ι → B) : Ideal R where
  carrier := {a | ∀ i, ∃ c : R, f c = f a * b i}
  zero_mem' := by
    intro i
    exact ⟨0, by simp⟩
  add_mem' := by
    intro a a' ha ha' i
    obtain ⟨c, hc⟩ := ha i
    obtain ⟨c', hc'⟩ := ha' i
    exact ⟨c + c', by simp only [map_add, hc, hc', add_mul]⟩
  smul_mem' := by
    intro r a ha i
    obtain ⟨c, hc⟩ := ha i
    exact ⟨r * c, by simp only [smul_eq_mul, map_mul, hc, mul_assoc]⟩

/-- The numerator ideal contains the denominators, so both centres
are admissible wherever common denominators can be chosen to be units. -/
def centre (f : R →+* B) (b : ι → B) : Ideal R :=
  denominators f b ⊔ Ideal.span {c | ∃ i a, a ∈ denominators f b ∧ f c = f a * b i}

/-- Individual denominators away from the same prime can be combined
into a common denominator away from that prime. -/
theorem denominators_not_le [Fintype ι] (f : R →+* B) (b : ι → B)
    (P : Ideal R) [P.IsPrime]
    (h : ∀ i, ∃ a : R, a ∉ P ∧ ∃ c : R, f c = f a * b i) :
    ¬ denominators f b ≤ P := by
  classical
  choose a ha c hc using h
  let d := ∏ i, a i
  have hd : d ∈ denominators f b := by
    intro i
    let e := ∏ j ∈ Finset.univ.erase i, a j
    have he : e * a i = d := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
    exact ⟨e * c i, by rw [map_mul, hc, ← mul_assoc, ← map_mul, he]⟩
  have hdP : d ∉ P := by
    intro hmem
    rcases Ideal.IsPrime.prod_mem_iff.mp hmem with ⟨i, _, hi⟩
    exact ha i hi
  exact fun hle => hdP (hle hd)

theorem centre_not_le [Fintype ι] (f : R →+* B) (b : ι → B)
    (P : Ideal R) [P.IsPrime]
    (h : ∀ i, ∃ a : R, a ∉ P ∧ ∃ c : R, f c = f a * b i) :
    ¬ centre f b ≤ P :=
  fun hle => denominators_not_le f b P h (le_sup_left.trans hle)

/-- The numerator ideal and the denominator ideal have the same
extension to the algebra containing the generators. -/
theorem map_centre (f : R →+* B) (b : ι → B) :
    (centre f b).map f = (denominators f b).map f := by
  unfold centre
  rw [Ideal.map_sup, sup_eq_left]
  apply (Ideal.map_le_iff_le_comap).mpr
  apply Ideal.span_le.mpr
  rintro c ⟨i, a, ha, hc⟩
  change f c ∈ (denominators f b).map f
  rw [hc, mul_comm]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem f ha)

/-- On a common-denominator chart where the numerators belong to the
principal ideal generated by the same denominator, the whole affine
algebra embeds in the chart ring inside the common fraction field. -/
theorem adjoin_le_of_principal {K : Type*} [Field K] [Algebra R K]
    (b : ι → K) (S : Subalgebra R K) (a : R)
    (ha : a ∈ denominators (algebraMap R K) b) (hne : algebraMap R K a ≠ 0)
    (h : (centre (algebraMap R K) b).map (algebraMap R S) ≤
      Ideal.span {algebraMap R S a}) :
    Algebra.adjoin R (Set.range b) ≤ S := by
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := ha i
  have hcI : c ∈ centre (algebraMap R K) b :=
    Ideal.mem_sup_right (Ideal.subset_span ⟨i, a, ha, hc⟩)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (h (Ideal.mem_map_of_mem (algebraMap R S) hcI))
  have hzK : algebraMap R K c = algebraMap R K a * (z : K) :=
    congrArg (fun x : S => (x : K)) hz
  have hb : b i = (z : K) := mul_left_cancel₀ hne (hc.symm.trans hzK)
  rw [hb]
  exact z.property

end PhilipponAdmissibleDenominators


end

/- PhilipponAdmissibleAffineCentre -/
section

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace PhilipponAdmissibleAffineCentre

open PhilipponAdmissibleDenominators

/-- Adding a power of the ideal of the excluded boundary makes both
centres admissible while leaving their extensions to the source equal
to the original denominator ideal. -/
theorem exists_adjusted_centres {R B ι : Type*} [CommRing R] [CommRing B]
    (f : R →+* B) (b : ι → B) (C : Ideal R) (hC : C.FG)
    (h : ∀ P : Ideal B, P.IsPrime → (denominators f b).map f ≤ P → C.map f ≤ P) :
    ∃ n : ℕ, ((denominators f b) ⊔ C ^ n).map f = (denominators f b).map f ∧
      ((centre f b) ⊔ C ^ n).map f = (denominators f b).map f ∧
      ∀ P : Ideal R, P.IsPrime → ¬ C ≤ P →
        ¬ ((denominators f b) ⊔ C ^ n) * ((centre f b) ⊔ C ^ n) ≤ P := by
  have hrad : C.map f ≤ ((denominators f b).map f).radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf (fun P hP => h P hP.2 hP.1)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (hC.map f)
  have hpow : (C ^ n).map f ≤ (denominators f b).map f := by
    rwa [Ideal.map_pow]
  refine ⟨n, ?_, ?_, ?_⟩
  · rw [Ideal.map_sup, sup_eq_left.mpr hpow]
  · rw [Ideal.map_sup, map_centre, sup_eq_left.mpr hpow]
  · intro P hP hnot hle
    have hp : C ^ n ≤ P := by
      have hle₁ : C ^ n ≤ denominators f b ⊔ C ^ n := le_sup_right
      have hle₂ : C ^ n ≤ centre f b ⊔ C ^ n := le_sup_right
      exact hP.mul_le.mp ((mul_le_mul' hle₁ hle₂).trans hle) |>.elim id id
    apply hnot
    intro a ha
    exact hP.mem_of_pow_mem n (hp (Ideal.pow_mem_pow ha n))

/-- Equality with a principal invertible ideal is detected at a local
image point if the extended generator is nonzero in the source. -/
theorem eq_span_of_map_eq_span {R B : Type*} [CommRing R] [CommRing B] [IsDomain B]
    [IsLocalRing R] [IsLocalRing B] (f : R →+* B) [IsLocalHom f]
    (I : Ideal R) (a : R) (ha : f a ≠ 0)
    (hle : I ≤ Ideal.span {a}) (h : I.map f = Ideal.span {f a}) :
    I = Ideal.span {a} := by
  refine le_antisymm hle (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
  by_contra hnot
  have hsmall : I ≤ Ideal.span {a} * IsLocalRing.maximalIdeal R := by
    intro x hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hle hx)
    refine Ideal.mem_span_singleton_mul.mpr ⟨c, ?_, hc.symm⟩
    apply (IsLocalRing.mem_maximalIdeal c).mpr
    intro hunit
    obtain ⟨u, rfl⟩ := hunit
    apply hnot
    have hmul := I.mul_mem_left (↑u⁻¹ : R) hx
    rw [hc, ← mul_assoc, mul_comm (↑u⁻¹ : R) a, mul_assoc, Units.inv_mul, mul_one] at hmul
    exact hmul
  have hmap : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hmem : f a ∈ (Ideal.span {a} * IsLocalRing.maximalIdeal R).map f :=
    Ideal.map_mono hsmall (h.symm ▸ Ideal.subset_span (Set.mem_singleton (f a)))
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hmem
  obtain ⟨c, hc, he⟩ := Ideal.mem_span_singleton_mul.mp
    (mul_le_mul' le_rfl hmap hmem)
  have hc' : c = 1 := mul_left_cancel₀ ha (he.trans (mul_one _).symm)
  exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top (Ideal.eq_top_of_isUnit_mem _ (hc' ▸ hc) isUnit_one)

/-- If a family of numerators generates the principal ideal after
passing to a local domain, some original denominator already has a
unit coefficient there. -/
theorem exists_generator_away {R A L : Type*} [CommRing R] [CommRing A] [CommRing L]
    [IsLocalRing L] [IsDomain L] (f : R →+* A) (g : A →+* L)
    (J : Ideal R) (r : A) (hr : g r ≠ 0)
    (hle : J.map f ≤ Ideal.span {r}) (h : J.map (g.comp f) = Ideal.span {g r}) :
    ∃ d ∈ J, ∃ c : A, f d = r * c ∧ IsUnit (g c) := by
  by_contra hnot
  have hsmall : J.map (g.comp f) ≤ Ideal.span {g r} * IsLocalRing.maximalIdeal L := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro d hd
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hle (Ideal.mem_map_of_mem f hd))
    change g (f d) ∈ Ideal.span {g r} * IsLocalRing.maximalIdeal L
    refine Ideal.mem_span_singleton_mul.mpr ⟨g c, (IsLocalRing.mem_maximalIdeal _).mpr ?_, ?_⟩
    · intro hunit
      exact hnot ⟨d, hd, c, hc, hunit⟩
    · rw [hc, map_mul]
  have hm : g r ∈ Ideal.span {g r} * IsLocalRing.maximalIdeal L := by
    rw [h] at hsmall
    exact hsmall (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨c, hc, he⟩ := Ideal.mem_span_singleton_mul.mp hm
  have hc' : c = 1 := mul_left_cancel₀ hr (he.trans (mul_one _).symm)
  exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top
    (Ideal.eq_top_of_isUnit_mem _ (hc' ▸ hc) isUnit_one)

end PhilipponAdmissibleAffineCentre


end

/- PhilipponAffineDenominatorLift -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

namespace PhilipponAffineDenominatorLift

/-- Simultaneously clear denominators in two evaluations of the same
polynomial when the linear numerator relations agree. -/
theorem common_numerator {R B D ι : Type*}
    [CommRing R] [CommRing B] [CommRing D]
    (f : R →+* B) (g : R →+* D) (b : ι → B) (t : ι → D)
    (a : R) (c : ι → R)
    (hf : ∀ i, f (c i) = f a * b i) (hg : ∀ i, g (c i) = g a * t i)
    (P : MvPolynomial ι R) :
    ∃ n : ℕ, ∃ C : R, f C = (f a)^n * MvPolynomial.eval₂ f b P ∧
      g C = (g a)^n * MvPolynomial.eval₂ g t P := by
  induction P using MvPolynomial.induction_on with
  | C r => exact ⟨0, r, by simp⟩
  | add P Q hP hQ =>
    obtain ⟨n, p, hp, hp'⟩ := hP
    obtain ⟨m, q, hq, hq'⟩ := hQ
    refine ⟨n + m, a^m * p + a^n * q, ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, hp, hq, MvPolynomial.eval₂_add, pow_add]
      ring
    · simp only [map_add, map_mul, map_pow, hp', hq', MvPolynomial.eval₂_add, pow_add]
      ring
  | mul_X P i hP =>
    obtain ⟨n, p, hp, hp'⟩ := hP
    refine ⟨n + 1, p * c i, ?_, ?_⟩
    · simp only [map_mul, hp, hf, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, pow_succ]
      ring
    · simp only [map_mul, hp', hg, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, pow_succ]
      ring

/-- An injective finitely generated affine algebra maps to any domain
in which the selected denominators are nonzero and their numerators
are divisible by the same denominator. -/
theorem exists_lift {R B D ι : Type*} [CommRing R] [CommRing B] [CommRing D] [IsDomain D]
    (f : R →+* B) (g : R →+* D) (hf : Function.Injective f)
    (b : ι → B) (t : ι → D) (a : R) (c : ι → R)
    (hgen : Function.Surjective (MvPolynomial.eval₂Hom f b))
    (hfc : ∀ i, f (c i) = f a * b i) (hgc : ∀ i, g (c i) = g a * t i)
    (ha : g a ≠ 0) : ∃ h : B →+* D, h.comp f = g := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R D := g.toAlgebra
  let p : MvPolynomial ι R →ₐ[R] B := MvPolynomial.aeval b
  let q : MvPolynomial ι R →ₐ[R] D := MvPolynomial.aeval t
  have hker : RingHom.ker p.toRingHom ≤ RingHom.ker q.toRingHom := by
    intro P hP
    change MvPolynomial.eval₂ f b P = 0 at hP
    change MvPolynomial.eval₂ g t P = 0
    obtain ⟨n, C, hB, hD⟩ := common_numerator f g b t a c hfc hgc P
    have hC : C = 0 := hf (by rw [hB, hP, mul_zero, map_zero])
    rw [hC, map_zero] at hD
    exact (mul_eq_zero.mp hD.symm).resolve_left (pow_ne_zero _ ha)
  let h := AlgHom.liftOfSurjective p hgen q hker
  exact ⟨h.toRingHom, RingHom.ext h.commutes⟩

end PhilipponAffineDenominatorLift


end

/- PhilipponCartierSections -/
section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace


namespace PhilipponCartierSections

variable {X : Scheme.{u}}

abbrev res {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

lemma res_res {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (s : Γ(X, U)) :
    res k (res h s) = res (k.trans h) s := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom s = _
  rw [← Functor.map_comp]
  rfl

/-- A section regular at every germ is regular on the whole open set. -/
theorem regular_of_germs {U : X.Opens} (r : Γ(X, U))
    (hr : ∀ x (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    r ∈ nonZeroDivisors Γ(X, U) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro s hs
  apply TopCat.Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change X.presheaf.germ U x hx s = X.presheaf.germ U x hx 0
  rw [map_zero]
  apply (mem_nonZeroDivisors_iff_left.mp (hr x hx))
  simpa only [map_mul, map_zero] using congrArg (X.presheaf.germ U x hx) hs

lemma regular_res {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U))
    (hr : ∀ x (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    res h r ∈ nonZeroDivisors Γ(X, V) := by
  apply regular_of_germs
  intro x hx
  simpa only [res, TopCat.Presheaf.germ_res_apply] using hr x (h hx)

/-- Divisibility of two germs spreads to an actual quotient on a neighborhood. -/
lemma exists_local_quotient {U : X.Opens} (r t : Γ(X, U)) (x : X) (hx : x ∈ U)
    (hdiv : ∃ s : X.presheaf.stalk x,
      X.presheaf.germ U x hx r * s = X.presheaf.germ U x hx t) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ s : Γ(X, V), res hVU r * s = res hVU t := by
  obtain ⟨s, hs⟩ := hdiv
  obtain ⟨V, hVU, hxV, v, hv⟩ := X.presheaf.exists_le_germ_eq s hx
  have hg : X.presheaf.germ V x hxV (res hVU r * v) =
      X.presheaf.germ V x hxV (res hVU t) := by
    rw [map_mul, hv]
    simpa only [res, TopCat.Presheaf.germ_res_apply] using hs
  obtain ⟨W, hxW, j, k, heq⟩ := X.presheaf.germ_eq x hxV hxV _ _ hg
  have hjk : k = j := Subsingleton.elim _ _
  subst k
  refine ⟨W, j.le.trans hVU, hxW, res j.le v, ?_⟩
  have heq' : res j.le (res hVU r * v) = res j.le (res hVU t) := heq
  simpa only [map_mul, res_res] using heq'

/-- Germwise division by a regular section gives a unique actual section.
No affine, Noetherian, integral or reduced hypothesis on the scheme is used. -/
theorem existsUnique_quotient {U : X.Opens} (r t : Γ(X, U))
    (hr : ∀ x (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x))
    (hdiv : ∀ x (hx : x ∈ U), ∃ s : X.presheaf.stalk x,
      X.presheaf.germ U x hx r * s = X.presheaf.germ U x hx t) :
    ∃! s : Γ(X, U), r * s = t := by
  choose V hVU hxV sf hsf using fun x : U => exists_local_quotient r t x.1 x.2 (hdiv x.1 x.2)
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro x y
    change res (inf_le_left : V x ⊓ V y ≤ V x) (sf x) =
      res (inf_le_right : V x ⊓ V y ≤ V y) (sf y)
    apply (isRegular_iff_mem_nonZeroDivisors.mpr
      (regular_res (inf_le_left.trans (hVU x) : V x ⊓ V y ≤ U) r hr)).left
    have hx := congrArg (res (inf_le_left : V x ⊓ V y ≤ V x)) (hsf x)
    have hy := congrArg (res (inf_le_right : V x ⊓ V y ≤ V y)) (hsf y)
    simp only [map_mul, res_res] at hx hy
    exact hx.trans hy.symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V U (fun x => homOfLE (hVU x)) hcover sf hcompat
  change Γ(X, U) at s
  have hst : r * s = t := by
    apply X.sheaf.eq_of_locally_eq' V U (fun x => homOfLE (hVU x)) hcover
    intro x
    change res (hVU x) (r * s) = res (hVU x) t
    have hxs : res (hVU x) s = sf x := hs x
    rw [map_mul, hxs]
    exact hsf x
  refine ⟨s, hst, ?_⟩
  intro z hz
  exact (isRegular_iff_mem_nonZeroDivisors.mpr (regular_of_germs r hr)).left (hz.trans hst.symm)

end PhilipponCartierSections

end
end

/- PhilipponCrossingPointHom -/
section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial MvPolynomial.CrossingQuotient
open AlgebraicGeometry CategoryTheory
namespace PhilipponCrossingPointHom
variable {R : Type u} [CommRing R]
variable {A : Type*} [CommRing A]


lemma mk_C_eq_algebraMap (s : R) (r : R) : mk s (C r) = algebraMap R _ r :=
  (mk s).commutes r

theorem eval₂Hom_rel (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    eval₂Hom f ![a, b] (X 0 * X 1 - C s : MvPolynomial (Fin 2) R) = 0 := by
  rw [map_sub, map_mul, eval₂Hom_X', eval₂Hom_X', eval₂Hom_C]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h, sub_self]

noncomputable def pointHom (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    CrossingQuotient R s →+* A :=
  Ideal.Quotient.lift (Ideal.span {(X 0 * X 1 - C s : MvPolynomial (Fin 2) R)}) (eval₂Hom f ![a, b])
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, eval₂Hom_rel s f a b h, mul_zero])

theorem pointHom_mk (s : R) (f : R →+* A) (a b : A) (h : a * b = f s)
    (p : MvPolynomial (Fin 2) R) :
    pointHom s f a b h (mk s p) = eval₂Hom f ![a, b] p := rfl

theorem pointHom_algebraMap (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) (w : R) :
    pointHom s f a b h (algebraMap R _ w) = f w := by
  rw [← mk_C_eq_algebraMap, pointHom_mk, eval₂Hom_C]

theorem pointHom_U (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    pointHom s f a b h (U s) = a := by
  change pointHom s f a b h (mk s (X 0)) = a
  rw [pointHom_mk, eval₂Hom_X']
  rfl

theorem pointHom_V (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    pointHom s f a b h (V s) = b := by
  change pointHom s f a b h (mk s (X 1)) = b
  rw [pointHom_mk, eval₂Hom_X']
  rfl

theorem ringHom_ext {s : R} {f g : CrossingQuotient R s →+* A}
    (hR : ∀ w : R, f (algebraMap R _ w) = g (algebraMap R _ w))
    (hU : f (U s) = g (U s)) (hV : f (V s) = g (V s)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    change f (mk s (C w)) = g (mk s (C w))
    rw [mk_C_eq_algebraMap]
    exact hR w
  · intro j
    fin_cases j
    · exact hU
    · exact hV


lemma specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]


end PhilipponCrossingPointHom
end
end

/- PhilipponNodeFactorCharts -/
section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponNodeFactorCharts

variable {R : Type u} [CommRing R]

lemma chart_ext {t : R} {A : Type*} [CommRing A] [Algebra R A]
    {f g : CrossingQuotient R t →ₐ[R] A}
    (hU : f (U t) = g (U t)) (hV : f (V t) = g (V t)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hU
  · exact hV

def toLeft (a b : R) : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R a :=
  lift (a * b) (U a) (algebraMap R _ b * V a) (by
    rw [mul_left_comm, U_mul_V, map_mul]
    ring)

def toRight (a b : R) : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R b :=
  lift (a * b) (algebraMap R _ a * U b) (V b) (by
    rw [mul_assoc, U_mul_V, map_mul])

@[simp] lemma toLeft_U (a b : R) : toLeft a b (U (a * b)) = U a := lift_U _ _ _ _
@[simp] lemma toLeft_V (a b : R) :
    toLeft a b (V (a * b)) = algebraMap R _ b * V a := lift_V _ _ _ _
@[simp] lemma toRight_U (a b : R) :
    toRight a b (U (a * b)) = algebraMap R _ a * U b := lift_U _ _ _ _
@[simp] lemma toRight_V (a b : R) : toRight a b (V (a * b)) = V b := lift_V _ _ _ _

abbrev LeftOverlap (a : R) := Localization.Away (V a)
abbrev RightOverlap (b : R) := Localization.Away (U b)

def rightToLeftOverlap (a b : R) : CrossingQuotient R b →ₐ[R] LeftOverlap a :=
  lift b (IsLocalization.Away.invSelf (V a))
    (algebraMap R _ b * algebraMap (CrossingQuotient R a) _ (V a)) (by
      rw [mul_left_comm, mul_comm (IsLocalization.Away.invSelf (V a)),
        IsLocalization.Away.mul_invSelf, mul_one])

def leftToRightOverlap (a b : R) : CrossingQuotient R a →ₐ[R] RightOverlap b :=
  lift a (algebraMap R _ a * algebraMap (CrossingQuotient R b) _ (U b))
    (IsLocalization.Away.invSelf (U b)) (by
      rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one])

lemma leftToRight_isUnit (a b : R) : IsUnit ((leftToRightOverlap a b).toRingHom (V a)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, leftToRightOverlap, lift_V]
  exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (U b))

lemma rightToLeft_isUnit (a b : R) : IsUnit ((rightToLeftOverlap a b).toRingHom (U b)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rightToLeftOverlap, lift_U]
  exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (V a))

def overlapToRightRing (a b : R) : LeftOverlap a →+* RightOverlap b :=
  IsLocalization.Away.lift (S := LeftOverlap a) (V a)
    (g := (leftToRightOverlap a b).toRingHom) (leftToRight_isUnit a b)

def overlapToLeftRing (a b : R) : RightOverlap b →+* LeftOverlap a :=
  IsLocalization.Away.lift (S := RightOverlap b) (U b)
    (g := (rightToLeftOverlap a b).toRingHom) (rightToLeft_isUnit a b)

lemma overlapToRightRing_algebraMap (a b : R) (z : CrossingQuotient R a) :
    overlapToRightRing a b (algebraMap _ _ z) = leftToRightOverlap a b z :=
  IsLocalization.Away.lift_eq (S := LeftOverlap a) _ (leftToRight_isUnit a b) z

lemma overlapToLeftRing_algebraMap (a b : R) (z : CrossingQuotient R b) :
    overlapToLeftRing a b (algebraMap _ _ z) = rightToLeftOverlap a b z :=
  IsLocalization.Away.lift_eq (S := RightOverlap b) _ (rightToLeft_isUnit a b) z

def overlapToRight (a b : R) : LeftOverlap a →ₐ[R] RightOverlap b :=
  { overlapToRightRing a b with
    commutes' := fun r => by
      change overlapToRightRing a b (algebraMap R (LeftOverlap a) r) = _
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a) r]
      rw [overlapToRightRing_algebraMap]
      exact (leftToRightOverlap a b).commutes r }

def overlapToLeft (a b : R) : RightOverlap b →ₐ[R] LeftOverlap a :=
  { overlapToLeftRing a b with
    commutes' := fun r => by
      change overlapToLeftRing a b (algebraMap R (RightOverlap b) r) = _
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R b) (RightOverlap b) r]
      rw [overlapToLeftRing_algebraMap]
      exact (rightToLeftOverlap a b).commutes r }

@[simp] lemma overlapToRight_algebraMap (a b : R) (z : CrossingQuotient R a) :
    overlapToRight a b (algebraMap _ _ z) = leftToRightOverlap a b z :=
  overlapToRightRing_algebraMap a b z

@[simp] lemma overlapToLeft_algebraMap (a b : R) (z : CrossingQuotient R b) :
    overlapToLeft a b (algebraMap _ _ z) = rightToLeftOverlap a b z :=
  overlapToLeftRing_algebraMap a b z

lemma overlapToRight_inv (a b : R) :
    overlapToRight a b (IsLocalization.Away.invSelf (V a)) =
      algebraMap (CrossingQuotient R b) (RightOverlap b) (U b) := by
  have h := congrArg (overlapToRight a b) (IsLocalization.Away.mul_invSelf (V a))
  simp only [map_mul, overlapToRight_algebraMap, leftToRightOverlap, lift_V, map_one] at h
  have h' := IsLocalization.Away.mul_invSelf (S := RightOverlap b) (U b)
  linear_combination (algebraMap (CrossingQuotient R b) (RightOverlap b) (U b)) * h -
    (overlapToRight a b (IsLocalization.Away.invSelf (V a))) * h'

lemma overlapToLeft_inv (a b : R) :
    overlapToLeft a b (IsLocalization.Away.invSelf (U b)) =
      algebraMap (CrossingQuotient R a) (LeftOverlap a) (V a) := by
  have h := congrArg (overlapToLeft a b) (IsLocalization.Away.mul_invSelf (U b))
  simp only [map_mul, overlapToLeft_algebraMap, rightToLeftOverlap, lift_U, map_one] at h
  have h' := IsLocalization.Away.mul_invSelf (S := LeftOverlap a) (V a)
  linear_combination (algebraMap (CrossingQuotient R a) (LeftOverlap a) (V a)) * h -
    (overlapToLeft a b (IsLocalization.Away.invSelf (U b))) * h'

lemma overlap_left_right (a b : R) :
    (overlapToLeft a b).comp (overlapToRight a b) = AlgHom.id R (LeftOverlap a) := by
  have h : ((overlapToLeft a b).comp (overlapToRight a b)).comp
      (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a)) =
      IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a) := by
    apply chart_ext
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToRight_algebraMap,
        leftToRightOverlap, lift_U, map_mul, AlgHom.commutes, overlapToLeft_algebraMap,
        rightToLeftOverlap, lift_U]
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a) a,
        ← U_mul_V, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToRight_algebraMap,
        leftToRightOverlap, lift_V, overlapToLeft_inv]
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (V a)) (S := LeftOverlap a)
  exact RingHom.ext fun z => congrArg (fun f : CrossingQuotient R a →ₐ[R] LeftOverlap a => f z) h

lemma overlap_right_left (a b : R) :
    (overlapToRight a b).comp (overlapToLeft a b) = AlgHom.id R (RightOverlap b) := by
  have h : ((overlapToRight a b).comp (overlapToLeft a b)).comp
      (IsScalarTower.toAlgHom R (CrossingQuotient R b) (RightOverlap b)) =
      IsScalarTower.toAlgHom R (CrossingQuotient R b) (RightOverlap b) := by
    apply chart_ext
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToLeft_algebraMap,
        rightToLeftOverlap, lift_U, overlapToRight_inv]
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToLeft_algebraMap,
        rightToLeftOverlap, lift_V, map_mul, AlgHom.commutes, overlapToRight_algebraMap,
        leftToRightOverlap, lift_V]
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R b) (RightOverlap b) b,
        ← U_mul_V, map_mul]
      rw [mul_comm (algebraMap _ _ (U b)), mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (U b)) (S := RightOverlap b)
  exact RingHom.ext fun z => congrArg (fun f : CrossingQuotient R b →ₐ[R] RightOverlap b => f z) h

def overlapEquiv (a b : R) : LeftOverlap a ≃ₐ[R] RightOverlap b :=
  AlgEquiv.ofAlgHom (overlapToRight a b) (overlapToLeft a b)
    (overlap_right_left a b) (overlap_left_right a b)

lemma charts_agree_on_overlap (a b : R) :
    (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a)).comp (toLeft a b) =
      (rightToLeftOverlap a b).comp (toRight a b) := by
  apply chart_ext
  · simp only [AlgHom.comp_apply, toLeft_U, toRight_U, map_mul, AlgHom.commutes,
      rightToLeftOverlap, lift_U, IsScalarTower.coe_toAlgHom']
    symm
    rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a) a,
      ← U_mul_V, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
  · simp only [AlgHom.comp_apply, toLeft_V, toRight_V, map_mul, AlgHom.commutes,
      rightToLeftOverlap, lift_V, IsScalarTower.coe_toAlgHom']

end PhilipponNodeFactorCharts

end
end

/- PhilipponNodeCartierLocalLift -/
section

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open MvPolynomial MvPolynomial.CrossingQuotient


namespace PhilipponNodeCartierLocalLift

variable {A : Type v} [CommRing A]

lemma cancel_regular {r x y : A} (hr : r ∈ nonZeroDivisors A)
    (h : r * x = r * y) : x = y := by
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_left.mp hr) (x - y)
  rw [mul_sub, h, sub_self]

/-- A two-generated effective Cartier ideal in a local ring is generated by one
of its two specified generators. The chosen generator is a non-zero-divisor. -/
lemma regular_generator_or [IsLocalRing A] {u a r : A}
    (hI : Ideal.span ({u, a} : Set A) = Ideal.span ({r} : Set A))
    (hr : r ∈ nonZeroDivisors A) :
    (u ∈ nonZeroDivisors A ∧ u ∣ a) ∨
      (a ∈ nonZeroDivisors A ∧ a ∣ u) := by
  have hu : u ∈ Ideal.span ({r} : Set A) := by
    rw [← hI]
    exact Ideal.subset_span (by simp)
  have ha : a ∈ Ideal.span ({r} : Set A) := by
    rw [← hI]
    exact Ideal.subset_span (by simp)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hu
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp ha
  have hrI : r ∈ Ideal.span ({u, a} : Set A) := by
    rw [hI]
    exact Ideal.subset_span (by simp)
  obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.mp hrI
  have hst : p * s + q * t = 1 := by
    apply cancel_regular hr
    calc
      r * (p * s + q * t) = p * u + q * a := by rw [hs, ht]; ring
      _ = r * 1 := by simpa using hpq
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hst with hps | hqt
  · have hsunit : IsUnit s := isUnit_of_mul_isUnit_right hps
    left
    refine ⟨?_, ?_⟩
    · rw [hs]
      exact mul_mem_nonZeroDivisors.mpr ⟨hr, hsunit.mem_nonZeroDivisors⟩
    · obtain ⟨sunit, rfl⟩ := hsunit
      refine ⟨(sunit⁻¹ : Aˣ) * t, ?_⟩
      rw [hs, ht]
      simp [mul_assoc]
  · have htunit : IsUnit t := isUnit_of_mul_isUnit_right hqt
    right
    refine ⟨?_, ?_⟩
    · rw [ht]
      exact mul_mem_nonZeroDivisors.mpr ⟨hr, htunit.mem_nonZeroDivisors⟩
    · obtain ⟨tunit, rfl⟩ := htunit
      refine ⟨(tunit⁻¹ : Aˣ) * s, ?_⟩
      rw [hs, ht]
      simp [mul_assoc]

variable {R : Type u} [CommRing R]
open PhilipponNodeFactorCharts PhilipponCrossingPointHom

/-- In the chart where the pullback of `u` generates the Cartier ideal,
the map to the left nodal chart exists and is unique. -/
lemma existsUnique_left_lift (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (hu : ψ (U (a * b)) ∈ nonZeroDivisors A)
    (hdiv : ψ (U (a * b)) ∣ ψ (algebraMap R _ a)) :
    ∃! φ : CrossingQuotient R a →+* A,
      φ.comp (toLeft a b).toRingHom = ψ := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hρ (r : R) : ρ r = ψ (algebraMap R _ r) := rfl
  obtain ⟨z, hz⟩ := hdiv
  have hrel : ψ (U (a * b)) * z = ρ a := hz.symm
  have hprod : ψ (U (a * b)) * ψ (V (a * b)) = ρ a * ρ b := by
    rw [← map_mul, U_mul_V, ← hρ, map_mul]
  have hbz : ρ b * z = ψ (V (a * b)) := by
    apply cancel_regular hu
    calc
      ψ (U (a * b)) * (ρ b * z) = (ψ (U (a * b)) * z) * ρ b := by ring
      _ = ψ (U (a * b)) * ψ (V (a * b)) := by rw [hrel, hprod]
  refine ⟨pointHom a ρ (ψ (U (a * b))) z hrel, ?_, ?_⟩
  · apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      change pointHom a ρ _ _ hrel (toLeft a b (algebraMap R _ r)) = _
      rw [AlgHom.commutes, pointHom_algebraMap, hρ]
    · change pointHom a ρ _ _ hrel (toLeft a b (U (a * b))) = _
      rw [toLeft_U, pointHom_U]
    · change pointHom a ρ _ _ hrel (toLeft a b (V (a * b))) = _
      rw [toLeft_V, map_mul, pointHom_algebraMap, pointHom_V, hbz]
  · intro φ hφ
    have hφR (r : R) : φ (algebraMap R _ r) = ρ r := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (algebraMap R _ r)) hφ
      change φ (toLeft a b (algebraMap R _ r)) = _ at h
      rw [AlgHom.commutes] at h
      exact h
    have hφU : φ (U a) = ψ (U (a * b)) := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (U (a * b))) hφ
      change φ (toLeft a b (U (a * b))) = _ at h
      rwa [toLeft_U] at h
    apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      rw [pointHom_algebraMap]
      exact hφR r
    · rw [pointHom_U]
      exact hφU
    · rw [pointHom_V]
      apply cancel_regular hu
      calc
        ψ (U (a * b)) * φ (V a) = φ (U a) * φ (V a) :=
          congrArg (fun t : A => t * φ (V a)) hφU.symm
        _ = φ (U a * V a) := (map_mul φ _ _).symm
        _ = ρ a := by rw [U_mul_V, hφR]
        _ = ψ (U (a * b)) * z := hrel.symm

/-- In the chart where the pullback of `a` generates the Cartier ideal,
the map to the right nodal chart exists and is unique. -/
lemma existsUnique_right_lift (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (ha : ψ (algebraMap R _ a) ∈ nonZeroDivisors A)
    (hdiv : ψ (algebraMap R _ a) ∣ ψ (U (a * b))) :
    ∃! φ : CrossingQuotient R b →+* A,
      φ.comp (toRight a b).toRingHom = ψ := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hρ (r : R) : ρ r = ψ (algebraMap R _ r) := rfl
  obtain ⟨w, hw⟩ := hdiv
  have hprod : ψ (U (a * b)) * ψ (V (a * b)) = ρ a * ρ b := by
    rw [← map_mul, U_mul_V, ← hρ, map_mul]
  have hrel : w * ψ (V (a * b)) = ρ b := by
    apply cancel_regular ha
    calc
      ψ (algebraMap R _ a) * (w * ψ (V (a * b))) =
          ψ (U (a * b)) * ψ (V (a * b)) := by rw [← mul_assoc, ← hw]
      _ = ψ (algebraMap R _ a) * ρ b := hprod
  refine ⟨pointHom b ρ w (ψ (V (a * b))) hrel, ?_, ?_⟩
  · apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      change pointHom b ρ _ _ hrel (toRight a b (algebraMap R _ r)) = _
      rw [AlgHom.commutes, pointHom_algebraMap, hρ]
    · change pointHom b ρ _ _ hrel (toRight a b (U (a * b))) = _
      rw [toRight_U, map_mul, pointHom_algebraMap, pointHom_U]
      exact hw.symm
    · change pointHom b ρ _ _ hrel (toRight a b (V (a * b))) = _
      rw [toRight_V, pointHom_V]
  · intro φ hφ
    have hφR (r : R) : φ (algebraMap R _ r) = ρ r := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (algebraMap R _ r)) hφ
      change φ (toRight a b (algebraMap R _ r)) = _ at h
      rw [AlgHom.commutes] at h
      exact h
    have hφV : φ (V b) = ψ (V (a * b)) := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (V (a * b))) hφ
      change φ (toRight a b (V (a * b))) = _ at h
      rwa [toRight_V] at h
    have hφU : ρ a * φ (U b) = ψ (U (a * b)) := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (U (a * b))) hφ
      change φ (toRight a b (U (a * b))) = _ at h
      rwa [toRight_U, map_mul, hφR] at h
    apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      rw [pointHom_algebraMap]
      exact hφR r
    · rw [pointHom_U]
      apply cancel_regular ha
      calc
        ψ (algebraMap R _ a) * φ (U b) = ψ (U (a * b)) := hφU
        _ = ψ (algebraMap R _ a) * w := hw
    · rw [pointHom_V]
      exact hφV

/-- Effective Cartier pullback of `(u,a)` gives a unique factorization through
at least one of the two specified affine charts of the actual nodal model. -/
theorem exists_unique_chart_lift [IsLocalRing A] (a b : R)
    (ψ : CrossingQuotient R (a * b) →+* A) (r : A)
    (hI : Ideal.span ({ψ (U (a * b)), ψ (algebraMap R _ a)} : Set A) =
      Ideal.span ({r} : Set A)) (hr : r ∈ nonZeroDivisors A) :
    (∃! φ : CrossingQuotient R a →+* A, φ.comp (toLeft a b).toRingHom = ψ) ∨
      (∃! φ : CrossingQuotient R b →+* A, φ.comp (toRight a b).toRingHom = ψ) := by
  rcases regular_generator_or hI hr with ⟨hu, hdiv⟩ | ⟨ha, hdiv⟩
  · exact Or.inl (existsUnique_left_lift a b ψ hu hdiv)
  · exact Or.inr (existsUnique_right_lift a b ψ ha hdiv)

/-- Two affine lifts over a Cartier generator meet in the actual localized
overlap, with both ring-map equations. No reducedness hypothesis is needed. -/
lemma chart_lifts_overlap (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (hu : ψ (U (a * b)) ∈ nonZeroDivisors A)
    (φL : CrossingQuotient R a →+* A) (φR : CrossingQuotient R b →+* A)
    (hL : φL.comp (toLeft a b).toRingHom = ψ)
    (hR : φR.comp (toRight a b).toRingHom = ψ) :
    ∃ ell : LeftOverlap a →+* A,
      ell.comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)) = φL ∧
      ell.comp (rightToLeftOverlap a b).toRingHom = φR := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hφLR (r : R) : φL (algebraMap R _ r) = ρ r := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (algebraMap R _ r)) hL
    change φL (toLeft a b (algebraMap R _ r)) = _ at h
    rw [AlgHom.commutes] at h
    exact h
  have hφRR (r : R) : φR (algebraMap R _ r) = ρ r := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (algebraMap R _ r)) hR
    change φR (toRight a b (algebraMap R _ r)) = _ at h
    rw [AlgHom.commutes] at h
    exact h
  have hφLU : φL (U a) = ψ (U (a * b)) := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (U (a * b))) hL
    change φL (toLeft a b (U (a * b))) = _ at h
    rwa [toLeft_U] at h
  have hleft : ψ (U (a * b)) * φL (V a) = ρ a := by
    calc
      ψ (U (a * b)) * φL (V a) = φL (U a) * φL (V a) :=
        congrArg (fun t : A => t * φL (V a)) hφLU.symm
      _ = φL (U a * V a) := (map_mul φL _ _).symm
      _ = ρ a := by rw [U_mul_V, hφLR]
  have hright : ρ a * φR (U b) = ψ (U (a * b)) := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (U (a * b))) hR
    change φR (toRight a b (U (a * b))) = _ at h
    rwa [toRight_U, map_mul, hφRR] at h
  have hinv : φL (V a) * φR (U b) = 1 := by
    apply cancel_regular hu
    calc
      ψ (U (a * b)) * (φL (V a) * φR (U b)) =
          (ψ (U (a * b)) * φL (V a)) * φR (U b) := (mul_assoc _ _ _).symm
      _ = ψ (U (a * b)) * 1 := by rw [hleft, hright, mul_one]
  have hz : IsUnit (φL (V a)) := IsUnit.of_mul_eq_one _ hinv
  let ell : LeftOverlap a →+* A := IsLocalization.Away.lift (V a) (g := φL) hz
  have hellL : ell.comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)) = φL := by
    apply RingHom.ext
    intro x
    exact IsLocalization.Away.lift_eq (V a) hz x
  have hcharts :
      (algebraMap (CrossingQuotient R a) (LeftOverlap a)).comp (toLeft a b).toRingHom =
        (rightToLeftOverlap a b).toRingHom.comp (toRight a b).toRingHom :=
    congrArg AlgHom.toRingHom (charts_agree_on_overlap a b)
  have hellR : (ell.comp (rightToLeftOverlap a b).toRingHom).comp
      (toRight a b).toRingHom = ψ := by
    calc
      _ = ell.comp ((rightToLeftOverlap a b).toRingHom.comp (toRight a b).toRingHom) := rfl
      _ = ell.comp ((algebraMap (CrossingQuotient R a) (LeftOverlap a)).comp
          (toLeft a b).toRingHom) := by rw [hcharts]
      _ = φL.comp (toLeft a b).toRingHom := by rw [← RingHom.comp_assoc, hellL]
      _ = ψ := hL
  have ha : ψ (algebraMap R _ a) ∈ nonZeroDivisors A :=
    (mul_mem_nonZeroDivisors.mp (hright.symm ▸ hu)).1
  have hdiv : ψ (algebraMap R _ a) ∣ ψ (U (a * b)) := ⟨φR (U b), hright.symm⟩
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_right_lift a b ψ ha hdiv
  exact ⟨ell, hellL, (huniq _ hellR).trans (huniq _ hR).symm⟩

end PhilipponNodeCartierLocalLift

end
end

/- PhilipponCartierLocalGenerator -/
section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PhilipponCartierSections


namespace PhilipponCartierLocalGenerator

variable {X : Scheme.{u}} {U : X.Opens}

lemma regular_germs_of_affine (hU : IsAffineOpen U) (r : Γ(X, U))
    (hr : r ∈ nonZeroDivisors Γ(X, U)) :
    ∀ x (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  intro x hx
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  haveI := hU.isLocalization_stalk (⟨x, hx⟩ : U)
  change algebraMap Γ(X, U) (X.presheaf.stalk x) r ∈ nonZeroDivisors (X.presheaf.stalk x)
  exact IsLocalization.nonZeroDivisors_le_comap
    (hU.primeIdealOf (⟨x, hx⟩ : U)).asIdeal.primeCompl (X.presheaf.stalk x) hr

/-- A regular divisor relation at one germ spreads to regular actual
sections on an affine neighborhood on a germ-injective scheme. -/
lemma exists_regular_neighborhood [X.IsGermInjective] (r t : Γ(X, U))
    (x : X) (hx : x ∈ U)
    (hr : X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x))
    (hdiv : X.presheaf.germ U x hx r ∣ X.presheaf.germ U x hx t) :
    ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧ IsAffineOpen W ∧
      (∀ y (hy : y ∈ W), X.presheaf.germ W y hy (res hWU r) ∈
        nonZeroDivisors (X.presheaf.stalk y)) ∧
      ∃ c : Γ(X, W), res hWU r * c = res hWU t := by
  obtain ⟨c, hc⟩ := hdiv
  obtain ⟨V, hVU, hxV, v, hv⟩ := exists_local_quotient r t x hx ⟨c, hc.symm⟩
  obtain ⟨W, hxW, hW, hWV, hginj⟩ := X.exists_le_and_germ_injective x V hxV
  have hrW : res (hWV.trans hVU) r ∈ nonZeroDivisors Γ(X, W) := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    apply hginj
    rw [map_zero]
    have hr' : X.presheaf.germ W x hxW (res (hWV.trans hVU) r) ∈
        nonZeroDivisors (X.presheaf.stalk x) := by
      simpa only [res, TopCat.Presheaf.germ_res_apply] using hr
    apply mem_nonZeroDivisors_iff_left.mp hr'
    simpa only [map_mul, map_zero] using congrArg (X.presheaf.germ W x hxW) ha
  refine ⟨W, hWV.trans hVU, hxW, hW, regular_germs_of_affine hW _ hrW, res hWV v, ?_⟩
  simpa only [map_mul, res_res] using congrArg (res hWV) hv

/-- A two-generated Cartier ideal in one stalk gives an actual regular
local equation on a whole affine neighborhood, with the specified ideal
identity at every point of that neighborhood. -/
theorem exists_local_generator [X.IsGermInjective] (r t : Γ(X, U))
    (x : X) (hx : x ∈ U)
    (hCartier : ∃ a : X.presheaf.stalk x,
      Ideal.span ({X.presheaf.germ U x hx r, X.presheaf.germ U x hx t} :
        Set (X.presheaf.stalk x)) = Ideal.span ({a} : Set (X.presheaf.stalk x)) ∧
      a ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧ IsAffineOpen W ∧ ∃ e : Γ(X, W),
      (∀ y (hy : y ∈ W), X.presheaf.germ W y hy e ∈ nonZeroDivisors (X.presheaf.stalk y)) ∧
      ∀ y (hy : y ∈ W),
        Ideal.span ({X.presheaf.germ W y hy e} : Set (X.presheaf.stalk y)) =
          Ideal.span ({X.presheaf.germ U y (hWU hy) r,
            X.presheaf.germ U y (hWU hy) t} : Set (X.presheaf.stalk y)) := by
  obtain ⟨a, ha, hreg⟩ := hCartier
  rcases PhilipponNodeCartierLocalLift.regular_generator_or ha hreg with ⟨hr, hrt⟩ | ⟨ht, htr⟩
  · obtain ⟨W, hWU, hxW, hW, hregular, c, hc⟩ := exists_regular_neighborhood r t x hx hr hrt
    refine ⟨W, hWU, hxW, hW, res hWU r, hregular, ?_⟩
    intro y hy
    have hI : Ideal.span ({res hWU r, res hWU t} : Set Γ(X, W)) =
        Ideal.span ({res hWU r} : Set Γ(X, W)) :=
      Ideal.span_pair_eq_span_left_iff_dvd.mpr ⟨c, hc.symm⟩
    have hm := congrArg (Ideal.map (X.presheaf.germ W y hy).hom) hI.symm
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      res, TopCat.Presheaf.germ_res_apply] using hm
  · obtain ⟨W, hWU, hxW, hW, hregular, c, hc⟩ := exists_regular_neighborhood t r x hx ht htr
    refine ⟨W, hWU, hxW, hW, res hWU t, hregular, ?_⟩
    intro y hy
    have hI : Ideal.span ({res hWU r, res hWU t} : Set Γ(X, W)) =
        Ideal.span ({res hWU t} : Set Γ(X, W)) :=
      Ideal.span_pair_eq_span_right_iff_dvd.mpr ⟨c, hc.symm⟩
    have hm := congrArg (Ideal.map (X.presheaf.germ W y hy).hom) hI.symm
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      res, TopCat.Presheaf.germ_res_apply] using hm

end PhilipponCartierLocalGenerator

end
end

/- PhilipponFlatteningDenominatorChart -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open OAI.PiExponentSeshadri
open PhilipponSpecIdealCoordinates PhilipponAdmissibleDenominators

namespace PhilipponFlatteningDenominatorChart

/-- If the numerator centre is invertible and its extension agrees
with the denominator ideal on the source, near each image point it
has an actual generator from the original denominator ideal. -/
theorem exists_chart {R : CommRingCat.{u}} {X Y : Scheme.{u}} [IsIntegral X]
    (g : Y ⟶ Spec R) (m : X ⟶ Y) (x : X) (J I P : Ideal R)
    (hJ : J ≤ P) (hI : I ≤ P)
    (hP : ((IdealPullback.specIdeal P).comap g).IsInvertible)
    (hPX : ((IdealPullback.specIdeal P).comap (m ≫ g)).IsInvertible)
    (hJX : (IdealPullback.specIdeal J).comap (m ≫ g) =
      (IdealPullback.specIdeal P).comap (m ≫ g)) :
    ∃ (W : Y.affineOpens) (a : R), m x ∈ W.1 ∧ a ∈ J ∧ coordinates g W a ≠ 0 ∧
      I.map (coordinates g W).hom ≤ Ideal.span {coordinates g W a} := by
  obtain ⟨V₀, z, hy, r, _, hgen⟩ := hP (m x)
  let V := Y.affineBasicOpen z
  let φ := coordinates g V
  let ψ := Y.presheaf.germ V.1 (m x) hy ≫ m.stalkMap x
  let κ := Spec.preimage (X.fromSpecStalk x ≫ m ≫ g)
  have hp : P.map φ.hom = Ideal.span {r} := (ideal_comap g V P).symm.trans hgen
  have hpκ : P.map κ.hom = Ideal.span {ψ r} := by
    rw [← map_ideal_to_stalk g m V x hy P, show P.map (coordinates g V).hom = Ideal.span {r} from hp,
      Ideal.map_span, Set.image_singleton]
  obtain ⟨U₀, t, hx, r', hr', hX⟩ := hPX x
  let U := X.affineBasicOpen t
  let ρ := X.presheaf.germ U.1 x hx
  have hpκ' : P.map κ.hom = Ideal.span {ρ r'} := by
    change P.map (Spec.preimage (X.fromSpecStalk x ≫ (m ≫ g))).hom = _
    rw [← ideal_germ (m ≫ g) U x hx P, hX, Ideal.map_span, Set.image_singleton]
  have hr'₀ : ρ r' ≠ 0 :=
    nonZeroDivisors.ne_zero (PhilipponCartierLocalGenerator.regular_germs_of_affine U.2 r' hr' x hx)
  have hr : ψ r ≠ 0 := by
    intro hz
    have he := hpκ'.symm.trans hpκ
    rw [hz, Ideal.span_singleton_zero] at he
    have hmem : ρ r' ∈ Ideal.span {ρ r'} := Ideal.subset_span (Set.mem_singleton _)
    rw [he] at hmem
    exact hr'₀ hmem
  have hjκ : J.map κ.hom = P.map κ.hom := by
    change J.map (Spec.preimage (X.fromSpecStalk x ≫ (m ≫ g))).hom =
      P.map (Spec.preimage (X.fromSpecStalk x ≫ (m ≫ g))).hom
    rw [← ideal_germ (m ≫ g) U x hx J, hJX, ideal_germ]
  have hj : J.map (ψ.hom.comp φ.hom) = Ideal.span {ψ r} := by
    rw [← Ideal.map_map]
    exact (map_ideal_to_stalk g m V x hy J).trans (hjκ.trans hpκ)
  obtain ⟨a, ha, c, hac, hunit⟩ :=
    PhilipponAdmissibleAffineCentre.exists_generator_away φ.hom ψ.hom J r hr
      ((Ideal.map_mono hJ).trans hp.le) hj
  let W := Y.affineBasicOpen c
  let hWV : W.1 ≤ V.1 := Y.affineBasicOpen_le c
  let res := Y.presheaf.map (homOfLE hWV).op
  let θ := coordinates g W
  have hyW : m x ∈ W.1 := by
    apply (Y.mem_basicOpen c (m x) hy).mpr
    exact isUnit_of_map_unit (m.stalkMap x).hom _ hunit
  have hθ : φ ≫ res = θ := coordinates_res g W V hWV
  have ht : θ a = res r * res c := by
    rw [← hθ, CommRingCat.comp_apply, hac, map_mul]
  letI : Algebra Γ(Y, V.1) Γ(Y, W.1) := res.hom.toAlgebra
  letI : IsLocalization.Away c Γ(Y, W.1) :=
    V.2.isLocalization_of_eq_basicOpen c (homOfLE hWV) rfl
  have hu : IsUnit (res c) :=
    IsLocalization.map_units (Γ(Y, W.1)) ⟨c, Submonoid.mem_powers _⟩
  have hmono : I.map θ.hom ≤ Ideal.span {res r} := by
    apply (Ideal.map_mono hI).trans
    rw [← hθ, CommRingCat.hom_comp, ← Ideal.map_map, hp, Ideal.map_span, Set.image_singleton]
  have hmono' : Ideal.span {res r} ≤ Ideal.span {θ a} := by
    apply Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
    apply Ideal.mem_span_singleton.mpr
    rw [ht]
    obtain ⟨u, hu⟩ := hu
    refine ⟨↑u⁻¹, ?_⟩
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have ha' : θ a ≠ 0 := by
    intro hzero
    have H : coordinates g W ≫ Y.presheaf.germ W.1 (m x) hyW ≫ m.stalkMap x = φ ≫ ψ := by
      rw [← Category.assoc, coordinates_germ, show φ ≫ ψ =
        (coordinates g V ≫ Y.presheaf.germ V.1 (m x) hy) ≫ m.stalkMap x from
          (Category.assoc _ _ _).symm, coordinates_germ]
    have hL : (coordinates g W ≫ Y.presheaf.germ W.1 (m x) hyW ≫ m.stalkMap x) a = 0 := by
      change m.stalkMap x (Y.presheaf.germ W.1 (m x) hyW (θ a)) = 0
      rw [hzero, map_zero, map_zero]
    have hR : (φ ≫ ψ) a ≠ 0 := by
      change ψ (φ a) ≠ 0
      rw [hac, map_mul]
      exact mul_ne_zero hr hunit.ne_zero
    exact hR ((congrArg (fun f : R ⟶ X.presheaf.stalk x => f a) H).symm.trans hL)
  exact ⟨W, a, hyW, ha, ha', hmono.trans hmono'⟩

/-- A denominator chart carries the actual map to the original affine
source, over the original affine base. -/
theorem exists_local_map {R B : CommRingCat.{u}} {Y : Scheme.{u}} [IsIntegral Y]
    (f : R ⟶ B) (hf : Function.Injective f.hom) {ι : Type v} (b : ι → B)
    (hgen : Function.Surjective (MvPolynomial.eval₂Hom f.hom b))
    (g : Y ⟶ Spec R) (W : Y.affineOpens) [Nonempty W.1] (a : R)
    (ha : a ∈ denominators f.hom b) (ha' : coordinates g W a ≠ 0)
    (h : (centre f.hom b).map (coordinates g W).hom ≤ Ideal.span {coordinates g W a}) :
    ∃ l : W.1.toScheme ⟶ Spec B, l ≫ Spec.map f = W.1.ι ≫ g := by
  classical
  let φ := coordinates g W
  letI : IsDomain Γ(Y, W) := IsIntegral.component_integral W.1
  have H (i : ι) : ∃ c : R, ∃ t : Γ(Y, W),
      f c = f a * b i ∧ φ c = φ a * t := by
    obtain ⟨c, hc⟩ := ha i
    have hcI : c ∈ centre f.hom b := Ideal.mem_sup_right (Ideal.subset_span ⟨i, a, ha, hc⟩)
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (h (Ideal.mem_map_of_mem φ.hom hcI))
    exact ⟨c, t, hc, ht⟩
  choose c t hc ht using H
  obtain ⟨k, hk⟩ := PhilipponAffineDenominatorLift.exists_lift
    f.hom φ.hom hf b t a c hgen hc ht ha'
  let K := CommRingCat.ofHom k
  have hK : f ≫ K = φ := CommRingCat.hom_ext hk
  refine ⟨W.2.isoSpec.hom ≫ Spec.map K, ?_⟩
  rw [Category.assoc, ← Spec.map_comp, hK, map_coordinates,
    ← Category.assoc]
  rw [← IsAffineOpen.isoSpec_inv_ι, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end PhilipponFlatteningDenominatorChart

end
end

/- PhilipponReducedClosedSubscheme -/
section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponReducedClosedSubscheme

theorem radical_eq_of_isReduced {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] : I.radical = I := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (I.ideal U).radical = I.ideal U
  apply Ideal.radical_eq_iff.mpr
  apply (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mpr
  exact isReduced_of_injective (I.subschemeObjIso U).inv.hom
    (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv.injective

theorem isReduced_of_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I.radical = I) : IsReduced I.subscheme := by
  have hU (U : X.affineOpens) : (I.ideal U).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    exact congrArg (fun J : X.IdealSheafData => J.ideal U) h
  haveI (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp (hU U)
  haveI (U : X.affineOpens) : IsReduced (I.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

theorem isReduced_iff_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsReduced I.subscheme ↔ I.radical = I :=
  ⟨fun h => @radical_eq_of_isReduced X I h, isReduced_of_radical_eq I⟩

theorem integral_of_prime_top {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData)
    [(I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime] : IsIntegral I.subscheme := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  haveI : (I.ideal U).IsPrime :=
    (inferInstance : (I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime)
  haveI : IsDomain (Γ(X, U) ⧸ I.ideal U) := inferInstance
  let f := I.subschemeCover.f U
  haveI : Surjective f := by
    constructor
    intro x
    have hx : x ∈ f.opensRange := by
      change x ∈ (I.subschemeCover.f U).opensRange
      rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
      trivial
    exact hx
  haveI : IsIso f := (isIso_iff_isOpenImmersion_and_surjective f).mpr
    ⟨inferInstance, inferInstance⟩
  haveI : IsIntegral (Spec (I.subschemeCover.X U)) := by
    change IsIntegral (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsIntegral.of_isIso f

theorem radical_comap_open {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] : (I.comap f).radical = I.radical.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  change ((I.comap f).ideal U).radical = (I.radical.comap f).ideal U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Ideal.comap_radical _ _).symm

theorem eq_of_reduced_support {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : I.radical = I) (hJ : J.radical = J) (hs : I.support = J.support) : I = J := by
  rw [← hI, ← Scheme.IdealSheafData.vanishingIdeal_support, hs,
    Scheme.IdealSheafData.vanishingIdeal_support, hJ]

end PhilipponReducedClosedSubscheme

end
end

/- PhilipponSchemeImageIntegral -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponSchemeImageIntegral

/-- The scheme-theoretic image of a reduced source is reduced. -/
theorem ker_radical {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [QuasiCompact f] : f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (f.ker.ideal U).radical = f.ker.ideal U
  rw [f.ker_apply U]
  change (Ideal.comap (f.app U).hom ⊥).radical = Ideal.comap (f.app U).hom ⊥
  rw [← Ideal.comap_radical,
    Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot : (⊥ : Ideal Γ(X, f ⁻¹ᵁ U)).IsRadical)]

instance image_isReduced {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [QuasiCompact f] : IsReduced f.image :=
  PhilipponReducedClosedSubscheme.isReduced_of_radical_eq f.ker (ker_radical f)

/-- No immersion hypothesis is needed for integrality of the actual
scheme-theoretic image of a quasi-compact map from an integral scheme. -/
theorem image_isIntegral {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) [QuasiCompact f] : IsIntegral f.image := by
  have hi : IsIrreducible (Set.range f.toImage) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := X)).image
        f.toImage f.toImage.continuous.continuousOn
  letI : IrreducibleSpace f.image := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PhilipponSchemeImageIntegral

end
end

/- PhilipponNagataGraphClosure -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponNagataGraphClosure

/-- A dense open section of a separated morphism over a specified open
identifies that entire inverse image with the original open. -/
theorem isPullback_of_dense_open {U G C : Scheme.{u}}
    (s : U ⟶ G) [IsOpenImmersion s] [IsDominant s]
    (p : G ⟶ C) [IsSeparated p] (a : U ⟶ C) [IsOpenImmersion a]
    (hs : s ≫ p = a) : IsPullback s (𝟙 U) p a := by
  let k := pullback.lift s (𝟙 U) (by simpa only [Category.id_comp] using hs)
  have hk₁ : k ≫ pullback.fst p a = s := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd p a = 𝟙 U := pullback.lift_snd _ _ _
  letI : IsOpenImmersion (k ≫ pullback.fst p a) := hk₁ ▸ inferInstanceAs (IsOpenImmersion s)
  letI : IsOpenImmersion k := IsOpenImmersion.of_comp k (pullback.fst p a)
  letI : IsClosedImmersion (k ≫ pullback.snd p a) := by rw [hk₂]; infer_instance
  letI : IsClosedImmersion k := IsClosedImmersion.of_comp k (pullback.snd p a)
  letI : IsDominant (k ≫ pullback.fst p a) := by rw [hk₁]; infer_instance
  letI : IsDominant k := IsDominant.of_comp_of_isOpenImmersion k (pullback.fst p a)
  letI : Surjective k := surjective_of_isDominant_of_isClosed_range k
    k.isClosedEmbedding.isClosed_range
  letI : IsIso k := (isIso_iff_isOpenImmersion_and_surjective k).mpr ⟨inferInstance, inferInstance⟩
  exact IsPullback.of_iso_pullback ⟨by simpa only [Category.id_comp] using hs⟩ (asIso k) hk₁ hk₂

/-- The actual common graph in the product of two separated models has
both prescribed opens as inverse images. A proper model makes the
projection to the other model proper. -/
theorem exists_common_graph {U C₁ C₂ S : Scheme.{u}} [IsIntegral U]
    [NoetherianSpace U] (q₁ : C₁ ⟶ S) (q₂ : C₂ ⟶ S) [IsSeparated q₁] [IsSeparated q₂]
    (a₁ : U ⟶ C₁) (a₂ : U ⟶ C₂) [IsOpenImmersion a₁] [IsOpenImmersion a₂]
    (h : a₁ ≫ q₁ = a₂ ≫ q₂) :
    ∃ (G : Scheme.{u}) (s : U ⟶ G) (p₁ : G ⟶ C₁) (p₂ : G ⟶ C₂),
      IsIntegral G ∧ IsOpenImmersion s ∧ IsDominant s ∧
      (IsProper q₂ → IsProper p₁) ∧ (IsProper q₁ → IsProper p₂) ∧
      p₁ ≫ q₁ = p₂ ≫ q₂ ∧ IsPullback s (𝟙 U) p₁ a₁ ∧ IsPullback s (𝟙 U) p₂ a₂ := by
  let g := pullback.lift a₁ a₂ h
  have hg₁ : g ≫ pullback.fst q₁ q₂ = a₁ := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd q₁ q₂ = a₂ := pullback.lift_snd _ _ _
  letI : IsImmersion (g ≫ pullback.fst q₁ q₂) := by rw [hg₁]; infer_instance
  letI : IsImmersion g := IsImmersion.of_comp g (pullback.fst q₁ q₂)
  letI : QuasiCompact g := inferInstance
  let G := g.image
  let s : U ⟶ G := g.toImage
  let p₁ : G ⟶ C₁ := g.imageι ≫ pullback.fst q₁ q₂
  let p₂ : G ⟶ C₂ := g.imageι ≫ pullback.snd q₁ q₂
  have hs₁ : s ≫ p₁ = a₁ := by
    change g.toImage ≫ g.imageι ≫ pullback.fst q₁ q₂ = a₁
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hg₁]
  have hs₂ : s ≫ p₂ = a₂ := by
    change g.toImage ≫ g.imageι ≫ pullback.snd q₁ q₂ = a₂
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hg₂]
  letI : IsSeparated p₁ := inferInstanceAs (IsSeparated (g.imageι ≫ pullback.fst q₁ q₂))
  letI : IsSeparated p₂ := inferInstanceAs (IsSeparated (g.imageι ≫ pullback.snd q₁ q₂))
  refine ⟨G, s, p₁, p₂, PhilipponSchemeImageIntegral.image_isIntegral g,
    inferInstanceAs (IsOpenImmersion g.toImage), inferInstanceAs (IsDominant g.toImage),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro hq₂
    letI := hq₂
    exact inferInstanceAs (IsProper (g.imageι ≫ pullback.fst q₁ q₂))
  · intro hq₁
    letI := hq₁
    exact inferInstanceAs (IsProper (g.imageι ≫ pullback.snd q₁ q₂))
  · simp only [p₁, p₂, Category.assoc, pullback.condition]
  · exact isPullback_of_dense_open s p₁ a₁ hs₁
  · exact isPullback_of_dense_open s p₂ a₂ hs₂

/-- When both models are proper, the common graph is a proper integral
model with proper projections and the actual common open preserved. -/
theorem exists_common_proper_graph {U C₁ C₂ S : Scheme.{u}} [IsIntegral U]
    [NoetherianSpace U] (q₁ : C₁ ⟶ S) (q₂ : C₂ ⟶ S) [IsProper q₁] [IsProper q₂]
    (a₁ : U ⟶ C₁) (a₂ : U ⟶ C₂) [IsOpenImmersion a₁] [IsOpenImmersion a₂]
    (h : a₁ ≫ q₁ = a₂ ≫ q₂) :
    ∃ (G : Scheme.{u}) (s : U ⟶ G) (p₁ : G ⟶ C₁) (p₂ : G ⟶ C₂),
      IsIntegral G ∧ IsOpenImmersion s ∧ IsDominant s ∧ IsProper p₁ ∧ IsProper p₂ ∧
      p₁ ≫ q₁ = p₂ ≫ q₂ ∧ IsPullback s (𝟙 U) p₁ a₁ ∧ IsPullback s (𝟙 U) p₂ a₂ := by
  obtain ⟨G, s, p₁, p₂, hG, hs, hd, hp₁, hp₂, hbase, h₁, h₂⟩ :=
    exists_common_graph q₁ q₂ a₁ a₂ h
  exact ⟨G, s, p₁, p₂, hG, hs, hd, hp₁ inferInstance, hp₂ inferInstance, hbase, h₁, h₂⟩

end PhilipponNagataGraphClosure

end
end

/- PhilipponTwoOpenChartIntegral -/
section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponTwoOpenChartIntegral
variable {L R X : Scheme.{u}} (i : L ⟶ X) (j : R ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (hcover : ∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x)

def cover : X.OpenCover where
  I₀ := Bool
  X b := if b then R else L
  f b := match b with | false => i | true => j
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun b => ?_⟩
    · rcases hcover x with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · cases b <;> infer_instance

include i j hcover

lemma smooth_of_charts {T : Scheme.{u}} (p : X ⟶ T) [Smooth (i ≫ p)] [Smooth (j ≫ p)] :
    Smooth p := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) (cover i j hcover)]
  intro b
  change Bool at b
  cases b
  · exact inferInstanceAs (Smooth (i ≫ p))
  · exact inferInstanceAs (Smooth (j ≫ p))

lemma reduced_of_charts [IsReduced L] [IsReduced R] : IsReduced X := by
  haveI : ∀ b, IsReduced ((cover i j hcover).X b) := fun b => by
    change Bool at b
    cases b <;> dsimp [cover] <;> infer_instance
  exact IsReduced.of_openCover X (cover i j hcover)

lemma dense_left [IrreducibleSpace R] {O : Scheme.{u}} [Nonempty O]
    (l : O ⟶ L) (r : O ⟶ R) [IsOpenImmersion r] (hglue : l ≫ i = r ≫ j) :
    DenseRange i := by
  have hd : DenseRange r :=
    IsOpenMap.denseRange_of_isPreirreducibleSpace r r.isOpenEmbedding.isOpenMap
  have hr : Set.range j ⊆ closure (Set.range i) := by
    rintro _ ⟨y, rfl⟩
    apply (closure_minimal ?_ (isClosed_closure.preimage j.continuous)) (hd y)
    rintro _ ⟨z, rfl⟩
    have h := congrArg (fun f : O ⟶ X => f z) hglue
    change i (l z) = j (r z) at h
    change j (r z) ∈ closure (Set.range i)
    rw [← h]
    exact subset_closure ⟨_, rfl⟩
  intro x
  rcases hcover x with h | h
  · exact subset_closure h
  · exact hr h

lemma integral_of_charts [IsIntegral L] [IsIntegral R] {O : Scheme.{u}} [Nonempty O]
    (l : O ⟶ L) (r : O ⟶ R) [IsOpenImmersion r] (hglue : l ≫ i = r ≫ j) :
    IsIntegral X := by
  have hd := dense_left i j hcover l r hglue
  haveI : IsReduced X := reduced_of_charts i j hcover
  haveI : IrreducibleSpace X := by
    apply (irreducibleSpace_def X).mpr
    have h : IsIrreducible (Set.range i) := by
      simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ L).image i i.continuous.continuousOn
    change IsIrreducible (Set.univ : Set X)
    rw [← hd.closure_range]
    exact h.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced X
end PhilipponTwoOpenChartIntegral
end
end

/- PhilipponNagataExtensionProduct -/
section

set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponNagataExtensionProduct

/-- A cartesian first projection has the exact inverse-image range. -/
theorem range_fst {O A B T : Scheme.{u}} {i : O ⟶ A} {j : O ⟶ B}
    {p : A ⟶ T} {q : B ⟶ T} (H : IsPullback i j p q) :
    Set.range i = p ⁻¹' Set.range q := by
  rw [← H.isoPullback_hom_fst]
  change Set.range (pullback.fst p q ∘ H.isoPullback.hom) = _
  rw [Set.range_comp, (show Function.Surjective H.isoPullback.hom from
    Surjective.surj).range_eq, Set.image_univ, Scheme.Pullback.range_fst]

/-- The chart on the product above the first original open is itself
an open of the second extension. -/
theorem isOpenImmersion_chart {T A B U : Scheme.{u}} (p : A ⟶ T) (q : B ⟶ T)
    (e : U ⟶ A) (u : U ⟶ T) [IsOpenImmersion u] (he : e ≫ p = u) :
    IsOpenImmersion (pullback.fst (pullback.fst p q) e ≫ pullback.snd p q) := by
  have H := (IsPullback.of_hasPullback (pullback.fst p q) e).paste_horiz
    (IsPullback.of_hasPullback p q).flip
  rw [he] at H
  exact MorphismProperty.of_isPullback H.flip (inferInstanceAs (IsOpenImmersion u))

/-- The product of the extensions along the union of the two original
charts is integral. Its two open charts embed in the respective
extensions and share the original intersection. -/
theorem integral_product {T A B U V : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (p : A ⟶ T) (q : B ⟶ T)
    (u : U ⟶ T) (v : V ⟶ T) [IsOpenImmersion u] [IsOpenImmersion v]
    (e : U ⟶ A) (f : V ⟶ B) [IsOpenImmersion e] [IsOpenImmersion f]
    (He : IsPullback e (𝟙 U) p u) (Hf : IsPullback f (𝟙 V) q v)
    (cover : ∀ x : T, x ∈ Set.range u ∨ x ∈ Set.range v)
    [Nonempty ↥(pullback u v)] :
    IsIntegral (pullback p q) := by
  let X := pullback p q
  let F : X ⟶ A := pullback.fst p q
  let G : X ⟶ B := pullback.snd p q
  let L := pullback F e
  let R := pullback G f
  let l : L ⟶ X := pullback.fst F e
  let r : R ⟶ X := pullback.fst G f
  have he : e ≫ p = u := by simpa only [Category.id_comp] using He.w
  have hf : f ≫ q = v := by simpa only [Category.id_comp] using Hf.w
  letI : IsOpenImmersion (l ≫ G) := isOpenImmersion_chart p q e u he
  have hR := (IsPullback.of_hasPullback G f).paste_horiz (IsPullback.of_hasPullback p q)
  rw [hf] at hR
  letI : IsOpenImmersion (r ≫ F) :=
    MorphismProperty.of_isPullback hR.flip (inferInstanceAs (IsOpenImmersion v))
  let O := pullback u v
  let a : O ⟶ U := pullback.fst u v
  let b : O ⟶ V := pullback.snd u v
  let o : O ⟶ X := pullback.lift (a ≫ e) (b ≫ f) (by
    dsimp [a, b]
    rw [Category.assoc, he, Category.assoc, hf, pullback.condition])
  have hoF : o ≫ F = a ≫ e := pullback.lift_fst _ _ _
  have hoG : o ≫ G = b ≫ f := pullback.lift_snd _ _ _
  let oL : O ⟶ L := pullback.lift o a hoF
  let oR : O ⟶ R := pullback.lift o b hoG
  have hoL : oL ≫ l = o := pullback.lift_fst _ _ _
  have hoR : oR ≫ r = o := pullback.lift_fst _ _ _
  have hoFR : oR ≫ (r ≫ F) = a ≫ e := by rw [← Category.assoc, hoR, hoF]
  letI : IsOpenImmersion (oR ≫ (r ≫ F)) :=
    hoFR ▸ inferInstanceAs (IsOpenImmersion (pullback.fst u v ≫ e))
  letI : IsOpenImmersion oR := IsOpenImmersion.of_comp oR (r ≫ F)
  letI : Nonempty ↥L := Nonempty.map (fun x : O => oL x) ‹Nonempty ↥(pullback u v)›
  letI : Nonempty ↥R := Nonempty.map (fun x : O => oR x) ‹Nonempty ↥(pullback u v)›
  letI : IsIntegral L := isIntegral_of_isOpenImmersion (l ≫ G)
  letI : IsIntegral R := isIntegral_of_isOpenImmersion (r ≫ F)
  have hl : Set.range l = (F ≫ p) ⁻¹' Set.range u := by
    rw [show l = pullback.fst F e from rfl, Scheme.Pullback.range_fst, range_fst He]
    rfl
  have hr : Set.range r = (G ≫ q) ⁻¹' Set.range v := by
    rw [show r = pullback.fst G f from rfl, Scheme.Pullback.range_fst, range_fst Hf]
    rfl
  have heq : F ≫ p = G ≫ q := pullback.condition
  have hcover : ∀ x : X, x ∈ Set.range l ∨ x ∈ Set.range r := by
    intro x
    rw [hl, hr, ← heq]
    exact cover ((F ≫ p) x)
  exact PhilipponTwoOpenChartIntegral.integral_of_charts l r hcover oL oR (hoL.trans hoR.symm)

end PhilipponNagataExtensionProduct

end
end

/- PhilipponOpenIdealExtension -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponOpenIdealExtension

/-- Scheme-theoretic closure extends an ideal on a quasi-compact open
without changing its actual restriction to that open. -/
theorem comap_map {U X : Scheme.{u}} (I : U.IdealSheafData)
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (I.map j).comap j = I := by
  have H : IsPullback I.subschemeι (𝟙 I.subscheme) j (I.subschemeι ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  apply Scheme.IdealSheafData.ext
  funext V
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  change ((I.subschemeι ≫ j).ker.ideal
    ⟨j ''ᵁ V, V.2.image_of_isOpenImmersion j⟩).comap (j.appIso V).inv.hom = _
  rw [← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (I.subschemeι ≫ j) I.subschemeι (𝟙 I.subscheme) j H V]
  rw [Scheme.IdealSheafData.ker_subschemeι]

/-- The support of the extended ideal is the actual closure of the
original support, including every boundary limit point. -/
theorem support_map {U X : Scheme.{u}} (I : U.IdealSheafData)
    (j : U ⟶ X) [QuasiCompact j] :
    ((I.map j).support : Set X) = closure (j '' (I.support : Set U)) := by
  rw [Scheme.IdealSheafData.map, Scheme.Hom.support_ker]
  change closure (Set.range (j ∘ I.subschemeι)) = _
  rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι]

/-- Extension preserves the original unit-ideal condition on any
specified protected subspace of the open. -/
theorem unit_on_protected {V U X : Scheme.{u}} (I : U.IdealSheafData)
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (k : V ⟶ U) (h : I.comap k = ⊤) :
    (I.map j).comap (k ≫ j) = ⊤ := by
  rw [Scheme.IdealSheafData.comap_comp, comap_map, h]

end PhilipponOpenIdealExtension

end
end

/- PhilipponBlowupBaseChange -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.PiExponentSeshadri OAI.PiExponentSeshadri.Geometry


namespace PhilipponBlowupBaseChange

/-- Flat pullback preserves the actual native invertible ideal on
arbitrary schemes, with no reducedness or Noetherian hypothesis. -/
theorem invertible_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (hI : I.IsInvertible)
    (f : X ⟶ Y) [Flat f] : (I.comap f).IsInvertible := by
  apply (PhilipponNativeBlowupIdealBridge.invertible_iff I f).mp
  apply InvertibleLocal.invertible_of_local_equations
  intro x
  obtain ⟨V, s, hfx, r, hr, hgen⟩ := hI (f x)
  let W := Y.affineBasicOpen s
  obtain ⟨U, hU, hxU, e⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ W from hfx)
  let φ := (f.appLE W.1 U e).hom
  have hleft : IsLeftRegular (φ r) :=
    IdealModule.regular_map_flat φ (f.flat_appLE W.2 hU e)
      (isRegular_iff_mem_nonZeroDivisors.mpr hr).left
  have hreg : IsRegular (φ r) :=
    ⟨hleft, hleft.right_of_commute (fun t => mul_comm (φ r) t)⟩
  have hbase : (I.comap f).ideal ⟨U, hU⟩ = Ideal.span {φ r} := by
    rw [IdealPullback.comap_ideal I f ⟨U, hU⟩ W e]
    erw [hgen, Ideal.map_span, Set.image_singleton]
  refine ⟨⟨U, hU⟩, hxU, U.topIso.inv (φ r), ?_, ?_⟩
  · apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact PhilipponNativeBlowupIdealBridge.nonZeroDivisors_map_equiv
      U.topIso.symm.commRingCatIsoToRingEquiv (isRegular_iff_mem_nonZeroDivisors.mp hreg)
  · rw [IdealPullback.comap_ι_top, hbase, Ideal.map_span, Set.image_singleton]

/-- The actual fiber product of a blowup along a flat map represents
invertible pullbacks of the actual pulled-back original ideal. -/
theorem flat_baseChange {X B Z : Scheme.{u}} {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) (j : Z ⟶ X) [Flat j] :
    IsBlowup (I.comap j) (pullback.fst j π) := by
  have hnative := invertible_comap (I.comap π)
    ((PhilipponNativeBlowupIdealBridge.invertible_iff I π).mp hπ.1) (pullback.snd j π)
  have hpic : InvertiblePullbackIdeal (I.comap j) (pullback.fst j π) := by
    apply (PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mpr
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
      Scheme.IdealSheafData.comap_comp]
    exact hnative
  have hcongr {W : Scheme.{u}} (g : W ⟶ Z) :
      InvertiblePullbackIdeal (I.comap j) g ↔ InvertiblePullbackIdeal I (g ≫ j) :=
    InvertibleLocal.invertible_congr (Scheme.IdealSheafData.comap_comp I g j).symm
  refine ⟨hpic, ?_⟩
  intro W f hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ j) ((hcongr f).mp hf)
  refine ⟨pullback.lift f l hl.symm, pullback.lift_fst _ _ _, ?_⟩
  intro m hm
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst] using hm
  · rw [pullback.lift_snd]
    apply huniq
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]

variable {X Z : Scheme.{u}} (I : X.IdealSheafData) (j : Z ⟶ X) [Flat j]

/-- The independently constructed global blowup of the actual pulled-back
ideal is the actual fiber product, not merely another proper cover. -/
def iso : PhilipponBlowup.scheme (I.comap j) ≅ pullback j (PhilipponBlowup.projection I) :=
  (PhilipponBlowup.isBlowup (I.comap j)).iso
    (flat_baseChange (PhilipponBlowup.isBlowup I) j)

@[reassoc (attr := simp)]
theorem iso_hom_fst :
    (iso I j).hom ≫ pullback.fst j (PhilipponBlowup.projection I) =
      PhilipponBlowup.projection (I.comap j) :=
  (PhilipponBlowup.isBlowup (I.comap j)).iso_hom_comp
    (flat_baseChange (PhilipponBlowup.isBlowup I) j)

def map : PhilipponBlowup.scheme (I.comap j) ⟶ PhilipponBlowup.scheme I :=
  (iso I j).hom ≫ pullback.snd j (PhilipponBlowup.projection I)

@[reassoc (attr := simp)]
theorem map_projection : map I j ≫ PhilipponBlowup.projection I =
    PhilipponBlowup.projection (I.comap j) ≫ j := by
  rw [map, Category.assoc, ← pullback.condition, ← Category.assoc, iso_hom_fst]

instance map_flat : Flat (map I j) := by unfold map; infer_instance

theorem isPullback : IsPullback (PhilipponBlowup.projection (I.comap j)) (map I j)
    j (PhilipponBlowup.projection I) := by
  refine IsPullback.of_iso_pullback ⟨(map_projection I j).symm⟩ (iso I j)
    (iso_hom_fst I j) rfl

end PhilipponBlowupBaseChange

end
end

/- PhilipponBlowupCartier -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.PiExponentSeshadri OAI.PiExponentSeshadri.Geometry

namespace PhilipponBlowupCartier

/-- Blowing up an actual native invertible ideal is an isomorphism. -/
theorem isIso_of_invertible {X B : Scheme.{u}} {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) (hI : I.IsInvertible) : IsIso π := by
  have hid : InvertiblePullbackIdeal I (𝟙 X) :=
    (PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mpr (by simpa using hI)
  obtain ⟨s, hs, hu⟩ := hπ.2 X (𝟙 X) hid
  have hsid : s ≫ π = 𝟙 X := hs
  have hpis : π ≫ s = 𝟙 B := by
    apply hπ.hom_ext π hπ.1
    · rw [Category.assoc, hsid, Category.comp_id]
    · exact Category.id_comp _
  exact ⟨⟨s, hpis, hsid⟩⟩

theorem projection_isIso {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible) :
    IsIso (PhilipponBlowup.projection I) :=
  isIso_of_invertible (PhilipponBlowup.isBlowup I) hI

/-- A flat chart on which the original center is already Cartier is
unchanged by the actual global blowup. -/
theorem pullback_isIso {X Z : Scheme.{u}} (I : X.IdealSheafData)
    (j : Z ⟶ X) [Flat j] (hj : (I.comap j).IsInvertible) :
    IsIso (pullback.fst j (PhilipponBlowup.projection I)) :=
  isIso_of_invertible (PhilipponBlowupBaseChange.flat_baseChange
    (PhilipponBlowup.isBlowup I) j) hj

/-- A protected open on which the actual center is the unit ideal is
unchanged. No reducedness, integrality or Noetherian assumption is used. -/
theorem unit_open_unchanged {X U : Scheme.{u}} (I : X.IdealSheafData)
    (j : U ⟶ X) [IsOpenImmersion j] (hj : I.comap j = ⊤) :
    IsIso (pullback.fst j (PhilipponBlowup.projection I)) :=
  pullback_isIso I j (hj ▸ Scheme.IdealSheafData.isInvertible_top)

end PhilipponBlowupCartier

end
end

/- PhilipponOpenBlowupExtension -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.PiExponentSeshadri OAI.PiExponentSeshadri.Geometry

namespace PhilipponOpenBlowupExtension

variable {U X : Scheme.{u}} (I : U.IdealSheafData)
variable (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

lemma pulled_isBlowup : IsBlowup I (pullback.fst j (PhilipponBlowup.projection (I.map j))) := by
  have H := PhilipponBlowupBaseChange.flat_baseChange (PhilipponBlowup.isBlowup (I.map j)) j
  simpa only [PhilipponOpenIdealExtension.comap_map] using H

/-- The blowup of the extended ideal restricts to the actual independently
constructed blowup of the original ideal on the given open. -/
def iso : PhilipponBlowup.scheme I ≅ pullback j (PhilipponBlowup.projection (I.map j)) :=
  (PhilipponBlowup.isBlowup I).iso (pulled_isBlowup I j)

@[reassoc (attr := simp)]
lemma iso_hom_fst : (iso I j).hom ≫ pullback.fst j (PhilipponBlowup.projection (I.map j)) =
    PhilipponBlowup.projection I :=
  (PhilipponBlowup.isBlowup I).iso_hom_comp (pulled_isBlowup I j)

def map : PhilipponBlowup.scheme I ⟶ PhilipponBlowup.scheme (I.map j) :=
  (iso I j).hom ≫ pullback.snd j (PhilipponBlowup.projection (I.map j))

@[reassoc (attr := simp)]
lemma map_projection : map I j ≫ PhilipponBlowup.projection (I.map j) =
    PhilipponBlowup.projection I ≫ j := by
  rw [map, Category.assoc, ← pullback.condition, ← Category.assoc, iso_hom_fst]

instance map_isOpenImmersion : IsOpenImmersion (map I j) := by
  unfold map
  infer_instance

lemma isPullback : IsPullback (PhilipponBlowup.projection I) (map I j)
    j (PhilipponBlowup.projection (I.map j)) :=
  IsPullback.of_iso_pullback ⟨(map_projection I j).symm⟩ (iso I j) (iso_hom_fst I j) rfl

/-- If the original ideal is the unit ideal on a protected open V of U,
its global extension gives a blowup which is still unchanged over V. -/
theorem protected_unchanged {V : Scheme.{u}} (k : V ⟶ U) [IsOpenImmersion k]
    (h : I.comap k = ⊤) :
    IsIso (pullback.fst (k ≫ j) (PhilipponBlowup.projection (I.map j))) :=
  PhilipponBlowupCartier.unit_open_unchanged (I.map j) (k ≫ j)
    (PhilipponOpenIdealExtension.unit_on_protected I j k h)

end PhilipponOpenBlowupExtension

end
end

/- PhilipponAdmissibleBlowupExtension -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponAdmissibleBlowupExtension

/-- An ideal supported away from an open restricts to the unit ideal. -/
lemma unit_on_open {X : Scheme.{u}} (I : X.IdealSheafData) (W : X.Opens)
    (h : Disjoint (I.support : Set X) (W : Set X)) : I.comap W.ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  apply SetLike.coe_injective
  ext x
  rw [Scheme.IdealSheafData.support_comap]
  change (x.val ∈ I.support) ↔ False
  exact ⟨fun hx => Set.disjoint_left.mp h hx x.property, False.elim⟩

/-- Extending a local center by scheme-theoretic closure cannot introduce
a center on a protected ambient open which already misses it. -/
lemma extended_unit_on_open {V X : Scheme.{u}} (I : V.IdealSheafData)
    (j : V ⟶ X) [QuasiCompact j] (W : X.Opens)
    (h : Disjoint (I.support : Set V) (j ⁻¹' (W : Set X))) :
    (I.map j).comap W.ι = ⊤ := by
  apply unit_on_open
  apply Set.disjoint_left.mpr
  intro x hx hxW
  rw [PhilipponOpenIdealExtension.support_map] at hx
  have hs : j '' (I.support : Set V) ⊆ (W : Set X)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩ hvW
    exact Set.disjoint_left.mp h hv hvW
  exact (closure_minimal hs W.isOpen.isClosed_compl hx) hxW

/-- The actual local blowup extends to one actual global blowup which
is unchanged on a protected ambient open, even when that open is not
contained in the domain of the local center. -/
theorem extends_admissibly {V X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : V.IdealSheafData) (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (W : X.Opens) (h : Disjoint (I.support : Set V) (j ⁻¹' (W : Set X))) :
    IsProper (PhilipponBlowup.projection (I.map j)) ∧
      IsOpenImmersion (PhilipponOpenBlowupExtension.map I j) ∧
      IsPullback (PhilipponBlowup.projection I) (PhilipponOpenBlowupExtension.map I j)
        j (PhilipponBlowup.projection (I.map j)) ∧
      IsIso (pullback.fst W.ι (PhilipponBlowup.projection (I.map j))) := by
  exact ⟨inferInstance, inferInstance, PhilipponOpenBlowupExtension.isPullback I j,
    PhilipponBlowupCartier.unit_open_unchanged _ W.ι (extended_unit_on_open I j W h)⟩

end PhilipponAdmissibleBlowupExtension

end
end

/- PhilipponBlowupIntegral -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.PiExponentSeshadri OAI.PiExponentSeshadri.Geometry

namespace PhilipponBlowupIntegral

instance affine_rees_isReduced {R : Type u} [CommRing R] [_root_.IsReduced R] (I : Ideal R) :
    IsReduced (ReesGrading.affineBlowup I) := by
  letI : _root_.IsReduced (Polynomial R) := {
    eq_zero := fun p hp => by
      ext n
      exact (Polynomial.isNilpotent_iff.mp hp n).eq_zero }
  letI : _root_.IsReduced (reesAlgebra I) :=
    isReduced_of_injective (reesAlgebra I).val Subtype.val_injective
  exact ProjectiveGeometry.proj_isReduced (ReesGrading.piece I)

instance affine_rees_isIntegral {R : Type u} [CommRing R] [IsDomain R] (I : Ideal R)
    [Nonempty (ReesGrading.affineBlowup I)] : IsIntegral (ReesGrading.affineBlowup I) := by
  letI : IsDomain (reesAlgebra I) :=
    Function.Injective.isDomain (reesAlgebra I).val Subtype.val_injective
  letI : Nonempty (Proj (ReesGrading.piece I)) :=
    inferInstanceAs (Nonempty (ReesGrading.affineBlowup I))
  exact ProjectiveGeometry.proj_isIntegral (ReesGrading.piece I)

instance affine_isReduced {X : Scheme.{u}} [IsAffine X] [IsReduced X]
    (I : X.IdealSheafData) : IsReduced (PhilipponAffineBlowup.scheme I) := by
  unfold PhilipponAffineBlowup.scheme
  infer_instance

instance affine_isIntegral {X : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (I : X.IdealSheafData) [Nonempty (PhilipponAffineBlowup.scheme I)] :
    IsIntegral (PhilipponAffineBlowup.scheme I) := by
  unfold PhilipponAffineBlowup.scheme
  infer_instance

instance global_isReduced {X : Scheme.{u}} [IsReduced X]
    (I : X.IdealSheafData) : IsReduced (PhilipponBlowup.scheme I) := by
  letI (U : (PhilipponBlowup.cover I).I₀) : IsReduced ((PhilipponBlowup.cover I).X U) := by
    letI : IsAffine U.toOpens.toScheme := U.2
    letI : IsReduced U.toOpens.toScheme := isReduced_of_isOpenImmersion U.toOpens.ι
    exact affine_isReduced _
  exact IsReduced.of_openCover _ (PhilipponBlowup.cover I)

abbrev complement {X : Scheme.{u}} (I : X.IdealSheafData) : X.Opens := I.support.compl

lemma complement_nonempty {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.support ≠ ⊤) :
    Nonempty (complement I).toScheme := by
  by_contra h
  apply hI
  ext x
  change x ∈ I.support ↔ True
  rw [iff_true]
  by_contra hx
  exact h ⟨⟨x, hx⟩⟩

lemma complement_unit {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.comap (complement I).ι = ⊤ :=
  PhilipponAdmissibleBlowupExtension.unit_on_open I (complement I)
    (Set.disjoint_left.mpr (fun _ hx hn => hn hx))

lemma complement_isIso {X B : Scheme.{u}} {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) : IsIso (pullback.fst (complement I).ι π) :=
  PhilipponBlowupCartier.isIso_of_invertible (hπ.open_baseChange (complement I).ι)
    ((complement_unit I) ▸ Scheme.IdealSheafData.isInvertible_top)

def complementLift {X B : Scheme.{u}} {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) : (complement I).toScheme ⟶ B := by
  letI := complement_isIso hπ
  exact inv (pullback.fst (complement I).ι π) ≫ pullback.snd (complement I).ι π

@[reassoc (attr := simp)]
lemma complementLift_comp {X B : Scheme.{u}} {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) : complementLift hπ ≫ π = (complement I).ι := by
  letI := complement_isIso hπ
  dsimp only [complementLift]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp]

lemma complementLift_range {X B : Scheme.{u}} {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) : Set.range (complementLift hπ) = π ⁻¹' (complement I : Set X) := by
  letI := complement_isIso hπ
  change Set.range ((pullback.snd (complement I).ι π) ∘
    (inv (pullback.fst (complement I).ι π))) = _
  rw [Set.range_comp, (inv (pullback.fst (complement I).ι π)).surjective.range_eq,
    Set.image_univ, Scheme.Pullback.range_snd]
  simp

lemma nonempty_of_support_ne_top {X B : Scheme.{u}} {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) (hI : I.support ≠ ⊤) : Nonempty B :=
  (complement_nonempty I hI).map (complementLift hπ)

lemma support_comap_ne_top_of_open {X Y : Scheme.{u}} [IrreducibleSpace X]
    (I : X.IdealSheafData) (hI : I.support ≠ ⊤)
    (j : Y ⟶ X) [IsOpenImmersion j] [Nonempty Y] : (I.comap j).support ≠ ⊤ := by
  have hc : (complement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty I hI
    exact ⟨x.val, x.property⟩
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range (complement I).isOpen (Set.range_nonempty j) hc
  intro he
  have hyn : y ∈ (I.comap j).support := by rw [he]; trivial
  rw [Scheme.IdealSheafData.support_comap] at hyn
  exact hy hyn

lemma cover_range {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.AffineZariskiSite) :
    Set.range ((PhilipponBlowup.cover I).f U) =
      PhilipponBlowup.projection I ⁻¹' (U.toOpens : Set X) := by
  have h := ((PhilipponBlowup.gluing I).preimage_toBase_eq_range_ι U).symm
  change Set.range ((PhilipponBlowup.cover I).f U) =
    PhilipponBlowup.projection I ⁻¹' Set.range U.toOpens.ι at h
  simpa only [Scheme.Opens.range_ι] using h

lemma local_isIntegral {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    (hI : I.support ≠ ⊤) (U : X.AffineZariskiSite) [Nonempty U.toOpens.toScheme] :
    IsIntegral (PhilipponBlowup.localScheme I U) := by
  letI : IsAffine U.toOpens.toScheme := U.2
  letI : IsIntegral U.toOpens.toScheme := isIntegral_of_isOpenImmersion U.toOpens.ι
  letI := nonempty_of_support_ne_top (PhilipponBlowup.local_isBlowup I U)
    (support_comap_ne_top_of_open I hI U.toOpens.ι)
  exact affine_isIntegral _

lemma complement_dense {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    (hI : I.support ≠ ⊤) : Dense (PhilipponBlowup.projection I ⁻¹' (complement I : Set X)) := by
  rw [dense_iff_inter_open]
  intro V hV ⟨y, hyV⟩
  obtain ⟨U, z, rfl⟩ := (PhilipponBlowup.cover I).exists_eq y
  letI : Nonempty U.toOpens.toScheme := ⟨PhilipponBlowup.localProjection I U z⟩
  letI : IsIntegral ((PhilipponBlowup.cover I).X U) := local_isIntegral I hI U
  have hc : (complement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty I hI
    exact ⟨x.val, x.property⟩
  have hU : (U.toOpens : Set X).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U.toOpens.toScheme)
    exact ⟨x.val, x.property⟩
  obtain ⟨x, hxU, hxc⟩ := nonempty_preirreducible_inter
    U.toOpens.isOpen (complement I).isOpen hU hc
  let b : PhilipponBlowup.scheme I := complementLift (PhilipponBlowup.isBlowup I) ⟨x, hxc⟩
  have hpb : PhilipponBlowup.projection I b = x :=
    congrArg (fun f : (complement I).toScheme ⟶ X => f ⟨x, hxc⟩)
      (complementLift_comp (PhilipponBlowup.isBlowup I))
  have hbr : b ∈ Set.range ((PhilipponBlowup.cover I).f U) := by
    erw [cover_range I U]
    change PhilipponBlowup.projection I b ∈ U.toOpens
    rwa [hpb]
  obtain ⟨w, hw⟩ := hbr
  have hwc : (PhilipponBlowup.cover I).f U w ∈
      PhilipponBlowup.projection I ⁻¹' (complement I : Set X) := by
    change PhilipponBlowup.projection I ((PhilipponBlowup.cover I).f U w) ∈ complement I
    rwa [hw, hpb]
  obtain ⟨q, hqV, hqc⟩ := nonempty_preirreducible_inter
    (hV.preimage ((PhilipponBlowup.cover I).f U).continuous)
    (((complement I).isOpen.preimage (PhilipponBlowup.projection I).continuous).preimage
      ((PhilipponBlowup.cover I).f U).continuous) ⟨z, hyV⟩ ⟨w, hwc⟩
  exact ⟨(PhilipponBlowup.cover I).f U q, hqV, hqc⟩

/-- The actual global blowup of an integral scheme in a center which
misses a point is integral, in the full original universe u. -/
theorem source_isIntegral {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    (hI : I.support ≠ ⊤) : IsIntegral (PhilipponBlowup.scheme I) := by
  letI := complement_nonempty I hI
  letI : IsIntegral (complement I).toScheme := isIntegral_of_isOpenImmersion (complement I).ι
  have hi : IsIrreducible (Set.range (complementLift (PhilipponBlowup.isBlowup I))) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := (complement I).toScheme)).image
        (complementLift (PhilipponBlowup.isBlowup I))
        (complementLift (PhilipponBlowup.isBlowup I)).continuous.continuousOn
  have hd : Dense (Set.range (complementLift (PhilipponBlowup.isBlowup I))) := by
    rw [complementLift_range]
    exact complement_dense I hI
  letI : IrreducibleSpace (PhilipponBlowup.scheme I) := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set (PhilipponBlowup.scheme I))
    rw [← hd.closure_eq]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PhilipponBlowupIntegral

end
end

/- PhilipponBlowupModification -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponBlowupModification
open PhilipponBlowupIntegral

lemma projection_isDominant {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I.support ≠ ⊤) :
    IsDominant (PhilipponBlowup.projection I) := by
  letI := complement_nonempty I hI
  haveI : IsDominant (complement I).ι :=
    ⟨(complement I).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI : IsDominant (complementLift (PhilipponBlowup.isBlowup I) ≫
      PhilipponBlowup.projection I) := by
    rw [complementLift_comp]
    infer_instance
  exact IsDominant.of_comp (complementLift (PhilipponBlowup.isBlowup I)) _

lemma restrict_isIso {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsIso (PhilipponBlowup.projection I ∣_ complement I) := by
  letI := complement_isIso (PhilipponBlowup.isBlowup I)
  rw [← (isPullback_morphismRestrict (PhilipponBlowup.projection I) (complement I)).isoPullback_hom_fst]
  infer_instance

/-- The original complement is a nonempty dense open over which the
actual global blowup projection is an isomorphism. -/
theorem exists_dense_open_isIso {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I.support ≠ ⊤) :
    ∃ W : X.Opens, Nonempty W ∧ Dense (W : Set X) ∧
      IsIso (PhilipponBlowup.projection I ∣_ W) := by
  have hW : Nonempty (complement I) := complement_nonempty I hI
  exact ⟨complement I, hW,
    (complement I).isOpen.dense (by obtain ⟨x⟩ := hW; exact ⟨x.val, x.property⟩),
    restrict_isIso I⟩

/-- A proper original center gives the actual integral proper dominant
modification, with a finite nonempty open locus. -/
theorem properties {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I.support ≠ ⊤) :
    IsIntegral (PhilipponBlowup.scheme I) ∧ IsProper (PhilipponBlowup.projection I) ∧
      IsDominant (PhilipponBlowup.projection I) ∧ Surjective (PhilipponBlowup.projection I) ∧
      ∃ W : X.Opens, Nonempty W ∧ Dense (W : Set X) ∧
        IsIso (PhilipponBlowup.projection I ∣_ W) ∧
        IsFinite (PhilipponBlowup.projection I ∣_ W) := by
  letI := projection_isDominant I hI
  obtain ⟨W, hW, hdW, hiso⟩ := exists_dense_open_isIso I hI
  letI := hiso
  exact ⟨source_isIntegral I hI, inferInstance, inferInstance, inferInstance,
    W, hW, hdW, hiso, inferInstance⟩

end PhilipponBlowupModification

end
end

/- PhilipponBlowupComparison -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponBlowupComparison

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)

lemma composite_invertible :
    (I.comap (PhilipponBlowup.projection (I.comap f) ≫ f)).IsInvertible := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact PhilipponBlowup.nativeInvertible _

/-- The actual blowup of the pulled-back ideal maps to the original
blowup for every base morphism, without assuming flatness. -/
def map : PhilipponBlowup.scheme (I.comap f) ⟶ PhilipponBlowup.scheme I :=
  (PhilipponBlowup.existsUnique_lift I (PhilipponBlowup.projection (I.comap f) ≫ f)
    (composite_invertible I f)).choose

@[reassoc (attr := simp)]
lemma map_projection : map I f ≫ PhilipponBlowup.projection I =
    PhilipponBlowup.projection (I.comap f) ≫ f :=
  (PhilipponBlowup.existsUnique_lift I (PhilipponBlowup.projection (I.comap f) ≫ f)
    (composite_invertible I f)).choose_spec.1

/-- The canonical comparison to the actual fiber product. -/
def comparison : PhilipponBlowup.scheme (I.comap f) ⟶
    pullback f (PhilipponBlowup.projection I) :=
  pullback.lift (PhilipponBlowup.projection (I.comap f)) (map I f) (map_projection I f).symm

@[reassoc (attr := simp)]
lemma comparison_fst : comparison I f ≫ pullback.fst f (PhilipponBlowup.projection I) =
    PhilipponBlowup.projection (I.comap f) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma comparison_snd : comparison I f ≫ pullback.snd f (PhilipponBlowup.projection I) =
    map I f := pullback.lift_snd _ _ _

instance comparison_proper [IsLocallyNoetherian X] [IsLocallyNoetherian Y] :
    IsProper (comparison I f) := by
  haveI : IsProper (comparison I f ≫ pullback.fst f (PhilipponBlowup.projection I)) := by
    rw [comparison_fst]
    infer_instance
  exact IsProper.of_comp (comparison I f) (pullback.fst f (PhilipponBlowup.projection I))

end PhilipponBlowupComparison

end
end

/- PhilipponNagataProtectedChart -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponBlowup

namespace PhilipponNagataProtectedChart

/-- A protected open has an actual open lift to the blowup. -/
theorem exists_unit_lift {X U : Scheme.{u}} (I : X.IdealSheafData)
    (s : U ⟶ X) [IsOpenImmersion s] (h : I.comap s = ⊤) :
    ∃ t : U ⟶ scheme I, IsOpenImmersion t ∧ t ≫ projection I = s := by
  letI := PhilipponBlowupCartier.unit_open_unchanged I s h
  let t := inv (pullback.fst s (projection I)) ≫ pullback.snd s (projection I)
  refine ⟨t, inferInstance, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

lemma support_ne_top_of_unit {G U : Scheme.{u}} [Nonempty U]
    (P : G.IdealSheafData) (s : U ⟶ G) (hP : P.comap s = ⊤) : P.support ≠ ⊤ := by
  intro h
  have e := congrArg Scheme.IdealSheafData.support hP
  rw [Scheme.IdealSheafData.support_comap, h, Scheme.IdealSheafData.support_top] at e
  obtain ⟨u⟩ := ‹Nonempty U›
  have hu : u ∈ (⊤ : TopologicalSpace.Closeds G).preimage s.continuous := trivial
  rw [e] at hu
  exact hu


end PhilipponNagataProtectedChart

end
end

/- PhilipponAdmissibleAffineCentreSpec -/
section

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PhilipponAdmissibleDenominators

namespace PhilipponAdmissibleAffineCentreSpec

/-- An open comparison over the protected open gives isomorphisms on
the original stalks at all source points over that open. -/
theorem isIso_stalkMap_over {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    [IsOpenImmersion (f ∣_ W)] (x : X) (hx : f x ∈ W) :
    IsIso (f.stalkMap x) := by
  let V := f ⁻¹ᵁ W
  let x' : V.toScheme := ⟨x, hx⟩
  letI : IsIso (((f ∣_ W) ≫ W.ι).stalkMap x') := inferInstance
  letI : IsIso ((V.ι ≫ f).stalkMap x') := by
    rw [← morphismRestrict_ι f W]
    infer_instance
  letI : IsIso (f.stalkMap (V.ι x') ≫ V.ι.stalkMap x') := by
    rw [← Scheme.Hom.stalkMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right (f.stalkMap (V.ι x')) (V.ι.stalkMap x')

/-- An isomorphism on the localized rings gives denominators for
every finite family of generators, avoiding the base prime. -/
theorem denominators_not_le_of_stalkIso {R B : CommRingCat.{u}} [IsDomain B]
    (f : R ⟶ B) (x : PrimeSpectrum B) [IsIso ((Spec.map f).stalkMap x)]
    {ι : Type v} [Fintype ι] (b : ι → B) :
    ¬ denominators f.hom b ≤ (x.comap f.hom).asIdeal := by
  let P := (x.comap f.hom).asIdeal
  let Q := x.asIdeal
  let g := Localization.localRingHom P Q f.hom rfl
  letI : IsIso (CommRingCat.ofHom g) :=
    ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso f x)).mp inferInstance
  let e := (asIso (CommRingCat.ofHom g)).commRingCatIsoToRingEquiv
  apply denominators_not_le f.hom b P
  intro i
  let z := e.symm (algebraMap B (Localization.AtPrime Q) (b i))
  obtain ⟨⟨c, d⟩, hd⟩ := IsLocalization.surj P.primeCompl z
  refine ⟨d, d.property, c, ?_⟩
  have he (a : R) : e (algebraMap R (Localization.AtPrime P) a) =
      algebraMap B (Localization.AtPrime Q) (f.hom a) :=
    Localization.localRingHom_to_map P Q f.hom rfl a
  have hz : e z = algebraMap B (Localization.AtPrime Q) (b i) := e.apply_symm_apply _
  apply IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
  have h := congrArg e hd
  rw [map_mul, hz, he, he] at h
  rw [map_mul, mul_comm]
  exact h.symm

/-- The open complementary to the support of the excluded ideal. -/
def openComplement {R : CommRingCat.{u}} (C : Ideal R) : (Spec R).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (C : Set R))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus (C : Set R)).isOpen_compl⟩

/-- The affine open-immersion hypothesis gives the prime-theoretic
condition needed to make the two denominator centres admissible. -/
theorem adjusted_centres {R B : CommRingCat.{u}} [IsDomain B] {ι : Type v} [Fintype ι]
    (f : R ⟶ B) (b : ι → B) (C : Ideal R) (hC : C.FG)
    [IsOpenImmersion (Spec.map f ∣_ openComplement C)] :
    ∃ n : ℕ, ((denominators f.hom b) ⊔ C ^ n).map f.hom = (denominators f.hom b).map f.hom ∧
      ((centre f.hom b) ⊔ C ^ n).map f.hom = (denominators f.hom b).map f.hom ∧
      ∀ P : Ideal R, P.IsPrime → ¬ C ≤ P →
        ¬ ((denominators f.hom b) ⊔ C ^ n) * ((centre f.hom b) ⊔ C ^ n) ≤ P := by
  refine PhilipponAdmissibleAffineCentre.exists_adjusted_centres f.hom b C hC ?_
  intro Q hQ hJ
  let x : PrimeSpectrum B := ⟨Q, hQ⟩
  rw [Ideal.map_le_iff_le_comap]
  by_contra h
  have hx : Spec.map f x ∈ openComplement C := h
  letI := isIso_stalkMap_over (Spec.map f) (openComplement C) x hx
  exact denominators_not_le_of_stalkIso f x b (Ideal.map_le_iff_le_comap.mp hJ)

end PhilipponAdmissibleAffineCentreSpec


end

/- PhilipponStrictTransformLocalLift -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup

namespace PhilipponStrictTransformLocalLift

/-- A section over an open is an isomorphism there if a dense open of
the integral source already identifies with a target open. -/
theorem isIso_of_open_section {X Y U : Scheme.{u}} [IsIntegral X] [Nonempty U]
    (f : X ⟶ Y) [IsSeparated f]
    (s : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion s] [IsOpenImmersion j] (hs : s ≫ f = j)
    (W : Y.Opens) [Nonempty (f ⁻¹ᵁ W).toScheme]
    (m : W.toScheme ⟶ X) (hm : m ≫ f = W.ι) :
    IsIso (f ∣_ W) := by
  let V := f ⁻¹ᵁ W
  let g := f ∣_ W
  let H := isPullback_morphismRestrict f W
  have hm' : (𝟙 W.toScheme) ≫ W.ι = m ≫ f := by simpa only [Category.id_comp] using hm.symm
  let k := H.lift (𝟙 W.toScheme) m hm'
  have hk₁ : k ≫ g = 𝟙 _ := H.lift_fst _ _ hm'
  have hk₂ : k ≫ V.ι = m := H.lift_snd _ _ hm'
  letI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  letI : IsDominant s := ⟨s.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let Hs := PhilipponNagataGraphClosure.isPullback_of_dense_open s f j hs
  have hd : Dense (V.ι ⁻¹' Set.range s) := by
    apply (s.opensRange.isOpen.preimage V.ι.continuous).dense
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ :=
      s.denseRange.inter_open_nonempty (Set.range V.ι) V.ι.opensRange.isOpen (Set.range_nonempty _)
    exact ⟨y, hy⟩
  have hsub : V.ι ⁻¹' Set.range s ⊆ Set.range k := by
    rintro y ⟨z, hz⟩
    let t := g y
    have hft : f (m t) = j z := by
      calc f (m t) = W.ι t := congrArg (fun a : W.toScheme ⟶ Y => a t) hm
        _ = f (V.ι y) := congrArg (fun a : V.toScheme ⟶ Y => a y) (morphismRestrict_ι f W)
        _ = f (s z) := congrArg f hz.symm
        _ = j z := congrArg (fun a : U ⟶ Y => a z) hs
    have hmem : m t ∈ Set.range s := by
      rw [PhilipponNagataExtensionProduct.range_fst Hs]
      exact ⟨z, hft.symm⟩
    obtain ⟨z', hz'⟩ := hmem
    have hj : j z' = j z := by
      rw [← congrArg (fun a : U ⟶ Y => a z') hs]
      exact (congrArg f hz').trans hft
    have heq : z' = z := j.isOpenEmbedding.injective hj
    refine ⟨t, V.ι.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun a : W.toScheme ⟶ X => a t) hk₂).trans
      (hz'.symm.trans ((congrArg s heq).trans hz))
  letI : IsDominant k := ⟨hd.mono hsub⟩
  letI : IsProper (k ≫ g) := hk₁ ▸ inferInstanceAs (IsProper (𝟙 W.toScheme))
  letI : IsProper k := IsProper.of_comp k g
  letI : IsImmersion (k ≫ g) := hk₁ ▸ inferInstanceAs (IsImmersion (𝟙 W.toScheme))
  letI : IsImmersion k := IsImmersion.of_comp k g
  letI : IsClosedImmersion k := IsClosedImmersion.of_isPreimmersion k k.isClosedMap.isClosed_range
  letI : Surjective k := surjective_of_isDominant_of_isClosed_range k k.isClosedMap.isClosed_range
  letI : IsIso k := isIso_of_isClosedImmersion_of_surjective k
  letI : IsIso (k ≫ g) := hk₁ ▸ inferInstanceAs (IsIso (𝟙 W.toScheme))
  exact IsIso.of_isIso_comp_left k g

/-- The comparison is flat when each source point lies over a target
open carrying a morphism to the original source over the base. -/
theorem flat_of_local_lifts {X Y U : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsIntegral (scheme (I.comap f))] [IsSeparated (PhilipponBlowupComparison.map I f)] [Nonempty U]
    (s : U ⟶ scheme (I.comap f)) (j : U ⟶ scheme I)
    [IsOpenImmersion s] [IsOpenImmersion j] (hs : s ≫ PhilipponBlowupComparison.map I f = j)
    (hl : ∀ x : scheme (I.comap f),
      ∃ W : (scheme I).Opens, PhilipponBlowupComparison.map I f x ∈ W ∧
        ∃ l : W.toScheme ⟶ X, l ≫ f = W.ι ≫ projection I) :
    Flat (PhilipponBlowupComparison.map I f) := by
  let g := PhilipponBlowupComparison.map I f
  apply Flat.of_stalkMap
  intro x
  obtain ⟨W, hx, l, hl⟩ := hl x
  have H : (I.comap (W.ι ≫ projection I)).IsInvertible := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact PhilipponBlowupBaseChange.invertible_comap _ (nativeInvertible I) W.ι
  have H' : ((I.comap f).comap l).IsInvertible := by
    rw [← Scheme.IdealSheafData.comap_comp, hl]
    exact H
  obtain ⟨m, hm, _⟩ := existsUnique_lift (I.comap f) l H'
  have hmg : m ≫ g = W.ι := by
    apply (existsUnique_lift I _ H).unique
    · rw [Category.assoc, show g ≫ projection I = projection (I.comap f) ≫ f from
        PhilipponBlowupComparison.map_projection I f, ← Category.assoc, hm, hl]
    · rfl
  letI : Nonempty (g ⁻¹ᵁ W).toScheme := ⟨⟨x, hx⟩⟩
  letI : IsIso (g ∣_ W) := isIso_of_open_section g s j hs W m hmg
  letI : IsIso (g.stalkMap x) := PhilipponAdmissibleAffineCentreSpec.isIso_stalkMap_over g W x hx
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (g.stalkMap x))

/-- Open charts on which the original comparison is unchanged lift
compatibly to the two actual blowups. -/
theorem exists_common_open {X Y U : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (s : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion s] [IsOpenImmersion j]
    (hs : s ≫ f = j) (hI : I.comap j = ⊤) :
    ∃ (s' : U ⟶ scheme (I.comap f)) (j' : U ⟶ scheme I),
      IsOpenImmersion s' ∧ IsOpenImmersion j' ∧
      s' ≫ projection (I.comap f) = s ∧ j' ≫ projection I = j ∧
      s' ≫ PhilipponBlowupComparison.map I f = j' := by
  have hJ : ((I.comap f).comap s) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, hs, hI]
  obtain ⟨s', hs', hs₁⟩ := PhilipponNagataProtectedChart.exists_unit_lift _ s hJ
  obtain ⟨j', hj', hj₁⟩ := PhilipponNagataProtectedChart.exists_unit_lift _ j hI
  refine ⟨s', j', hs', hj', hs₁, hj₁, ?_⟩
  apply (existsUnique_lift I j (hI ▸ Scheme.IdealSheafData.isInvertible_top)).unique
  · rw [Category.assoc, PhilipponBlowupComparison.map_projection, ← Category.assoc, hs₁, hs]
  · exact hj₁

end PhilipponStrictTransformLocalLift

end
end

/- PhilipponIdealSheafProductPullback -/
section

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponentSeshadri

namespace PhilipponIdealSheafProductPullback

/-- Actual inverse image ideals commute with products for any scheme
morphism. Affine charts contained in inverse images of affine charts
form a cover, where inverse image is ordinary extension of ideals. -/
theorem comap_mul {X Y : Scheme.{u}} (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  let P := {p : X.affineOpens × Y.affineOpens // p.1.1 ≤ f ⁻¹ᵁ p.2.1}
  let A (p : P) : X.affineOpens := p.1.1
  have hA : ⨆ p : P, (A p).1 = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨U, hU, hxU, e⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ f ⁻¹ᵁ V from hxV)
    exact Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), e⟩, hxU⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top A hA
  intro p
  have e : (A p).1 ≤ f ⁻¹ᵁ p.1.2.1 := p.2
  rw [IdealPullback.comap_ideal (I * J) f (A p) p.1.2 e]
  change ((I.ideal p.1.2) * (J.ideal p.1.2)).map (f.appLE _ _ e).hom =
    (I.comap f).ideal (A p) * (J.comap f).ideal (A p)
  rw [IdealPullback.comap_ideal I f (A p) p.1.2 e,
    IdealPullback.comap_ideal J f (A p) p.1.2 e, Ideal.map_mul]

end PhilipponIdealSheafProductPullback

end
end

/- PhilipponCartierProductFactors -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite IsLocalRing

namespace PhilipponCartierProductFactors

/-- If the product is generated by a nonzero element, at each prime some
product of one element from each ideal generates after localization. -/
theorem exists_factor {R : Type u} [CommRing R] [IsDomain R]
    (I J P : Ideal R) (hP : P ≠ ⊤) {g : R} (hg : g ≠ 0) (h : I * J = Ideal.span {g}) :
    ∃ a ∈ I, ∃ b ∈ J, ∃ c ∉ P, g * c = a * b := by
  classical
  by_contra hn
  push Not at hn
  have hle : I * J ≤ Ideal.span {g} * P := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have hab : a * b ∈ Ideal.span {g} := h ▸ Ideal.mul_mem_mul ha hb
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hab
    have hc' : g * c = a * b := by simpa only [mul_comm g c] using hc
    refine Ideal.mem_span_singleton_mul.mpr ⟨c, ?_, hc'⟩
    by_contra hnc
    exact hn a ha b hb c hnc hc'
  rw [h] at hle
  have hmem : g ∈ Ideal.span {g} * P := hle (Ideal.mem_span_singleton_self g)
  obtain ⟨c, hc, hgc⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have h1 : c = 1 := mul_left_cancel₀ hg (hgc.trans (mul_one g).symm)
  exact hP (Ideal.eq_top_of_isUnit_mem P hc (h1 ▸ isUnit_one))

/-- Cancellation of a nonzero principal ideal recovers both generators. -/
theorem span_factors {R : Type u} [CommRing R] [IsDomain R] (I J : Ideal R)
    {a b : R} (ha : a ∈ I) (hb : b ∈ J) (ha₀ : a ≠ 0) (hb₀ : b ≠ 0)
    (h : I * J = Ideal.span {a * b}) : I = Ideal.span {a} ∧ J = Ideal.span {b} := by
  have hI : Ideal.span {a} ≤ I := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)
  have hJ : Ideal.span {b} ≤ J := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hb)
  have e : I * J = Ideal.span {a} * Ideal.span {b} :=
    h.trans (Ideal.span_singleton_mul_span_singleton a b).symm
  constructor
  · refine le_antisymm ((Ideal.span_singleton_mul_left_mono hb₀).mp ?_) hI
    exact (Ideal.mul_mono le_rfl hJ).trans_eq e
  · refine le_antisymm ((Ideal.span_singleton_mul_right_mono ha₀).mp ?_) hJ
    exact (Ideal.mul_mono hI le_rfl).trans_eq e

/-- An invertible product of two actual ideals on an integral scheme
has invertible factors. The generating sections are obtained over a
principal open from a factor of the product outside the point prime. -/
theorem of_mul {X : Scheme.{u}} [IsIntegral X] {I J : X.IdealSheafData}
    (h : (I * J).IsInvertible) : I.IsInvertible ∧ J.IsInvertible := by
  have both (x : X) : ∃ (U : X.affineOpens) (c : Γ(X, U)), x ∈ X.basicOpen c ∧
      ∃ a ∈ nonZeroDivisors Γ(X, X.affineBasicOpen c),
      ∃ b ∈ nonZeroDivisors Γ(X, X.affineBasicOpen c),
        I.ideal (X.affineBasicOpen c) = Ideal.span {a} ∧
          J.ideal (X.affineBasicOpen c) = Ideal.span {b} := by
    obtain ⟨V, v, hx, g, hg, hprod⟩ := h x
    let U := X.affineBasicOpen v
    have hxU : x ∈ U.1 := hx
    letI : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    letI : IsDomain Γ(X, U) := IsIntegral.component_integral U.1
    let P := (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ U.1 x hxU).hom
    letI : P.IsPrime := inferInstanceAs
      (((maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ U.1 x hxU).hom)).IsPrime
    obtain ⟨a, ha, b, hb, c, hc, hgc⟩ := exists_factor (I.ideal U) (J.ideal U) P
      Ideal.IsPrime.ne_top' (nonZeroDivisors.ne_zero hg) hprod
    have hxc : x ∈ X.basicOpen c := (X.mem_basicOpen c x hxU).mpr (by
      change ¬ IsUnit (X.presheaf.germ U.1 x hxU c) → False at hc
      exact not_not.mp hc)
    let W := X.affineBasicOpen c
    have hWU : W.1 ≤ U.1 := X.basicOpen_le c
    letI : Nonempty W.1 := ⟨⟨x, hxc⟩⟩
    letI : IsDomain Γ(X, W) := IsIntegral.component_integral W.1
    let f := (X.presheaf.map (homOfLE hWU).op).hom
    letI : Algebra Γ(X, U) Γ(X, W) := f.toAlgebra
    letI : IsLocalization (.powers c) Γ(X, W) := U.2.isLocalization_basicOpen c
    have hfg : f g ∈ nonZeroDivisors Γ(X, W) :=
      IsLocalization.nonZeroDivisors_le_comap (M := .powers c) (S := Γ(X, W)) hg
    have hfc : IsUnit (f c) := IsLocalization.map_units (M := .powers c) (S := Γ(X, W))
      ⟨c, Submonoid.mem_powers _⟩
    have hab : f g * f c = f a * f b := by rw [← map_mul, ← map_mul, hgc]
    have hab₀ : f a * f b ≠ 0 := hab ▸ mul_ne_zero (nonZeroDivisors.ne_zero hfg) hfc.ne_zero
    have hfa : f a ∈ I.ideal W := by
      rw [← I.map_ideal hWU]
      exact Ideal.mem_map_of_mem f ha
    have hfb : f b ∈ J.ideal W := by
      rw [← J.map_ideal hWU]
      exact Ideal.mem_map_of_mem f hb
    have hWprod : I.ideal W * J.ideal W = Ideal.span {f a * f b} := by
      rw [← I.map_ideal hWU, ← J.map_ideal hWU, ← Ideal.map_mul]
      change Ideal.map f (I.ideal U * J.ideal U) = _
      rw [show I.ideal U * J.ideal U = Ideal.span {g} from hprod,
        Ideal.map_span, Set.image_singleton, ← hab, Ideal.span_singleton_mul_right_unit hfc]
    obtain ⟨hI, hJ⟩ := span_factors (I.ideal W) (J.ideal W) hfa hfb
      (left_ne_zero_of_mul hab₀) (right_ne_zero_of_mul hab₀) hWprod
    exact ⟨U, c, hxc, f a, mem_nonZeroDivisors_of_ne_zero (left_ne_zero_of_mul hab₀),
      f b, mem_nonZeroDivisors_of_ne_zero (right_ne_zero_of_mul hab₀), hI, hJ⟩
  constructor
  · intro x
    obtain ⟨U, c, hc, a, ha, b, hb, hI, hJ⟩ := both x
    exact ⟨U, c, hc, a, ha, hI⟩
  · intro x
    obtain ⟨U, c, hc, a, ha, b, hb, hI, hJ⟩ := both x
    exact ⟨U, c, hc, b, hb, hJ⟩

end PhilipponCartierProductFactors

end
end

/- PhilipponAdmissibleFlatteningSpec -/
section

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponentSeshadri
open PhilipponBlowup PhilipponSpecIdealCoordinates PhilipponAdmissibleDenominators
open PhilipponAdmissibleAffineCentreSpec

namespace PhilipponAdmissibleFlatteningSpec

/-- The finite-type map on spectra has an admissible flat strict
transform, with its centre constructed from the original denominator
and numerator ideals and the ideal of the excluded boundary. -/
theorem exists_centre {R B : CommRingCat.{u}} [IsDomain R] [IsDomain B]
    [IsNoetherianRing R] [IsNoetherianRing B]
    (f : R ⟶ B) (hf : Function.Injective f.hom) [IsDominant (Spec.map f)]
    {ι : Type v} [Fintype ι] (b : ι → B)
    (hgen : Function.Surjective (MvPolynomial.eval₂Hom f.hom b))
    (C : Ideal R) [Nonempty (openComplement C).toScheme]
    [IsOpenImmersion (Spec.map f ∣_ openComplement C)] :
    ∃ I : (Spec R).IdealSheafData, I.comap (openComplement C).ι = ⊤ ∧
      Flat (PhilipponBlowupComparison.map I (Spec.map f)) := by
  let p := Spec.map f
  let U := openComplement C
  obtain ⟨N, _, hP, hadm⟩ := adjusted_centres f b C C.fg_of_isNoetherianRing
  let D := denominators f.hom b
  let E := centre f.hom b
  let K := D ⊔ C ^ N
  let P := E ⊔ C ^ N
  let I := IdealPullback.specIdeal (K * P)
  have hI : I.comap U.ι = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    apply SetLike.coe_injective
    ext y
    rw [Scheme.IdealSheafData.support_comap]
    change y.val ∈ (I.support : Set (Spec R)) ↔ False
    rw [show I = IdealPullback.specIdeal (K * P) from rfl, PhilipponBlowupSupport.support_specIdeal]
    exact ⟨fun h => hadm y.val.asIdeal y.val.isPrime y.property h, False.elim⟩
  let S := p ⁻¹ᵁ U
  let s := S.ι
  let j := (p ∣_ U) ≫ U.ι
  have hs : s ≫ p = j := (morphismRestrict_ι p U).symm
  letI : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion ((p ∣_ U) ≫ U.ι))
  letI : Nonempty S.toScheme := by
    obtain ⟨u⟩ := (inferInstance : Nonempty U.toScheme)
    obtain ⟨_, hu, x, rfl⟩ :=
      p.denseRange.inter_open_nonempty (U : Set (Spec R)) U.isOpen ⟨u.val, u.property⟩
    exact ⟨⟨x, hu⟩⟩
  have hj : I.comap j = ⊤ := by
    change I.comap ((p ∣_ U) ≫ U.ι) = ⊤
    rw [Scheme.IdealSheafData.comap_comp, hI, Scheme.IdealSheafData.comap_top]
  have hsI : ((I.comap p).comap s) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, hs, hj]
  letI : IsIntegral (scheme I) := PhilipponBlowupIntegral.source_isIntegral _
    (PhilipponNagataProtectedChart.support_ne_top_of_unit I j hj)
  letI : IsIntegral (scheme (I.comap p)) := PhilipponBlowupIntegral.source_isIntegral _
    (PhilipponNagataProtectedChart.support_ne_top_of_unit _ s hsI)
  obtain ⟨s', j', hs', hj', _, _, hsj⟩ :=
    PhilipponStrictTransformLocalLift.exists_common_open I p s j hs hj
  letI := hs'
  letI := hj'
  let g := PhilipponBlowupComparison.map I p
  let a := projection I
  let p' := projection (I.comap p)
  have hga : g ≫ a = p' ≫ p := PhilipponBlowupComparison.map_projection I p
  letI : IsSeparated p := inferInstanceAs (IsSeparated (Spec.map f))
  letI : IsSeparated (g ≫ a) := by
    rw [hga]
    infer_instance
  letI : IsSeparated g := IsSeparated.of_comp g a
  have hprod : I = IdealPullback.specIdeal K * IdealPullback.specIdeal P := specIdeal_mul _ _
  have hY : ((IdealPullback.specIdeal K).comap a * (IdealPullback.specIdeal P).comap a).IsInvertible := by
    rw [← PhilipponIdealSheafProductPullback.comap_mul, ← hprod]
    exact nativeInvertible I
  have hX : ((IdealPullback.specIdeal K).comap (g ≫ a) *
      (IdealPullback.specIdeal P).comap (g ≫ a)).IsInvertible := by
    rw [← PhilipponIdealSheafProductPullback.comap_mul, ← hprod, hga, Scheme.IdealSheafData.comap_comp]
    exact nativeInvertible (I.comap p)
  have hden : (IdealPullback.specIdeal D).comap (g ≫ a) =
      (IdealPullback.specIdeal P).comap (g ≫ a) := by
    rw [hga, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    have hD' : (IdealPullback.specIdeal D).comap p = IdealPullback.specIdeal (D.map f.hom) :=
      IdealPullback.specIdeal_comap D f.hom
    have hP' : (IdealPullback.specIdeal P).comap p = IdealPullback.specIdeal (P.map f.hom) :=
      IdealPullback.specIdeal_comap P f.hom
    rw [hD', hP', show P.map f.hom = D.map f.hom from hP]
  refine ⟨I, hI, PhilipponStrictTransformLocalLift.flat_of_local_lifts I p s' j' hsj ?_⟩
  intro x
  obtain ⟨W, d, hx, hd, hd₀, hE⟩ := PhilipponFlatteningDenominatorChart.exists_chart
    a g x D E P (le_sup_left.trans le_sup_left) le_sup_left
    (PhilipponCartierProductFactors.of_mul hY).2
    (PhilipponCartierProductFactors.of_mul hX).2 hden
  letI : Nonempty W.1 := ⟨⟨g x, hx⟩⟩
  obtain ⟨l, hl⟩ :=
    PhilipponFlatteningDenominatorChart.exists_local_map f hf b hgen a W d hd hd₀ hE
  exact ⟨W.1, hx, l, hl⟩

end PhilipponAdmissibleFlatteningSpec

end
end

/- PhilipponStrictTransformRestriction -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponBlowup

namespace PhilipponStrictTransformRestriction

/-- The pullback of the blowup along a flat map, with the pulled-back
centre presented by a specified equal ideal. -/
theorem exists_blowup_pullback {X X₀ : Scheme.{u}} (I : X.IdealSheafData)
    (k : X₀ ⟶ X) [Flat k] (J : X₀.IdealSheafData) (h : I.comap k = J) :
    ∃ a : scheme J ⟶ scheme I, IsPullback (projection J) a k (projection I) := by
  subst J
  exact ⟨_, PhilipponBlowupBaseChange.isPullback I k⟩

/-- The actual strict-transform map commutes with flat restriction on
the target and its inverse-image restriction on the source. -/
theorem exists_pullback {X Y X₀ Y₀ : Scheme.{u}}
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (k : X₀ ⟶ X) [Flat k] (j : Y₀ ⟶ Y)
    (H : IsPullback k f₀ f j)
    (I : Y.IdealSheafData) (I₀ : Y₀.IdealSheafData) (hI : I.comap j = I₀)
    (b : scheme I₀ ⟶ scheme I) (Hb : IsPullback (projection I₀) b j (projection I)) :
    ∃ a : scheme (I₀.comap f₀) ⟶ scheme (I.comap f),
      IsPullback a (PhilipponBlowupComparison.map I₀ f₀)
        (PhilipponBlowupComparison.map I f) b := by
  let J := I.comap f
  let J₀ := I₀.comap f₀
  let g := PhilipponBlowupComparison.map I f
  let g₀ := PhilipponBlowupComparison.map I₀ f₀
  have hJ : J.comap k = J₀ := by
    change (I.comap f).comap k = I₀.comap f₀
    rw [← Scheme.IdealSheafData.comap_comp, H.w, Scheme.IdealSheafData.comap_comp, hI]
  obtain ⟨a, Ha⟩ := exists_blowup_pullback J k J₀ hJ
  have eq : a ≫ g = g₀ ≫ b := by
    have hfirst : (I.comap (projection J₀ ≫ f₀ ≫ j)).IsInvertible := by
      rw [← Category.assoc, Scheme.IdealSheafData.comap_comp, hI, Scheme.IdealSheafData.comap_comp]
      exact nativeInvertible J₀
    apply (existsUnique_lift I _ hfirst).unique
    · change a ≫ PhilipponBlowupComparison.map I f ≫ projection I = _
      rw [PhilipponBlowupComparison.map_projection, ← Category.assoc, ← Ha.w,
        Category.assoc, H.w]
    · change g₀ ≫ b ≫ projection I = _
      rw [← Hb.w, ← Category.assoc, PhilipponBlowupComparison.map_projection, Category.assoc]
  have outer := Ha.flip.paste_vert H
  rw [← PhilipponBlowupComparison.map_projection I f,
    ← PhilipponBlowupComparison.map_projection I₀ f₀] at outer
  exact ⟨a, outer.of_bot eq Hb.flip⟩

end PhilipponStrictTransformRestriction

end
end

/- PhilipponAdmissibleFlatteningAffine -/
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup PhilipponAdmissibleAffineCentreSpec

namespace PhilipponAdmissibleFlatteningAffine

/-- Transport the affine spectrum construction to the actual schemes
and their actual protected open immersion. -/
theorem exists_centre {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y] [IsAffine X] [IsAffine Y] [Nonempty U]
    (f : X ⟶ Y) [IsDominant f] [IsSeparated f] [LocallyOfFiniteType f]
    (j : U ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion (f ∣_ j.opensRange)] :
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧ Flat (PhilipponBlowupComparison.map I f) := by
  let R := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  let φ := f.appTop
  let p := Spec.map φ
  let eX := X.isoSpec
  let eY := Y.isoSpec
  let k := eX.hom
  let g := eY.hom
  let j₀ := j ≫ g
  have hkp : k ≫ p = f ≫ g := Scheme.isoSpec_hom_naturality f
  letI : IsDominant (k ≫ p) := by
    rw [hkp]
    infer_instance
  letI : IsDominant p := IsDominant.of_comp k p
  letI : IsOpenImmersion j₀ := inferInstanceAs (IsOpenImmersion (j ≫ g))
  letI : IsOpenImmersion (pullback.snd f j) :=
    (MorphismProperty.arrow_mk_iso_iff @IsOpenImmersion (morphismRestrictOpensRange f j)).mp
      inferInstance
  have H : IsPullback (pullback.fst f j ≫ k) (pullback.snd f j) p j₀ :=
    (IsPullback.of_hasPullback f j).of_iso (Iso.refl _) eX (Iso.refl _) eY
      (by simp [k]) (by simp) hkp.symm rfl
  letI : IsOpenImmersion (pullback.snd p j₀) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion H.isoPullback.hom,
      H.isoPullback_hom_snd]
    infer_instance
  letI : IsOpenImmersion (p ∣_ j₀.opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff @IsOpenImmersion (morphismRestrictOpensRange p j₀)).mpr
      inferInstance
  let C : Ideal R := PrimeSpectrum.vanishingIdeal (j₀.opensRange : Set (Spec R))ᶜ
  have hC : openComplement C = j₀.opensRange := by
    apply SetLike.coe_injective
    change (PrimeSpectrum.zeroLocus (C : Set R))ᶜ = (j₀.opensRange : Set (Spec R))
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      j₀.opensRange.isOpen.isClosed_compl.closure_eq, compl_compl]
  letI : Nonempty (openComplement C).toScheme := hC.symm ▸
    Nonempty.map (fun x : U => j₀.isoOpensRange.hom x) (inferInstance : Nonempty U)
  letI : IsOpenImmersion (p ∣_ openComplement C) := by rw [hC]; infer_instance
  letI : IsDomain R := inferInstanceAs (IsDomain Γ(Y, ⊤))
  letI : IsDomain B := inferInstanceAs (IsDomain Γ(X, ⊤))
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  letI : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  letI : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have hφ : Function.Injective φ.hom := f.app_injective ⊤
  letI : Algebra R B := φ.hom.toAlgebra
  have hft : φ.hom.FiniteType := HasRingHomProperty.appTop (@LocallyOfFiniteType) f inferInstance
  letI : Algebra.FiniteType R B := hft
  obtain ⟨n, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)
  let b : Fin n → B := fun i => ψ (MvPolynomial.X i)
  have hgen : Function.Surjective (MvPolynomial.eval₂Hom φ.hom b) := by
    have heq : MvPolynomial.eval₂Hom φ.hom b = ψ.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro x
        rw [MvPolynomial.eval₂Hom_C]
        exact (ψ.commutes x).symm
      · intro i
        rw [MvPolynomial.eval₂Hom_X']
        rfl
    rw [heq]
    exact hψ
  obtain ⟨I, hI, hflat⟩ := PhilipponAdmissibleFlatteningSpec.exists_centre φ hφ b hgen C
  let J := I.comap g
  have hI' : I.comap j₀ = ⊤ := by
    have hj : I.comap j₀.opensRange.ι = ⊤ := by rwa [← hC]
    rw [← j₀.isoOpensRange_hom_ι, Scheme.IdealSheafData.comap_comp, hj,
      Scheme.IdealSheafData.comap_top]
  have hJ : J.comap j = ⊤ := by
    change (I.comap g).comap j = ⊤
    rw [← Scheme.IdealSheafData.comap_comp]
    exact hI'
  have Hiso : IsPullback k f p g := IsPullback.of_horiz_isIso ⟨hkp⟩
  obtain ⟨a, Ha⟩ := PhilipponStrictTransformRestriction.exists_pullback p f k g Hiso
    I J rfl (PhilipponBlowupBaseChange.map I g) (PhilipponBlowupBaseChange.isPullback I g)
  exact ⟨J, hJ, MorphismProperty.of_isPullback Ha hflat⟩

end PhilipponAdmissibleFlatteningAffine

end
end

/- PhilipponBlowupUniversalFlat -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory
open OAI.PiExponentSeshadri.Geometry
open PhilipponBlowup

namespace PhilipponBlowupUniversalFlat

/-- Universal blowups with the same centre are isomorphic over the
base. The unique comparison therefore has the same flatness. -/
theorem flat_of_universal {X Y X' Y' : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (p : X' ⟶ X) (q : Y' ⟶ Y) (m : X' ⟶ Y') (hm : m ≫ q = p ≫ f)
    (hP : ((I.comap f).comap p).IsInvertible) (hQ : (I.comap q).IsInvertible)
    (hp : ∀ (Z : Scheme.{u}) (g : Z ⟶ X), ((I.comap f).comap g).IsInvertible →
      ∃! l : Z ⟶ X', l ≫ p = g)
    (hq : ∀ (Z : Scheme.{u}) (g : Z ⟶ Y), (I.comap g).IsInvertible →
      ∃! l : Z ⟶ Y', l ≫ q = g)
    [Flat (PhilipponBlowupComparison.map I f)] : Flat m := by
  let Hx : IsBlowup (I.comap f) p :=
    ⟨(PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mpr hP,
      fun Z g h => hp Z g ((PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mp h)⟩
  let Hy : IsBlowup I q :=
    ⟨(PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mpr hQ,
      fun Z g h => hq Z g ((PhilipponNativeBlowupIdealBridge.invertible_iff _ _).mp h)⟩
  let eX := Hx.iso (isBlowup (I.comap f))
  let eY := Hy.iso (isBlowup I)
  have hX : eX.hom ≫ projection (I.comap f) = p := Hx.iso_hom_comp _
  have hY : eY.hom ≫ projection I = q := Hy.iso_hom_comp _
  have hcomp : (I.comap (p ≫ f)).IsInvertible := by
    rwa [Scheme.IdealSheafData.comap_comp]
  have he : m ≫ eY.hom = eX.hom ≫ PhilipponBlowupComparison.map I f := by
    apply (existsUnique_lift I _ hcomp).unique
    · rw [Category.assoc, hY, hm]
    · rw [Category.assoc, PhilipponBlowupComparison.map_projection, ← Category.assoc, hX]
  apply (MorphismProperty.cancel_right_of_respectsIso @Flat m eY.hom).mp
  rw [he]
  infer_instance

end PhilipponBlowupUniversalFlat

end
end

/- PhilipponAdmissibleAffineSolution -/
section

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory

theorem solution
    {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y] [IsAffine X] [IsAffine Y] [Nonempty U]
    (f : X ⟶ Y) [IsDominant f] [IsSeparated f] [LocallyOfFiniteType f]
    (j : U ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion (f ∣_ j.opensRange)] :
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧
      ∀ (X' Y' : Scheme.{u}) (p : X' ⟶ X) (q : Y' ⟶ Y) (m : X' ⟶ Y'),
        m ≫ q = p ≫ f →
        ((I.comap f).comap p).IsInvertible →
        (I.comap q).IsInvertible →
        (∀ (Z : Scheme.{u}) (g : Z ⟶ X), ((I.comap f).comap g).IsInvertible →
          ∃! l : Z ⟶ X', l ≫ p = g) →
        (∀ (Z : Scheme.{u}) (g : Z ⟶ Y), (I.comap g).IsInvertible →
          ∃! l : Z ⟶ Y', l ≫ q = g) →
        Flat m := by
  obtain ⟨I, hI, hflat⟩ := PhilipponAdmissibleFlatteningAffine.exists_centre f j
  letI := hflat
  exact ⟨I, hI, fun _ _ p q m hm hP hQ hp hq =>
    PhilipponBlowupUniversalFlat.flat_of_universal I f p q m hm hP hQ hp hq⟩

end
end

#print axioms PhilipponNativeBlowupIdealBridge.nonZeroDivisors_map_equiv
#print axioms PhilipponNativeBlowupIdealBridge.invertible_iff
#print axioms PhilipponAffineBlowupUniversal.invertible_unique
#print axioms PhilipponAffineBlowupUniversal.local_lift
#print axioms PhilipponAffineBlowupUniversal.universal
#print axioms PhilipponAffineBlowupUniversal.existsUnique_lift
#print axioms PhilipponAffineBlowupCenter.presents
#print axioms PhilipponAffineBlowupCenter.nativeInvertible
#print axioms PhilipponAffineBlowupCenter.isBlowup
#print axioms PhilipponAffineBlowup.isBlowup
#print axioms PhilipponAffineBlowup.projection_proper
#print axioms PhilipponBlowup.gluing
#print axioms PhilipponBlowup.local_pullback
#print axioms PhilipponBlowup.nativeInvertible
#print axioms PhilipponBlowup.existsUnique_lift
#print axioms PhilipponBlowup.isBlowup
#print axioms PhilipponBlowup.projection_proper
#print axioms PhilipponBlowupSupport.support_specIdeal
#print axioms PhilipponBlowupSupport.affine_preimage_support
#print axioms PhilipponBlowupSupport.affine_preimage_difference
#print axioms PhilipponBlowupSupport.strict_preimage
#print axioms PhilipponIdealStalkComparison.map_germ_of_le
#print axioms PhilipponIdealStalkComparison.map_germ_eq
#print axioms PhilipponSpecIdealCoordinates.map_coordinates
#print axioms PhilipponSpecIdealCoordinates.ideal_comap
#print axioms PhilipponSpecIdealCoordinates.specIdeal_mono
#print axioms PhilipponSpecIdealCoordinates.specIdeal_mul
#print axioms PhilipponSpecIdealCoordinates.coordinates_germ
#print axioms PhilipponSpecIdealCoordinates.map_ideal_to_stalk
#print axioms PhilipponSpecIdealCoordinates.coordinates_res
#print axioms PhilipponSpecIdealCoordinates.ideal_germ
#print axioms PhilipponAdmissibleDenominators.denominators_not_le
#print axioms PhilipponAdmissibleDenominators.centre_not_le
#print axioms PhilipponAdmissibleDenominators.map_centre
#print axioms PhilipponAdmissibleDenominators.adjoin_le_of_principal
#print axioms PhilipponAdmissibleAffineCentre.exists_adjusted_centres
#print axioms PhilipponAdmissibleAffineCentre.eq_span_of_map_eq_span
#print axioms PhilipponAdmissibleAffineCentre.exists_generator_away
#print axioms PhilipponAffineDenominatorLift.common_numerator
#print axioms PhilipponAffineDenominatorLift.exists_lift
#print axioms PhilipponCartierSections.regular_of_germs
#print axioms PhilipponCartierSections.exists_local_quotient
#print axioms PhilipponCartierSections.existsUnique_quotient
#print axioms PhilipponCrossingPointHom.pointHom
#print axioms PhilipponNodeFactorCharts.overlapEquiv
#print axioms PhilipponNodeFactorCharts.charts_agree_on_overlap
#print axioms PhilipponNodeCartierLocalLift.regular_generator_or
#print axioms PhilipponNodeCartierLocalLift.exists_unique_chart_lift
#print axioms PhilipponNodeCartierLocalLift.chart_lifts_overlap
#print axioms PhilipponCartierLocalGenerator.regular_germs_of_affine
#print axioms PhilipponCartierLocalGenerator.exists_regular_neighborhood
#print axioms PhilipponCartierLocalGenerator.exists_local_generator
#print axioms PhilipponFlatteningDenominatorChart.exists_chart
#print axioms PhilipponFlatteningDenominatorChart.exists_local_map
#print axioms PhilipponReducedClosedSubscheme.isReduced_iff_radical_eq
#print axioms PhilipponReducedClosedSubscheme.integral_of_prime_top
#print axioms PhilipponReducedClosedSubscheme.radical_comap_open
#print axioms PhilipponReducedClosedSubscheme.eq_of_reduced_support
#print axioms PhilipponSchemeImageIntegral.ker_radical
#print axioms PhilipponSchemeImageIntegral.image_isReduced
#print axioms PhilipponSchemeImageIntegral.image_isIntegral
#print axioms PhilipponNagataGraphClosure.isPullback_of_dense_open
#print axioms PhilipponNagataGraphClosure.exists_common_graph
#print axioms PhilipponNagataGraphClosure.exists_common_proper_graph
#print axioms PhilipponTwoOpenChartIntegral.integral_of_charts
#print axioms PhilipponNagataExtensionProduct.range_fst
#print axioms PhilipponNagataExtensionProduct.isOpenImmersion_chart
#print axioms PhilipponNagataExtensionProduct.integral_product
#print axioms PhilipponOpenIdealExtension.comap_map
#print axioms PhilipponOpenIdealExtension.support_map
#print axioms PhilipponOpenIdealExtension.unit_on_protected
#print axioms PhilipponBlowupBaseChange.invertible_comap
#print axioms PhilipponBlowupBaseChange.flat_baseChange
#print axioms PhilipponBlowupBaseChange.iso
#print axioms PhilipponBlowupBaseChange.map_projection
#print axioms PhilipponBlowupBaseChange.isPullback
#print axioms PhilipponBlowupCartier.isIso_of_invertible
#print axioms PhilipponBlowupCartier.projection_isIso
#print axioms PhilipponBlowupCartier.pullback_isIso
#print axioms PhilipponBlowupCartier.unit_open_unchanged
#print axioms PhilipponOpenBlowupExtension.pulled_isBlowup
#print axioms PhilipponOpenBlowupExtension.iso
#print axioms PhilipponOpenBlowupExtension.isPullback
#print axioms PhilipponOpenBlowupExtension.protected_unchanged
#print axioms PhilipponAdmissibleBlowupExtension.unit_on_open
#print axioms PhilipponAdmissibleBlowupExtension.extended_unit_on_open
#print axioms PhilipponAdmissibleBlowupExtension.extends_admissibly
#print axioms PhilipponBlowupIntegral.affine_rees_isIntegral
#print axioms PhilipponBlowupIntegral.global_isReduced
#print axioms PhilipponBlowupIntegral.complementLift
#print axioms PhilipponBlowupIntegral.complement_dense
#print axioms PhilipponBlowupIntegral.source_isIntegral
#print axioms PhilipponBlowupModification.projection_isDominant
#print axioms PhilipponBlowupModification.restrict_isIso
#print axioms PhilipponBlowupModification.exists_dense_open_isIso
#print axioms PhilipponBlowupModification.properties
#print axioms PhilipponBlowupComparison.composite_invertible
#print axioms PhilipponBlowupComparison.map
#print axioms PhilipponBlowupComparison.comparison
#print axioms PhilipponBlowupComparison.comparison_proper
#print axioms PhilipponNagataProtectedChart.exists_unit_lift
#print axioms PhilipponNagataProtectedChart.support_ne_top_of_unit
#print axioms PhilipponAdmissibleAffineCentreSpec.isIso_stalkMap_over
#print axioms PhilipponAdmissibleAffineCentreSpec.denominators_not_le_of_stalkIso
#print axioms PhilipponAdmissibleAffineCentreSpec.adjusted_centres
#print axioms PhilipponStrictTransformLocalLift.isIso_of_open_section
#print axioms PhilipponStrictTransformLocalLift.flat_of_local_lifts
#print axioms PhilipponStrictTransformLocalLift.exists_common_open
#print axioms PhilipponIdealSheafProductPullback.comap_mul
#print axioms PhilipponCartierProductFactors.exists_factor
#print axioms PhilipponCartierProductFactors.span_factors
#print axioms PhilipponCartierProductFactors.of_mul
#print axioms PhilipponAdmissibleFlatteningSpec.exists_centre
#print axioms PhilipponStrictTransformRestriction.exists_blowup_pullback
#print axioms PhilipponStrictTransformRestriction.exists_pullback
#print axioms PhilipponAdmissibleFlatteningAffine.exists_centre
#print axioms PhilipponBlowupUniversalFlat.flat_of_universal
#print axioms solution
