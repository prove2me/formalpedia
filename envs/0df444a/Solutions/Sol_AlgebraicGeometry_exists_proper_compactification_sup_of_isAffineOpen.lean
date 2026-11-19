-- Prove2me | solution 1 for AlgebraicGeometry.exists_proper_compactification_sup_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-18T15:45:02.957481+00:00
-- url     : https://prove2.me/submissions/ab3e4d38-157b-4464-b39a-3a9d073c8cda

import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_OAIQ068A013
import Definitions.Def_OAIQ068A020
import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_two_chart_blowup_model_of_isAffineOpen

universe u v

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

section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup PhilipponNagataProtectedChart

namespace PhilipponNagataChartLifts

/-- A dominating modification can lift a map from a chart once the
extension of the pulled-back centre becomes invertible. -/
theorem chart_invertible {G Z A : Scheme.{u}} (D : G.Opens) [QuasiCompact D.ι]
    (a : D.toScheme ⟶ A) (I : A.IdealSheafData) (p : Z ⟶ G)
    (h : (((I.comap a).map D.ι).comap p).IsInvertible) :
    (I.comap ((p ∣_ D) ≫ a)).IsInvertible := by
  have H := PhilipponBlowupBaseChange.invertible_comap _ h (p ⁻¹ᵁ D).ι
  rw [← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι,
    Scheme.IdealSheafData.comap_comp, PhilipponOpenIdealExtension.comap_map,
    ← Scheme.IdealSheafData.comap_comp] at H
  exact H

theorem lift_protected_open {G Z U : Scheme.{u}} (p : Z ⟶ G) (D : G.Opens)
    (t : U ⟶ Z) [IsOpenImmersion t] (s : U ⟶ D.toScheme)
    (h : s ≫ D.ι = t ≫ p) :
    ∃ v : U ⟶ (p ⁻¹ᵁ D).toScheme,
      IsOpenImmersion v ∧ v ≫ (p ⁻¹ᵁ D).ι = t ∧ v ≫ p ∣_ D = s := by
  let P := isPullback_morphismRestrict p D
  let v := P.lift s t h
  have hv : v ≫ (p ⁻¹ᵁ D).ι = t := P.lift_snd s t h
  letI : IsOpenImmersion (v ≫ (p ⁻¹ᵁ D).ι) := hv ▸ inferInstanceAs (IsOpenImmersion t)
  exact ⟨v, IsOpenImmersion.of_comp v (p ⁻¹ᵁ D).ι, hv, P.lift_fst s t h⟩

/-- One blowup of the proper graph suffices to lift both chart maps.
Its centre is the product of the extensions of the two centres pulled
back to the graph's open cover. -/
theorem simultaneous_lifts {G A B U : Scheme.{u}} [IsIntegral G]
    [IsLocallyNoetherian G] [Nonempty U]
    (D E : G.Opens) [QuasiCompact D.ι] [QuasiCompact E.ι]
    (a : D.toScheme ⟶ A) (b : E.toScheme ⟶ B)
    (I : A.IdealSheafData) (J : B.IdealSheafData)
    (s : U ⟶ G) [IsOpenImmersion s]
    (sD : U ⟶ D.toScheme) (sE : U ⟶ E.toScheme)
    (hsD : sD ≫ D.ι = s) (hsE : sE ≫ E.ι = s)
    (hI : I.comap (sD ≫ a) = ⊤) (hJ : J.comap (sE ≫ b) = ⊤) :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ G) (t : U ⟶ Z)
      (tD : U ⟶ (p ⁻¹ᵁ D).toScheme) (tE : U ⟶ (p ⁻¹ᵁ E).toScheme),
      IsIntegral Z ∧ IsProper p ∧ IsOpenImmersion t ∧ t ≫ p = s ∧
      IsOpenImmersion tD ∧ IsOpenImmersion tE ∧
      tD ≫ (p ⁻¹ᵁ D).ι = t ∧ tE ≫ (p ⁻¹ᵁ E).ι = t ∧
      tD ≫ p ∣_ D = sD ∧ tE ≫ p ∣_ E = sE ∧
      (I.comap ((p ∣_ D) ≫ a)).IsInvertible ∧
      (J.comap ((p ∣_ E) ≫ b)).IsInvertible := by
  let P := (I.comap a).map D.ι
  let Q := (J.comap b).map E.ι
  have hP : P.comap s = ⊤ := by
    rw [← hsD]
    apply PhilipponOpenIdealExtension.unit_on_protected
    rwa [← Scheme.IdealSheafData.comap_comp]
  have hQ : Q.comap s = ⊤ := by
    rw [← hsE]
    apply PhilipponOpenIdealExtension.unit_on_protected
    rwa [← Scheme.IdealSheafData.comap_comp]
  have hPQ : (P * Q).comap s = ⊤ := by
    rw [PhilipponIdealSheafProductPullback.comap_mul, hP, hQ, Scheme.IdealSheafData.top_mul]
  let Z := scheme (P * Q)
  let p := projection (P * Q)
  letI : IsIntegral Z := PhilipponBlowupIntegral.source_isIntegral _ (support_ne_top_of_unit _ s hPQ)
  have H : (P.comap p * Q.comap p).IsInvertible := by
    rw [← PhilipponIdealSheafProductPullback.comap_mul]
    exact nativeInvertible (P * Q)
  obtain ⟨hP', hQ'⟩ := PhilipponCartierProductFactors.of_mul H
  obtain ⟨t, ht, htp⟩ := exists_unit_lift (P * Q) s hPQ
  letI := ht
  obtain ⟨tD, htD, htDι, htDr⟩ := lift_protected_open p D t sD (hsD.trans htp.symm)
  obtain ⟨tE, htE, htEι, htEr⟩ := lift_protected_open p E t sE (hsE.trans htp.symm)
  exact ⟨Z, p, t, tD, tE, inferInstance,
    inferInstanceAs (IsProper (projection (P * Q))), ht, htp, htD, htE,
    htDι, htEι, htDr, htEr, chart_invertible D a I p hP', chart_invertible E b J p hQ'⟩

end PhilipponNagataChartLifts

end
end

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponNagataSeparatedGluing

/-- A separated finite-type target is proper once a proper model maps
dominantly to it over the base. The map is proper and therefore surjective. -/
theorem proper_of_dominant_model {G W T : Scheme.{u}} (p : W ⟶ T)
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (a : G ⟶ W) [IsDominant a] [IsProper (a ≫ p)] : IsProper p := by
  letI : IsProper a := IsProper.of_comp a p
  letI : Surjective a := surjective_of_isDominant_of_isClosed_range a a.isClosedMap.isClosed_range
  letI : UniversallyClosed p := UniversallyClosed.of_comp_surjective a p
  exact ⟨⟩

end PhilipponNagataSeparatedGluing

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponNagataDominatingGraph

/-- Maps over the base agree on an overlap when they agree on a
nonempty open of that overlap in an integral scheme. -/
theorem compatible {Z L R U W S : Scheme.{u}} [IsIntegral Z] [Nonempty U]
    (i : L ⟶ Z) (j : R ⟶ Z) [IsOpenImmersion i] [IsOpenImmersion j]
    (tL : U ⟶ L) (tR : U ⟶ R) [IsOpenImmersion tL]
    (ht : tL ≫ i = tR ≫ j)
    (p : W ⟶ S) [IsSeparated p] (g : Z ⟶ S)
    (m : L ⟶ W) (n : R ⟶ W) (hm : m ≫ p = i ≫ g) (hn : n ≫ p = j ≫ g)
    (hU : tL ≫ m = tR ≫ n) :
    pullback.fst i j ≫ m = pullback.snd i j ≫ n := by
  let l := pullback.lift tL tR ht
  have hl : l ≫ pullback.fst i j = tL := pullback.lift_fst _ _ _
  letI : IsOpenImmersion (l ≫ pullback.fst i j) := hl ▸ inferInstanceAs (IsOpenImmersion tL)
  letI : IsOpenImmersion l := IsOpenImmersion.of_comp l (pullback.fst i j)
  letI : Nonempty ↥(pullback i j) := Nonempty.map (fun x : U => l x) ‹Nonempty U›
  letI : IsOpenImmersion (pullback.fst i j ≫ i) := inferInstance
  letI : IsIntegral (pullback i j) := isIntegral_of_isOpenImmersion (pullback.fst i j ≫ i)
  letI : IsDominant l := ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace l l.isOpenMap⟩
  have hbase : (pullback.fst i j ≫ m) ≫ p = (pullback.snd i j ≫ n) ≫ p := by
    rw [Category.assoc, hm, Category.assoc, hn, pullback.condition_assoc]
  refine ext_of_isDominant_of_isSeparated p hbase l ?_
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd, l] using hU

/-- Glue the two maps at the level of the proper source. -/
theorem glue_two {Z L R U W S : Scheme.{u}} [IsIntegral Z] [Nonempty U]
    (i : L ⟶ Z) (j : R ⟶ Z) [IsOpenImmersion i] [IsOpenImmersion j]
    (hcover : ∀ x : Z, (∃ y, i y = x) ∨ ∃ y, j y = x)
    (tL : U ⟶ L) (tR : U ⟶ R) [IsOpenImmersion tL]
    (ht : tL ≫ i = tR ≫ j)
    (p : W ⟶ S) [IsSeparated p] (g : Z ⟶ S)
    (m : L ⟶ W) (n : R ⟶ W) (hm : m ≫ p = i ≫ g) (hn : n ≫ p = j ≫ g)
    (hU : tL ≫ m = tR ≫ n) :
    ∃ b : Z ⟶ W, i ≫ b = m ∧ j ≫ b = n ∧ b ≫ p = g := by
  let C := PhilipponTwoOpenChartIntegral.cover i j hcover
  let f : ∀ z : C.I₀, C.X z ⟶ W := fun z => match z with
    | false => m
    | true => n
  have H (x y : C.I₀) : pullback.fst (C.f x) (C.f y) ≫ f x =
      pullback.snd (C.f x) (C.f y) ≫ f y := by
    change Bool at x y
    cases x <;> cases y
    · change pullback.fst i i ≫ m = pullback.snd i i ≫ m
      rw [(cancel_mono i).mp (pullback.condition (f := i) (g := i))]
    · exact compatible i j tL tR ht p g m n hm hn hU
    · change pullback.fst j i ≫ n = pullback.snd j i ≫ m
      rw [← cancel_epi (pullbackSymmetry i j).hom]
      simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
        using (compatible i j tL tR ht p g m n hm hn hU).symm
    · change pullback.fst j j ≫ n = pullback.snd j j ≫ n
      rw [(cancel_mono j).mp (pullback.condition (f := j) (g := j))]
  let b := C.glueMorphisms f H
  have hL : i ≫ b = m := C.ι_glueMorphisms f H false
  have hR : j ≫ b = n := C.ι_glueMorphisms f H true
  refine ⟨b, hL, hR, C.hom_ext _ _ ?_⟩
  intro k
  change Bool at k
  cases k
  · change i ≫ b ≫ p = i ≫ g
    rw [← Category.assoc, hL, hm]
  · change j ≫ b ≫ p = j ≫ g
    rw [← Category.assoc, hR, hn]

/-- Properness from a covering of a proper integral graph by two charts
whose maps land in the bases of the indicated blowups. -/
theorem proper_of_chart_blowups {G A B L R U W S : Scheme.{u}} [IsIntegral G]
    [IsLocallyNoetherian G] [Nonempty U]
    (g : G ⟶ S) [IsProper g] (q : W ⟶ S)
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (D E : G.Opens) [QuasiCompact D.ι] [QuasiCompact E.ι] (hcover : D ⊔ E = ⊤)
    (a : D.toScheme ⟶ A) (b : E.toScheme ⟶ B)
    (qA : A ⟶ S) (qB : B ⟶ S)
    (ha : a ≫ qA = D.ι ≫ g) (hb : b ≫ qB = E.ι ≫ g)
    (I : A.IdealSheafData) (J : B.IdealSheafData)
    (pL : L ⟶ A) (pR : R ⟶ B)
    (liftL : ∀ {Y : Scheme.{u}} (f : Y ⟶ A), (I.comap f).IsInvertible →
      ∃! l : Y ⟶ L, l ≫ pL = f)
    (liftR : ∀ {Y : Scheme.{u}} (f : Y ⟶ B), (J.comap f).IsInvertible →
      ∃! r : Y ⟶ R, r ≫ pR = f)
    (iL : L ⟶ W) (iR : R ⟶ W)
    (hiL : iL ≫ q = pL ≫ qA) (hiR : iR ≫ q = pR ≫ qB)
    (s : U ⟶ G) [IsOpenImmersion s]
    (sD : U ⟶ D.toScheme) (sE : U ⟶ E.toScheme)
    (hsD : sD ≫ D.ι = s) (hsE : sE ≫ E.ι = s)
    (hI : I.comap (sD ≫ a) = ⊤) (hJ : J.comap (sE ≫ b) = ⊤)
    (sL : U ⟶ L) (sR : U ⟶ R) (d : U ⟶ W) [IsDominant d]
    (hsL : sL ≫ pL = sD ≫ a) (hsR : sR ≫ pR = sE ≫ b)
    (hdL : sL ≫ iL = d) (hdR : sR ≫ iR = d) :
    IsProper q := by
  obtain ⟨Z, p, t, tD, tE, hZ, hp, ht, _, htD, _, htDι, htEι, htDr, htEr, hIL, hJR⟩ :=
    PhilipponNagataChartLifts.simultaneous_lifts D E a b I J s sD sE hsD hsE hI hJ
  letI := hZ
  letI := hp
  letI := htD
  obtain ⟨m, hm, _⟩ := liftL _ hIL
  obtain ⟨n, hn, _⟩ := liftR _ hJR
  have hml : tD ≫ m = sL := by
    apply (liftL _ (hI ▸ Scheme.IdealSheafData.isInvertible_top)).unique
    · rw [Category.assoc, hm, ← Category.assoc, htDr]
    · exact hsL
  have hnr : tE ≫ n = sR := by
    apply (liftR _ (hJ ▸ Scheme.IdealSheafData.isInvertible_top)).unique
    · rw [Category.assoc, hn, ← Category.assoc, htEr]
    · exact hsR
  have hcover' : (p ⁻¹ᵁ D) ⊔ (p ⁻¹ᵁ E) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  have hsurj : ∀ x : Z, (∃ y, (p ⁻¹ᵁ D).ι y = x) ∨ ∃ y, (p ⁻¹ᵁ E).ι y = x := by
    intro x
    have hx : x ∈ (p ⁻¹ᵁ D) ⊔ (p ⁻¹ᵁ E) := hcover' ▸ trivial
    rcases hx with hx | hx
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  have hm' : (m ≫ iL) ≫ q = (p ⁻¹ᵁ D).ι ≫ (p ≫ g) := by
    rw [Category.assoc, hiL, ← Category.assoc, hm, Category.assoc, ha, morphismRestrict_ι_assoc]
  have hn' : (n ≫ iR) ≫ q = (p ⁻¹ᵁ E).ι ≫ (p ≫ g) := by
    rw [Category.assoc, hiR, ← Category.assoc, hn, Category.assoc, hb, morphismRestrict_ι_assoc]
  have hd : tD ≫ (m ≫ iL) = tE ≫ (n ≫ iR) := by
    rw [← Category.assoc, hml, hdL, ← Category.assoc, hnr, hdR]
  obtain ⟨c, hc, _, hcq⟩ :=
    glue_two (p ⁻¹ᵁ D).ι (p ⁻¹ᵁ E).ι hsurj tD tE (htDι.trans htEι.symm)
      q (p ≫ g) (m ≫ iL) (n ≫ iR) hm' hn' hd
  have htd : t ≫ c = d := by
    rw [← htDι, Category.assoc, hc, ← Category.assoc, hml, hdL]
  letI : IsDominant (t ≫ c) := htd ▸ inferInstanceAs (IsDominant d)
  letI : IsDominant c := IsDominant.of_comp t c
  letI : IsProper (c ≫ q) := hcq ▸ inferInstanceAs (IsProper (p ≫ g))
  exact PhilipponNagataSeparatedGluing.proper_of_dominant_model q c

end PhilipponNagataDominatingGraph

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π]
    (U V : X.Opens) (hU : Nonempty U) (hV : Nonempty V) (hAff : IsAffineOpen V)
    (C : Scheme.{u}) (q : C ⟶ Spec (.of K)) [IsProper q]
    (j : U.toScheme ⟶ C) [IsOpenImmersion j] (hj : j ≫ q = U.ι ≫ π) :
    ∃ (D : Scheme.{u}) (p : D ⟶ Spec (.of K)) (i : (U ⊔ V).toScheme ⟶ D),
      IsProper p ∧ IsOpenImmersion i ∧ i ≫ p = (U ⊔ V).ι ≫ π := by
  obtain ⟨W, G, O, A, B, L, R, w, g, i, v, s, D, E, sD, sE, a, b, qA, qB,
    I, J, pL, pR, iL, iR, sL, sR, hi, hiw, hwsep, hwft, hwqc, hG, hg, hO, hs, hd,
    hcover, hsD, hsE, ha, hb, hI, hJ, liftL, liftR, hiL, hiR, hsL, hsR, hdL, hdR⟩ :=
    AlgebraicGeometry.exists_two_chart_blowup_model_of_isAffineOpen K π U V hU hV hAff C q j hj
  letI := hwsep
  letI := hwft
  letI := hwqc
  letI := hG
  letI := hg
  letI := hO
  letI := hs
  letI := hd
  letI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace g
  letI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian g
  letI : IsNoetherian G := ⟨⟩
  letI : NoetherianSpace D.toScheme := by
    change NoetherianSpace ↥(D : Set G)
    exact (noetherianSpace_set_iff _).mpr (fun Z _ => NoetherianSpace.isCompact Z)
  letI : NoetherianSpace E.toScheme := by
    change NoetherianSpace ↥(E : Set G)
    exact (noetherianSpace_set_iff _).mpr (fun Z _ => NoetherianSpace.isCompact Z)
  exact ⟨W, w, i, PhilipponNagataDominatingGraph.proper_of_chart_blowups g w D E hcover
    a b qA qB ha hb I J pL pR (fun {Y} f h => liftL Y f h) (fun {Y} f h => liftR Y f h)
    iL iR hiL hiR s sD sE hsD hsE hI hJ sL sR (v ≫ i) hsL hsR hdL hdR, hi, hiw⟩

end
end

#print axioms PhilipponOpenIdealExtension.comap_map
#print axioms PhilipponOpenIdealExtension.support_map
#print axioms PhilipponOpenIdealExtension.unit_on_protected
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
#print axioms PhilipponCartierProductFactors.exists_factor
#print axioms PhilipponCartierProductFactors.span_factors
#print axioms PhilipponCartierProductFactors.of_mul
#print axioms PhilipponIdealSheafProductPullback.comap_mul
#print axioms PhilipponTwoOpenChartIntegral.integral_of_charts
#print axioms PhilipponNagataChartLifts.chart_invertible
#print axioms PhilipponNagataChartLifts.lift_protected_open
#print axioms PhilipponNagataChartLifts.simultaneous_lifts
#print axioms PhilipponNagataSeparatedGluing.proper_of_dominant_model
#print axioms PhilipponNagataDominatingGraph.compatible
#print axioms PhilipponNagataDominatingGraph.glue_two
#print axioms PhilipponNagataDominatingGraph.proper_of_chart_blowups
#print axioms solution
