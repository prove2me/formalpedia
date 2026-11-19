-- Prove2me | solution 1 for AlgebraicGeometry.exists_admissible_flattening_of_open_iso
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-18T17:16:47.692167+00:00
-- url     : https://prove2.me/submissions/ef8314c3-a79d-4a5f-b20e-86693405d23a

import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_MvPolynomial_CrossingResolution
import Definitions.Def_OAIQ068A013
import Definitions.Def_OAIQ068A020
import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_exists_admissible_flattening_of_affine_open_immersion

universe u v

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

/- PhilipponInvertibleIdealDominantPullback -/
section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace


namespace PhilipponInvertibleIdealDominantPullback

theorem ne_bot {Y : Scheme.{u}} [Nonempty Y] (I : Y.IdealSheafData) (hI : I.IsInvertible) :
    I ≠ ⊥ := by
  intro hbot
  let y : Y := Classical.choice inferInstance
  obtain ⟨V, f, hy, r, hr, hgen⟩ := hI y
  rw [hbot, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at hgen
  have hr0 : r = 0 := Ideal.span_singleton_eq_bot.mp hgen.symm
  have hreg := PhilipponCartierLocalGenerator.regular_germs_of_affine
    (Y.affineBasicOpen f).2 r hr y hy
  rw [hr0, map_zero] at hreg
  exact nonZeroDivisors.ne_zero hreg rfl

theorem support_ne_univ {Y : Scheme.{u}} [IsIntegral Y]
    (I : Y.IdealSheafData) (hI : I.IsInvertible) : (I.support : Set Y) ≠ Set.univ := by
  intro htop
  apply ne_bot I hI
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  exact SetLike.coe_injective htop

/-- A dominant map between integral schemes preserves every already
invertible ideal. The support condition is derived from dominance. -/
theorem isInvertible_comap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (I : Y.IdealSheafData) (hI : I.IsInvertible) (p : X ⟶ Y) [IsDominant p] :
    (I.comap p).IsInvertible := by
  apply hI.comap_of_isIntegral p
  intro hfull
  have hsub : Set.range p ⊆ (I.support : Set Y) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ ((I.comap p).support : Set X) := hfull.symm ▸ Set.mem_univ x
    rw [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  have hc := closure_minimal hsub I.support.isClosed
  rw [p.denseRange.closure_range] at hc
  exact support_ne_univ I hI (Set.Subset.antisymm (Set.subset_univ _) hc)

end PhilipponInvertibleIdealDominantPullback

end
end

/- PhilipponBlowupProduct -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PhilipponBlowup PhilipponIdealSheafProductPullback

namespace PhilipponBlowupProduct

lemma support_ne_top_comap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    (J : Y.IdealSheafData) (hJ : J.support ≠ ⊤) : (J.comap f).support ≠ ⊤ := by
  intro h
  have hs : Set.range f ⊆ (J.support : Set Y) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ (J.comap f).support := by rw [h]; trivial
    rwa [Scheme.IdealSheafData.support_comap] at hx
  have hall := closure_minimal hs J.support.isClosed
  rw [f.denseRange.closure_range] at hall
  exact hJ (SetLike.coe_injective (Set.Subset.antisymm (Set.subset_univ _) hall))

variable {X : Scheme.{u}} [IsIntegral X]
    (I J : X.IdealSheafData)

abbrev secondCenter : (scheme I).IdealSheafData := J.comap (projection I)

/-- The actual blowup of a product is the actual iterated blowup, over
the original base. Each factor is made invertible by the same model. -/
theorem exists_iterated_iso (h : (I * J).support ≠ ⊤) :
    ∃ e : scheme (I * J) ≅ scheme (secondCenter I J),
      e.hom ≫ projection (secondCenter I J) ≫ projection I = projection (I * J) := by
  let P := I * J
  let D := secondCenter I J
  have hI : I.support ≠ ⊤ := by
    intro e
    apply h
    rw [Scheme.IdealSheafData.support_mul, e, top_sup_eq]
  have hJ : J.support ≠ ⊤ := by
    intro e
    apply h
    rw [Scheme.IdealSheafData.support_mul, e, sup_top_eq]
  letI : IsIntegral (scheme P) := PhilipponBlowupIntegral.source_isIntegral P h
  letI : IsIntegral (scheme I) := PhilipponBlowupIntegral.source_isIntegral I hI
  letI : IsDominant (projection I) := PhilipponBlowupModification.projection_isDominant I hI
  have hD : D.support ≠ ⊤ := support_ne_top_comap (projection I) J hJ
  letI : IsIntegral (scheme D) := PhilipponBlowupIntegral.source_isIntegral D hD
  letI : IsDominant (projection D) := PhilipponBlowupModification.projection_isDominant D hD
  have hP : (I.comap (projection P) * J.comap (projection P)).IsInvertible :=
    comap_mul I J (projection P) ▸ nativeInvertible P
  obtain ⟨hPI, hPJ⟩ := PhilipponCartierProductFactors.of_mul hP
  obtain ⟨i, hi, _⟩ := existsUnique_lift I (projection P) hPI
  have hPD : (D.comap i).IsInvertible := by
    change ((J.comap (projection I)).comap i).IsInvertible
    rw [← Scheme.IdealSheafData.comap_comp, hi]
    exact hPJ
  obtain ⟨m, hm, _⟩ := existsUnique_lift D i hPD
  let p := projection D ≫ projection I
  have hIp : (I.comap p).IsInvertible := by
    change (I.comap (projection D ≫ projection I)).IsInvertible
    rw [Scheme.IdealSheafData.comap_comp]
    exact PhilipponInvertibleIdealDominantPullback.isInvertible_comap _ (nativeInvertible I)
      (projection D)
  have hJp : (J.comap p).IsInvertible := by
    change (J.comap (projection D ≫ projection I)).IsInvertible
    rw [Scheme.IdealSheafData.comap_comp]
    exact nativeInvertible D
  have hPp : (P.comap p).IsInvertible := by
    change ((I * J).comap p).IsInvertible
    rw [comap_mul]
    exact hIp.mul hJp
  obtain ⟨k, hk, _⟩ := existsUnique_lift P p hPp
  have hmp : m ≫ p = projection P := by
    change m ≫ projection D ≫ projection I = _
    rw [← Category.assoc, hm, hi]
  have hki : k ≫ i = projection D := by
    apply (existsUnique_lift I p hIp).unique
    · rw [Category.assoc, hi, hk]
    · rfl
  refine ⟨⟨m, k, ?_, ?_⟩, hmp⟩
  · exact (existsUnique_lift P (projection P) (nativeInvertible P)).unique
      (show (m ≫ k) ≫ projection P = projection P by rw [Category.assoc, hk, hmp])
      (Category.id_comp _)
  · exact (existsUnique_lift D (projection D) (nativeInvertible D)).unique
      (show (k ≫ m) ≫ projection D = projection D by rw [Category.assoc, hm, hki])
      (Category.id_comp _)

end PhilipponBlowupProduct

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

/- PhilipponNagataCommonModification -/
section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponBlowup PhilipponBlowupProduct

namespace PhilipponNagataCommonModification

/-- If the first strict transform is an open subscheme of its modified
chart, extend the second centre to that chart. The product blowup then
embeds as the actual open in this further blowup. -/
theorem exists_open_product_blowup {G M : Scheme.{u}} [IsIntegral G]
    (P Q : G.IdealSheafData) (h : (P * Q).support ≠ ⊤)
    (a : scheme P ⟶ M) [IsOpenImmersion a] [QuasiCompact a]
    {U : Scheme.{u}} (u : U ⟶ M) [IsOpenImmersion u]
    (hu : Disjoint ((secondCenter P Q).support : Set (scheme P)) (a ⁻¹' Set.range u)) :
    ∃ (I : M.IdealSheafData) (j : scheme (P * Q) ⟶ scheme I)
      (t : scheme (P * Q) ⟶ scheme P),
      IsOpenImmersion j ∧ j ≫ projection I = t ≫ a ∧
      t ≫ projection P = projection (P * Q) ∧ I.comap u = ⊤ := by
  obtain ⟨e, he⟩ := exists_iterated_iso P Q h
  let D := secondCenter P Q
  let I := D.map a
  let j := e.hom ≫ PhilipponOpenBlowupExtension.map D a
  let t := e.hom ≫ projection D
  refine ⟨I, j, t, inferInstance, ?_, ?_, ?_⟩
  · simp [j, t, I, Category.assoc, PhilipponOpenBlowupExtension.map_projection]
  · exact (Category.assoc _ _ _).trans he
  · have hU : (I.comap u.opensRange.ι) = ⊤ :=
      PhilipponAdmissibleBlowupExtension.extended_unit_on_open D a u.opensRange hu
    rw [← u.isoOpensRange_hom_ι, Scheme.IdealSheafData.comap_comp, hU]
    simp

/-- A graph immersion into the product of the modified charts is closed
if its composite into the original product is proper. Both modified
charts retain their original structure maps through the modifications. -/
theorem closed_graph_of_proper_composite {G L R L' R' S : Scheme.{u}}
    (qL : L ⟶ S) (qR : R ⟶ S) [IsSeparated qR]
    (pL : L' ⟶ L) (pR : R' ⟶ R) [IsSeparated pL] [IsSeparated pR]
    (l : G ⟶ L') (r : G ⟶ R') [IsOpenImmersion l]
    (h : l ≫ (pL ≫ qL) = r ≫ (pR ≫ qR))
    (k : G ⟶ pullback qL qR) [IsProper k]
    (hkL : k ≫ pullback.fst qL qR = l ≫ pL)
    (hkR : k ≫ pullback.snd qL qR = r ≫ pR) :
    IsClosedImmersion (pullback.lift l r h) := by
  let b := pullback.map (pL ≫ qL) (pR ≫ qR) qL qR pL pR (𝟙 S)
    (Category.comp_id _) (Category.comp_id _)
  let g := pullback.lift l r h
  have hc : g ≫ b = k := by
    apply pullback.hom_ext
    · simpa only [g, b, Category.assoc, pullback.map, pullback.lift_fst_assoc,
        pullback.lift_fst] using hkL.symm
    · simpa only [g, b, Category.assoc, pullback.map, pullback.lift_snd_assoc,
        pullback.lift_snd] using hkR.symm
  letI : IsSeparated (b ≫ pullback.fst qL qR) := by
    change IsSeparated (pullback.lift _ _ _ ≫ pullback.fst _ _)
    rw [pullback.lift_fst]
    infer_instance
  letI : IsSeparated b := IsSeparated.of_comp b (pullback.fst qL qR)
  letI : IsProper (g ≫ b) := by rw [hc]; infer_instance
  letI : IsProper g := IsProper.of_comp g b
  letI : IsImmersion (g ≫ pullback.fst (pL ≫ qL) (pR ≫ qR)) := by
    change IsImmersion (pullback.lift l r h ≫ pullback.fst _ _)
    rw [pullback.lift_fst]
    infer_instance
  letI : IsImmersion g := IsImmersion.of_comp g (pullback.fst (pL ≫ qL) (pR ≫ qR))
  exact IsClosedImmersion.of_isPreimmersion g g.isClosedMap.isClosed_range

end PhilipponNagataCommonModification

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
open PhilipponBlowup PhilipponBlowupProduct PhilipponNagataCommonModification

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

/- PhilipponNagataSeparatedCover -/
section

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponNagataSeparatedCover

/-- Separatedness can be checked on all pairs of members of a source
open cover. Each pair checks the corresponding base change of the diagonal. -/
theorem isSeparated_of_cover {X S : Scheme.{u}} (f : X ⟶ S) (C : X.OpenCover.{v})
    (h : ∀ i j : C.I₀, IsClosedImmersion (pullback.mapDesc (C.f i) (C.f j) f)) :
    IsSeparated f := by
  let D := Scheme.Pullback.openCoverOfLeftRight C C f f
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) D
  intro k
  change C.I₀ × C.I₀ at k
  obtain ⟨i, j⟩ := k
  change IsClosedImmersion (pullback.snd (pullback.diagonal f)
    (pullback.map _ _ _ _ (C.f i) (C.f j) (𝟙 S) (Category.comp_id _) (Category.comp_id _)))
  let H := pullback_map_diagonal_isPullback (C.f i) (C.f j) f
  rw [← H.isoPullback_inv_snd]
  letI := h i j
  exact inferInstanceAs (IsClosedImmersion (H.isoPullback.inv ≫ pullback.mapDesc (C.f i) (C.f j) f))

lemma isClosedImmersion_self {L X S : Scheme.{u}} (i : L ⟶ X) [Mono i] (f : X ⟶ S)
    [IsSeparated (i ≫ f)] : IsClosedImmersion (pullback.mapDesc i i f) := by
  have h : pullback.mapDesc i i f = pullback.fst i i ≫ pullback.diagonal (i ≫ f) := by
    apply pullback.hom_ext
    · simp
    · simpa only [pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id,
        Category.assoc, pullback.diagonal_snd]
        using (cancel_mono i).mp (pullback.condition (f := i) (g := i)).symm
  rw [h]
  infer_instance

lemma isClosedImmersion_swap {L R X S : Scheme.{u}} (i : L ⟶ X) (j : R ⟶ X) (f : X ⟶ S)
    [IsClosedImmersion (pullback.mapDesc i j f)] : IsClosedImmersion (pullback.mapDesc j i f) := by
  have h : pullback.mapDesc j i f = (pullbackSymmetry j i).hom ≫ pullback.mapDesc i j f ≫
      (pullbackSymmetry (i ≫ f) (j ≫ f)).hom := by
    apply pullback.hom_ext <;> simp [pullback.mapDesc]
  rw [h]
  infer_instance

/-- The two-chart case of the closed overlap criterion. The cross term
is the actual overlap in the fibre product of the two charts. -/
theorem isSeparated_of_two_charts {L R X S : Scheme.{u}} (f : X ⟶ S)
    (i : L ⟶ X) (j : R ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (cover : ∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x)
    [IsSeparated (i ≫ f)] [IsSeparated (j ≫ f)]
    [IsClosedImmersion (pullback.mapDesc i j f)] : IsSeparated f := by
  apply isSeparated_of_cover f (PhilipponTwoOpenChartIntegral.cover i j cover)
  intro a b
  change Bool at a b
  cases a <;> cases b
  · exact isClosedImmersion_self i f
  · exact inferInstanceAs (IsClosedImmersion (pullback.mapDesc i j f))
  · exact isClosedImmersion_swap i j f
  · exact isClosedImmersion_self j f

end PhilipponNagataSeparatedCover

end
end

/- PhilipponOpenSpanGluing -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponOpenSpanGluing

variable {O L R : Scheme.{u}} (l : O ⟶ L) (r : O ⟶ R)
  [IsOpenImmersion l] [IsOpenImmersion r]

abbrev Model : Scheme.{u} := pushout l r

def inl : L ⟶ Model l r := pushout.inl l r
def inr : R ⟶ Model l r := pushout.inr l r

instance inl_isOpenImmersion : IsOpenImmersion (inl l r) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span l r) WalkingSpan.left))

instance inr_isOpenImmersion : IsOpenImmersion (inr l r) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span l r) WalkingSpan.right))

@[reassoc]
lemma condition : l ≫ inl l r = r ≫ inr l r := pushout.condition

theorem jointly_surjective (x : Model l r) :
    (∃ y, inl l r y = x) ∨ ∃ y, inr l r y = x := by
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span l r) x
  rcases j with (_ | (_ | _))
  · left
    refine ⟨l y, ?_⟩
    change (l ≫ inl l r) y = x
    rw [show l ≫ inl l r = colimit.ι (span l r) WalkingSpan.zero from
      (by simpa only [inl, pushout.inl, span_map_fst, span_zero, span_left] using
        colimit.w (span l r) WalkingSpan.Hom.fst)]
    exact hy
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

theorem overlap_isPullback : IsPullback r l (inr l r) (inl l r) := by
  apply IsOpenImmersion.isPullback
  · exact condition l r
  · ext x
    change inl l r x ∈ Set.range (inr l r) ↔ x ∈ Set.range l
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨k, fkL, fkR, z, hzL, _⟩ :=
        (Scheme.IsLocallyDirected.ι_eq_ι_iff (span l r)).mp hy.symm
      rcases k with (_ | (_ | _))
      · refine ⟨z, ?_⟩
        have hfk : fkL = WalkingSpan.Hom.fst := Subsingleton.elim _ _
        subst fkL
        convert! hzL
      · change WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) at fkR
        cases fkR
      · change WidePushoutShape.Hom (some WalkingPair.right) (some WalkingPair.left) at fkL
        cases fkL
    · rintro ⟨z, rfl⟩
      refine ⟨r z, ?_⟩
      exact congrArg (fun h : O ⟶ Model l r => h z) (condition l r).symm

end PhilipponOpenSpanGluing

end
end

/- PhilipponNagataSeparatedGluing -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponNagataSeparatedGluing

open PhilipponOpenSpanGluing

variable {O L R S : Scheme.{u}} (l : O ⟶ L) (r : O ⟶ R)
    [IsOpenImmersion l] [IsOpenImmersion r] (qL : L ⟶ S) (qR : R ⟶ S)
    (h : l ≫ qL = r ≫ qR)

def toBase : Model l r ⟶ S := pushout.desc qL qR h

@[reassoc (attr := simp)]
theorem inl_toBase : inl l r ≫ toBase l r qL qR h = qL := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_toBase : inr l r ≫ toBase l r qL qR h = qR := pushout.inr_desc _ _ _

/-- The pullback of the two chart inclusions of the actual gluing gives
the prescribed scheme and its map to the product over the base. -/
theorem overlap_graph
    (H := (overlap_isPullback l r).flip) :
    H.isoPullback.hom ≫ pullback.mapDesc (inl l r) (inr l r) (toBase l r qL qR h) ≫
      (pullback.congrHom (inl_toBase l r qL qR h) (inr_toBase l r qL qR h)).hom =
        pullback.lift l r h := by
  apply pullback.hom_ext <;> simp [pullback.mapDesc]

/-- Glue the two actual open charts along the supplied overlap. Its
closed graph in the product and the separated charts give separatedness. -/
theorem isSeparated [IsSeparated qL] [IsSeparated qR]
    [IsClosedImmersion (pullback.lift l r h)] : IsSeparated (toBase l r qL qR h) := by
  let f := toBase l r qL qR h
  let e := (overlap_isPullback l r).flip.isoPullback
  let c := pullback.congrHom (inl_toBase l r qL qR h) (inr_toBase l r qL qR h)
  letI : IsSeparated (inl l r ≫ f) := by
    rw [show f = toBase l r qL qR h from rfl, inl_toBase]
    infer_instance
  letI : IsSeparated (inr l r ≫ f) := by
    rw [show f = toBase l r qL qR h from rfl, inr_toBase]
    infer_instance
  have hc : pullback.mapDesc (inl l r) (inr l r) f =
      e.inv ≫ pullback.lift l r h ≫ c.inv := by
    rw [← overlap_graph l r qL qR h]
    change _ = e.inv ≫ (e.hom ≫ pullback.mapDesc (inl l r) (inr l r) f ≫ c.hom) ≫ c.inv
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  letI : IsClosedImmersion (pullback.mapDesc (inl l r) (inr l r) f) := by
    rw [hc]
    infer_instance
  exact PhilipponNagataSeparatedCover.isSeparated_of_two_charts f _ _ (jointly_surjective l r)

theorem locallyOfFiniteType [LocallyOfFiniteType qL] [LocallyOfFiniteType qR] :
    LocallyOfFiniteType (toBase l r qL qR h) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (PhilipponTwoOpenChartIntegral.cover (inl l r) (inr l r) (jointly_surjective l r))
  intro b
  change Bool at b
  cases b
  · change LocallyOfFiniteType (inl l r ≫ toBase l r qL qR h)
    rw [inl_toBase]
    infer_instance
  · change LocallyOfFiniteType (inr l r ≫ toBase l r qL qR h)
    rw [inr_toBase]
    infer_instance

theorem compactSpace [CompactSpace L] [CompactSpace R] : CompactSpace (Model l r) := by
  let C := PhilipponTwoOpenChartIntegral.cover (inl l r) (inr l r) (jointly_surjective l r)
  letI : Finite C.I₀ := inferInstanceAs (Finite Bool)
  letI (i : C.I₀) : CompactSpace (C.X i) := by
    change Bool at i
    cases i <;> dsimp [C, PhilipponTwoOpenChartIntegral.cover] <;> infer_instance
  exact C.compactSpace

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

/- PhilipponNagataAmalgam -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup PhilipponNagataCommonModification PhilipponNagataProtectedChart

namespace PhilipponNagataAmalgam

lemma projection_eqToIso {G : Scheme.{u}} {P Q : G.IdealSheafData} (e : P = Q) :
    (eqToIso (congrArg PhilipponBlowup.scheme e)).hom ≫ projection Q = projection P := by
  subst Q
  simp


end PhilipponNagataAmalgam

end
end

/- PhilipponFlatBlowupRefinement -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory
open PhilipponBlowup PhilipponBlowupProduct

namespace PhilipponFlatBlowupRefinement

/-- The canonical comparison under a flat map is the flat projection
from the actual fibred product. -/
theorem flat_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (I : Y.IdealSheafData) : Flat (PhilipponBlowupComparison.map I f) := by
  have h : PhilipponBlowupComparison.map I f = PhilipponBlowupBaseChange.map I f := by
    apply (existsUnique_lift I _ (PhilipponBlowupComparison.composite_invertible I f)).unique
    · exact PhilipponBlowupComparison.map_projection I f
    · exact PhilipponBlowupBaseChange.map_projection I f
  rw [h]
  infer_instance

/-- Once a centre makes the strict transform flat, adjoining another
centre by taking the product preserves flatness. -/
theorem flat_product {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (I J : Y.IdealSheafData)
    (hY : (I * J).support ≠ ⊤) (hX : ((I * J).comap f).support ≠ ⊤)
    [Flat (PhilipponBlowupComparison.map I f)] :
    Flat (PhilipponBlowupComparison.map (I * J) f) := by
  let P := I.comap f
  let Q := J.comap f
  let C := secondCenter I J
  let f₁ := PhilipponBlowupComparison.map I f
  let g := PhilipponBlowupComparison.map C f₁
  let F := PhilipponBlowupComparison.map (I * J) f
  have hc : C.comap f₁ = secondCenter P Q := by
    change ((J.comap (projection I)).comap (PhilipponBlowupComparison.map I f)) =
      (J.comap f).comap (projection (I.comap f))
    rw [← Scheme.IdealSheafData.comap_comp, PhilipponBlowupComparison.map_projection,
      Scheme.IdealSheafData.comap_comp]
  have hprod : (I * J).comap f = P * Q := PhilipponIdealSheafProductPullback.comap_mul I J f
  obtain ⟨eY, heY⟩ := exists_iterated_iso I J hY
  obtain ⟨e, he⟩ := exists_iterated_iso P Q (hprod ▸ hX)
  let e₀ := eqToIso (congrArg scheme hprod)
  let e₁ := eqToIso (congrArg scheme hc.symm)
  let eX := e₀ ≪≫ e ≪≫ e₁
  have hx₁ : e₁.hom ≫ projection (C.comap f₁) = projection (secondCenter P Q) :=
    PhilipponNagataAmalgam.projection_eqToIso hc.symm
  have hx₀ : e₀.hom ≫ projection (P * Q) = projection ((I * J).comap f) :=
    PhilipponNagataAmalgam.projection_eqToIso hprod
  have hx : eX.hom ≫ projection (C.comap f₁) ≫ projection P = projection ((I * J).comap f) := by
    change (e₀.hom ≫ e.hom ≫ e₁.hom) ≫ _ = _
    simp only [Category.assoc, reassoc_of% hx₁, he, hx₀]
  have hy : eY.inv ≫ projection (I * J) = projection C ≫ projection I := by
    rw [← heY, Iso.inv_hom_id_assoc]
  have h₁ : f₁ ≫ projection I = projection P ≫ f :=
    PhilipponBlowupComparison.map_projection I f
  have h₂ : g ≫ projection C = projection (C.comap f₁) ≫ f₁ :=
    PhilipponBlowupComparison.map_projection C f₁
  have hg : eX.hom ≫ g ≫ eY.inv = F := by
    apply (existsUnique_lift (I * J) _ (PhilipponBlowupComparison.composite_invertible (I * J) f)).unique
    · simp only [Category.assoc, hy, reassoc_of% h₂, h₁]
      simpa only [Category.assoc] using congrArg (fun m => m ≫ f) hx
    · exact PhilipponBlowupComparison.map_projection (I * J) f
  letI : Flat g := flat_comparison f₁ C
  change Flat F
  rw [← hg]
  infer_instance

end PhilipponFlatBlowupRefinement

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

/- PhilipponAffineBlowupSeparation -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.PiExponentSeshadri OAI.PiExponentSeshadri.ReesGrading

namespace PhilipponAffineBlowupSeparation

variable {R : Type u} [CommRing R]

/-- On the chart with denominator a belonging to I, vanishing of I
forces vanishing of the whole blowup center K. -/
lemma chart_vanishing (K I : Ideal R) (a : K) (ha : a.val ∈ I)
    (z : Spec (.of (chart K a)))
    (hz : projection K ((chartCover K).f a z) ∈ PrimeSpectrum.zeroLocus (I : Set R)) :
    projection K ((chartCover K).f a z) ∈ PrimeSpectrum.zeroLocus (K : Set R) := by
  have heq : projection K ((chartCover K).f a z) =
      Spec.map (CommRingCat.ofHom (chartBase K a)) z :=
    congrArg (fun f : Spec (.of (chart K a)) ⟶ Spec (.of R) => f z)
      (chartCover_projection K a)
  rw [heq] at hz ⊢
  change I ≤ Ideal.comap (chartBase K a) z.asIdeal at hz
  change K ≤ Ideal.comap (chartBase K a) z.asIdeal
  rw [← Ideal.map_le_iff_le_comap, map_ideal_principal, Ideal.span_singleton_le_iff_mem]
  exact hz ha

/-- The strict transform of V(I), defined by closure away from the
blowup center, avoids every chart whose denominator lies in I. -/
lemma strict_avoids_chart (K I : Ideal R) (a : K) (ha : a.val ∈ I) :
    Disjoint
      (closure ((projection K) ⁻¹' (Set.diff (PrimeSpectrum.zeroLocus (I : Set R)) (PrimeSpectrum.zeroLocus (K : Set R)))))
      ((Proj.basicOpen (piece K) (generator K a)).carrier : Set (affineBlowup K)) := by
  have hs : (projection K) ⁻¹' (Set.diff (PrimeSpectrum.zeroLocus (I : Set R)) (PrimeSpectrum.zeroLocus (K : Set R))) ⊆
      ((Proj.basicOpen (piece K) (generator K a)).carrier : Set (affineBlowup K))ᶜ := by
    intro x hx hxa
    have hmem : x ∈ ((chartCover K).f a).opensRange := by
      change x ∈ (Proj.awayι (piece K) (generator K a) (generator_mem K a) (by decide)).opensRange
      rwa [Proj.opensRange_awayι]
    obtain ⟨z, rfl⟩ := hmem
    exact hx.2 (chart_vanishing K I a ha z hx.1)
  exact Set.disjoint_left.mpr fun x hx hxa =>
    (closure_minimal hs (Proj.basicOpen (piece K) (generator K a)).isOpen.isClosed_compl hx) hxa

/-- Blowing up I+J separates the actual strict transforms of V(I) and
V(J). The assertion holds over every commutative coefficient ring. -/
theorem disjoint_strict_transforms (I J : Ideal R) :
    Disjoint
      (closure ((projection (I ⊔ J)) ⁻¹'
        (Set.diff (PrimeSpectrum.zeroLocus (I : Set R)) (PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal R) : Set R)))))
      (closure ((projection (I ⊔ J)) ⁻¹'
        (Set.diff (PrimeSpectrum.zeroLocus (J : Set R)) (PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal R) : Set R))))) := by
  apply Set.disjoint_left.mpr
  intro x hxI hxJ
  obtain ⟨a, hxa⟩ := Opens.mem_iSup.mp
    ((iSup_generator_basicOpen (I ⊔ J)).ge (Set.mem_univ x))
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp a.property
  let ai : ↥(I ⊔ J) := ⟨i, (le_sup_left : I ≤ I ⊔ J) hi⟩
  let aj : ↥(I ⊔ J) := ⟨j, (le_sup_right : J ≤ I ⊔ J) hj⟩
  have hgen : generator (I ⊔ J) a = generator (I ⊔ J) ai + generator (I ⊔ J) aj := by
    apply Subtype.ext
    change Polynomial.monomial 1 a.val = Polynomial.monomial 1 i + Polynomial.monomial 1 j
    rw [← hij, map_add]
  have hnotI : generator (I ⊔ J) ai ∈ x.asHomogeneousIdeal := by
    by_contra h
    have hopen : x ∈ Proj.basicOpen (piece (I ⊔ J)) (generator (I ⊔ J) ai) := h
    exact Set.disjoint_left.mp (strict_avoids_chart (I ⊔ J) I ai hi) hxI hopen
  have hnotJ : generator (I ⊔ J) aj ∈ x.asHomogeneousIdeal := by
    by_contra h
    have hopen : x ∈ Proj.basicOpen (piece (I ⊔ J)) (generator (I ⊔ J) aj) := h
    exact Set.disjoint_left.mp (strict_avoids_chart (I ⊔ J) J aj hj) hxJ hopen
  apply hxa
  rw [hgen]
  exact x.asHomogeneousIdeal.toIdeal.add_mem hnotI hnotJ

end PhilipponAffineBlowupSeparation

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

/- PhilipponBlowupSeparation -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.PiExponentSeshadri

namespace PhilipponBlowupSeparation

lemma affine_disjoint {X : Scheme.{u}} [IsAffine X] (I J : X.IdealSheafData) :
    Disjoint
      (closure ((PhilipponAffineBlowup.projection (I ⊔ J)) ⁻¹'
        Set.diff (I.support : Set X) (I ⊔ J).support))
      (closure ((PhilipponAffineBlowup.projection (I ⊔ J)) ⁻¹'
        Set.diff (J.support : Set X) (I ⊔ J).support)) := by
  rw [PhilipponBlowupSupport.affine_preimage_difference,
    PhilipponBlowupSupport.affine_preimage_difference]
  exact PhilipponAffineBlowupSeparation.disjoint_strict_transforms
    (I.ideal ⟨⊤, isAffineOpen_top X⟩) (J.ideal ⟨⊤, isAffineOpen_top X⟩)

lemma affine_disjoint_of_sum {X : Scheme.{u}} [IsAffine X]
    (K I J : X.IdealSheafData) (hK : K = I ⊔ J) :
    Disjoint
      (closure ((PhilipponAffineBlowup.projection K) ⁻¹'
        Set.diff (I.support : Set X) K.support))
      (closure ((PhilipponAffineBlowup.projection K) ⁻¹'
        Set.diff (J.support : Set X) K.support)) := by
  subst K
  exact affine_disjoint I J

/-- The actual global blowup of the sum of two ideal sheaves separates
their actual strict-transform supports, in the original universe and
without Noetherian, reducedness or integrality assumptions. -/
theorem disjoint_strict_transforms {X : Scheme.{u}} (I J : X.IdealSheafData) :
    Disjoint
      (closure ((PhilipponBlowup.projection (I ⊔ J)) ⁻¹'
        Set.diff (I.support : Set X) (I ⊔ J).support))
      (closure ((PhilipponBlowup.projection (I ⊔ J)) ⁻¹'
        Set.diff (J.support : Set X) (I ⊔ J).support)) := by
  apply Set.disjoint_left.mpr
  intro x hxI hxJ
  let U := (PhilipponBlowup.cover (I ⊔ J)).idx x
  obtain ⟨y, hy⟩ := (PhilipponBlowup.cover (I ⊔ J)).covers x
  have hy' : (PhilipponBlowup.cover (I ⊔ J)).f U y = x := hy
  letI : IsAffine U.toOpens.toScheme := U.2
  have hpI := PhilipponBlowupSupport.strict_preimage
    (PhilipponBlowup.projection (I ⊔ J)) (PhilipponBlowup.localProjection (I ⊔ J) U)
    ((PhilipponBlowup.cover (I ⊔ J)).f U) U.toOpens.ι
    (PhilipponBlowup.cover_projection (I ⊔ J) U) I (I ⊔ J)
  have hpJ := PhilipponBlowupSupport.strict_preimage
    (PhilipponBlowup.projection (I ⊔ J)) (PhilipponBlowup.localProjection (I ⊔ J) U)
    ((PhilipponBlowup.cover (I ⊔ J)).f U) U.toOpens.ι
    (PhilipponBlowup.cover_projection (I ⊔ J) U) J (I ⊔ J)
  have hyI : y ∈ closure ((PhilipponBlowup.localProjection (I ⊔ J) U) ⁻¹'
      Set.diff ((I.comap U.toOpens.ι).support : Set U.toOpens.toScheme)
        ((I ⊔ J).comap U.toOpens.ι).support) := by
    rw [← hpI]
    exact (congrArg (fun z : PhilipponBlowup.scheme (I ⊔ J) => z ∈
      closure ((PhilipponBlowup.projection (I ⊔ J)) ⁻¹'
        Set.diff (I.support : Set X) (I ⊔ J).support)) hy').mpr hxI
  have hyJ : y ∈ closure ((PhilipponBlowup.localProjection (I ⊔ J) U) ⁻¹'
      Set.diff ((J.comap U.toOpens.ι).support : Set U.toOpens.toScheme)
        ((I ⊔ J).comap U.toOpens.ι).support) := by
    rw [← hpJ]
    exact (congrArg (fun z : PhilipponBlowup.scheme (I ⊔ J) => z ∈
      closure ((PhilipponBlowup.projection (I ⊔ J)) ⁻¹'
        Set.diff (J.support : Set X) (I ⊔ J).support)) hy').mpr hxJ
  have hd : Disjoint
      (closure ((PhilipponBlowup.localProjection (I ⊔ J) U) ⁻¹'
        Set.diff ((I.comap U.toOpens.ι).support : Set U.toOpens.toScheme)
          ((I ⊔ J).comap U.toOpens.ι).support))
      (closure ((PhilipponBlowup.localProjection (I ⊔ J) U) ⁻¹'
        Set.diff ((J.comap U.toOpens.ι).support : Set U.toOpens.toScheme)
          ((I ⊔ J).comap U.toOpens.ι).support)) := by
    exact affine_disjoint_of_sum ((I ⊔ J).comap U.toOpens.ι)
      (I.comap U.toOpens.ι) (J.comap U.toOpens.ι) (by simp)
  exact Set.disjoint_left.mp hd hyI hyJ

end PhilipponBlowupSeparation

end
end

/- PhilipponAdmissibleBlowupSeparation -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponAdmissibleBlowupSeparation

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- The original closed boundary extended by scheme-theoretic closure. -/
def extendedIdeal (T : Closeds U) : X.IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal T).map j

lemma support_restrict (T : Closeds U) :
    j ⁻¹' ((extendedIdeal j T).support : Set X) = (T : Set U) := by
  have h := congrArg (fun I : U.IdealSheafData => (I.support : Set U))
    (PhilipponOpenIdealExtension.comap_map (Scheme.IdealSheafData.vanishingIdeal T) j)
  rw [Scheme.IdealSheafData.support_comap] at h
  exact h

def center (T₁ T₂ : Closeds U) : X.IdealSheafData :=
  extendedIdeal j T₁ ⊔ extendedIdeal j T₂

lemma center_restrict (T₁ T₂ : Closeds U) (h : Disjoint (T₁ : Set U) (T₂ : Set U)) :
    (center j T₁ T₂).comap j = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [center, Scheme.IdealSheafData.comap_sup]
  unfold extendedIdeal
  rw [PhilipponOpenIdealExtension.comap_map, PhilipponOpenIdealExtension.comap_map,
    Scheme.IdealSheafData.support_sup]
  change T₁ ⊓ T₂ = ⊥
  apply SetLike.coe_injective
  exact Set.disjoint_iff_inter_eq_empty.mp h

lemma image_subset_source (T₁ T₂ : Closeds U) (h : Disjoint (T₁ : Set U) (T₂ : Set U)) :
    j '' (T₁ : Set U) ⊆
      Set.diff ((extendedIdeal j T₁).support : Set X) (center j T₁ T₂).support := by
  rintro _ ⟨x, hx, rfl⟩
  have h₁ : j x ∈ (extendedIdeal j T₁).support := by
    change x ∈ j ⁻¹' ((extendedIdeal j T₁).support : Set X)
    rw [support_restrict]
    exact hx
  refine ⟨h₁, ?_⟩
  intro hbad
  have h₂ : j x ∈ (extendedIdeal j T₂).support := by
    have hp : j x ∈ ((extendedIdeal j T₁).support : Set X) ∩
        ((extendedIdeal j T₂).support : Set X) := by
      simpa only [center, Scheme.IdealSheafData.support_sup, Closeds.coe_inf] using hbad
    exact hp.2
  have hx₂ : x ∈ T₂ := by
    change x ∈ (T₂ : Set U)
    rw [← support_restrict j T₂]
    exact h₂
  exact Set.disjoint_left.mp h hx hx₂

/-- The original disjoint closed subsets in the protected open have
actually disjoint closures in the one global blowup. -/
theorem separates (T₁ T₂ : Closeds U) (h : Disjoint (T₁ : Set U) (T₂ : Set U)) :
    Disjoint
      (closure ((PhilipponBlowup.projection (center j T₁ T₂)) ⁻¹' (j '' (T₁ : Set U))))
      (closure ((PhilipponBlowup.projection (center j T₁ T₂)) ⁻¹' (j '' (T₂ : Set U)))) := by
  have h₂ : j '' (T₂ : Set U) ⊆
      Set.diff ((extendedIdeal j T₂).support : Set X) (center j T₁ T₂).support := by
    simpa only [center, sup_comm] using image_subset_source j T₂ T₁ h.symm
  exact (PhilipponBlowupSeparation.disjoint_strict_transforms
    (extendedIdeal j T₁) (extendedIdeal j T₂)).mono
      (closure_mono (Set.preimage_mono (image_subset_source j T₁ T₂ h)))
      (closure_mono (Set.preimage_mono h₂))

/-- The same global blowup is unchanged on the entire original open. -/
theorem unchanged (T₁ T₂ : Closeds U) (h : Disjoint (T₁ : Set U) (T₂ : Set U)) :
    IsIso (pullback.fst j (PhilipponBlowup.projection (center j T₁ T₂))) :=
  PhilipponBlowupCartier.unit_open_unchanged _ j (center_restrict j T₁ T₂ h)

/-- Noetherian boundary separation, with its actual global center and
its actual proper blowup, as used in Nagata's compactification argument. -/
theorem exists_separator [IsLocallyNoetherian X]
    (T₁ T₂ : Closeds U) (h : Disjoint (T₁ : Set U) (T₂ : Set U)) :
    ∃ I : X.IdealSheafData,
      I.comap j = ⊤ ∧ IsProper (PhilipponBlowup.projection I) ∧
      IsIso (pullback.fst j (PhilipponBlowup.projection I)) ∧
      Disjoint
        (closure ((PhilipponBlowup.projection I) ⁻¹' (j '' (T₁ : Set U))))
        (closure ((PhilipponBlowup.projection I) ⁻¹' (j '' (T₂ : Set U)))) :=
  ⟨center j T₁ T₂, center_restrict j T₁ T₂ h, inferInstance,
    unchanged j T₁ T₂ h, separates j T₁ T₂ h⟩

end PhilipponAdmissibleBlowupSeparation

end
end

/- PhilipponNagataBoundaryNeighbourhood -/
section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup

namespace PhilipponNagataBoundaryNeighbourhood

/-- The lift of a protected open is the actual inverse image of that
open. -/
theorem exists_unit_pullback {Y V : Scheme.{u}} (I : Y.IdealSheafData)
    (v : V ⟶ Y) [IsOpenImmersion v] (h : I.comap v = ⊤) :
    ∃ t : V ⟶ scheme I, IsOpenImmersion t ∧
      IsPullback (𝟙 V) t v (projection I) := by
  letI := PhilipponBlowupCartier.unit_open_unchanged I v h
  let e : V ≅ pullback v (projection I) := (asIso (pullback.fst v (projection I))).symm
  let t := e.hom ≫ pullback.snd v (projection I)
  have h₁ : e.hom ≫ pullback.fst v (projection I) = 𝟙 V :=
    IsIso.inv_hom_id _
  have h₂ : (𝟙 V) ≫ v = t ≫ projection I := by
    rw [Category.id_comp, Category.assoc, ← pullback.condition, ← Category.assoc,
      h₁, Category.id_comp]
  exact ⟨t, inferInstance, IsPullback.of_iso_pullback ⟨h₂⟩ e h₁ rfl⟩

/-- A protected blowup separates the closure of the boundary from the
closure of the complement of its given neighbourhood. The resulting
open has exactly the specified restriction to the original scheme V. -/
theorem exists_neighbourhood {Y V : Scheme.{u}} (v : V ⟶ Y)
    [IsOpenImmersion v] [QuasiCompact v]
    (H : V.Opens) (T : Closeds V) (hT : (T : Set V) ⊆ (H : Set V)) :
    ∃ (I : Y.IdealSheafData) (v' : V ⟶ scheme I) (W : (scheme I).Opens),
      I.comap v = ⊤ ∧ IsOpenImmersion v' ∧
      IsPullback (𝟙 V) v' v (projection I) ∧
      closure (v' '' (T : Set V)) ⊆ (W : Set (scheme I)) ∧ v' ⁻¹ᵁ W = H := by
  let B : Closeds V := ⟨(H : Set V)ᶜ, H.isOpen.isClosed_compl⟩
  have hdisj : Disjoint (T : Set V) (B : Set V) :=
    Set.disjoint_left.mpr (fun _ hx hy => hy (hT hx))
  let I := PhilipponAdmissibleBlowupSeparation.center v T B
  have hI : I.comap v = ⊤ := PhilipponAdmissibleBlowupSeparation.center_restrict v T B hdisj
  obtain ⟨v', hv', hpb⟩ := exists_unit_pullback I v hI
  letI := hv'
  have hv : v' ≫ projection I = v := by simpa only [Category.id_comp] using hpb.w.symm
  have image_le (A : Set V) : v' '' A ⊆ projection I ⁻¹' (v '' A) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (congrArg (fun f : V ⟶ Y => f x) hv).symm⟩
  have hd := (PhilipponAdmissibleBlowupSeparation.separates v T B hdisj).mono
    (closure_mono (image_le T)) (closure_mono (image_le B))
  let W : (scheme I).Opens := ⟨(closure (v' '' (B : Set V)))ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨I, v', W, hI, hv', hpb, fun _ hx hy => Set.disjoint_left.mp hd hx hy, ?_⟩
  apply SetLike.coe_injective
  change v' ⁻¹' (closure (v' '' (B : Set V)))ᶜ = H
  rw [Set.preimage_compl, v'.isOpenMap.preimage_closure_eq_closure_preimage v'.continuous,
    Set.preimage_image_eq _ v'.isOpenEmbedding.injective, B.isClosed.closure_eq]
  exact compl_compl (H : Set V)

end PhilipponNagataBoundaryNeighbourhood

end
end

/- PhilipponNagataLocalModification -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup

namespace PhilipponNagataLocalModification

/-- On the inverse image of the local chart, the extended blowup has
exactly the given local strict transform. -/
theorem isIso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : Y.Opens) [QuasiCompact W.ι] (I : W.toScheme.IdealSheafData)
    [IsIso (PhilipponBlowupComparison.map I (f ∣_ W))] :
    IsIso (PhilipponBlowupComparison.map (I.map W.ι) f ∣_ (projection (I.map W.ι) ⁻¹ᵁ W)) := by
  let J := I.map W.ι
  let b := PhilipponOpenBlowupExtension.map I W.ι
  let p := PhilipponBlowupComparison.map J f
  let g := PhilipponBlowupComparison.map I (f ∣_ W)
  let R := projection J ⁻¹ᵁ W
  let Hb := PhilipponOpenBlowupExtension.isPullback I W.ι
  let Hπ := isPullback_morphismRestrict (projection J) W
  let e : scheme I ≅ R.toScheme := Hb.isoPullback ≪≫ Hπ.isoPullback.symm
  have he : e.hom ≫ R.ι = b := by
    change (Hb.isoPullback.hom ≫ Hπ.isoPullback.inv) ≫ (projection J ⁻¹ᵁ W).ι = b
    rw [Category.assoc, Hπ.isoPullback_inv_snd, Hb.isoPullback_hom_snd]
  obtain ⟨a, Ha⟩ := PhilipponStrictTransformRestriction.exists_pullback f
    (f ∣_ W) (f ⁻¹ᵁ W).ι W.ι (isPullback_morphismRestrict f W).flip J I
      (PhilipponOpenIdealExtension.comap_map I W.ι) b Hb
  have H : IsPullback (g ≫ e.hom) a R.ι p :=
    Ha.flip.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp [g]) (by simp) (by simpa only [Iso.refl_hom, Category.comp_id] using he.symm) (by simp [p])
  let Hr := isPullback_morphismRestrict p R
  let c := H.isoPullback ≪≫ Hr.isoPullback.symm
  have hc : c.hom ≫ p ∣_ R = g ≫ e.hom := by simp [c]
  letI : IsIso (c.hom ≫ p ∣_ R) := hc ▸ inferInstanceAs (IsIso (g ≫ e.hom))
  exact IsIso.of_isIso_comp_left c.hom (p ∣_ R)

/-- A centre extended from the local chart is still admissible for
the entire protected open when its support misses their intersection. -/
theorem extended_unit {Y V : Scheme.{u}} (v : V ⟶ Y) [IsOpenImmersion v]
    (W : Y.Opens) [QuasiCompact W.ι] (I : W.toScheme.IdealSheafData)
    (h : Disjoint (I.support : Set W.toScheme) (W.ι ⁻¹' Set.range v)) :
    (I.map W.ι).comap v = ⊤ := by
  rw [← v.isoOpensRange_hom_ι, Scheme.IdealSheafData.comap_comp]
  have hv : (I.map W.ι).comap v.opensRange.ι = ⊤ :=
    PhilipponAdmissibleBlowupExtension.extended_unit_on_open I W.ι v.opensRange h
  rw [hv, Scheme.IdealSheafData.comap_top]

/-- Extend a local modification while preserving the protected open
and an isomorphism near a prescribed boundary closure. -/
theorem extend_neighbourhood {X Y V : Scheme.{u}} (f : X ⟶ Y)
    (v : V ⟶ Y) [IsOpenImmersion v] (A : Set V)
    (W : Y.Opens) [QuasiCompact W.ι] (hA : closure (v '' A) ⊆ (W : Set Y))
    (I : W.toScheme.IdealSheafData)
    (hunit : Disjoint (I.support : Set W.toScheme) (W.ι ⁻¹' Set.range v))
    [IsIso (PhilipponBlowupComparison.map I (f ∣_ W))] :
    ∃ (v' : V ⟶ scheme (I.map W.ι)),
      IsOpenImmersion v' ∧ IsPullback (𝟙 V) v' v (projection (I.map W.ι)) ∧
      closure (v' '' A) ⊆ (projection (I.map W.ι) ⁻¹ᵁ W : Set (scheme (I.map W.ι))) ∧
      IsIso (PhilipponBlowupComparison.map (I.map W.ι) f ∣_ (projection (I.map W.ι) ⁻¹ᵁ W)) := by
  let J := I.map W.ι
  obtain ⟨v', hv', H⟩ := PhilipponNagataBoundaryNeighbourhood.exists_unit_pullback J v
    (extended_unit v W I hunit)
  have hv : v' ≫ projection J = v := by simpa only [Category.id_comp] using H.w.symm
  refine ⟨v', hv', H, ?_, isIso_restrict f W I⟩
  have hpre : closure (v' '' A) ⊆ projection J ⁻¹' closure (v '' A) := by
    apply closure_minimal _ (isClosed_closure.preimage (projection J).continuous)
    rintro _ ⟨x, hx, rfl⟩
    change projection J (v' x) ∈ closure (v '' A)
    rw [show projection J (v' x) = v x from congrArg (fun m : V ⟶ Y => m x) hv]
    exact subset_closure ⟨x, hx, rfl⟩
  exact hpre.trans (Set.preimage_mono hA)

end PhilipponNagataLocalModification

end
end

/- PhilipponFlatteningLocality -/
section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup
open scoped BigOperators

namespace PhilipponFlatteningLocality

/-- A property of the restricted comparison can be checked on the
comparison of the actual restricted blowups. -/
theorem restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens) (I : Y.IdealSheafData)
    (J : W.toScheme.IdealSheafData) (hJ : I.comap W.ι = J) :
    P (PhilipponBlowupComparison.map I f ∣_ (projection I ⁻¹ᵁ W)) ↔
      P (PhilipponBlowupComparison.map J (f ∣_ W)) := by
  obtain ⟨b, Hb⟩ :=
    PhilipponStrictTransformRestriction.exists_blowup_pullback I W.ι J hJ
  let p := PhilipponBlowupComparison.map I f
  let g := PhilipponBlowupComparison.map J (f ∣_ W)
  let R := projection I ⁻¹ᵁ W
  let Hπ := isPullback_morphismRestrict (projection I) W
  let e : scheme J ≅ R.toScheme := Hb.isoPullback ≪≫ Hπ.isoPullback.symm
  have he : e.hom ≫ R.ι = b := by
    change (Hb.isoPullback.hom ≫ Hπ.isoPullback.inv) ≫ (projection I ⁻¹ᵁ W).ι = b
    rw [Category.assoc, Hπ.isoPullback_inv_snd, Hb.isoPullback_hom_snd]
  obtain ⟨a, Ha⟩ := PhilipponStrictTransformRestriction.exists_pullback f
    (f ∣_ W) (f ⁻¹ᵁ W).ι W.ι (isPullback_morphismRestrict f W).flip I J hJ b Hb
  have H : IsPullback (g ≫ e.hom) a R.ι p :=
    Ha.flip.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp [g]) (by simp) (by simpa only [Iso.refl_hom, Category.comp_id] using he.symm) (by simp [p])
  let Hr := isPullback_morphismRestrict p R
  let c := H.isoPullback ≪≫ Hr.isoPullback.symm
  have hc : c.hom ≫ p ∣_ R = g ≫ e.hom := by simp [c]
  change P (p ∣_ R) ↔ P g
  rw [← P.cancel_left_of_respectsIso c.hom (p ∣_ R), hc, P.cancel_right_of_respectsIso g e.hom]

/-- Pullback of a finite product of ideal sheaves is the product
of the pulled-back ideals, including the empty product. -/
theorem comap_prod {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type v}
    (A : Finset ι) (I : ι → Y.IdealSheafData) :
    (∏ i ∈ A, I i).comap f = ∏ i ∈ A, (I i).comap f := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [Scheme.IdealSheafData.comap_top]
  | @insert i A hi ih =>
    rw [Finset.prod_insert hi, PhilipponIdealSheafProductPullback.comap_mul, ih, Finset.prod_insert hi]

/-- The ideals giving flat strict transforms on a finite open cover
can be extended and multiplied into a single admissible global centre. -/
theorem exists_global_centre {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Nonempty U] (f : X ⟶ Y) (s : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion j]
    (hs : s ≫ f = j) {ι : Type v} [Fintype ι]
    (W : ι → Y.Opens) [∀ i, QuasiCompact (W i).ι] (hcover : iSup W = ⊤)
    (J : ∀ i, (W i).toScheme.IdealSheafData)
    (hJ : ∀ i, Disjoint ((J i).support : Set (W i).toScheme) ((W i).ι ⁻¹' Set.range j))
    (hflat : ∀ i, Flat (PhilipponBlowupComparison.map (J i) (f ∣_ W i))) :
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧ Flat (PhilipponBlowupComparison.map I f) := by
  classical
  let K : ι → Y.IdealSheafData := fun i => (J i).map (W i).ι
  let I : Y.IdealSheafData := ∏ i, K i
  have hK (i : ι) : (K i).comap j = ⊤ :=
    PhilipponNagataLocalModification.extended_unit j (W i) (J i) (hJ i)
  have hI : I.comap j = ⊤ := by
    rw [show I = ∏ i, K i from rfl, comap_prod]
    simp only [hK, ← Scheme.IdealSheafData.one_eq_top, Finset.prod_const_one]
  have hIs : ((I.comap f).comap s) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, hs, hI]
  have hnY := PhilipponNagataProtectedChart.support_ne_top_of_unit I j hI
  have hnX := PhilipponNagataProtectedChart.support_ne_top_of_unit (I.comap f) s hIs
  have hcover' : (⨆ i, projection I ⁻¹ᵁ W i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  refine ⟨I, hI, IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Flat)
    (fun i => projection I ⁻¹ᵁ W i) hcover' ?_⟩
  intro i
  apply (restrict_iff @Flat f (W i) I (I.comap (W i).ι) rfl).mpr
  let F := f ∣_ W i
  let P := I.comap (W i).ι
  by_cases hX : Nonempty ↥(f ⁻¹ᵁ W i).toScheme
  · letI := hX
    letI : Nonempty ↥(W i).toScheme := Nonempty.map (fun x => F x) hX
    letI : IsIntegral (W i).toScheme := isIntegral_of_isOpenImmersion (W i).ι
    letI : IsIntegral (f ⁻¹ᵁ W i).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ W i).ι
    letI : IsDominant (W i).ι := ⟨(W i).ι.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (f ⁻¹ᵁ W i).ι :=
      ⟨(f ⁻¹ᵁ W i).ι.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    have hp : P.support ≠ ⊤ :=
      PhilipponBlowupProduct.support_ne_top_comap (W i).ι I hnY
    have hPF : P.comap F = (I.comap f).comap (f ⁻¹ᵁ W i).ι := by
      rw [show P = I.comap (W i).ι from rfl, ← Scheme.IdealSheafData.comap_comp,
        morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
    have hpf : (P.comap F).support ≠ ⊤ := hPF ▸
      PhilipponBlowupProduct.support_ne_top_comap (f ⁻¹ᵁ W i).ι (I.comap f) hnX
    let R := ∏ k ∈ Finset.univ.erase i, (K k).comap (W i).ι
    have hfac : P = J i * R := by
      change (∏ k, K k).comap (W i).ι = _
      rw [comap_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_comm,
        show (K i).comap (W i).ι = J i from PhilipponOpenIdealExtension.comap_map _ _]
    change Flat (PhilipponBlowupComparison.map P F)
    rw [hfac] at hp hpf ⊢
    letI := hflat i
    exact PhilipponFlatBlowupRefinement.flat_product F (J i) R hp hpf
  · letI : IsEmpty ↥(f ⁻¹ᵁ W i).toScheme := not_nonempty_iff.mp hX
    apply Flat.of_stalkMap
    intro x
    exact isEmptyElim (projection (P.comap F) x)

end PhilipponFlatteningLocality

end
end

/- PhilipponFlatteningSourceLocality -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup
open scoped BigOperators

namespace PhilipponFlatteningSourceLocality

/-- Restricting the strict-transform source to the inverse image of an
open gives the strict transform of the original source open. -/
theorem restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : X.Opens) (I : Y.IdealSheafData) :
    P ((projection (I.comap f) ⁻¹ᵁ W).ι ≫ PhilipponBlowupComparison.map I f) ↔
      P (PhilipponBlowupComparison.map I (W.ι ≫ f)) := by
  let J := I.comap f
  let J₀ := I.comap (W.ι ≫ f)
  let g := PhilipponBlowupComparison.map I f
  let g₀ := PhilipponBlowupComparison.map I (W.ι ≫ f)
  let R := projection J ⁻¹ᵁ W
  obtain ⟨a, Ha⟩ := PhilipponStrictTransformRestriction.exists_blowup_pullback
    J W.ι J₀ (Scheme.IdealSheafData.comap_comp I W.ι f).symm
  let Hπ := isPullback_morphismRestrict (projection J) W
  let e : scheme J₀ ≅ R.toScheme := Ha.isoPullback ≪≫ Hπ.isoPullback.symm
  have he : e.hom ≫ R.ι = a := by
    change (Ha.isoPullback.hom ≫ Hπ.isoPullback.inv) ≫ (projection J ⁻¹ᵁ W).ι = a
    rw [Category.assoc, Hπ.isoPullback_inv_snd, Ha.isoPullback_hom_snd]
  have hag : a ≫ g = g₀ := by
    apply (existsUnique_lift I _ (PhilipponBlowupComparison.composite_invertible I (W.ι ≫ f))).unique
    · rw [Category.assoc, show g ≫ projection I = projection J ≫ f from
        PhilipponBlowupComparison.map_projection I f, ← Category.assoc, ← Ha.w, Category.assoc]
    · exact PhilipponBlowupComparison.map_projection I (W.ι ≫ f)
  change P (R.ι ≫ g) ↔ P g₀
  rw [← P.cancel_left_of_respectsIso e.hom (R.ι ≫ g), ← Category.assoc, he, hag]

/-- Finitely many source opens with admissible centres also have a
single common admissible centre. Each centre is on the original base. -/
theorem exists_global_centre {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Nonempty U] (f : X ⟶ Y) (s : U ⟶ X) (j : U ⟶ Y) (hs : s ≫ f = j)
    {ι : Type v} [Fintype ι] (W : ι → X.Opens) (hcover : iSup W = ⊤)
    (J : ι → Y.IdealSheafData) (hJ : ∀ i, (J i).comap j = ⊤)
    (hflat : ∀ i, Flat (PhilipponBlowupComparison.map (J i) ((W i).ι ≫ f))) :
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧ Flat (PhilipponBlowupComparison.map I f) := by
  classical
  let I : Y.IdealSheafData := ∏ i, J i
  have hI : I.comap j = ⊤ := by
    rw [show I = ∏ i, J i from rfl, PhilipponFlatteningLocality.comap_prod]
    simp only [hJ, ← Scheme.IdealSheafData.one_eq_top, Finset.prod_const_one]
  have hIs : ((I.comap f).comap s) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, hs, hI]
  have hnY := PhilipponNagataProtectedChart.support_ne_top_of_unit I j hI
  have hnX := PhilipponNagataProtectedChart.support_ne_top_of_unit (I.comap f) s hIs
  have hcover' : (⨆ i, projection (I.comap f) ⁻¹ᵁ W i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  refine ⟨I, hI, IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat)
    (fun i => projection (I.comap f) ⁻¹ᵁ W i) hcover' ?_⟩
  intro i
  apply (restrict_iff @Flat f (W i) I).mpr
  let g := (W i).ι ≫ f
  by_cases hX : Nonempty ↥(W i).toScheme
  · letI := hX
    letI : IsIntegral (W i).toScheme := isIntegral_of_isOpenImmersion (W i).ι
    letI : IsDominant (W i).ι := ⟨(W i).ι.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    have hIg : (I.comap g).support ≠ ⊤ := by
      change (I.comap ((W i).ι ≫ f)).support ≠ ⊤
      rw [Scheme.IdealSheafData.comap_comp]
      exact PhilipponBlowupProduct.support_ne_top_comap (W i).ι (I.comap f) hnX
    let Q := ∏ k ∈ Finset.univ.erase i, J k
    have hfac : I = J i * Q :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm.trans (mul_comm _ _)
    change Flat (PhilipponBlowupComparison.map I g)
    rw [hfac] at hnY hIg ⊢
    letI := hflat i
    exact PhilipponFlatBlowupRefinement.flat_product g (J i) Q hnY hIg
  · letI : IsEmpty ↥(W i).toScheme := not_nonempty_iff.mp hX
    apply Flat.of_stalkMap
    intro x
    exact isEmptyElim (projection (I.comap g) x)

end PhilipponFlatteningSourceLocality

end
end

/- PhilipponFlatBirationalOpen -/
section

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponFlatBirationalOpen

/-- A flat separated morphism which is an isomorphism over a
scheme-theoretically dense open is a monomorphism. The pullback of the
dense open to the self fibre product is still scheme-theoretically dense. -/
theorem mono_of_iso_over_dense {X S U : Scheme.{u}} (p : X ⟶ S) [Flat p] [IsSeparated p]
    (j : U ⟶ S) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    [IsIso (pullback.fst j p)] : Mono p := by
  let b := pullback.fst p p ≫ p
  let d := pullback.snd j b
  let v := pullback.fst j b
  let f₁ := d ≫ pullback.fst p p
  let f₂ := d ≫ pullback.snd p p
  have h₁ : v ≫ j = f₁ ≫ p := by
    simpa only [b, d, v, f₁, Category.assoc] using pullback.condition (f := j) (g := b)
  have h₂ : v ≫ j = f₂ ≫ p := h₁.trans (by
    simp only [f₁, f₂, Category.assoc, pullback.condition])
  have hEq : pullback.lift v f₁ h₁ = pullback.lift v f₂ h₂ := by
    apply (cancel_mono (pullback.fst j p)).mp
    simp
  have hf : f₁ = f₂ := by
    have he := congrArg (fun h => h ≫ pullback.snd j p) hEq
    simpa only [pullback.lift_snd] using he
  have hd : f₁ ≫ pullback.diagonal p = d := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, f₁]
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using hf
  letI : Flat b := inferInstanceAs (Flat (pullback.fst p p ≫ p))
  letI : IsSchemeTheoreticallyDominant d := inferInstanceAs
    (IsSchemeTheoreticallyDominant (pullback.snd j b))
  have hker : (pullback.diagonal p).ker = ⊥ := by
    apply le_antisymm _ bot_le
    have hh := f₁.le_ker_comp (pullback.diagonal p)
    rw [hd, d.ker_eq_bot] at hh
    exact hh
  exact (pullback.isIso_diagonal_iff p).mp (IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker)

/-- The open immersion conclusion of flattening for an integral model.
The input is the actual isomorphism over the dense open, and finite
presentation upgrades the resulting flat monomorphism. -/
theorem isOpenImmersion_of_iso_over_dense {X S U : Scheme.{u}} (p : X ⟶ S)
    [Flat p] [IsSeparated p] [LocallyOfFinitePresentation p] [IsReduced S]
    (j : U ⟶ S) [IsDominant j] [QuasiCompact j] [IsIso (pullback.fst j p)] :
    IsOpenImmersion p := by
  letI : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  letI : Mono p := mono_of_iso_over_dense p j
  exact IsOpenImmersion.of_flat_of_mono p

end PhilipponFlatBirationalOpen

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

/- PhilipponNoetherianPresentation -/
section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PhilipponNoetherianPresentation

lemma locallyOfFinitePresentation_of_locallyOfFiniteType
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] : LocallyOfFinitePresentation f := by
  constructor
  intro U hU V hV hVU
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact RingHom.FinitePresentation.of_finiteType.mp (f.finiteType_appLE hU hV hVU)

end PhilipponNoetherianPresentation
end
end

/- PhilipponNagataFlatTransform -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup PhilipponNagataProtectedChart

namespace PhilipponNagataFlatTransform

/-- For the actual strict-transform map, a centre outside the protected
open preserves the isomorphism there. If the map after blowing up is
flat, it is an open immersion. -/
theorem isOpenImmersion_of_flat {G X U : Scheme.{u}} [IsIntegral G] [IsIntegral X]
    [IsLocallyNoetherian G] [IsLocallyNoetherian X]
    (f : G ⟶ X) [IsSeparated f] [LocallyOfFiniteType f]
    (s : U ⟶ G) (j : U ⟶ X) [IsOpenImmersion s] [IsOpenImmersion j]
    [Nonempty U] [NoetherianSpace U] (h : s ≫ f = j)
    (I : X.IdealSheafData) (hI : I.comap j = ⊤) [Flat (PhilipponBlowupComparison.map I f)] :
    IsOpenImmersion (PhilipponBlowupComparison.map I f) := by
  let J := I.comap f
  let p := PhilipponBlowupComparison.map I f
  have hJ : J.comap s = ⊤ := by
    change (I.comap f).comap s = ⊤
    rw [← Scheme.IdealSheafData.comap_comp, h, hI]
  letI : IsIntegral (scheme I) := PhilipponBlowupIntegral.source_isIntegral I
    (support_ne_top_of_unit I j hI)
  letI : IsIntegral (scheme J) := PhilipponBlowupIntegral.source_isIntegral J
    (support_ne_top_of_unit J s hJ)
  obtain ⟨j', hj', hj⟩ := exists_unit_lift I j hI
  obtain ⟨s', hs', hs⟩ := exists_unit_lift J s hJ
  letI := hj'
  letI := hs'
  have hcomm : s' ≫ p = j' := by
    apply (existsUnique_lift I j (hI ▸ Scheme.IdealSheafData.isInvertible_top)).unique
    · rw [Category.assoc, PhilipponBlowupComparison.map_projection,
        ← Category.assoc, hs, h]
    · exact hj
  letI : IsSeparated (p ≫ projection I) := by
    rw [show p ≫ projection I = projection J ≫ f from PhilipponBlowupComparison.map_projection I f]
    infer_instance
  letI : IsSeparated p := IsSeparated.of_comp p (projection I)
  letI : IsDominant s' := ⟨s'.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant j' := ⟨j'.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : LocallyOfFiniteType p := by
    rw [show p = PhilipponBlowupComparison.comparison I f ≫ pullback.snd f (projection I) from
      (PhilipponBlowupComparison.comparison_snd I f).symm]
    infer_instance
  letI : LocallyOfFinitePresentation p :=
    PhilipponNoetherianPresentation.locallyOfFinitePresentation_of_locallyOfFiniteType p
  let H := (PhilipponNagataGraphClosure.isPullback_of_dense_open s' p j' hcomm).flip
  letI : IsIso (pullback.fst j' p) := by rw [← H.isoPullback_inv_fst]; infer_instance
  exact PhilipponFlatBirationalOpen.isOpenImmersion_of_iso_over_dense p j'

/-- The same comparison is an isomorphism for a proper original map.
Its image is closed by properness and dense by the protected open. -/
theorem isIso_of_flat_of_proper {G X U : Scheme.{u}} [IsIntegral G] [IsIntegral X]
    [IsLocallyNoetherian G] [IsLocallyNoetherian X]
    (f : G ⟶ X) [IsProper f]
    (s : U ⟶ G) (j : U ⟶ X) [IsOpenImmersion s] [IsOpenImmersion j]
    [Nonempty U] [NoetherianSpace U] (h : s ≫ f = j)
    (I : X.IdealSheafData) (hI : I.comap j = ⊤) [Flat (PhilipponBlowupComparison.map I f)] :
    IsIso (PhilipponBlowupComparison.map I f) := by
  let p := PhilipponBlowupComparison.map I f
  letI : IsOpenImmersion p := isOpenImmersion_of_flat f s j h I hI
  letI : IsIntegral (scheme I) := PhilipponBlowupIntegral.source_isIntegral I
    (support_ne_top_of_unit I j hI)
  have hJ : ((I.comap f).comap s) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, h, hI]
  obtain ⟨t, _, _⟩ := exists_unit_lift (I.comap f) s hJ
  letI : Nonempty (scheme (I.comap f)) := Nonempty.map t ‹Nonempty U›
  letI : IsDominant p := ⟨p.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsProper (p ≫ projection I) := by
    rw [show p ≫ projection I = projection (I.comap f) ≫ f from
      PhilipponBlowupComparison.map_projection I f]
    infer_instance
  letI : IsProper p := IsProper.of_comp p (projection I)
  letI : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  exact (isIso_iff_isOpenImmersion_and_surjective p).mpr ⟨inferInstance, inferInstance⟩

end PhilipponNagataFlatTransform

end
end

/- PhilipponNagataFlatteningCentres -/
section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PhilipponBlowup

namespace PhilipponNagataFlatteningCentres

/-- The admissible flattening input for the integral strict transforms
in the proof of Nagata compactification. The specified common open
maps to both schemes by the original open immersions. -/
def Available : Prop :=
  ∀ {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y] [Nonempty U]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (s : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion s] [IsOpenImmersion j], s ≫ f = j →
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧ Flat (PhilipponBlowupComparison.map I f)

theorem noetherian_open {X Y : Scheme.{u}} [NoetherianSpace Y]
    (j : X ⟶ Y) [IsOpenImmersion j] : NoetherianSpace X := by
  let e := j.isoOpensRange
  letI : NoetherianSpace j.opensRange.toScheme := by
    change NoetherianSpace ↥(j.opensRange : Set Y)
    exact (noetherianSpace_set_iff _).mpr (fun Z _ => NoetherianSpace.isCompact Z)
  exact noetherianSpace_of_surjective e.inv e.inv.continuous Surjective.surj

theorem noetherian_blowup {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) :
    IsNoetherian (scheme I) := by
  letI : CompactSpace (scheme I) := QuasiCompact.compactSpace_of_compactSpace (projection I)
  exact ⟨⟩

/-- An admissible flat strict transform is open, and its actual
source is Noetherian, so the chart inclusion is quasi-compact. -/
theorem exists_open_transform (F : Available.{u}) {X Y U : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y] [Nonempty U]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (s : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion s] [IsOpenImmersion j] (h : s ≫ f = j) :
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧
      IsOpenImmersion (PhilipponBlowupComparison.map I f) ∧
      QuasiCompact (PhilipponBlowupComparison.map I f) := by
  obtain ⟨I, hI, hFlat⟩ := F f s j h
  letI := hFlat
  letI : NoetherianSpace U := noetherian_open s
  letI : IsNoetherian (scheme (I.comap f)) := noetherian_blowup _
  exact ⟨I, hI, PhilipponNagataFlatTransform.isOpenImmersion_of_flat f s j h I hI, inferInstance⟩

/-- In the proper case the same flattening input provides the
isomorphism of the actual strict transform used near a boundary. -/
theorem exists_iso_transform (F : Available.{u}) {X Y U : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [CompactSpace Y] [Nonempty U] (f : X ⟶ Y) [IsProper f]
    (s : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion s] [IsOpenImmersion j] (h : s ≫ f = j) :
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧ IsIso (PhilipponBlowupComparison.map I f) := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsNoetherian X := ⟨⟩
  letI : IsNoetherian Y := ⟨⟩
  letI : NoetherianSpace U := noetherian_open s
  obtain ⟨I, hI, hFlat⟩ := F f s j h
  letI := hFlat
  exact ⟨I, hI, PhilipponNagataFlatTransform.isIso_of_flat_of_proper f s j h I hI⟩

end PhilipponNagataFlatteningCentres

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

/- PhilipponFlatteningAffineReduction -/
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponBlowup PhilipponNagataFlatteningCentres

namespace PhilipponFlatteningAffineReduction

/-- The remaining affine problem allows the restriction to be an open
immersion over the protected open. In particular, an affine source
chart need only contain part of that open. -/
def OnAffines : Prop :=
  ∀ {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y] [IsAffine X] [IsAffine Y] [Nonempty U]
    (f : X ⟶ Y) [IsDominant f] [IsSeparated f] [LocallyOfFiniteType f]
    (j : U ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion (f ∣_ j.opensRange)],
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧ Flat (PhilipponBlowupComparison.map I f)

theorem noetherian_open_scheme {X Y : Scheme.{u}} [IsNoetherian Y]
    (j : X ⟶ Y) [IsOpenImmersion j] : IsNoetherian X := by
  letI : NoetherianSpace X := noetherian_open j
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
  letI : CompactSpace X := NoetherianSpace.compactSpace X
  exact ⟨⟩

/-- A nonempty open in the target meets the image of the protected
open, since that image is a dense open of the integral target. -/
theorem nonempty_preimage {U Y : Scheme.{u}} [IsIntegral Y] [Nonempty U]
    (j : U ⟶ Y) [IsOpenImmersion j] (W : Y.Opens) [Nonempty W.toScheme] :
    Nonempty (j ⁻¹ᵁ W).toScheme := by
  have hd : DenseRange j := j.isOpenMap.denseRange_of_isPreirreducibleSpace
  obtain ⟨w⟩ := ‹Nonempty (W.toScheme : Scheme.{u})›
  obtain ⟨_, hw, u, rfl⟩ := hd.inter_open_nonempty (W : Set Y) W.isOpen ⟨w.val, w.property⟩
  exact ⟨⟨u, hw⟩⟩

/-- The specified open section identifies the actual inverse image of
its range with the given open. -/
theorem isIso_over {X Y U : Scheme.{u}} [IsIntegral X] [Nonempty U]
    (f : X ⟶ Y) [IsSeparated f] (s : U ⟶ X) (j : U ⟶ Y)
    [IsOpenImmersion s] [IsOpenImmersion j] (hs : s ≫ f = j) :
    IsIso (f ∣_ j.opensRange) := by
  letI : IsDominant s := ⟨s.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let H := PhilipponNagataGraphClosure.isPullback_of_dense_open s f j hs
  letI : IsIso (H.isoPullback.hom ≫ pullback.snd f j) := by
    rw [H.isoPullback_hom_snd]
    infer_instance
  letI : IsIso (pullback.snd f j) := IsIso.of_isIso_comp_left H.isoPullback.hom _
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictOpensRange f j)).mpr inferInstance

/-- With affine target, localize on the source and combine the centres
obtained from the affine theorem. -/
theorem of_affine_target (F : OnAffines.{u}) {X Y U : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y] [IsAffine Y]
    [Nonempty U] (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (s : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion s] [IsOpenImmersion j] (hs : s ≫ f = j) :
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧ Flat (PhilipponBlowupComparison.map I f) := by
  classical
  letI : IsIso (f ∣_ j.opensRange) := isIso_over f s j hs
  letI : IsDominant (s ≫ f) := hs ▸
    (show IsDominant j from ⟨j.isOpenMap.denseRange_of_isPreirreducibleSpace⟩)
  letI : IsDominant f := IsDominant.of_comp s f
  let 𝒰 := X.affineCover.finiteSubcover
  let W : 𝒰.I₀ → X.Opens := fun i => (𝒰.f i).opensRange
  have hcover : iSup W = ⊤ := 𝒰.iSup_opensRange
  have chooseJ (i : 𝒰.I₀) : ∃ J : Y.IdealSheafData,
      J.comap j = ⊤ ∧ Flat (PhilipponBlowupComparison.map J ((W i).ι ≫ f)) := by
    let g := (W i).ι ≫ f
    by_cases hX : Nonempty (W i).toScheme
    · letI := hX
      letI : IsIntegral (W i).toScheme := isIntegral_of_isOpenImmersion (W i).ι
      letI : IsNoetherian (W i).toScheme := noetherian_open_scheme (W i).ι
      letI : IsAffine (𝒰.X i) := by
        rw [X.affineCover.finiteSubcover_X]
        infer_instance
      letI : IsAffine (W i).toScheme := isAffineOpen_opensRange (𝒰.f i)
      letI : IsDominant (W i).ι := ⟨(W i).ι.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
      letI : IsDominant g := inferInstanceAs (IsDominant ((W i).ι ≫ f))
      letI : IsSeparated g := inferInstanceAs (IsSeparated ((W i).ι ≫ f))
      letI : LocallyOfFiniteType g := inferInstanceAs (LocallyOfFiniteType ((W i).ι ≫ f))
      letI : IsOpenImmersion (g ∣_ j.opensRange) := by
        change IsOpenImmersion (((W i).ι ≫ f) ∣_ j.opensRange)
        rw [morphismRestrict_comp]
        infer_instance
      exact F g j
    · letI : IsEmpty (W i).toScheme := not_nonempty_iff.mp hX
      refine ⟨⊤, Scheme.IdealSheafData.comap_top _, ?_⟩
      apply Flat.of_stalkMap
      intro x
      exact isEmptyElim (projection ((⊤ : Y.IdealSheafData).comap g) x)
  choose J hJ hflat using chooseJ
  exact PhilipponFlatteningSourceLocality.exists_global_centre f s j hs W hcover J hJ hflat

/-- Admissible flattening follows from the affine-source and
affine-target case, with open immersions over the protected open. -/
theorem available (F : OnAffines.{u}) : Available.{u} := by
  intro X Y U _ _ _ _ _ f _ _ s j _ _ hs
  classical
  let 𝒰 := Y.affineCover.finiteSubcover
  let W : 𝒰.I₀ → Y.Opens := fun i => (𝒰.f i).opensRange
  letI (i : 𝒰.I₀) : IsNoetherian (W i).toScheme := noetherian_open_scheme (W i).ι
  letI (i : 𝒰.I₀) : QuasiCompact (W i).ι := inferInstance
  have hcover : iSup W = ⊤ := 𝒰.iSup_opensRange
  have chooseJ (i : 𝒰.I₀) : ∃ J : (W i).toScheme.IdealSheafData,
      Disjoint (J.support : Set (W i).toScheme) ((W i).ι ⁻¹' Set.range j) ∧
        Flat (PhilipponBlowupComparison.map J (f ∣_ W i)) := by
    let g := f ∣_ W i
    by_cases hY : Nonempty (W i).toScheme
    · letI := hY
      let U' := (j ⁻¹ᵁ W i).toScheme
      let j' := j ∣_ W i
      letI : Nonempty U' := nonempty_preimage j (W i)
      let H := isPullback_morphismRestrict f (W i)
      have hc : j' ≫ (W i).ι = ((j ⁻¹ᵁ W i).ι ≫ s) ≫ f := by
        rw [show j' ≫ (W i).ι = (j ⁻¹ᵁ W i).ι ≫ j from morphismRestrict_ι j (W i),
          Category.assoc, hs]
      let s' := H.lift j' ((j ⁻¹ᵁ W i).ι ≫ s) hc
      have hs' : s' ≫ (f ⁻¹ᵁ W i).ι = (j ⁻¹ᵁ W i).ι ≫ s := H.lift_snd _ _ hc
      letI : IsOpenImmersion (s' ≫ (f ⁻¹ᵁ W i).ι) := hs' ▸
        inferInstanceAs (IsOpenImmersion ((j ⁻¹ᵁ W i).ι ≫ s))
      letI : IsOpenImmersion s' := IsOpenImmersion.of_comp s' (f ⁻¹ᵁ W i).ι
      letI : Nonempty (f ⁻¹ᵁ W i).toScheme :=
        Nonempty.map (fun x : U' => s' x) (inferInstance : Nonempty U')
      letI : IsIntegral (f ⁻¹ᵁ W i).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ W i).ι
      letI : IsIntegral (W i).toScheme := isIntegral_of_isOpenImmersion (W i).ι
      letI : IsNoetherian (f ⁻¹ᵁ W i).toScheme := noetherian_open_scheme (f ⁻¹ᵁ W i).ι
      letI : IsAffine (𝒰.X i) := by
        rw [Y.affineCover.finiteSubcover_X]
        infer_instance
      letI : IsAffine (W i).toScheme := isAffineOpen_opensRange (𝒰.f i)
      letI : IsSeparated g := inferInstanceAs (IsSeparated (f ∣_ W i))
      letI : LocallyOfFiniteType g := inferInstanceAs (LocallyOfFiniteType (f ∣_ W i))
      letI : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion (j ∣_ W i))
      obtain ⟨J, hJ, hflat⟩ := of_affine_target F g s' j' (H.lift_fst _ _ hc)
      refine ⟨J, ?_, hflat⟩
      rw [← PhilipponNagataExtensionProduct.range_fst (isPullback_morphismRestrict j (W i))]
      apply Set.disjoint_left.mpr
      rintro _ hx ⟨z, rfl⟩
      change z ∈ J.support.preimage j'.continuous at hx
      rw [← Scheme.IdealSheafData.support_comap, hJ, Scheme.IdealSheafData.support_top] at hx
      exact hx
    · letI : IsEmpty (W i).toScheme := not_nonempty_iff.mp hY
      refine ⟨⊤, by simp [Scheme.IdealSheafData.support_top], ?_⟩
      apply Flat.of_stalkMap
      intro x
      exact isEmptyElim (g (projection ((⊤ : (W i).toScheme.IdealSheafData).comap g) x))
  choose J hJ hflat using chooseJ
  exact PhilipponFlatteningLocality.exists_global_centre f s j hs W hcover J hJ hflat

end PhilipponFlatteningAffineReduction

end
end

/- PhilipponAdmissibleFlatteningAssembly -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory
open OAI.PiExponentSeshadri.Geometry
open PhilipponBlowup

namespace PhilipponAdmissibleFlatteningAssembly

theorem affine_input : PhilipponFlatteningAffineReduction.OnAffines.{u} := by
  intro X Y U _ _ _ _ _ _ _ f _ _ _ j _ _
  obtain ⟨I, hI, hFlat⟩ := AlgebraicGeometry.exists_admissible_flattening_of_affine_open_immersion f j
  exact ⟨I, hI, hFlat _ _ (projection (I.comap f)) (projection I)
    (PhilipponBlowupComparison.map I f) (PhilipponBlowupComparison.map_projection I f)
    (nativeInvertible (I.comap f)) (nativeInvertible I)
    (fun _ g hg => existsUnique_lift (I.comap f) g hg)
    (fun _ g hg => existsUnique_lift I g hg)⟩

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

end PhilipponAdmissibleFlatteningAssembly

theorem solution {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y] [Nonempty U]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (s : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion s] [IsOpenImmersion j]
    (hs : s ≫ f = j) :
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
  obtain ⟨I, hI, hflat⟩ := PhilipponFlatteningAffineReduction.available
    PhilipponAdmissibleFlatteningAssembly.affine_input f s j hs
  letI := hflat
  exact ⟨I, hI, fun _ _ p q m hm hP hQ hp hq =>
    PhilipponAdmissibleFlatteningAssembly.flat_of_universal I f p q m hm hP hQ hp hq⟩

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
#print axioms PhilipponBlowupModification.projection_isDominant
#print axioms PhilipponBlowupModification.restrict_isIso
#print axioms PhilipponBlowupModification.exists_dense_open_isIso
#print axioms PhilipponBlowupModification.properties
#print axioms PhilipponCartierProductFactors.exists_factor
#print axioms PhilipponCartierProductFactors.span_factors
#print axioms PhilipponCartierProductFactors.of_mul
#print axioms PhilipponIdealSheafProductPullback.comap_mul
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
#print axioms PhilipponInvertibleIdealDominantPullback.ne_bot
#print axioms PhilipponInvertibleIdealDominantPullback.support_ne_univ
#print axioms PhilipponInvertibleIdealDominantPullback.isInvertible_comap
#print axioms PhilipponBlowupProduct.support_ne_top_comap
#print axioms PhilipponBlowupProduct.exists_iterated_iso
#print axioms PhilipponBlowupComparison.composite_invertible
#print axioms PhilipponBlowupComparison.map
#print axioms PhilipponBlowupComparison.comparison
#print axioms PhilipponBlowupComparison.comparison_proper
#print axioms PhilipponNagataCommonModification.exists_open_product_blowup
#print axioms PhilipponNagataCommonModification.closed_graph_of_proper_composite
#print axioms PhilipponNagataProtectedChart.exists_unit_lift
#print axioms PhilipponNagataProtectedChart.support_ne_top_of_unit
#print axioms PhilipponTwoOpenChartIntegral.integral_of_charts
#print axioms PhilipponNagataSeparatedCover.isSeparated_of_cover
#print axioms PhilipponNagataSeparatedCover.isClosedImmersion_self
#print axioms PhilipponNagataSeparatedCover.isClosedImmersion_swap
#print axioms PhilipponNagataSeparatedCover.isSeparated_of_two_charts
#print axioms PhilipponOpenSpanGluing.jointly_surjective
#print axioms PhilipponOpenSpanGluing.overlap_isPullback
#print axioms PhilipponNagataSeparatedGluing.overlap_graph
#print axioms PhilipponNagataSeparatedGluing.isSeparated
#print axioms PhilipponNagataSeparatedGluing.locallyOfFiniteType
#print axioms PhilipponNagataSeparatedGluing.compactSpace
#print axioms PhilipponNagataSeparatedGluing.proper_of_dominant_model
#print axioms PhilipponNagataAmalgam.projection_eqToIso
#print axioms PhilipponFlatBlowupRefinement.flat_comparison
#print axioms PhilipponFlatBlowupRefinement.flat_product
#print axioms PhilipponStrictTransformRestriction.exists_blowup_pullback
#print axioms PhilipponStrictTransformRestriction.exists_pullback
#print axioms PhilipponAffineBlowupSeparation.chart_vanishing
#print axioms PhilipponAffineBlowupSeparation.strict_avoids_chart
#print axioms PhilipponAffineBlowupSeparation.disjoint_strict_transforms
#print axioms PhilipponBlowupSupport.support_specIdeal
#print axioms PhilipponBlowupSupport.affine_preimage_support
#print axioms PhilipponBlowupSupport.affine_preimage_difference
#print axioms PhilipponBlowupSupport.strict_preimage
#print axioms PhilipponBlowupSeparation.affine_disjoint
#print axioms PhilipponBlowupSeparation.disjoint_strict_transforms
#print axioms PhilipponAdmissibleBlowupSeparation.support_restrict
#print axioms PhilipponAdmissibleBlowupSeparation.center_restrict
#print axioms PhilipponAdmissibleBlowupSeparation.separates
#print axioms PhilipponAdmissibleBlowupSeparation.unchanged
#print axioms PhilipponAdmissibleBlowupSeparation.exists_separator
#print axioms PhilipponNagataBoundaryNeighbourhood.exists_unit_pullback
#print axioms PhilipponNagataBoundaryNeighbourhood.exists_neighbourhood
#print axioms PhilipponNagataLocalModification.isIso_restrict
#print axioms PhilipponNagataLocalModification.extended_unit
#print axioms PhilipponNagataLocalModification.extend_neighbourhood
#print axioms PhilipponFlatteningLocality.restrict_iff
#print axioms PhilipponFlatteningLocality.comap_prod
#print axioms PhilipponFlatteningLocality.exists_global_centre
#print axioms PhilipponFlatteningSourceLocality.restrict_iff
#print axioms PhilipponFlatteningSourceLocality.exists_global_centre
#print axioms PhilipponFlatBirationalOpen.mono_of_iso_over_dense
#print axioms PhilipponFlatBirationalOpen.isOpenImmersion_of_iso_over_dense
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
#print axioms PhilipponNoetherianPresentation.locallyOfFinitePresentation_of_locallyOfFiniteType
#print axioms PhilipponNagataFlatTransform.isOpenImmersion_of_flat
#print axioms PhilipponNagataFlatTransform.isIso_of_flat_of_proper
#print axioms PhilipponNagataFlatteningCentres.noetherian_open
#print axioms PhilipponNagataFlatteningCentres.noetherian_blowup
#print axioms PhilipponNagataFlatteningCentres.exists_open_transform
#print axioms PhilipponNagataFlatteningCentres.exists_iso_transform
#print axioms PhilipponNagataExtensionProduct.range_fst
#print axioms PhilipponNagataExtensionProduct.isOpenImmersion_chart
#print axioms PhilipponNagataExtensionProduct.integral_product
#print axioms PhilipponFlatteningAffineReduction.noetherian_open_scheme
#print axioms PhilipponFlatteningAffineReduction.nonempty_preimage
#print axioms PhilipponFlatteningAffineReduction.isIso_over
#print axioms PhilipponFlatteningAffineReduction.of_affine_target
#print axioms PhilipponFlatteningAffineReduction.available
#print axioms PhilipponAdmissibleFlatteningAssembly.affine_input
#print axioms PhilipponAdmissibleFlatteningAssembly.flat_of_universal
#print axioms solution
