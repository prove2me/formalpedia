-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_noetherian_ambientModels_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-22T02:31:09.646426+00:00
-- url     : https://prove2.me/submissions/e5093657-d918-4baa-92dc-52a1e7c764da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_Scheme_ProperAmbientModels
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_noetherian_affineModels_of_isProper

noncomputable section

section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PhilipponProperAmbientModels

universe u

/-- An isomorphism over the base transfers an ambient approximation. -/
def transport {R : Type u} [CommRing R] [IsLocalRing R] {X Y : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of R)} (e : X ≅ Y) (h : e.hom ≫ g = f)
    (M : AmbientModels g) : AmbientModels f := by
  let : Category.{u} M.index := M.category
  let ρ : (Functor.const M.index).obj X ⟶ M.ambient := (Functor.const M.index).map e.hom ≫ M.projection
  refine
    { index := M.index
      category := M.category
      cofiltered := M.cofiltered
      rings := M.rings
      localRing := M.localRing
      noetherian := M.noetherian
      localMap := fun v => M.localMap v
      baseInclusion := M.baseInclusion
      localInclusion := M.localInclusion
      baseColimit := M.baseColimit
      ambient := M.ambient
      affine := fun v => M.affine v
      maps := M.maps
      proper := M.proper
      projection := ρ
      ambientLimit := ?_
      commutes := ?_ }
  · apply M.ambientLimit.ofIsoLimit (Cone.ext e.symm ?_)
    intro j
    change M.projection.app j = e.inv ≫ e.hom ≫ M.projection.app j
    rw [Iso.inv_hom_id_assoc]
  · intro j
    change (e.hom ≫ M.projection.app j) ≫ M.maps.app j = f ≫ Spec.map (M.baseInclusion.app (op j))
    rw [Category.assoc, M.commutes, ← Category.assoc, h]

end PhilipponProperAmbientModels

end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponLocalizeRingDiagram

universe u v

variable {I : Type v} [Category I] {A : I ⥤ CommRingCat.{u}}
  (c : Cocone A) [IsLocalRing c.pt]

private abbrev center (i : I) := (IsLocalRing.maximalIdeal c.pt).comap (c.ι.app i).hom

instance (i : I) : (center c i).IsPrime :=
  (IsLocalRing.maximalIdeal.isMaximal c.pt).isPrime.comap (c.ι.app i).hom

abbrev ring (i : I) := Localization.AtPrime (center c i)

private theorem complement {i j : I} (f : i ⟶ j) :
    (center c i).primeCompl ≤ ((center c j).primeCompl).comap (A.map f).hom := by
  intro x hx
  change ¬ (c.ι.app j).hom ((A.map f).hom x) ∈ IsLocalRing.maximalIdeal c.pt
  have h : (c.ι.app j).hom ((A.map f).hom x) = (c.ι.app i).hom x :=
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (c.w f)) x
  rw [h]
  exact hx

private def transition {i j : I} (f : i ⟶ j) : ring c i →+* ring c j :=
  IsLocalization.map (ring c j) (A.map f).hom (complement c f)

private theorem transition_algebraMap {i j : I} (f : i ⟶ j) (x : A.obj i) :
    transition c f (algebraMap (A.obj i) (ring c i) x) =
      algebraMap (A.obj j) (ring c j) ((A.map f).hom x) :=
  IsLocalization.map_eq (complement c f) x

private theorem units (i : I) (x : (center c i).primeCompl) :
    IsUnit ((c.ι.app i).hom x) :=
  (IsLocalRing.notMem_maximalIdeal (R := c.pt)).mp x.property

def inclusion (i : I) : ring c i →+* c.pt := IsLocalization.lift (units c i)

@[simp]
theorem inclusion_algebraMap (i : I) (x : A.obj i) :
    inclusion c i (algebraMap (A.obj i) (ring c i) x) = (c.ι.app i).hom x :=
  IsLocalization.lift_eq (units c i) x

instance (i : I) : IsLocalHom (inclusion c i) where
  map_nonunit x hx := by
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq (center c i).primeCompl x
    have h := hx.mul ((IsLocalization.map_units (ring c i) t).map (inclusion c i))
    rw [← map_mul, IsLocalization.mk'_spec, inclusion_algebraMap] at h
    have ha : a ∈ (center c i).primeCompl := IsLocalRing.notMem_maximalIdeal.mpr h
    have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (ring c i) (center c i) a).mpr ha
    rw [← IsLocalization.mk'_spec (ring c i) a t] at hu
    exact (IsUnit.mul_iff.mp hu).1

private theorem inclusion_comp_transition {i j : I} (f : i ⟶ j) :
    (inclusion c j).comp (transition c f) = inclusion c i := by
  apply IsLocalization.ringHom_ext (center c i).primeCompl
  ext x
  change inclusion c j (transition c f (algebraMap (A.obj i) (ring c i) x)) =
    inclusion c i (algebraMap (A.obj i) (ring c i) x)
  rw [transition_algebraMap, inclusion_algebraMap, inclusion_algebraMap]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (c.w f)) x

private instance transition_local {i j : I} (f : i ⟶ j) : IsLocalHom (transition c f) where
  map_nonunit x hx := by
    apply (isUnit_map_iff (inclusion c i) x).mp
    rw [← DFunLike.congr_fun (inclusion_comp_transition c f) x]
    exact hx.map (inclusion c j)

/-- Localize the rings at the inverse images of the maximal ideal of the cocone vertex. -/
def diagram : I ⥤ CommRingCat.{u} where
  obj i := .of (ring c i)
  map f := CommRingCat.ofHom (transition c f)
  map_id i := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (center c i).primeCompl
    ext x
    change transition c (𝟙 i) (algebraMap (A.obj i) (ring c i) x) = _
    rw [transition_algebraMap, A.map_id]
    rfl
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (center c i).primeCompl
    ext x
    change transition c (f ≫ g) (algebraMap (A.obj i) (ring c i) x) =
      transition c g (transition c f (algebraMap (A.obj i) (ring c i) x))
    simp only [transition_algebraMap, A.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]

instance (i : I) : IsLocalRing ((diagram c).obj i) := inferInstanceAs (IsLocalRing (ring c i))

instance [∀ i, IsNoetherianRing (A.obj i)] (i : I) : IsNoetherianRing ((diagram c).obj i) :=
  IsLocalization.isNoetherianRing (center c i).primeCompl (ring c i) inferInstance

instance {i j : I} (f : i ⟶ j) : IsLocalHom ((diagram c).map f).hom := transition_local c f

/-- The localization maps from the original ring diagram. -/
def localization : A ⟶ diagram c where
  app i := CommRingCat.ofHom (algebraMap (A.obj i) (ring c i))
  naturality _ _ f := CommRingCat.hom_ext (RingHom.ext fun x => (transition_algebraMap c f x).symm)

/-- The ring maps to the local colimit factor uniquely through the localizations. -/
def cocone : Cocone (diagram c) where
  pt := c.pt
  ι :=
    { app := fun i => CommRingCat.ofHom (inclusion c i)
      naturality := fun i j f => by
        apply CommRingCat.hom_ext
        change (inclusion c j).comp (transition c f) = (RingHom.id c.pt).comp (inclusion c i)
        rw [RingHom.id_comp]
        exact inclusion_comp_transition c f }

instance (i : I) : IsLocalHom ((cocone c).ι.app i).hom := inferInstanceAs (IsLocalHom (inclusion c i))

@[simp, reassoc]
theorem localization_compat (i : I) : (localization c).app i ≫ (cocone c).ι.app i = c.ι.app i :=
  CommRingCat.hom_ext (RingHom.ext (inclusion_algebraMap c i))

/-- Localizing each stage at the inverse image of the limit's closed point
preserves the colimit. -/
def isColimit (h : IsColimit c) : IsColimit (cocone c) where
  desc t := h.desc ((Cocone.precompose (localization c)).obj t)
  fac t i := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (S := ring c i) (center c i).primeCompl
    ext x
    have hx := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (h.fac ((Cocone.precompose (localization c)).obj t) i)) x
    change (h.desc ((Cocone.precompose (localization c)).obj t)).hom
      (inclusion c i (algebraMap (A.obj i) (ring c i) x)) = _
    rwa [inclusion_algebraMap]
  uniq t m hm := h.uniq ((Cocone.precompose (localization c)).obj t) m fun i => by
    change c.ι.app i ≫ m = (localization c).app i ≫ t.ι.app i
    exact (localization_compat_assoc c i m).symm.trans (congrArg ((localization c).app i ≫ ·) (hm i))

end PhilipponLocalizeRingDiagram

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponProperAmbientModels (AmbientModels)


namespace PhilipponLocalizeAmbientModels

universe u

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
  {A : Jᵒᵖ ⥤ CommRingCat.{u}} (c : Cocone A) [IsLocalRing c.pt]

private abbrev localA := PhilipponLocalizeRingDiagram.diagram c
private abbrev localCocone := PhilipponLocalizeRingDiagram.cocone c
private abbrev baseCone := Scheme.Spec.mapCone (coneRightOpOfCocone c)
private abbrev localBaseCone := Scheme.Spec.mapCone (coneRightOpOfCocone (localCocone c))

private abbrev loc : (localA c).rightOp ⋙ Scheme.Spec ⟶ A.rightOp ⋙ Scheme.Spec :=
  Functor.whiskerRight (PhilipponLocalizeRingDiagram.localization c).rightOp Scheme.Spec

omit [IsCofiltered J] in
private theorem loc_compat (j : J) :
    (localBaseCone c).π.app j ≫ (loc c).app j = 𝟙 (Spec c.pt) ≫ (baseCone c).π.app j := by
  change Spec.map ((localCocone c).ι.app (op j)) ≫
    Spec.map ((PhilipponLocalizeRingDiagram.localization c).app (op j)) = _
  rw [← Spec.map_comp, PhilipponLocalizeRingDiagram.localization_compat]
  exact (Category.id_comp ((baseCone c).π.app j)).symm

variable {Y : J ⥤ Scheme.{u}} (g : Y ⟶ A.rightOp ⋙ Scheme.Spec)

private abbrev localized := PhilipponPullbackLimit.diagram (loc c) g

omit [IsCofiltered J] in
private theorem affine_projection (j : J) :
    IsAffineHom ((PhilipponPullbackLimit.second (loc c) g).app j) :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback ((loc c).app j) (g.app j))
    (inferInstanceAs (IsAffineHom (Spec.map ((PhilipponLocalizeRingDiagram.localization c).app (op j)))))

omit [IsCofiltered J] in
private theorem affine_transition [∀ {j k : J} (v : j ⟶ k), IsAffineHom (Y.map v)]
    {j k : J} (v : j ⟶ k) : IsAffineHom ((localized c g).map v) := by
  let p := PhilipponPullbackLimit.second (loc c) g
  let : IsAffineHom (p.app j) := affine_projection c g j
  let : IsAffineHom (p.app k) := affine_projection c g k
  let : IsAffineHom ((localized c g).map v ≫ p.app k) := by rw [p.naturality]; infer_instance
  exact IsAffineHom.of_comp ((localized c g).map v) (p.app k)

variable (d : Cone Y) (f : d.pt ⟶ Spec c.pt)
  (hf : ∀ j, d.π.app j ≫ g.app j = f ≫ (baseCone c).π.app j)

private abbrev localizedCone :=
  PhilipponPullbackLimit.cone (loc c) g (cX := localBaseCone c) (cY := d) (cS := baseCone c)
    (𝟙 (Spec c.pt)) f (loc_compat c) hf

/-- An affine Noetherian approximation over a local base gives a local Noetherian
approximation by pulling each stage back to the corresponding local ring. -/
def ofAffineDiagram (hc : IsColimit c) (hd : IsLimit d)
    [∀ j, IsNoetherianRing (A.obj j)] [∀ j, IsProper (g.app j)]
    [∀ {j k : J} (v : j ⟶ k), IsAffineHom (Y.map v)] : AmbientModels f := by
  let e : d.pt ≅ pullback (𝟙 (Spec c.pt)) f := (asIso (pullback.snd (𝟙 (Spec c.pt)) f)).symm
  have he : e.hom ≫ pullback.fst (𝟙 (Spec c.pt)) f = f := by
    rw [← Category.comp_id (pullback.fst _ _), pullback.condition, ← Category.assoc]
    exact Iso.inv_hom_id_assoc (asIso (pullback.snd (𝟙 (Spec c.pt)) f)) f
  apply PhilipponProperAmbientModels.transport e he
  refine
    { index := J
      category := inferInstance
      cofiltered := inferInstance
      rings := localA c
      localRing := inferInstance
      noetherian := inferInstance
      localMap := fun v => inferInstanceAs (IsLocalHom ((localA c).map v).hom)
      baseInclusion := (localCocone c).ι
      localInclusion j := inferInstanceAs (IsLocalHom ((localCocone c).ι.app j).hom)
      baseColimit := PhilipponLocalizeRingDiagram.isColimit c hc
      ambient := localized c g
      affine := affine_transition c g
      maps := PhilipponPullbackLimit.first (loc c) g
      proper j := inferInstanceAs (IsProper (pullback.fst ((loc c).app j) (g.app j)))
      projection := (localizedCone c g d f hf).π
      ambientLimit := ?_
      commutes := ?_ }
  · exact PhilipponPullbackLimit.isLimit (loc c) g (cX := localBaseCone c) (cY := d) (cS := baseCone c)
      (𝟙 (Spec c.pt)) f (loc_compat c) hf
      (isLimitOfPreserves Scheme.Spec
        (isLimitConeRightOpOfCocone _ (PhilipponLocalizeRingDiagram.isColimit c hc))) hd
      (isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ hc))
  · intro j
    exact PhilipponPullbackLimit.cone_first (loc c) g
      (cX := localBaseCone c) (cY := d) (cS := baseCone c) (𝟙 (Spec c.pt)) f (loc_compat c) hf j

end PhilipponLocalizeAmbientModels

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PhilipponProperAffineApproximation
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
/-- Localize the affine models at the images of the closed point of the base. -/
def localize [IsLocalRing R] (M : AffineModels f) : PhilipponProperAmbientModels.AmbientModels f := by
  let : Category.{u} M.index := M.category
  let : IsCofiltered M.index := M.cofiltered
  let : ∀ j, IsNoetherianRing (M.rings.obj j) := M.noetherian
  let : ∀ {j k : M.index} (v : j ⟶ k), IsAffineHom (M.ambient.map v) := fun v => M.affine v
  let : ∀ j, IsProper (M.maps.app j) := M.proper
  let c : Cocone M.rings := ⟨CommRingCat.of R, M.baseInclusion⟩
  let d : Cone M.ambient := ⟨X, M.projection⟩
  exact PhilipponLocalizeAmbientModels.ofAffineDiagram c M.maps d f M.commutes M.baseColimit M.ambientLimit

end PhilipponProperAffineApproximation

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    Nonempty (PhilipponProperAmbientModels.AmbientModels f) := by
  obtain ⟨M⟩ := AlgebraicGeometry.Scheme.nonempty_noetherian_affineModels_of_isProper f
  exact ⟨PhilipponProperAffineApproximation.localize f M⟩

end

end
