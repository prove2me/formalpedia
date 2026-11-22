-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
-- name    : AlgebraicGeometry_EtaleClosedFiberSections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T23:47:07.687711+00:00
-- url     : https://prove2.me/theorems/1a43939c-ee75-4785-b8dc-af10f8dd2319
-- title:
--   Lifting étale sections on a proper closed fiber
-- statement:
--   Injectivity of restriction to the closed fiber and existence of lifts on finite covers when the proper point closures have connected closed fibers.

import Definitions.Def_AlgebraicGeometry_EtaleRefinedSectionLifts

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSectionsIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleRefinedSectionLifts (exists_global_lift_on_finite_cover pullClosedSection)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleZariskiSections (openToTerminal exists_global_lift_of_open_lifts)
open PhilipponZariskiTorsorCoordinates (opensToEtale)


namespace PhilipponEtaleClosedFiberSections

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

private abbrev residueMap (R : Type u) [CommRing R] [IsLocalRing R] :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

abbrev closedFiberι {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) :=
  pullback.snd (residueMap R) f

theorem range_closedFiberι {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) :
    Set.range (closedFiberι f) = f ⁻¹' {IsLocalRing.closedPoint R} := by
  change Set.range (pullback.snd (residueMap R) f) = _
  rw [Scheme.Pullback.range_snd]
  congr 1
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨y, rfl⟩
    exact Set.mem_singleton_iff.mpr (IsLocalRing.PrimeSpectrum.comap_residue R y)
  · intro hx
    let y := IsLocalRing.closedPoint (IsLocalRing.ResidueField R)
    refine ⟨y, ?_⟩
    change PrimeSpectrum.comap (IsLocalRing.residue R) y = x
    exact (IsLocalRing.PrimeSpectrum.comap_residue R y).trans (Set.mem_singleton_iff.mp hx).symm

/-- A field-valued point over the closed point factors through the closed fiber. -/
theorem exists_closedFiber_point {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of K) ⟶ Y)
    (hs : f (s default) = IsLocalRing.closedPoint R) :
    ∃ t : Spec (CommRingCat.of K) ⟶ pullback (residueMap R) f, t ≫ closedFiberι f = s := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of K := Spec.preimage (s ≫ f)
  have hφ : Spec.map φ = s ≫ f := Spec.map_preimage _
  have : IsLocalHom φ.hom := (IsLocalRing.isLocalHom_iff_comap_closedPoint φ.hom).2 (by
    change (Spec.map φ) (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint R
    rw [hφ, Scheme.Hom.comp_apply]
    exact (congrArg (fun x : Spec (CommRingCat.of K) => f (s x)) (Subsingleton.elim _ _)).trans hs)
  let ρ := CommRingCat.ofHom (IsLocalRing.ResidueField.lift φ.hom)
  have hρ : Spec.map ρ ≫ residueMap R = s ≫ f := by
    change Spec.map ρ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) = s ≫ f
    rw [← Spec.map_comp, ← hφ]
    rfl
  exact ⟨pullback.lift (Spec.map ρ) s hρ, pullback.lift_snd _ _ _⟩

/-- Restriction of sections is injective if all chosen geometric points
over the closed point lift along the restriction morphism. -/
theorem restrictGlobalSections_app_injective_of_lifts {Y Z : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f] (i : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (hLift : ∀ y : Y, f y = IsLocalRing.closedPoint R →
      ∃ t : Spec (CommRingCat.of (SeparableClosure (Y.residueField y))) ⟶ Z,
        t ≫ i = geometricMap y) :
    Function.Injective ((restrictGlobalSections i).app F) := by
  let T := Scheme.Etale.mk (𝟙 Y)
  let F' := (pushforward i).obj ((pullbackSheaves i).obj F)
  let η : F ⟶ F' := (pullbackAdjunction i).unit.app F
  let e := (globalSectionsIso i).app ((pullbackSheaves i).obj F)
  intro a b hab
  have hη : η.hom.app (op T) a = η.hom.app (op T) b := by
    apply (AddCommGrpCat.mono_iff_injective e.hom).1 inferInstance
    exact hab
  apply PhilipponEtaleClosedFiberCovers.globalSections_eq_of_germs_eq_along_closedFiber f F
  intro y hy
  let Φ := geometricPoint y
  obtain ⟨t, ht⟩ := hLift y hy
  let P (s : Spec (CommRingCat.of (SeparableClosure (Y.residueField y))) ⟶ Y) :=
    Function.Injective ((Scheme.pointSmallEtale s).sheafFiber.map η)
  have hinj : P (geometricMap y) :=
    (congrArg P ht).mp (PhilipponEtaleStalkPullback.stalk_unit_injective i t F)
  let v : Φ.fiber.obj T := Over.homMk (geometricMap y) (Category.comp_id _)
  apply hinj
  change (Φ.presheafFiber.map η.hom) (Φ.toPresheafFiber T v F.obj a) =
    (Φ.presheafFiber.map η.hom) (Φ.toPresheafFiber T v F.obj b)
  calc
    _ = Φ.toPresheafFiber T v F'.obj (η.hom.app (op T) a) :=
      Φ.toPresheafFiber_naturality_apply η.hom T v a
    _ = Φ.toPresheafFiber T v F'.obj (η.hom.app (op T) b) := congrArg _ hη
    _ = _ := (Φ.toPresheafFiber_naturality_apply η.hom T v b).symm

/-- Restriction of global étale sections to the closed fiber is injective
for a proper scheme over any local ring. -/
theorem restrictGlobalSections_app_injective {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Injective ((restrictGlobalSections (closedFiberι f)).app F) := by
  apply restrictGlobalSections_app_injective_of_lifts f (closedFiberι f) F
  intro y hy
  exact exists_closedFiber_point f (geometricMap y) (by simpa using hy)

/-- On a proper scheme over the original proper scheme, restriction to
the inverse image of the closed fiber is injective. -/
theorem restrictGlobalSections_app_injective_on_baseChange {Y Q : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f] (p : Q ⟶ Y) [IsProper p]
    (F : Sheaf Q.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Injective ((restrictGlobalSections (pullback.fst p (closedFiberι f))).app F) := by
  apply restrictGlobalSections_app_injective_of_lifts (p ≫ f) (pullback.fst p (closedFiberι f)) F
  intro y hy
  have h : f ((geometricMap y ≫ p) default) = IsLocalRing.closedPoint R := by
    simpa only [Scheme.Hom.comp_apply, PhilipponEtaleGeometricStalks.geometricMap_apply] using hy
  obtain ⟨t, ht⟩ := exists_closedFiber_point f (geometricMap y ≫ p) h
  exact ⟨pullback.lift (geometricMap y) t ht.symm, pullback.lift_fst ..⟩

/-- Zariski-local lifts suffice for surjectivity of closed-fiber restriction
when the intersections with point closures are preconnected. -/
theorem restrictGlobalSections_app_surjective_of_open_lifts {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (hConn : ∀ y : Y, IsPreconnected
      (f ⁻¹' {IsLocalRing.closedPoint R} ∩ closure ({y} : Set Y)))
    (hLocal :
      let i := closedFiberι f
      let G := (pushforward i).obj ((pullbackSheaves i).obj F)
      ∀ (a : ↥(G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))))) (y : Y),
        f y = IsLocalRing.closedPoint R →
        ∃ (U : Y.Opens) (_ : y ∈ U)
          (b : ↥(F.obj.obj (op ((opensToEtale Y).obj U)))),
          ((pullbackAdjunction i).unit.app F).hom.app (op ((opensToEtale Y).obj U)) b =
            G.obj.map (openToTerminal U).op a) :
    Function.Surjective ((restrictGlobalSections (closedFiberι f)).app F) := by
  let i := closedFiberι f
  have : IsClosedImmersion (residueMap R) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (IsLocalRing.residue R))
      IsLocalRing.residue_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.snd (residueMap R) f))
  have : SpectralSpace Y := {
    toCompactSpace := (quasiCompact_iff_compactSpace f).mp inferInstance
    toQuasiSeparatedSpace := quasiSeparatedSpace_of_quasiSeparated f }
  have hC (y : Y) : IsConnected (Set.range i ∩ closure ({y} : Set Y)) := by
    rw [show Set.range i = _ from range_closedFiberι f]
    exact ⟨PhilipponEtaleClosedFiberCovers.closedFiber_inter_closure_nonempty f y, hConn y⟩
  let e := (globalSectionsIso i).app ((pullbackSheaves i).obj F)
  intro a
  obtain ⟨b, hb⟩ := exists_global_lift_of_open_lifts i F hC (e.inv a) (fun y hy => by
    have hy' : y ∈ f ⁻¹' {IsLocalRing.closedPoint R} := range_closedFiberι f ▸ hy
    exact hLocal (e.inv a) y (Set.mem_singleton_iff.mp hy'))
  refine ⟨b, ?_⟩
  change e.hom (((pullbackAdjunction i).unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 Y))) b) = a
  exact (congrArg (fun t => e.hom t) hb).trans (ConcreteCategory.congr_hom e.inv_hom_id a)

/-- Preconnectedness of closed fibers of preconnected proper schemes implies
preconnectedness of their intersections with point closures in every proper scheme. -/
theorem closedFiber_inter_closure_preconnected {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hFiber : ∀ {V : Scheme.{u}} (g : V ⟶ Spec (CommRingCat.of R))
      [IsProper g] [PreconnectedSpace V], _root_.IsPreconnected (g ⁻¹' {IsLocalRing.closedPoint R}))
    (y : Y) : IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint R} ∩ closure ({y} : Set Y)) := by
  let S : TopologicalSpace.Closeds Y := ⟨closure {y}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have hS : (I.support : Set Y) = closure ({y} : Set Y) := by simp [I, S]
  have : PreconnectedSpace I.subscheme := by
    change PreconnectedSpace (I.support : Set Y)
    rw [hS]
    exact Subtype.preconnectedSpace isPreconnected_singleton.closure
  have h := (hFiber (I.subschemeι ≫ f)).image I.subschemeι I.subschemeι.continuous.continuousOn
  change _root_.IsPreconnected
    (I.subschemeι '' (I.subschemeι ⁻¹' (f ⁻¹' {IsLocalRing.closedPoint R}))) at h
  rwa [Set.image_preimage_eq_inter_range, I.range_subschemeι, hS] at h

/-- Every section on the restriction has a lift after a finite surjective cover. -/
def FiniteCoverLifts {X Z : Scheme.{u}} (i : Z ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  ∀ a : ↥(((pushforward i).obj ((pullbackSheaves i).obj F)).obj.obj
      (op (Scheme.Etale.mk (𝟙 X)))),
    ∃ (P : Scheme.{u}) (p : P ⟶ X), IsFinite p ∧ Surjective p ∧
      ∃ b : ↥(((pullbackSheaves p).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 P)))),
        ((pullbackAdjunction (pullback.fst p i)).unit.app
          ((pullbackSheaves p).obj F)).hom.app (op (Scheme.Etale.mk (𝟙 P))) b =
          pullClosedSection i p F a

/-- A section on the closed fiber lifts globally after a finite surjective
cover if preconnected proper schemes have preconnected closed fibers. -/
theorem exists_closedFiber_lift_on_finite_cover {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (hFiber : ∀ {V : Scheme.{u}} (g : V ⟶ Spec (CommRingCat.of R))
      [IsProper g] [PreconnectedSpace V], _root_.IsPreconnected (g ⁻¹' {IsLocalRing.closedPoint R})) :
    FiniteCoverLifts (closedFiberι f) F := by
  intro a
  have : IsClosedImmersion (residueMap R) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (IsLocalRing.residue R))
      IsLocalRing.residue_surjective
  have : SpectralSpace Y :=
    { toCompactSpace := (quasiCompact_iff_compactSpace f).mp inferInstance
      toQuasiSeparatedSpace := quasiSeparatedSpace_of_quasiSeparated f }
  apply exists_global_lift_on_finite_cover (closedFiberι f) F _ a
  intro P p hp _ x
  let _ : IsFinite p := hp
  rw [Scheme.Pullback.range_fst, range_closedFiberι, ← Set.preimage_comp]
  change IsConnected ((p ≫ f) ⁻¹' {IsLocalRing.closedPoint R} ∩ closure ({x} : Set P))
  exact ⟨PhilipponEtaleClosedFiberCovers.closedFiber_inter_closure_nonempty (p ≫ f) x,
    closedFiber_inter_closure_preconnected (p ≫ f) (fun g => hFiber g) x⟩

end PhilipponEtaleClosedFiberSections

end

end


