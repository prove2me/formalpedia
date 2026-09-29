-- Prove2me | solution 1 for AlgebraicGeometry.flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5731eae4-e62c-53ec-ad95-8d22e8d54816

import Theorems.Thm_AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology

universe u

namespace P2M
namespace FlatClosedFibre

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

noncomputable abbrev secMap (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top

noncomputable abbrev stkMap (x : X) : CommRingCat.of R ⟶ X.presheaf.stalk x :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial

theorem appTop_germ (U : X.Opens) (x : X) (hx : x ∈ U) :
    f.appTop ≫ X.presheaf.germ ⊤ x trivial = f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hx := by
  have h := X.presheaf.germ_res (homOfLE (le_top : U ≤ ⊤)) x hx
  rw [← h]
  rfl

theorem stkMap_eq (U : X.Opens) (x : X) (hx : x ∈ U) :
    stkMap f x = secMap f U ≫ X.presheaf.germ U x hx := by
  simp only [stkMap, secMap, Category.assoc, appTop_germ f U x hx]

theorem stkMap_apply (U : X.Opens) (x : X) (hx : x ∈ U) (c : R) :
    stkMap f x c = X.presheaf.germ U x hx (secMap f U c) := by
  rw [stkMap_eq f U x hx, CommRingCat.comp_apply]

theorem stkMap_eq_stalkMap (x : X) :
    stkMap f x = StructureSheaf.toStalk R (f x) ≫ f.stalkMap x := by
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f x) trivial) ≫ f.stalkMap x
  rw [Category.assoc, Scheme.Hom.germ_stalkMap f ⊤ x trivial]
  rfl

theorem isUnit_stkMap (x : X) (c : R) (hc : c ∉ (f x).asIdeal) : IsUnit (stkMap f x c) := by
  rw [stkMap_eq_stalkMap, CommRingCat.comp_apply]
  have h1 : IsUnit (StructureSheaf.toStalk R (f x) c) := by
    rw [← StructureSheaf.stalkAlgebra_map]
    exact IsLocalization.map_units ((Spec.structureSheaf R).presheaf.stalk (f x))
      (⟨c, hc⟩ : (f x).asIdeal.primeCompl)
  exact h1.map (f.stalkMap x).hom

theorem torsionFree_of_not_mem (x : X) (c : R) (hc : c ∉ (f x).asIdeal) (z : X.presheaf.stalk x)
    (hz : stkMap f x c * z = 0) : z = 0 :=
  ((isUnit_stkMap f x c hc).mul_right_eq_zero).mp hz

theorem exists_isClosed_specializes [LocallyOfFiniteType f] (x : X)
    (hfx : IsClosed ({f x} : Set (Spec (CommRingCat.of R)))) :
    ∃ y : X, IsClosed ({y} : Set X) ∧ x ⤳ y ∧ f y = f x := by
  set x' : ↥(f.fiber (f x)) := f.asFiber x with hx'
  have hZ : IsLocallyClosed (closure ({x'} : Set ↥(f.fiber (f x)))) := isClosed_closure.isLocallyClosed
  obtain ⟨y', hy'Z, hy'cl⟩ :=
    nonempty_inter_closedPoints (Z := closure ({x'} : Set ↥(f.fiber (f x)))) ⟨x', subset_closure rfl⟩ hZ
  rw [mem_closedPoints_iff] at hy'cl
  have hrange : Set.range (f.fiberι (f x)) = f ⁻¹' {f x} := Scheme.Hom.range_fiberι f (f x)
  have hemb : IsClosedEmbedding (f.fiberι (f x)) :=
    ⟨(f.fiberι (f x)).isEmbedding, by rw [hrange]; exact hfx.preimage f.continuous⟩
  refine ⟨f.fiberι (f x) y', ?_, ?_, ?_⟩
  · have := hemb.isClosedMap _ hy'cl
    rwa [Set.image_singleton] at this
  · have h1 : x' ⤳ y' := specializes_iff_mem_closure.mpr hy'Z
    have h2 := h1.map (f.fiberι (f x)).continuous
    rwa [hx', Scheme.Hom.fiberι_asFiber] at h2
  · have hmem : f.fiberι (f x) y' ∈ Set.range (f.fiberι (f x)) := ⟨y', rfl⟩
    rw [hrange] at hmem
    simpa using hmem

theorem torsionFree_of_specializes_affine {W : X.Opens} (hW : IsAffineOpen W) (x y : ↥W)
    (hxy : (x : X) ⤳ (y : X)) (a : Γ(X, W))
    (hy : ∀ z : X.presheaf.stalk (y : X), X.presheaf.germ W y y.2 a * z = 0 → z = 0)
    (z : X.presheaf.stalk (x : X)) (hz : X.presheaf.germ W x x.2 a * z = 0) : z = 0 := by
  haveI hlx := hW.isLocalization_stalk x
  haveI hly := hW.isLocalization_stalk y
  have hle : hW.primeIdealOf x ≤ hW.primeIdealOf y := by
    rw [PrimeSpectrum.le_iff_specializes]
    have h1 : x ⤳ y := Topology.IsInducing.subtypeVal.specializes_iff.mp hxy
    exact h1.map (hW.isoSpec.hom).continuous
  obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.mk'_surjective (hW.primeIdealOf x).asIdeal.primeCompl z
  simp only at hbt
  subst hbt
  have hz' : IsLocalization.mk' (X.presheaf.stalk (x : X)) (a * b) t = 0 := by
    rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, TopCat.Presheaf.stalk_open_algebraMap]
    exact hz
  rw [IsLocalization.mk'_eq_zero_iff] at hz'
  obtain ⟨m, hm⟩ := hz'

  have h1 : X.presheaf.germ W y y.2 a * X.presheaf.germ W y y.2 (↑m * b) = 0 := by
    rw [← map_mul, ← mul_assoc, mul_comm a, mul_assoc, hm, map_zero]
  have h2 : algebraMap Γ(X, W) (X.presheaf.stalk (y : X)) (↑m * b) = 0 := hy _ h1
  rw [IsLocalization.map_eq_zero_iff (hW.primeIdealOf y).asIdeal.primeCompl] at h2
  obtain ⟨m', hm'⟩ := h2
  rw [IsLocalization.mk'_eq_zero_iff]
  have hm'x : (m' : Γ(X, W)) ∈ (hW.primeIdealOf x).asIdeal.primeCompl := fun h => m'.2 (hle h)
  refine ⟨⟨m' * m, mul_mem hm'x m.2⟩, ?_⟩
  simpa [mul_assoc] using hm'

theorem torsionFree_of_specializes {x y : X} (hxy : x ⤳ y) (c : R)
    (hy : ∀ z : X.presheaf.stalk y, stkMap f y c * z = 0 → z = 0)
    (z : X.presheaf.stalk x) (hz : stkMap f x c * z = 0) : z = 0 := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hxW : x ∈ W := hxy.mem_open W.isOpen hyW
  have hy' : ∀ z : X.presheaf.stalk ((⟨y, hyW⟩ : ↥W) : X),
      X.presheaf.germ W _ (⟨y, hyW⟩ : ↥W).2 (secMap f W c) * z = 0 → z = 0 := by
    intro w hw
    apply hy w
    rw [stkMap_apply f W y hyW]
    exact hw
  refine torsionFree_of_specializes_affine hW ⟨x, hxW⟩ ⟨y, hyW⟩ hxy (secMap f W c) hy' z ?_
  rw [← stkMap_apply f W x hxW]
  exact hz

theorem torsionFree_stalk [IsDedekindDomain R] [LocallyOfFiniteType f]
    (h : ∀ x : X, IsClosed ({x} : Set X) → (f x).asIdeal ≠ ⊥ →
      ∀ (c : R) (z : X.presheaf.stalk x), c ≠ 0 → stkMap f x c * z = 0 → z = 0)
    (x : X) (c : R) (hc : c ≠ 0) (z : X.presheaf.stalk x) (hz : stkMap f x c * z = 0) : z = 0 := by
  by_cases h0 : (f x).asIdeal = ⊥
  ·
    refine torsionFree_of_not_mem f x c ?_ z hz
    rw [h0]
    simpa using hc
  · by_cases hxc : IsClosed ({x} : Set X)
    · exact h x hxc h0 c z hc hz
    ·
      have hmax : (f x).asIdeal.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h0
      have hfx : IsClosed ({f x} : Set (Spec (CommRingCat.of R))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hmax
      obtain ⟨y, hyc, hxy, hfy⟩ := exists_isClosed_specializes f x hfx
      have h0y : (f y).asIdeal ≠ ⊥ := by rw [hfy]; exact h0
      exact torsionFree_of_specializes f hxy c (fun w hw => h y hyc h0y c w hc hw) z hz

theorem flat_of_forall_isClosed [IsDedekindDomain R] [LocallyOfFiniteType f]
    (h : ∀ x : X, IsClosed ({x} : Set X) → (f x).asIdeal ≠ ⊥ →
      ∀ (c : R) (z : X.presheaf.stalk x), c ≠ 0 → stkMap f x c * z = 0 → z = 0) : Flat f := by
  refine (AlgebraicGeometry.flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain f).mpr ?_
  intro U c s hc hcs
  have hcs' : secMap f U.1 c * s = 0 := hcs
  apply TopCat.Presheaf.section_ext X.sheaf U.1 s 0
  intro x hx
  change (X.presheaf.germ U.1 x hx) s = (X.presheaf.germ U.1 x hx) 0
  rw [map_zero]
  apply torsionFree_stalk f h x c hc
  rw [stkMap_apply f U.1 x hx, ← map_mul, hcs', map_zero]

end P2M.FlatClosedFibre

open CategoryTheory AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] [IsDedekindDomain R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f]
    (h : ∀ x : X, IsClosed ({x} : Set X) → (f x).asIdeal ≠ ⊥ →
      ∀ (c : R) (z : X.presheaf.stalk x), c ≠ 0 →
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial) c * z = 0 → z = 0) :
    Flat f :=
  P2M.FlatClosedFibre.flat_of_forall_isClosed f h

end S_AlgebraicGeometry_flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain
end P2MW
export P2MW.S_AlgebraicGeometry_flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain (solution)
