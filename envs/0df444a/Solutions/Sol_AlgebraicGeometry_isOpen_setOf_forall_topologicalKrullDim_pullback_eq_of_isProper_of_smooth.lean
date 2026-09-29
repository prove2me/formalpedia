-- Prove2me | solution 1 for AlgebraicGeometry.isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c3b2bfa4-656d-59ab-81e7-57a348b0091e

import Mathlib
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace H2a3

theorem specMap_base_eq {S : Type u} [CommRing S] {k : Type u} [Field k] (x : S →+* k)
    (p : ↥(Spec (CommRingCat.of k))) :
    (Spec.map (CommRingCat.ofHom x)).base p = (⟨RingHom.ker x, RingHom.ker_isPrime x⟩ : PrimeSpectrum S) := by
  apply PrimeSpectrum.ext
  show (PrimeSpectrum.comap (CommRingCat.ofHom x).hom p).asIdeal = RingHom.ker x
  rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime p.asIdeal, ← RingHom.ker_eq_comap_bot]
  rfl

theorem exists_geomPoint {S : Type u} [CommRing S] (s : ↥(Spec (CommRingCat.of S))) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (x : S →+* k), RingHom.ker x = s.asIdeal := by
  refine ⟨AlgebraicClosure s.asIdeal.ResidueField, inferInstance, inferInstance,
    (algebraMap s.asIdeal.ResidueField (AlgebraicClosure s.asIdeal.ResidueField)).comp (algebraMap S s.asIdeal.ResidueField), ?_⟩
  rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap s.asIdeal.ResidueField _).injective,
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

variable {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))

theorem exists_smoothOfRelativeDimension_nhd [Smooth f] (z : Z) :
    ∃ (n : ℕ) (V : Z.Opens), z ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hzV, e, hstd⟩ := Smooth.exists_isStandardSmooth f z
  algebraize [(f.appLE U V e).hom]
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hstd
  have hn : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension P.dimension :=
    P.isStandardSmoothOfRelativeDimension rfl
  have h1 : SmoothOfRelativeDimension P.dimension (f.resLE U V e) := by
    haveI : IsAffine (↑V) := hV
    haveI : IsAffine (↑U) := hU
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)]
    refine RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso) _ ?_
    exact ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso).arrow_mk_iso_iff
      (arrowResLEAppIso f U V e)).mpr hn
  refine ⟨P.dimension, V, hzV, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact inferInstanceAs (SmoothOfRelativeDimension (P.dimension + 0) (f.resLE U V e ≫ U.ι))

theorem topologicalKrullDim_pullback_eq [Smooth f] {k : Type u} [Field k] (x : S →+* k)
    [IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))]
    (n : ℕ) (V : Z.Opens) [SmoothOfRelativeDimension n (V.ι ≫ f)]
    (w : ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) (hw : (pullback.fst f (Spec.map (CommRingCat.ofHom x))).base w ∈ V) :
    topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = n := by
  have hsq : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom x)) ∣_ V)
      ((pullback.fst f (Spec.map (CommRingCat.ofHom x)) ⁻¹ᵁ V).ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom x)))
      (V.ι ≫ f) (Spec.map (CommRingCat.ofHom x)) :=
    (isPullback_morphismRestrict (pullback.fst f (Spec.map (CommRingCat.ofHom x))) V).paste_vert
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom x)))
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n
  haveI : SmoothOfRelativeDimension n
      ((pullback.fst f (Spec.map (CommRingCat.ofHom x)) ⁻¹ᵁ V).ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom x))) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n) hsq (inferInstance : SmoothOfRelativeDimension n (V.ι ≫ f))
  haveI : SmoothOfRelativeDimension n (pullback.snd f (Spec.map (CommRingCat.ofHom x))) :=
    AlgebraicGeometry.smoothOfRelativeDimension_of_irreducibleSpace n (f := pullback.snd f (Spec.map (CommRingCat.ofHom x)))
      (V := (pullback.fst f (Spec.map (CommRingCat.ofHom x))) ⁻¹ᵁ V) ⟨w, hw⟩
  haveI : Nonempty ↥(pullback f (Spec.map (CommRingCat.ofHom x))) := ⟨w⟩
  exact le_antisymm
    (AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le (pullback.snd f (Spec.map (CommRingCat.ofHom x))) n)
    (AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim (pullback.snd f (Spec.map (CommRingCat.ofHom x))) n)

theorem exists_fst_eq {k : Type u} [Field k] (x : S →+* k) (z : Z) (hz : RingHom.ker x = (f.base z).asIdeal) :
    ∃ w : ↥(pullback f (Spec.map (CommRingCat.ofHom x))), (pullback.fst f (Spec.map (CommRingCat.ofHom x))).base w = z := by
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := Spec.map (CommRingCat.ofHom x)) z
    (IsLocalRing.closedPoint k) (by rw [specMap_base_eq]; exact PrimeSpectrum.ext hz.symm)
  exact ⟨w, hw⟩

theorem main [IsProper f] [Smooth f]
    (hirr : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (g : ℕ) :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} := by
  let Zg : Set Z := {z | ∃ V : Z.Opens, z ∈ (V : Set Z) ∧ SmoothOfRelativeDimension g (V.ι ≫ f)}
  have hZg : IsOpen Zg := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨V, hzV, hV⟩
    exact ⟨V, fun z' hz' => ⟨V, hz', hV⟩, V.2, hzV⟩
  have key : {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} = f.base '' Zg := by
    ext s
    constructor
    · intro hs
      obtain ⟨k, _, _, x, hx⟩ := exists_geomPoint s
      haveI := hirr k x
      obtain ⟨w⟩ := (inferInstance : Nonempty ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
      let z := (pullback.fst f (Spec.map (CommRingCat.ofHom x))).base w
      have hfz : f.base z = s := by
        have hc := congrArg (fun φ => φ.base w) (pullback.condition (f := f) (g := Spec.map (CommRingCat.ofHom x)))
        simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hc
        show f.base ((pullback.fst f (Spec.map (CommRingCat.ofHom x))).base w) = s
        rw [hc, specMap_base_eq]
        exact PrimeSpectrum.ext hx
      obtain ⟨n, V, hzV, hV⟩ := exists_smoothOfRelativeDimension_nhd f z
      have hdim := topologicalKrullDim_pullback_eq f x n V w hzV
      have hg' := hs k x hx
      rw [hdim] at hg'
      have hng : n = g := by exact_mod_cast hg'
      subst hng
      exact ⟨z, ⟨V, hzV, hV⟩, hfz⟩
    · rintro ⟨z, ⟨V, hzV, hV⟩, rfl⟩ k _ _ x hx
      haveI := hirr k x
      obtain ⟨w, hw⟩ := exists_fst_eq f x z hx
      exact topologicalKrullDim_pullback_eq f x g V w (by rw [hw]; exact hzV)
  rw [key]
  exact f.isOpenMap _ hZg

end H2a3

theorem solution
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Smooth f]
    (hirr : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (g : ℕ) :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} :=
  H2a3.main f hirr g

end S_AlgebraicGeometry_isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth (solution)
