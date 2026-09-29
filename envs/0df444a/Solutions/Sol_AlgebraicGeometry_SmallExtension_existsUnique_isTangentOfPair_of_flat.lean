-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.existsUnique_isTangentOfPair_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1db4ba96-af52-5f75-83a7-3197c4bf8062

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
import Theorems.Thm_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_existsUnique_isTangentOfPair_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

namespace T2aAux

open AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

theorem mem_pairRing_zero_iff (d : C) :
    ((0 : C), d) ∈ pairRing I C ↔ d ∈ I.map (algebraMap T' C) := by
  rw [mem_pairRing]
  simp only [map_zero]
  rw [eq_comm, Ideal.Quotient.eq_zero_iff_mem]

theorem schlessinger_unique (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (ϑ ϑ' : pairRing I C →+* thickening T' V C)
    (h : IsSchlessingerMap I V ι C ϑ) (h' : IsSchlessingerMap I V ι C ϑ') : ϑ = ϑ' := by
  classical
  have hdiag : ∀ (a : C) (ha : (a, a) ∈ pairRing I C), ϑ ⟨(a, a), ha⟩ = ϑ' ⟨(a, a), ha⟩ := by
    intro a ha
    rw [h.1 a ha, h'.1 a ha]
  have hgen : ∀ (d : C) (hd : d ∈ I.map (algebraMap T' C)),
      ϑ ⟨((0 : C), d), (mem_pairRing_zero_iff I C d).mpr hd⟩ = ϑ' ⟨((0 : C), d), (mem_pairRing_zero_iff I C d).mpr hd⟩ := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hi' : i ∈ LinearMap.range ι := by rw [hιI]; exact hi
      obtain ⟨w, rfl⟩ := hi'
      have hmem : ((0 : C), algebraMap T' C (ι w) * 1) ∈ pairRing I C := by
        rw [mul_one]; exact (mem_pairRing_zero_iff I C _).mpr (Ideal.mem_map_of_mem _ hi)
      have e : (⟨((0 : C), algebraMap T' C (ι w)), (mem_pairRing_zero_iff I C _).mpr
          (Ideal.subset_span ⟨ι w, hi, rfl⟩)⟩ : pairRing I C) = ⟨((0 : C), algebraMap T' C (ι w) * 1), hmem⟩ := by
        apply Subtype.ext; simp
      rw [e, h.2 w 1 hmem, h'.2 w 1 hmem]
    | zero =>
      have e : (⟨((0 : C), (0 : C)), (mem_pairRing_zero_iff I C _).mpr (Submodule.zero_mem _)⟩ : pairRing I C) = 0 :=
        Subtype.ext rfl
      rw [e, ϑ.map_zero, ϑ'.map_zero]
    | add x y hx hy ihx ihy =>
      have e : (⟨((0 : C), x + y), (mem_pairRing_zero_iff I C _).mpr (Submodule.add_mem _ hx hy)⟩ : pairRing I C) =
          ⟨((0 : C), x), (mem_pairRing_zero_iff I C _).mpr hx⟩ + ⟨((0 : C), y), (mem_pairRing_zero_iff I C _).mpr hy⟩ :=
        Subtype.ext (by simp)
      rw [e, ϑ.map_add, ϑ'.map_add, ihx, ihy]
    | smul c x hx ihx =>
      have hc : (c, c) ∈ pairRing I C := by rw [mem_pairRing]
      have e : (⟨((0 : C), c • x), (mem_pairRing_zero_iff I C _).mpr (Submodule.smul_mem _ c hx)⟩ : pairRing I C) =
          ⟨(c, c), hc⟩ * ⟨((0 : C), x), (mem_pairRing_zero_iff I C _).mpr hx⟩ :=
        Subtype.ext (by simp [smul_eq_mul])
      rw [e, ϑ.map_mul, ϑ'.map_mul, hdiag c hc, ihx]
  apply RingHom.ext
  rintro ⟨⟨a, b⟩, hab⟩
  have hba : b - a ∈ I.map (algebraMap T' C) := by
    rw [mem_pairRing] at hab
    exact (Ideal.Quotient.eq.mp hab.symm)
  have haa : (a, a) ∈ pairRing I C := by rw [mem_pairRing]
  have e : (⟨(a, b), hab⟩ : pairRing I C) =
      ⟨(a, a), haa⟩ + ⟨((0 : C), b - a), (mem_pairRing_zero_iff I C _).mpr hba⟩ :=
    Subtype.ext (by simp)
  rw [e, ϑ.map_add, ϑ'.map_add, hdiag a haa, hgen (b - a) hba]

end T2aAux

open T2aAux in
theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (v : Spec (CommRingCat.of C) ⟶ Y) (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v) :
    ∃! w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y, IsTangentOfPair I V ι C u v w := by
  classical

  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ :=
    IsLocalRing.exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot I hI hsmall V ι hι hιI C
  let ϑ : pairRing I C →+* thickening T' V C :=
    (RingHom.snd C (thickening T' V C)).comp ((Subring.subtype _).comp Θ.toRingHom)
  have hϑ : IsSchlessingerMap I V ι C ϑ := by
    constructor
    · intro a ha
      exact hΘ2 a ha
    · intro w c h
      exact hΘ3 w c h

  let q : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ I.map (algebraMap T' C)) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))
  have H : IsPullback (CommRingCat.ofHom (pairFst I C)) (CommRingCat.ofHom (pairSnd I C)) q q :=
    IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit q q)
  have hI2 : I ^ 2 = ⊥ := by
    rw [pow_two]
    exact le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)
  have hnil : ∀ x ∈ RingHom.ker q.hom, IsNilpotent x := by
    intro x hx
    have hx' : x ∈ I.map (algebraMap T' C) := by
      simpa [q, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
    refine ⟨2, ?_⟩
    have := Ideal.pow_mem_pow hx' 2
    rwa [← Ideal.map_pow, hI2, Ideal.map_bot, Ideal.mem_bot] at this
  have hsurj : Function.Surjective q.hom := Ideal.Quotient.mk_surjective
  have HP := AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent H hsurj hnil

  let φ : Spec (CommRingCat.of (pairRing I C)) ⟶ Y := HP.desc u v huv
  have hφ1 : Spec.map (CommRingCat.ofHom (pairFst I C)) ≫ φ = u := HP.inl_desc u v huv
  have hφ2 : Spec.map (CommRingCat.ofHom (pairSnd I C)) ≫ φ = v := HP.inr_desc u v huv
  refine ⟨Spec.map (CommRingCat.ofHom ϑ) ≫ φ, ⟨ϑ, hϑ, φ, hφ1, hφ2, rfl⟩, ?_⟩

  rintro w' ⟨ϑ', hϑ', φ', hφ1', hφ2', rfl⟩
  have e1 : ϑ' = ϑ := schlessinger_unique I V ι C hιI ϑ' ϑ hϑ' hϑ
  have e2 : φ' = φ := by
    apply HP.hom_ext
    · rw [hφ1', hφ1]
    · rw [hφ2', hφ2]
  rw [e1, e2]

end S_AlgebraicGeometry_SmallExtension_existsUnique_isTangentOfPair_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_existsUnique_isTangentOfPair_of_flat (solution)
