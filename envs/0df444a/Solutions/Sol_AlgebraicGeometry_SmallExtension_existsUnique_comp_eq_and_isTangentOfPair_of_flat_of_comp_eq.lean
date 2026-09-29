-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/65e7a4d1-8865-5c11-835f-9ba209627165

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

namespace P2MW.S_AlgebraicGeometry_SmallExtension_existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

namespace T2bAux

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

omit [IsLocalRing T'] in

theorem sq_eq_zero_of_mem_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (K : Ideal R)
    (hK : K * K = ⊥) (z : S) (hz : z ∈ Ideal.map f K) : z ^ 2 = 0 := by
  have := Ideal.mul_mem_mul hz hz
  rw [← Ideal.map_mul, hK, Ideal.map_bot] at this
  rw [pow_two]
  exact (Submodule.mem_bot _).1 this

end T2bAux

theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y)
    (hw : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
        (thickening_isPullback V C) ≫ w = Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u)
    (hwq : w ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' (thickening T' V C)))) :
    ∃! v : Spec (CommRingCat.of C) ⟶ Y,
      v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v ∧
      IsTangentOfPair I V ι C u v w := by
  classical

  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ :=
    IsLocalRing.exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot I hI hsmall V ι hι hιI C

  let toCk : C →+* (ResidueField T') ⊗[T'] C := Algebra.TensorProduct.includeRight.toRingHom
  let aug : (thickening T' V C) →+* (ResidueField T') ⊗[T'] C :=
    (Algebra.TensorProduct.lift (AlgHom.id (ResidueField T') ((ResidueField T') ⊗[T'] C))
      ((Algebra.ofId (ResidueField T') ((ResidueField T') ⊗[T'] C)).comp (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V)) (fun _ _ => Commute.all _ _)).toRingHom
  let Q : Subring (C × (thickening T' V C)) := RingHom.eqLocus (toCk.comp (RingHom.fst C (thickening T' V C))) (aug.comp (RingHom.snd C (thickening T' V C)))
  let fstQ : Q →+* C := (RingHom.fst C (thickening T' V C)).comp Q.subtype
  let sndQ : Q →+* (thickening T' V C) := (RingHom.snd C (thickening T' V C)).comp Q.subtype

  have HQ : IsPullback (CommRingCat.ofHom fstQ) (CommRingCat.ofHom (R := Q) (S := (thickening T' V C)) sndQ) (CommRingCat.ofHom (R := C) (S := (ResidueField T') ⊗[T'] C) toCk) (CommRingCat.ofHom (R := (thickening T' V C)) (S := (ResidueField T') ⊗[T'] C) aug) := by
    refine IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_) (fun s m e₁ e₂ => ?_))
    · exact CommRingCat.hom_ext (RingHom.ext fun x => x.2)
    · refine CommRingCat.ofHom ((s.fst.hom.prod s.snd.hom).codRestrict Q fun x => ?_)
      exact congr_arg (fun f : s.pt →+* ((ResidueField T') ⊗[T'] C) => f x) (congrArg CommRingCat.Hom.hom s.condition)
    · exact CommRingCat.hom_ext (RingHom.ext fun x => rfl)
    · exact CommRingCat.hom_ext (RingHom.ext fun x => rfl)
    · refine CommRingCat.hom_ext (RingHom.ext fun (x : s.pt) => Subtype.ext ?_)
      change ((m.hom x : Q) : C × (thickening T' V C)) = (_, _)
      have eq1 := (congr_arg (fun f : s.pt →+* C => f x) (congrArg CommRingCat.Hom.hom e₁) :)
      have eq2 := (congr_arg (fun f : s.pt →+* (thickening T' V C) => f x) (congrArg CommRingCat.Hom.hom e₂) :)
      rw [← eq1, ← eq2]
      rfl
  have haug_tmul : ∀ (x : (ResidueField T') ⊗[T'] C) (t : TrivSqZeroExt (ResidueField T') V), aug (x ⊗ₜ t) = x * algebraMap (ResidueField T') _ t.fst := by
    intro x t
    show Algebra.TensorProduct.lift _ _ _ (x ⊗ₜ t) = _
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have haug_surj : Function.Surjective (CommRingCat.ofHom (R := (thickening T' V C)) (S := (ResidueField T') ⊗[T'] C) aug).hom := by
    intro x; refine ⟨x ⊗ₜ 1, ?_⟩
    show aug (x ⊗ₜ 1) = x
    rw [haug_tmul, TrivSqZeroExt.fst_one, map_one, mul_one]

  have haug_alg : (Algebra.TensorProduct.lift (AlgHom.id (ResidueField T') ((ResidueField T') ⊗[T'] C))
      ((Algebra.ofId (ResidueField T') ((ResidueField T') ⊗[T'] C)).comp (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V)) (fun _ _ => Commute.all _ _)) =
      (Algebra.TensorProduct.rid (ResidueField T') (ResidueField T') ((ResidueField T') ⊗[T'] C)).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') ((ResidueField T') ⊗[T'] C)) (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V)) := by
    apply Algebra.TensorProduct.ext
    · ext a
      simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul]
    · ext t
      simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul, Algebra.algebraMap_eq_smul_one]
  have haug_nil : ∀ z ∈ RingHom.ker (CommRingCat.ofHom (R := (thickening T' V C)) (S := (ResidueField T') ⊗[T'] C) aug).hom,
      IsNilpotent z := by
    intro z hz
    have hz0 : aug z = 0 := hz
    have e1 : (Algebra.TensorProduct.rid (ResidueField T') (ResidueField T') ((ResidueField T') ⊗[T'] C))
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') ((ResidueField T') ⊗[T'] C)) (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V) z) = 0 := by
      have := congrArg (fun f : thickening T' V C →ₐ[(ResidueField T')] (ResidueField T') ⊗[T'] C => f z) haug_alg
      exact this.symm.trans hz0
    have hz1 : Algebra.TensorProduct.map (AlgHom.id (ResidueField T') ((ResidueField T') ⊗[T'] C)) (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V) z = 0 :=
      (Algebra.TensorProduct.rid (ResidueField T') (ResidueField T') ((ResidueField T') ⊗[T'] C)).injective (e1.trans (map_zero _).symm)
    have hz2 : z ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') ((ResidueField T') ⊗[T'] C)) (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V)) := hz1
    rw [Algebra.TensorProduct.lTensor_ker _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)] at hz2
    have hsq : RingHom.ker (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V) *
        RingHom.ker (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V) = ⊥ := by
      rw [← le_bot_iff, Ideal.mul_le]
      intro a ha b' hb
      have ha' : a = TrivSqZeroExt.inr a.snd := by
        ext
        · exact ha
        · rfl
      have hb' : b' = TrivSqZeroExt.inr b'.snd := by
        ext
        · exact hb
        · rfl
      rw [ha', hb', TrivSqZeroExt.inr_mul_inr]; exact Ideal.zero_mem _
    have hz3 : z ∈ Ideal.map (Algebra.TensorProduct.includeRight :
        TrivSqZeroExt (ResidueField T') V →ₐ[ResidueField T'] thickening T' V C).toRingHom
        (RingHom.ker (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V)) := hz2
    exact ⟨2, T2bAux.sq_eq_zero_of_mem_map _ _ hsq z hz3⟩
  have HP := AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent HQ haug_surj haug_nil

  have hzero : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) = Spec.map (CommRingCat.ofHom (R := (thickening T' V C)) (S := (ResidueField T') ⊗[T'] C) aug) := by
    apply (thickening_isPullback V C).hom_ext
    · rw [SquareZero.zeroSection_fst]
      show 𝟙 _ = Spec.map (CommRingCat.ofHom (R := (thickening T' V C)) (S := (ResidueField T') ⊗[T'] C) aug) ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      show x = aug (Algebra.TensorProduct.includeLeftRingHom x)
      show x = aug (x ⊗ₜ 1)
      rw [haug_tmul, TrivSqZeroExt.fst_one, map_one, mul_one]
    · rw [SquareZero.zeroSection_snd]
      show Spec.map _ ≫ Spec.map _ = Spec.map (CommRingCat.ofHom (R := (thickening T' V C)) (S := (ResidueField T') ⊗[T'] C) aug) ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
      show algebraMap (ResidueField T') ((ResidueField T') ⊗[T'] C) t.fst = aug ((1 : (ResidueField T') ⊗[T'] C) ⊗ₜ t)
      rw [haug_tmul, one_mul]
  have hcompat : Spec.map (CommRingCat.ofHom (R := C) (S := (ResidueField T') ⊗[T'] C) toCk) ≫ u = Spec.map (CommRingCat.ofHom (R := (thickening T' V C)) (S := (ResidueField T') ⊗[T'] C) aug) ≫ w := by
    rw [← hzero]; exact hw.symm

  let φ₀ : Spec (CommRingCat.of Q) ⟶ Y := HP.desc u w hcompat
  have hφ₀1 : Spec.map (CommRingCat.ofHom fstQ) ≫ φ₀ = u := HP.inl_desc u w hcompat
  have hφ₀2 : Spec.map (CommRingCat.ofHom (R := Q) (S := (thickening T' V C)) sndQ) ≫ φ₀ = w := HP.inr_desc u w hcompat
  let φ : Spec (CommRingCat.of (pairRing I C)) ⟶ Y := Spec.map (CommRingCat.ofHom Θ.symm.toRingHom) ≫ φ₀
  let ϑ : pairRing I C →+* (thickening T' V C) := sndQ.comp Θ.toRingHom
  have hϑ : IsSchlessingerMap I V ι C ϑ := ⟨fun a ha => hΘ2 a ha, fun w' c h => hΘ3 w' c h⟩

  have hfst : fstQ.comp Θ.toRingHom = pairFst I C := RingHom.ext fun x => hΘ1 x
  have hfst' : (pairFst I C).comp Θ.symm.toRingHom = fstQ := by
    rw [← hfst]
    exact RingHom.ext fun x => by
      show fstQ (Θ (Θ.symm x)) = fstQ x
      rw [RingEquiv.apply_symm_apply]
  have hΘΘ : Θ.toRingHom.comp Θ.symm.toRingHom = RingHom.id _ :=
    RingHom.ext fun x => by show Θ (Θ.symm x) = x; exact Θ.apply_symm_apply x
  have hΘΘ' : Θ.symm.toRingHom.comp Θ.toRingHom = RingHom.id _ :=
    RingHom.ext fun x => by show Θ.symm (Θ x) = x; exact Θ.symm_apply_apply x
  have hSpecΘ : Spec.map (CommRingCat.ofHom Θ.toRingHom) ≫ Spec.map (CommRingCat.ofHom Θ.symm.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hΘΘ, CommRingCat.ofHom_id, Spec.map_id]
  have hSpecΘ' : Spec.map (CommRingCat.ofHom Θ.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom Θ.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hΘΘ', CommRingCat.ofHom_id, Spec.map_id]
  have hSpecΘ_assoc : ∀ {Z : Scheme.{u}} (h : Spec (CommRingCat.of Q) ⟶ Z),
      Spec.map (CommRingCat.ofHom Θ.toRingHom) ≫ Spec.map (CommRingCat.ofHom Θ.symm.toRingHom) ≫ h = h := fun h => by
    rw [← Category.assoc, hSpecΘ, Category.id_comp]
  have hc1 : Spec.map (CommRingCat.ofHom (pairFst I C)) ≫ φ = u := by
    show Spec.map (CommRingCat.ofHom (pairFst I C)) ≫ Spec.map (CommRingCat.ofHom Θ.symm.toRingHom) ≫ φ₀ = u
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfst', hφ₀1]
  have hc2 : w = Spec.map (CommRingCat.ofHom (R := pairRing I C) (S := (thickening T' V C)) ϑ) ≫ φ := by
    show w = Spec.map (CommRingCat.ofHom (R := pairRing I C) (S := (thickening T' V C)) (sndQ.comp Θ.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom Θ.symm.toRingHom) ≫ φ₀
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hφ₀2]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun x => by
      show sndQ x = sndQ (Θ (Θ.symm x))
      rw [RingEquiv.apply_symm_apply])

  have hρmem : ∀ t : T', (algebraMap T' C t, toCk (algebraMap T' C t) ⊗ₜ[(ResidueField T')] (1 : TrivSqZeroExt (ResidueField T') V)) ∈ Q := by
    intro t
    show toCk (algebraMap T' C t) = aug (toCk (algebraMap T' C t) ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V))
    rw [haug_tmul, TrivSqZeroExt.fst_one, map_one, mul_one]
  let ρQ : T' →+* Q :=
    { toFun := fun t => ⟨(algebraMap T' C t, toCk (algebraMap T' C t) ⊗ₜ[(ResidueField T')] (1 : TrivSqZeroExt (ResidueField T') V)), hρmem t⟩
      map_one' := Subtype.ext (Prod.ext (by simp) (by simp [Algebra.TensorProduct.one_def]))
      map_mul' := fun a b => Subtype.ext (Prod.ext (by simp) (by simp [Algebra.TensorProduct.tmul_mul_tmul]))
      map_zero' := Subtype.ext (Prod.ext (by simp) (by simp))
      map_add' := fun a b => Subtype.ext (Prod.ext (by simp) (by simp [TensorProduct.add_tmul])) }
  have hρ1 : fstQ.comp ρQ = algebraMap T' C := RingHom.ext fun t => rfl
  have hφ₀q : φ₀ ≫ qY = Spec.map (CommRingCat.ofHom ρQ) := by
    apply HP.hom_ext
    · rw [← Category.assoc, hφ₀1, hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ1]
    · rw [← Category.assoc, hφ₀2, hwq, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun t => by
        show _ = toCk (algebraMap T' C t) ⊗ₜ[(ResidueField T')] (1 : TrivSqZeroExt (ResidueField T') V)
        simp [toCk, Algebra.TensorProduct.algebraMap_apply])
  have hdiag : ∀ t : T', (algebraMap T' C t, algebraMap T' C t) ∈ pairRing I C := fun t => by rw [mem_pairRing]
  let diagP : T' →+* pairRing I C :=
    { toFun := fun t => ⟨(algebraMap T' C t, algebraMap T' C t), hdiag t⟩
      map_one' := Subtype.ext (Prod.ext (by simp) (by simp))
      map_mul' := fun a b => Subtype.ext (Prod.ext (by simp) (by simp))
      map_zero' := Subtype.ext (Prod.ext (by simp) (by simp))
      map_add' := fun a b => Subtype.ext (Prod.ext (by simp) (by simp)) }
  have hΘρ : Θ.symm.toRingHom.comp ρQ = diagP := by
    apply RingHom.ext; intro t
    apply Θ.injective
    show Θ (Θ.symm (ρQ t)) = Θ (diagP t)
    rw [RingEquiv.apply_symm_apply]
    symm
    show Θ ⟨(algebraMap T' C t, algebraMap T' C t), hdiag t⟩ = ρQ t
    apply Subtype.ext
    apply Prod.ext
    · rw [hΘ1]; rfl
    · rw [hΘ2 _ (hdiag t)]; rfl
  have hφq : φ ≫ qY = Spec.map (CommRingCat.ofHom diagP) := by
    show (Spec.map (CommRingCat.ofHom Θ.symm.toRingHom) ≫ φ₀) ≫ qY = _
    rw [Category.assoc, hφ₀q, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hΘρ]
    rfl
  have hc3 : (Spec.map (CommRingCat.ofHom (pairSnd I C)) ≫ φ) ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)) := by
    rw [Category.assoc, hφq, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hc4 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ (Spec.map (CommRingCat.ofHom (pairSnd I C)) ≫ φ) := by
    have e : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ Spec.map (CommRingCat.ofHom (pairFst I C)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ Spec.map (CommRingCat.ofHom (pairSnd I C)) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun x => x.2)
    rw [← hc1, ← Category.assoc, e, Category.assoc]
  refine ⟨Spec.map (CommRingCat.ofHom (pairSnd I C)) ≫ φ, ⟨hc3, hc4, ⟨ϑ, hϑ, φ, hc1, rfl, hc2⟩⟩, ?_⟩

  rintro v' ⟨-, -, ⟨ϑ', hϑ', φ', h1', h2', h3'⟩⟩
  have eϑ : ϑ' = ϑ := T2bAux.schlessinger_unique I V ι C hιI ϑ' ϑ hϑ' hϑ
  have eφ₀ : Spec.map (CommRingCat.ofHom Θ.toRingHom) ≫ φ' = φ₀ := by
    apply HP.hom_ext
    · rw [hφ₀1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfst]
      exact h1'
    · rw [hφ₀2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h3', eϑ]
      congr 2
  have eφ : φ' = φ := by
    show φ' = Spec.map (CommRingCat.ofHom Θ.symm.toRingHom) ≫ φ₀
    rw [← eφ₀, ← Category.assoc, hSpecΘ', Category.id_comp]
  rw [← h2', eφ]

end S_AlgebraicGeometry_SmallExtension_existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq (solution)
