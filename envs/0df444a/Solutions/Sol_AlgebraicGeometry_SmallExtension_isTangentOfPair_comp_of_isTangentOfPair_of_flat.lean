-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isTangentOfPair_comp_of_isTangentOfPair_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1f99033e-d240-5a23-aec7-950eda5d63cd

import Mathlib
import Theorems.Thm_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isTangentOfPair_comp_of_isTangentOfPair_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

namespace T2cAux

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

theorem ringHom_ext_of_pairRing (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {S : Type u} [NonAssocSemiring S] (ϑ ϑ' : pairRing I C →+* S)
    (hdiag : ∀ (a : C) (ha : (a, a) ∈ pairRing I C), ϑ ⟨(a, a), ha⟩ = ϑ' ⟨(a, a), ha⟩)
    (hgen0 : ∀ (v : V) (h : ((0 : C), algebraMap T' C (ι v)) ∈ pairRing I C),
      ϑ ⟨((0 : C), algebraMap T' C (ι v)), h⟩ = ϑ' ⟨((0 : C), algebraMap T' C (ι v)), h⟩) : ϑ = ϑ' := by
  classical
  have hgen : ∀ (d : C) (hd : d ∈ I.map (algebraMap T' C)),
      ϑ ⟨((0 : C), d), (mem_pairRing_zero_iff I C d).mpr hd⟩ = ϑ' ⟨((0 : C), d), (mem_pairRing_zero_iff I C d).mpr hd⟩ := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hi' : i ∈ LinearMap.range ι := by rw [hιI]; exact hi
      obtain ⟨w, rfl⟩ := hi'
      exact hgen0 w _
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

variable (C' : Type u) [CommRing C'] [Algebra T' C'] (h : C →ₐ[T'] C')

def pairMap : pairRing I C →+* pairRing I C' where
  toFun x := ⟨(h (x : C × C).1, h (x : C × C).2), by
    rw [mem_pairRing]
    have hx := (mem_pairRing I C).mp x.2
    have hd : (x : C × C).2 - (x : C × C).1 ∈ I.map (algebraMap T' C) := Ideal.Quotient.eq.mp hx.symm
    have hcomp : h.toRingHom.comp (algebraMap T' C) = algebraMap T' C' := RingHom.ext fun t => h.commutes t
    have : h (x : C × C).2 - h (x : C × C).1 ∈ I.map (algebraMap T' C') := by
      rw [← map_sub]
      have := Ideal.mem_map_of_mem h.toRingHom hd
      rw [Ideal.map_map, hcomp] at this
      exact this
    exact (Ideal.Quotient.eq.mpr this).symm⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

end T2cAux

open T2cAux in
theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] (C' : Type u) [CommRing C'] [Algebra T' C'] [Module.Flat T' C']
    (h : C →ₐ[T'] C')
    {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y) (w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y)
    (huvw : IsTangentOfPair I V ι C u v w) :
    IsTangentOfPair I V ι C'
      (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ u)
      (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ v)
      (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map
              (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h)
              (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V)) :
            thickening T' V C →ₐ[ResidueField T'] thickening T' V C').toRingHom) ≫ w) := by
  classical
  obtain ⟨ϑ, hϑ, φ, hφ1, hφ2, hw⟩ := huvw

  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ :=
    IsLocalRing.exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot I hI hsmall V ι hι hιI C'
  let ϑ' : pairRing I C' →+* thickening T' V C' :=
    (RingHom.snd C' (thickening T' V C')).comp ((Subring.subtype _).comp Θ.toRingHom)
  have hϑ' : IsSchlessingerMap I V ι C' ϑ' := ⟨fun a ha => hΘ2 a ha, fun v c hh => hΘ3 v c hh⟩

  have hkey : ϑ'.comp (pairMap I C C' h) = ((Algebra.TensorProduct.map
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h)
      (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V)) :
        thickening T' V C →ₐ[ResidueField T'] thickening T' V C').toRingHom).comp ϑ := by
    apply ringHom_ext_of_pairRing I V ι C hιI
    · intro a ha
      have ha' : (h a, h a) ∈ pairRing I C' := by rw [mem_pairRing]
      show ϑ' ⟨(h a, h a), ha'⟩ =
        Algebra.TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h)
          (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V)) (ϑ ⟨(a, a), ha⟩)
      rw [hϑ'.1 (h a) ha', hϑ.1 a ha, Algebra.TensorProduct.map_tmul]
      show ((1 : ResidueField T') ⊗ₜ[T'] h a) ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V) =
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h ((1 : ResidueField T') ⊗ₜ[T'] a)) ⊗ₜ _
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    · intro w hw0
      have e1 : (⟨((0 : C), algebraMap T' C (ι w)), hw0⟩ : pairRing I C) =
          ⟨((0 : C), algebraMap T' C (ι w) * 1), by rw [mul_one]; exact hw0⟩ := Subtype.ext (by simp)
      have hw0' : ((0 : C'), algebraMap T' C' (ι w) * 1) ∈ pairRing I C' := by
        rw [mul_one]; exact (mem_pairRing_zero_iff I C' _).mpr (Ideal.mem_map_of_mem _ (by
          have : ι w ∈ LinearMap.range ι := ⟨w, rfl⟩
          rw [hιI] at this; exact this))
      have e2 : pairMap I C C' h ⟨((0 : C), algebraMap T' C (ι w) * 1), by rw [mul_one]; exact hw0⟩ =
          ⟨((0 : C'), algebraMap T' C' (ι w) * 1), hw0'⟩ := by
        apply Subtype.ext
        show (h 0, h (algebraMap T' C (ι w) * 1)) = ((0 : C'), algebraMap T' C' (ι w) * 1)
        rw [map_zero, map_mul, map_one, AlgHom.commutes]
      rw [e1]
      show ϑ' (pairMap I C C' h _) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h)
          (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V)) (ϑ _)
      rw [e2, hϑ'.2 w 1 hw0', hϑ.2 w 1, Algebra.TensorProduct.map_tmul]
      simp only [map_one]
      rfl

  refine ⟨ϑ', hϑ', Spec.map (CommRingCat.ofHom (pairMap I C C' h)) ≫ φ, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (pairFst I C').comp (pairMap I C C' h) = h.toRingHom.comp (pairFst I C) := RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ1]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (pairSnd I C').comp (pairMap I C C' h) = h.toRingHom.comp (pairSnd I C) := RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ2]
  · rw [hw, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hkey, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc]

end S_AlgebraicGeometry_SmallExtension_isTangentOfPair_comp_of_isTangentOfPair_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isTangentOfPair_comp_of_isTangentOfPair_of_flat (solution)
