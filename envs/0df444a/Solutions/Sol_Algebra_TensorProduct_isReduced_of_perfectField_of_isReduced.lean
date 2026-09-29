-- Prove2me | solution 1 for Algebra.TensorProduct.isReduced_of_perfectField_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a26c3586-9b48-5ed9-84a2-49aef4543493

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

set_option synthInstance.maxHeartbeats 800000

open TensorProduct

namespace F1

variable {A : Type u} [CommRing A]

theorem isPrime_of_mem_minimalPrimes {p : Ideal A} (hp : p ∈ minimalPrimes A) : p.IsPrime := hp.1.1

theorem sInf_minimalPrimes_eq_bot [IsReduced A] : sInf (minimalPrimes A) = (⊥ : Ideal A) := by
  have h : sInf ((⊥ : Ideal A).minimalPrimes) = (⊥ : Ideal A).radical := Ideal.sInf_minimalPrimes
  rw [minimalPrimes, h]
  exact nilradical_eq_zero A

abbrev MinP (A : Type u) [CommRing A] : Type u := ↥(minimalPrimes A)

noncomputable scoped instance fintypeMinP [IsNoetherianRing A] : Fintype (MinP A) :=
  (minimalPrimes.finite_of_isNoetherianRing (R := A)).fintype

scoped instance isPrime_minP (p : MinP A) : (p.1).IsPrime := isPrime_of_mem_minimalPrimes p.2
scoped instance isDomain_quot_minP (p : MinP A) : IsDomain (A ⧸ p.1) := Ideal.Quotient.isDomain p.1

noncomputable def toProd (k : Type v) [CommRing k] [Algebra k A] :
    A →ₐ[k] (∀ p : MinP A, FractionRing (A ⧸ p.1)) :=
  Pi.algHom k _ fun p => (IsScalarTower.toAlgHom k (A ⧸ p.1) (FractionRing (A ⧸ p.1))).comp
    (Ideal.Quotient.mkₐ k p.1)

theorem toProd_apply (k : Type v) [CommRing k] [Algebra k A] (a : A) (p : MinP A) :
    toProd k a p = algebraMap (A ⧸ p.1) (FractionRing (A ⧸ p.1)) (Ideal.Quotient.mk p.1 a) := rfl

theorem toProd_injective (k : Type v) [CommRing k] [Algebra k A] [IsReduced A] :
    Function.Injective (toProd (A := A) k) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : ∀ p : MinP A, a ∈ p.1 := by
    intro p
    have := congrFun ha p
    rw [toProd_apply, Pi.zero_apply, map_eq_zero_iff _ (IsFractionRing.injective (A ⧸ p.1) (FractionRing (A ⧸ p.1))),
      Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have : a ∈ sInf (minimalPrimes A) := by
    rw [Submodule.mem_sInf]
    exact fun p hp => hmem ⟨p, hp⟩
  rwa [sInf_minimalPrimes_eq_bot, Submodule.mem_bot] at this

theorem isReduced_tensor_of_forall_minimalPrimes {k : Type v} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [IsReduced A] (K : Type w) [Field K] [Algebra k K]
    (h : ∀ p ∈ minimalPrimes A, IsReduced (K ⊗[k] FractionRing (A ⧸ p))) :
    IsReduced (K ⊗[k] A) := by
  classical

  let B : MinP A → Type u := fun p => FractionRing (A ⧸ p.1)
  let e : K ⊗[k] (∀ p : MinP A, B p) ≃ₐ[K] (∀ p : MinP A, K ⊗[k] B p) := Algebra.TensorProduct.piRight k K K B
  let m : K ⊗[k] A →ₐ[K] K ⊗[k] (∀ p : MinP A, B p) := Algebra.TensorProduct.map (AlgHom.id K K) (toProd k)
  have hm : Function.Injective m := by
    have h1 : Function.Injective ((toProd (A := A) k).toLinearMap.lTensor K) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (toProd_injective k)
    intro x y hxy
    exact h1 hxy
  haveI : ∀ p : MinP A, IsReduced (K ⊗[k] B p) := fun p => h p.1 p.2
  exact isReduced_of_injective (e.toAlgHom.comp m) (e.injective.comp hm)

end F1
p2m_reactivate "P2MW.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced.F1"

namespace F1

section DOM

variable (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] (ι : Type*)

noncomputable def polyToE : MvPolynomial ι k →+* FractionRing (MvPolynomial ι K) :=
  (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))).comp (MvPolynomial.map (algebraMap k K))

theorem polyToE_injective : Function.Injective (polyToE k K ι) :=
  (IsFractionRing.injective (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))).comp
    (MvPolynomial.map_injective _ (algebraMap k K).injective)

noncomputable def fracToE : FractionRing (MvPolynomial ι k) →ₐ[k] FractionRing (MvPolynomial ι K) :=
  { IsFractionRing.lift (polyToE_injective k K ι) with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)),
        IsFractionRing.lift_algebraMap, polyToE, RingHom.comp_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C,
        IsScalarTower.algebraMap_apply k K (FractionRing (MvPolynomial ι K)),
        IsScalarTower.algebraMap_apply K (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)), MvPolynomial.algebraMap_eq] }

theorem fracToE_algebraMap (p : MvPolynomial ι k) :
    fracToE k K ι (algebraMap (MvPolynomial ι k) _ p) = polyToE k K ι p := by
  show IsFractionRing.lift (polyToE_injective k K ι) _ = _
  exact IsFractionRing.lift_algebraMap _ _

noncomputable def liftFrac : K ⊗[k] FractionRing (MvPolynomial ι k) →ₐ[k] FractionRing (MvPolynomial ι K) :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k K _) (fracToE k K ι) (fun _ _ => Commute.all _ _)

noncomputable def inclPoly : K ⊗[k] MvPolynomial ι k →ₐ[k] K ⊗[k] FractionRing (MvPolynomial ι k) :=
  Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k (MvPolynomial ι k) _)

theorem liftFrac_comp_inclPoly_apply (w : K ⊗[k] MvPolynomial ι k) :
    liftFrac k K ι (inclPoly k K ι w) =
      algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (MvPolynomial.algebraTensorAlgEquiv k K w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    simp only [inclPoly, liftFrac, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.lift_tmul, fracToE_algebraMap,
      MvPolynomial.algebraTensorAlgEquiv_tmul, Algebra.smul_def, map_mul, polyToE, RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem liftFrac_inclPoly_injective : Function.Injective (fun w => liftFrac k K ι (inclPoly k K ι w)) := by
  intro w₁ w₂ h
  simp only [liftFrac_comp_inclPoly_apply] at h
  exact (MvPolynomial.algebraTensorAlgEquiv k K).injective
    (IsFractionRing.injective (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) h)

theorem exists_denom (z : K ⊗[k] FractionRing (MvPolynomial ι k)) :
    ∃ s : MvPolynomial ι k, s ≠ 0 ∧ ∃ w : K ⊗[k] MvPolynomial ι k,
      ((1 : K) ⊗ₜ[k] algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) s) * z = inclPoly k K ι w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul a f =>
    obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (MvPolynomial ι k)) f
    refine ⟨s.1, nonZeroDivisors.ne_zero s.2, a ⊗ₜ p, ?_⟩
    simp only [inclPoly, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [mul_comm, IsLocalization.mk'_spec]
  | add x y hx hy =>
    obtain ⟨s₁, hs₁, w₁, h₁⟩ := hx
    obtain ⟨s₂, hs₂, w₂, h₂⟩ := hy
    refine ⟨s₁ * s₂, mul_ne_zero hs₁ hs₂, ((1 : K) ⊗ₜ s₂) * w₁ + ((1 : K) ⊗ₜ s₁) * w₂, ?_⟩
    have e : ((1 : K) ⊗ₜ[k] algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) (s₁ * s₂)) =
        ((1 : K) ⊗ₜ[k] algebraMap _ (FractionRing (MvPolynomial ι k)) s₁) *
          ((1 : K) ⊗ₜ[k] algebraMap _ (FractionRing (MvPolynomial ι k)) s₂) := by
      rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have i₁ : inclPoly k K ι ((1 : K) ⊗ₜ s₁) = (1 : K) ⊗ₜ algebraMap _ (FractionRing (MvPolynomial ι k)) s₁ := by
      simp [inclPoly]
    have i₂ : inclPoly k K ι ((1 : K) ⊗ₜ s₂) = (1 : K) ⊗ₜ algebraMap _ (FractionRing (MvPolynomial ι k)) s₂ := by
      simp [inclPoly]
    rw [e, mul_add, map_add, map_mul, map_mul, i₁, i₂, ← h₁, ← h₂]
    ring

theorem liftFrac_injective : Function.Injective (liftFrac k K ι) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨s, hs, w, hw⟩ := exists_denom k K ι z
  have h1 : liftFrac k K ι (inclPoly k K ι w) = 0 := by rw [← hw, map_mul, hz, mul_zero]
  have hw0 : w = 0 := liftFrac_inclPoly_injective k K ι (by simpa using h1)
  rw [hw0, map_zero] at hw

  have hsF : algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) s ≠ 0 :=
    fun h => hs ((IsFractionRing.injective _ _) (by rw [h, map_zero]))
  have hunit : ((1 : K) ⊗ₜ[k] (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) s)⁻¹) *
      ((1 : K) ⊗ₜ[k] algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) s) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hsF]; rfl
  calc z = (((1 : K) ⊗ₜ[k] (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) s)⁻¹) *
      ((1 : K) ⊗ₜ[k] algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) s)) * z := by rw [hunit, one_mul]
    _ = 0 := by rw [mul_assoc, hw, mul_zero]

end DOM
p2m_reactivate "P2MW.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced.F1"

section Interface

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] {L : Type*} [Field L] [Algebra k L]
  {ι : Type*} (x : ι → L) (hx : AlgebraicIndependent k x)

noncomputable def toEAlgHom : ↥(IntermediateField.adjoin k (Set.range x)) →ₐ[k] FractionRing (MvPolynomial ι K) :=
  (fracToE k K ι).comp (hx.aevalEquivField.symm : ↥(IntermediateField.adjoin k (Set.range x)) →ₐ[k] _)

noncomputable def toE : ↥(IntermediateField.adjoin k (Set.range x)) →+* FractionRing (MvPolynomial ι K) :=
  (toEAlgHom K x hx).toRingHom

theorem toE_algebraMap (c : k) :
    toE K x hx (algebraMap k _ c) = algebraMap k (FractionRing (MvPolynomial ι K)) c :=
  (toEAlgHom K x hx).commutes c

theorem injective_liftToE :
    Function.Injective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k K (FractionRing (MvPolynomial ι K)))
      (toEAlgHom K x hx) (fun _ _ => Commute.all _ _)) := by
  let e : K ⊗[k] ↥(IntermediateField.adjoin k (Set.range x)) ≃ₐ[k] K ⊗[k] FractionRing (MvPolynomial ι k) :=
    Algebra.TensorProduct.congr AlgEquiv.refl hx.aevalEquivField.symm
  have hfac : (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k K (FractionRing (MvPolynomial ι K)))
      (toEAlgHom K x hx) (fun _ _ => Commute.all _ _)) = (liftFrac k K ι).comp e.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a f
    simp [liftFrac, toEAlgHom, e]
  rw [hfac]
  exact (liftFrac_injective k K ι).comp e.injective

end Interface
p2m_reactivate "P2MW.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced.F1"

end F1
p2m_reactivate "P2MW.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced.F1"

namespace F1

section FieldCase

theorem isReduced_tensor_of_isSeparable (F E L : Type*) [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
    [Algebra.IsSeparable F L] [Algebra.EssFiniteType F L] : IsReduced (L ⊗[F] E) := by
  haveI : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  haveI : Algebra.FormallyUnramified E (E ⊗[F] L) := inferInstance
  haveI : Algebra.EssFiniteType E (E ⊗[F] L) := inferInstance
  haveI : IsReduced (E ⊗[F] L) := Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[F] L)
  exact isReduced_of_injective (Algebra.TensorProduct.comm F L E) (Algebra.TensorProduct.comm F L E).injective

theorem isReduced_tensor_of_injective {k F K E L : Type*} [Field k] [Field F] [Field K] [Field E] [Field L]
    [Algebra k F] [Algebra k K] [Algebra k E] [Algebra F E] [Algebra K E] [IsScalarTower k F E] [IsScalarTower k K E]
    [Algebra k L] [Algebra F L] [IsScalarTower k F L] [Algebra.IsSeparable F L] [Algebra.EssFiniteType F L]
    (hψ : Function.Injective (Algebra.TensorProduct.lift (Algebra.ofId F E) (IsScalarTower.toAlgHom k K E)
      (fun _ _ => Commute.all _ _) : F ⊗[k] K →ₐ[F] E)) : IsReduced (K ⊗[k] L) := by
  haveI : IsReduced (L ⊗[F] E) := isReduced_tensor_of_isSeparable F E L
  set ψ : F ⊗[k] K →ₐ[F] E := Algebra.TensorProduct.lift (Algebra.ofId F E) (IsScalarTower.toAlgHom k K E)
      (fun _ _ => Commute.all _ _) with hψdef

  let φ : L ⊗[F] (F ⊗[k] K) →ₐ[F] L ⊗[F] E := Algebra.TensorProduct.map (AlgHom.id F L) ψ
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) ψ.toLinearMap hψ

  let e : K ⊗[k] L ≃ₐ[k] L ⊗[F] (F ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K L).trans
      ((Algebra.TensorProduct.cancelBaseChange k F F L K).symm.restrictScalars k)
  exact isReduced_of_injective ((φ.restrictScalars k).comp e.toAlgHom) (hφ.comp e.injective)

set_option synthInstance.maxHeartbeats 400000 in

theorem isReduced_tensor_of_adjoin_of_isSeparable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    {L : Type*} [Field L] [Algebra k L] {ι : Type*} (x : ι → L) (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) L]
    [Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range x)) L] : IsReduced (K ⊗[k] L) := by
  letI : Algebra (IntermediateField.adjoin k (Set.range x)) (FractionRing (MvPolynomial ι K)) :=
    (toEAlgHom K x hx).toRingHom.toAlgebra
  haveI : IsScalarTower k (IntermediateField.adjoin k (Set.range x)) (FractionRing (MvPolynomial ι K)) :=
    IsScalarTower.of_algebraMap_eq (fun c => ((toEAlgHom K x hx).commutes c).symm)
  refine isReduced_tensor_of_injective (F := IntermediateField.adjoin k (Set.range x))
    (E := FractionRing (MvPolynomial ι K)) ?_

  have h1 := injective_liftToE K x hx
  set ψ := (Algebra.TensorProduct.lift (Algebra.ofId (IntermediateField.adjoin k (Set.range x)) (FractionRing (MvPolynomial ι K)))
      (IsScalarTower.toAlgHom k K (FractionRing (MvPolynomial ι K))) (fun _ _ => Commute.all _ _) :
      (IntermediateField.adjoin k (Set.range x)) ⊗[k] K →ₐ[IntermediateField.adjoin k (Set.range x)] FractionRing (MvPolynomial ι K))
  have heq : ∀ z, ψ z = (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k K (FractionRing (MvPolynomial ι K)))
      (toEAlgHom K x hx) (fun _ _ => Commute.all _ _)) (Algebra.TensorProduct.comm k _ K z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [ψ, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.comm_tmul]
      rw [mul_comm]
      rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  intro z w hzw
  have : Algebra.TensorProduct.comm k _ K z = Algebra.TensorProduct.comm k _ K w := h1 (by rw [← heq, ← heq, hzw])
  exact (Algebra.TensorProduct.comm k _ K).injective this

theorem isReduced_tensor_field_of_perfectField {k : Type*} [Field k] [PerfectField k] (L : Type*) [Field L] [Algebra k L]
    [Algebra.EssFiniteType k L] (K : Type*) [Field K] [Algebra k K] : IsReduced (K ⊗[k] L) := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L
  have hrange : Set.range ((↑) : s → L) = (s : Set L) := Subtype.range_coe
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → L))) L := by
    rw [hrange]; exact hsep
  haveI : Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range ((↑) : s → L))) L :=
    Algebra.EssFiniteType.of_comp k _ L
  exact isReduced_tensor_of_adjoin_of_isSeparable K ((↑) : s → L) hs.1

end FieldCase
p2m_reactivate "P2MW.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced.F1"

theorem main (k : Type*) [Field k] [PerfectField k] (A : Type*) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [IsReduced A] (K : Type*) [Field K] [Algebra k K] : IsReduced (K ⊗[k] A) := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine isReduced_tensor_of_forall_minimalPrimes K (fun p hp => ?_)
  haveI : p.IsPrime := hp.1.1
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  haveI : Algebra.FiniteType k (A ⧸ p) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI : Algebra.EssFiniteType k (FractionRing (A ⧸ p)) :=
    Algebra.EssFiniteType.comp k (A ⧸ p) (FractionRing (A ⧸ p))
  exact isReduced_tensor_field_of_perfectField (FractionRing (A ⧸ p)) K

end F1
p2m_reactivate "P2MW.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced.F1"

theorem solution
    (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]
    (K : Type w) [Field K] [Algebra k K] :
    IsReduced (K ⊗[k] A) := by
  exact F1.main k A K

end S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced
end P2MW
export P2MW.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced (solution)
