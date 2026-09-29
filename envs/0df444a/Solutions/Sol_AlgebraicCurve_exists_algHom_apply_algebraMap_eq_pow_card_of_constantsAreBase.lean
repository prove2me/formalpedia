-- Prove2me | solution 1 for AlgebraicCurve.exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1925155a-940c-5a22-bfc2-d74bc980184f

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isAlgebraic_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase

set_option autoImplicit false

open scoped TensorProduct

section ConstantsBridge

open AlgebraicCurve

section Bridge

variable {k F₀ : Type*} [Field k] [Field F₀] [Algebra k F₀]

private theorem b0_forall_isAlgebraic_mem_range (hC : ConstantsAreBase k F₀) :
    ∀ y : F₀, IsAlgebraic k y → y ∈ (algebraMap k F₀).range := by
  intro y hy
  have hint : IsIntegral k y := hy.isIntegral
  have hmem : y ∈ LSpace (0 : Divisor k F₀) := by
    rw [mem_lSpace_iff]
    intro v
    have h1 : IsIntegral v.toValuationSubring y := hint.tower_top
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
    have ha' : ((a : v.toValuationSubring) : F₀) = y := ha
    rw [← ha', v.adicValuation_coe]
    simpa using v.heightOneSpectrum.intValuation_le_one a
  rw [ConstantsAreBase] at hC
  rw [hC] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by simpa using hc⟩

end Bridge

section Separable

variable (k K : Type*) [Field k] [Finite k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

private theorem b0_isSeparable : Algebra.IsSeparable k K := inferInstance

end Separable

end ConstantsBridge

section FrobeniusTransport

open TensorProduct

private theorem b0_exists_frob (k F₀ : Type*) [Field k] [Finite k] [Field F₀] [Algebra k F₀] :
    ∃ fr : F₀ →ₐ[k] F₀, ∀ x : F₀, fr x = x ^ Nat.card k := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  haveI : Fact (ringChar k).Prime := ⟨hp⟩
  haveI : CharP F₀ (ringChar k) :=
    charP_of_injective_algebraMap (algebraMap k F₀).injective (ringChar k)
  have hq : Nat.card k = ringChar k ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  refine ⟨{ toFun := fun x => x ^ Nat.card k
            map_one' := one_pow _
            map_mul' := fun x y => mul_pow x y _
            map_zero' := zero_pow Nat.card_pos.ne'
            map_add' := fun x y => ?_
            commutes' := fun c => ?_ }, fun _ => rfl⟩
  · show (x + y) ^ Nat.card k = x ^ Nat.card k + y ^ Nat.card k
    rw [hq]
    exact add_pow_char_pow (x := x) (y := y) (p := ringChar k) (n := (n : ℕ))
  · show algebraMap k F₀ c ^ Nat.card k = algebraMap k F₀ c
    rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

private theorem b0_closing (k K F₀ F : Type*) [Field k] [Field K] [Field F₀] [Field F]
    [Algebra k K] [Algebra k F₀] [Algebra F₀ F] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F]
    (q : ℕ) (fr : F₀ →ₐ[k] F₀) (hfr : ∀ x : F₀, fr x = x ^ q)
    (e : (K ⊗[k] F₀) ≃ₐ[K] F) (he : ∀ x : F₀, e ((1 : K) ⊗ₜ[k] x) = algebraMap F₀ F x) :
    ∃ φ : F →ₐ[K] F, ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ q) := by
  refine ⟨(e.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id K K) fr)).comp
    e.symm.toAlgHom, fun x => ?_⟩
  have h1 : e.symm (algebraMap F₀ F x) = (1 : K) ⊗ₜ[k] x := by
    rw [← he x, e.symm_apply_apply]
  show e (Algebra.TensorProduct.map (AlgHom.id K K) fr (e.symm (algebraMap F₀ F x))) = _
  rw [h1, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hfr, he]

end FrobeniusTransport

namespace ConstantFieldFrobenius

private noncomputable def productHom (k K F₀ F : Type*) [Field k] [Field K] [Field F₀] [Field F]
    [Algebra k K] [Algebra k F₀] [Algebra F₀ F] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F] : K ⊗[k] F₀ →ₐ[K] F :=
  Algebra.TensorProduct.lift (Algebra.ofId K F) (IsScalarTower.toAlgHom k F₀ F)
    (fun _ _ => Commute.all _ _)

private theorem productHom_tmul (k K F₀ F : Type*) [Field k] [Field K] [Field F₀] [Field F]
    [Algebra k K] [Algebra k F₀] [Algebra F₀ F] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F] (a : K) (x : F₀) :
    productHom k K F₀ F (a ⊗ₜ[k] x) = algebraMap K F a * algebraMap F₀ F x := by
  simp [productHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

private theorem productHom_injective (k K F₀ F : Type*) [Field k] [Field K] [Field F₀] [Field F]
    [Algebra k K] [Algebra k F₀] [Algebra F₀ F] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F] (hT : IsField (F₀ ⊗[k] K)) :
    Function.Injective (productHom k K F₀ F) := by
  have hT' : IsField (K ⊗[k] F₀) :=
    MulEquiv.isField hT (Algebra.TensorProduct.comm k K F₀).toMulEquiv
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  obtain ⟨y, hy⟩ := hT'.mul_inv_cancel hx0
  have h1 := congrArg (productHom k K F₀ F) hy
  rw [map_mul, hx, zero_mul, map_one] at h1
  exact zero_ne_one h1

private theorem productHom_surjective (k K F₀ F : Type*) [Field k] [Field K] [Field F₀] [Field F]
    [Algebra k K] [Algebra k F₀] [Algebra F₀ F] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F]
    (hgen : Algebra.adjoin F₀ (Set.range (algebraMap K F)) = ⊤) :
    Function.Surjective (productHom k K F₀ F) := by
  intro z
  have hz : z ∈ Algebra.adjoin F₀ (Set.range (algebraMap K F)) := by
    rw [hgen]; exact Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun x _ => ∃ t, productHom k K F₀ F t = x) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, rfl⟩
    exact ⟨a ⊗ₜ[k] 1, by rw [productHom_tmul, map_one, mul_one]⟩
  · intro r
    exact ⟨1 ⊗ₜ[k] r, by rw [productHom_tmul, map_one, one_mul]⟩
  · rintro x y - - ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, map_add _ _ _⟩
  · rintro x y - - ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s * t, map_mul _ _ _⟩

private theorem exists_algEquiv_tmul_eq (k K F₀ F : Type*) [Field k] [Field K] [Field F₀]
    [Field F] [Algebra k K] [Algebra k F₀] [Algebra F₀ F] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F] (hT : IsField (F₀ ⊗[k] K))
    (hgen : Algebra.adjoin F₀ (Set.range (algebraMap K F)) = ⊤) :
    ∃ e : K ⊗[k] F₀ ≃ₐ[K] F, ∀ x : F₀, e (1 ⊗ₜ[k] x) = algebraMap F₀ F x := by
  refine ⟨AlgEquiv.ofBijective (productHom k K F₀ F)
    ⟨productHom_injective k K F₀ F hT, productHom_surjective k K F₀ F hgen⟩, fun x => ?_⟩
  rw [AlgEquiv.coe_ofBijective, productHom_tmul, map_one, one_mul]

end ConstantFieldFrobenius

theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [Field F₀] [Field F]
    [Algebra k K] [Algebra k F₀] [Algebra F₀ F] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] [Algebra.IsAlgebraic k K]
    (hC : AlgebraicCurve.ConstantsAreBase k F₀)
    (hgen : Algebra.adjoin F₀ (Set.range (algebraMap K F)) = ⊤) :
    ∃ φ : F →ₐ[K] F, ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k) := by
  obtain ⟨fr, hfr⟩ := b0_exists_frob k F₀
  have hT : IsField (F₀ ⊗[k] K) :=
    Algebra.TensorProduct.isField_of_isSeparable_of_forall_isAlgebraic_mem_range k F₀ K
      (b0_forall_isAlgebraic_mem_range hC)
  obtain ⟨e, he⟩ := ConstantFieldFrobenius.exists_algEquiv_tmul_eq k K F₀ F hT hgen
  exact b0_closing k K F₀ F (Nat.card k) fr hfr e he

end S_AlgebraicCurve_exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase
end P2MW
export P2MW.S_AlgebraicCurve_exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase (solution)
