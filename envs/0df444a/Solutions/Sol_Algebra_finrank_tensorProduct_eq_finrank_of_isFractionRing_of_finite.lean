-- Prove2me | solution 1 for Algebra.finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/2b2e25ea-cda0-5f3c-9b22-30cfba1d97bd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite

set_option autoImplicit false

universe u v w x

open scoped TensorProduct

namespace FinrankTensorFrac

variable (A : Type u) (B : Type v) (K : Type w) (L : Type x)
  [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]

private noncomputable def toFrac : K ⊗[A] B →ₐ[K] L :=
  Algebra.TensorProduct.lift (Algebra.ofId K L) (IsScalarTower.toAlgHom A B L) (fun _ _ => Commute.all _ _)

omit [IsDomain B] [IsFractionRing A K] [IsFractionRing B L] in
private theorem toFrac_tmul (k : K) (b : B) : toFrac A B K L (k ⊗ₜ b) = algebraMap K L k * algebraMap B L b := by
  simp [toFrac, Algebra.ofId_apply]

omit [IsDomain B] in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem toFrac_injective : Function.Injective (toFrac A B K L) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (K ⊗[A] B) :=
    IsLocalization.tensorRight (R := A) (S := B) (nonZeroDivisors A) (A := K)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) x
  have hf : ∀ b : B, toFrac A B K L (algebraMap B (K ⊗[A] B) b) = algebraMap B L b := fun b => by
    rw [show algebraMap B (K ⊗[A] B) b = (1 : K) ⊗ₜ b from rfl, toFrac_tmul, map_one, one_mul]
  have hspec := IsLocalization.mk'_spec (K ⊗[A] B) b m
  have := congrArg (toFrac A B K L) hspec
  dsimp only at hx
  rw [map_mul, hx, zero_mul, hf] at this
  have hb : b = 0 := (IsFractionRing.injective B L) (by rw [← this, map_zero])
  show IsLocalization.mk' (K ⊗[A] B) b m = 0
  rw [hb, IsLocalization.mk'_zero]

private theorem toFrac_surjective [Module.Finite A B] : Function.Surjective (toFrac A B K L) := by

  haveI : IsDomain (K ⊗[A] B) := (toFrac_injective A B K L).isDomain (toFrac A B K L).toRingHom
  have hfield : IsField (K ⊗[A] B) :=
    isField_of_isIntegral_of_isField' (R := K) (S := K ⊗[A] B) (Field.toIsField K)
  letI := hfield.toField
  intro l
  obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := B) l
  have h2 : toFrac A B K L (1 ⊗ₜ b₂) ≠ 0 := by
    rw [toFrac_tmul, map_one, one_mul]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb₂
  refine ⟨(1 ⊗ₜ b₁) * (1 ⊗ₜ b₂)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, toFrac_tmul, toFrac_tmul, map_one, one_mul, one_mul, div_eq_mul_inv]

private theorem finrank_tensor_eq [Module.Finite A B] :
    Module.finrank K (K ⊗[A] B) = Module.finrank K L :=
  (AlgEquiv.ofBijective (toFrac A B K L) ⟨toFrac_injective A B K L, toFrac_surjective A B K L⟩).toLinearEquiv.finrank_eq

end FinrankTensorFrac

open FinrankTensorFrac in
theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {F F' : Type*} [Field F] [Field F'] [Algebra A F] [IsFractionRing A F]
    [Algebra B F'] [IsFractionRing B F'] (φ : F →+* F')
    (hφ : ∀ a : A, algebraMap B F' (algebraMap A B a) = φ (algebraMap A F a)) :
    Module.finrank K (K ⊗[A] B) = @Module.finrank F F' _ _ φ.toAlgebra.toModule := by

  haveI : IsDomain B := (IsFractionRing.injective B F').isDomain (algebraMap B F')

  let e : K ≃ₐ[A] F := IsLocalization.algEquiv (nonZeroDivisors A) K F
  letI algKF' : Algebra K F' := (φ.comp (e : K →+* F)).toAlgebra
  letI algAF' : Algebra A F' := ((algebraMap B F').comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A K F' := IsScalarTower.of_algebraMap_eq (fun a => by
    show (algebraMap B F') (algebraMap A B a) = φ (e (algebraMap A K a))
    rw [hφ, AlgEquiv.commutes])
  rw [finrank_tensor_eq A B K F']
  letI algFF' : Algebra F F' := φ.toAlgebra
  exact Algebra.finrank_eq_of_equiv_equiv (e : K ≃+* F) (RingEquiv.refl F') (RingHom.ext fun k => rfl)

end S_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
end P2MW
export P2MW.S_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite (solution)
