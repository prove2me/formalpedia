-- Prove2me | solution 1 for Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isReduced_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c934bf92-277c-5144-ae91-2a0cbbc6b13d

import Mathlib
import Theorems.Thm_IsIntegrallyClosedIn_of_isReduced_quotient_span_singleton
import Theorems.Thm_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isReduced_fibre

open scoped TensorProduct

theorem isReduced_of_injective_map'' {A B : Type*} [Semiring A] [Ring B]
    (g : A → B) (hg : Function.Injective g)
    (hadd : ∀ x y : A, g (x + y) = g x + g y) (hmul : ∀ x y : A, g (x * y) = g x * g y)
    (hB : IsReduced B) : IsReduced A := by
  have h0 : g 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact add_right_cancel (this.symm.trans (zero_add _).symm)
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero] at hn
    exact eq_zero_of_zero_eq_one hn.symm x
  · have hpow : ∀ m, 0 < m → g (x ^ m) = g x ^ m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => rw [pow_one, pow_one]
      | succ m hm ih => rw [pow_succ, hmul, ih, pow_succ]
    apply hg
    rw [h0]
    exact IsReduced.eq_zero _ ⟨n, by rw [← hpow n hpos, hn, h0]⟩

section NormBaseChange
open TensorProduct

universe u

namespace Algebra p2m_export "Algebra" "TensorProduct.tmul_mul_tmul TensorProduct.quotIdealMapEquivTensorQuot algebraMap TensorProduct.congr TensorProduct.map_tmul TensorProduct.comm TensorProduct.algebraMap_apply TensorProduct.tmul_pow algebraMap_self id restrictScalars TensorProduct.map TensorProduct.cancelBaseChange" namespace TensorProduct p2m_export "Algebra.TensorProduct" "tmul_mul_tmul quotIdealMapEquivTensorQuot congr map_tmul rTensor algebraMap_apply tmul_pow map cancelBaseChange" end Algebra.TensorProduct
p2m_open_scoped "Algebra Algebra.TensorProduct" in

theorem Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isReduced_fibre
    {R B R' K' k' : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    [CommRing R'] [Algebra R R'] (ϖ : R') (hϖ : ϖ ∈ nonZeroDivisors R')
    [CommRing K'] [Algebra R' K'] [IsLocalization.Away ϖ K'] [Algebra R K'] [IsScalarTower R R' K']
    [IsDomain (K' ⊗[R] B)] [IsIntegrallyClosed (K' ⊗[R] B)]
    [CommRing k'] [Algebra R' k'] [Algebra R k'] [IsScalarTower R R' k']
    (hk : Function.Surjective (algebraMap R' k')) (hker : RingHom.ker (algebraMap R' k') = Ideal.span {ϖ})
    (hred : IsReduced (k' ⊗[R] B)) :
    IsDomain (R' ⊗[R] B) ∧ IsIntegrallyClosed (R' ⊗[R] B) := by
  classical

  let f₀ : R' →ₐ[R] K' := IsScalarTower.toAlgHom R R' K'
  let φ : R' ⊗[R] B →ₐ[R] K' ⊗[R] B := Algebra.TensorProduct.map f₀ (AlgHom.id R B)
  have hinjRK : Function.Injective (algebraMap R' K') :=
    IsLocalization.injective K' (Submonoid.powers_le.mpr hϖ)
  have hφ : Function.Injective φ := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := B) f₀.toLinearMap hinjRK
    have h2 : ∀ x, φ x = LinearMap.rTensor B f₀.toLinearMap x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp [φ]
      | tmul a b => simp [φ]
      | add x y hx hy => simp only [map_add, hx, hy]
    intro x y hxy
    apply h1
    rw [← h2, ← h2, hxy]

  haveI hdom : IsDomain (R' ⊗[R] B) := Function.Injective.isDomain φ.toRingHom hφ

  set ϖC : R' ⊗[R] B := algebraMap R' (R' ⊗[R] B) ϖ with hϖCdef
  have hφϖ : φ ϖC = algebraMap K' (K' ⊗[R] B) (algebraMap R' K' ϖ) := by
    rw [hϖCdef, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_self, RingHom.id_apply]
    simp [φ, f₀]
  have hunit : IsUnit (φ ϖC) := by
    rw [hφϖ]
    exact (IsLocalization.Away.algebraMap_isUnit ϖ).map _
  have hϖC : ϖC ∈ nonZeroDivisors (R' ⊗[R] B) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply hunit.ne_zero
    rw [h0, map_zero]

  letI algCL : Algebra (R' ⊗[R] B) (K' ⊗[R] B) := φ.toRingHom.toAlgebra
  have halgCL : ∀ x, algebraMap (R' ⊗[R] B) (K' ⊗[R] B) x = φ x := fun _ => rfl
  haveI : IsLocalization.Away ϖC (K' ⊗[R] B) := by
    rw [IsLocalization.Away, isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      rw [halgCL, map_pow]
      exact hunit.pow n
    · intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨(0, 1), by simp [halgCL]⟩
      | tmul κ b =>
        obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers ϖ) κ
        refine ⟨(r ⊗ₜ b, ⟨ϖC ^ n, n, rfl⟩), ?_⟩
        simp only [halgCL]
        rw [map_pow, hφϖ]
        simp only [φ, f₀, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
        rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          ← map_pow]
        dsimp only at hr
        rw [hr]
      | add x y hx hy =>
        obtain ⟨⟨x₁, ⟨_, n₁, rfl⟩⟩, h₁⟩ := hx
        obtain ⟨⟨y₁, ⟨_, n₂, rfl⟩⟩, h₂⟩ := hy
        refine ⟨(x₁ * ϖC ^ n₂ + y₁ * ϖC ^ n₁, ⟨ϖC ^ (n₁ + n₂), n₁ + n₂, rfl⟩), ?_⟩
        simp only [halgCL, map_add, map_mul, map_pow] at h₁ h₂ ⊢
        rw [pow_add]
        calc (x + y) * (φ ϖC ^ n₁ * φ ϖC ^ n₂)
            = x * φ ϖC ^ n₁ * φ ϖC ^ n₂ + y * φ ϖC ^ n₂ * φ ϖC ^ n₁ := by ring
          _ = φ x₁ * φ ϖC ^ n₂ + φ y₁ * φ ϖC ^ n₁ := by rw [h₁, h₂]
    · intro x y hxy
      exact ⟨1, by rw [hφ hxy]⟩

  have hI : (Ideal.span {ϖ}).map (algebraMap R' (R' ⊗[R] B)) = Ideal.span {ϖC} := by
    rw [Ideal.map_span, Set.image_singleton]
  let e2 : (R' ⧸ Ideal.span {ϖ}) ⊗[R'] (R' ⊗[R] B) ≃ₐ[R']
      (R' ⊗[R] B) ⧸ (Ideal.span {ϖ}).map (algebraMap R' (R' ⊗[R] B)) :=
    (Algebra.TensorProduct.comm R' _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R' ⊗[R] B) (Ideal.span {ϖ})).symm.restrictScalars R')
  have e3 := Algebra.TensorProduct.cancelBaseChange R R' R' (R' ⧸ Ideal.span {ϖ}) B
  let g₀ : R' →ₐ[R] k' := IsScalarTower.toAlgHom R R' k'
  have hg₀ : Function.Surjective g₀ := hk
  have hkerg : RingHom.ker g₀ = Ideal.span {ϖ} := hker
  let eI : (R' ⧸ Ideal.span {ϖ}) ≃ₐ[R] k' :=
    (Ideal.quotientEquivAlgOfEq R hkerg.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hg₀)
  have e4 := Algebra.TensorProduct.congr eI (AlgEquiv.refl (R := R) (A₁ := B))

  have e1 := Ideal.quotEquivOfEq hI.symm
  have etot := e1.trans (e2.symm.toRingEquiv.trans (e3.toRingEquiv.trans e4.toRingEquiv))
  haveI : IsReduced ((R' ⊗[R] B) ⧸ Ideal.span {ϖC}) :=
    isReduced_of_injective_map'' (fun x => etot x) etot.injective etot.map_add etot.map_mul hred

  haveI : IsIntegrallyClosedIn (R' ⊗[R] B) (K' ⊗[R] B) :=
    IsIntegrallyClosedIn.of_isReduced_quotient_span_singleton ϖC hϖC (K' ⊗[R] B)

  have hle : Submonoid.powers ϖC ≤ nonZeroDivisors (R' ⊗[R] B) := Submonoid.powers_le.mpr hϖC
  exact ⟨hdom, IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization (Submonoid.powers ϖC) hle
    (K' ⊗[R] B)⟩

end NormBaseChange

universe u in
theorem solution
    {R B R' K' k' : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    [CommRing R'] [Algebra R R'] (ϖ : R') (hϖ : ϖ ∈ nonZeroDivisors R')
    [CommRing K'] [Algebra R' K'] [IsLocalization.Away ϖ K'] [Algebra R K'] [IsScalarTower R R' K']
    [IsDomain (K' ⊗[R] B)] [IsIntegrallyClosed (K' ⊗[R] B)]
    [CommRing k'] [Algebra R' k'] [Algebra R k'] [IsScalarTower R R' k']
    (hk : Function.Surjective (algebraMap R' k')) (hker : RingHom.ker (algebraMap R' k') = Ideal.span {ϖ})
    (hred : IsReduced (k' ⊗[R] B)) :
    IsDomain (R' ⊗[R] B) ∧ IsIntegrallyClosed (R' ⊗[R] B) :=
  Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isReduced_fibre (K' := K') ϖ hϖ hk hker hred

end S_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isReduced_fibre
end P2MW
export P2MW.S_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isReduced_fibre (solution)
