-- Prove2me | solution 1 for AlgebraicGeometry.exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/bc3b32d4-1018-5433-b14a-d28f2e5db075

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two

set_option autoImplicit false

universe u

noncomputable section

section
p2m_open "Algebra Coalgebra Bialgebra TensorProduct Algebra.TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"

namespace HopfPiTwo

private lemma int_idem {c : ℤ} (h : c * c = c) : c = 0 ∨ c = 1 := by
  have h0 : c * (c - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by omega)

private lemma single_add_single {i₀ i₁ : Fin 2} (hne : i₀ ≠ i₁) :
    (Pi.single i₀ 1 : Fin 2 → ℤ) + Pi.single i₁ 1 = 1 := by
  ext j
  have hj : j = i₀ ∨ j = i₁ := by omega
  rcases hj with rfl | rfl <;>
    simp [hne, hne.symm]

private lemma single_mul_single {i₀ i₁ : Fin 2} (hne : i₀ ≠ i₁) :
    (Pi.single i₀ 1 : Fin 2 → ℤ) * Pi.single i₁ 1 = 0 := by
  ext j
  have hj : j = i₀ ∨ j = i₁ := by omega
  rcases hj with rfl | rfl <;>
    simp [hne, hne.symm]

private lemma pi_decomp (p : Fin 2 → ℤ) (i₀ i₁ : Fin 2) (hne : i₀ ≠ i₁) :
    p = p i₀ • (Pi.single i₀ 1 : Fin 2 → ℤ) + p i₁ • Pi.single i₁ 1 := by
  ext j
  have hj : j = i₀ ∨ j = i₁ := by omega
  rcases hj with rfl | rfl <;>
    simp [hne, hne.symm]

private lemma pi_decomp_mul (p : Fin 2 → ℤ) :
    p = ((p 0 : ℤ) : Fin 2 → ℤ) * Pi.single 0 1 + ((p 1 : ℤ) : Fin 2 → ℤ) * Pi.single 1 1 := by
  ext j
  fin_cases j <;> simp [Pi.intCast_apply]

private lemma algHom_pi2_int_eq_eval (ε : (Fin 2 → ℤ) →ₐ[ℤ] ℤ) :
    ∃ i₀ i₁ : Fin 2, i₀ ≠ i₁ ∧ ε = Pi.evalAlgHom ℤ (fun _ => ℤ) i₀ := by
  set a := ε (Pi.single 0 1) with ha
  set b := ε (Pi.single 1 1) with hb
  have hab : a * b = 0 := by
    rw [ha, hb, ← map_mul, single_mul_single (by omega), map_zero]
  have hsum : a + b = 1 := by
    rw [ha, hb, ← map_add, single_add_single (by omega), map_one]
  have haa : a * a = a := by
    have : a * (a + b) = a * 1 := by rw [hsum]
    rw [mul_add, hab, add_zero, mul_one] at this
    exact this
  have key : ∀ i₀ i₁ : Fin 2, i₀ ≠ i₁ → ε (Pi.single i₀ 1) = 1 → ε (Pi.single i₁ 1) = 0 →
      ε = Pi.evalAlgHom ℤ (fun _ => ℤ) i₀ := by
    intro i₀ i₁ hne h1 h0
    ext p
    conv_lhs => rw [pi_decomp p i₀ i₁ hne]
    rw [map_add, map_zsmul, map_zsmul, h1, h0]
    simp [Pi.evalAlgHom_apply]
  rcases int_idem haa with h | h
  · refine ⟨1, 0, by omega, key 1 0 (by omega) ?_ ?_⟩
    · omega
    · rw [← ha]; omega
  · refine ⟨0, 1, by omega, key 0 1 (by omega) ?_ ?_⟩
    · rw [← ha]; omega
    · omega

private def pi2Hom (i₀ i₁ : Fin 2) {R : Type} [CommRing R] (x : R) (hx : IsIdempotentElem x) :
    (Fin 2 → ℤ) →ₐ[ℤ] R :=
  RingHom.toIntAlgHom
  { toFun := fun p => (p i₀ : R) * (1 - x) + (p i₁ : R) * x
    map_one' := by simp only [Pi.one_apply]; push_cast; ring
    map_mul' := fun p q => by
      have hx' : x * x = x := hx
      simp only [Pi.mul_apply]
      push_cast
      linear_combination ((p i₀ : R) - p i₁) * ((q i₁ : R) - q i₀) * hx'
    map_zero' := by simp only [Pi.zero_apply]; push_cast; ring
    map_add' := fun p q => by simp only [Pi.add_apply]; push_cast; ring }

private lemma pi2Hom_apply (i₀ i₁ : Fin 2) {R : Type} [CommRing R] (x : R) (hx : IsIdempotentElem x)
    (p : Fin 2 → ℤ) : pi2Hom i₀ i₁ x hx p = (p i₀ : R) * (1 - x) + (p i₁ : R) * x := rfl

section Transport

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K]

attribute [local instance 10000] Algebra.toModule

private noncomputable def sVec (f : K ≃ₐ[ℤ] (Fin 2 → ℤ)) (a : Fin 2) : K :=
  f.symm (Pi.single a 1)

private lemma single_sq (j : Fin 2) :
    (Pi.single j 1 : Fin 2 → ℤ) * Pi.single j 1 = Pi.single j 1 := by
  ext k
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

private lemma sVec_sq (f : K ≃ₐ[ℤ] (Fin 2 → ℤ)) (a : Fin 2) :
    sVec f a * sVec f a = sVec f a := by
  rw [sVec, ← map_mul, single_sq]

private lemma sVec_orth (f : K ≃ₐ[ℤ] (Fin 2 → ℤ)) {a b : Fin 2} (hab : a ≠ b) :
    sVec f a * sVec f b = 0 := by
  rw [sVec, sVec, ← map_mul, single_mul_single hab, map_zero]

private lemma f_sVec (f : K ≃ₐ[ℤ] (Fin 2 → ℤ)) (a : Fin 2) :
    f (sVec f a) = Pi.single a 1 := by
  rw [sVec, AlgEquiv.apply_symm_apply]

private lemma gen_decomp (f : K ≃ₐ[ℤ] (Fin 2 → ℤ)) (x : K) :
    x = algebraMap ℤ K (f x 0) * sVec f 0 + algebraMap ℤ K (f x 1) * sVec f 1 := by
  apply f.injective
  rw [map_add, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, f_sVec, f_sVec]
  ext j
  fin_cases j <;>
    simp [Pi.intCast_apply]

private lemma tmul_intCast_mul (k : K) (c : ℤ) (x : Fin 2 → ℤ) :
    k ⊗ₜ[ℤ] (((c : ℤ) : Fin 2 → ℤ) * x) = (algebraMap ℤ K c * k) ⊗ₜ[ℤ] x := by
  have h1 : ((c : ℤ) : Fin 2 → ℤ) = algebraMap ℤ (Fin 2 → ℤ) c :=
    (eq_intCast (algebraMap ℤ (Fin 2 → ℤ)) c).symm
  calc k ⊗ₜ[ℤ] (((c : ℤ) : Fin 2 → ℤ) * x)
      = ((1 : K) ⊗ₜ[ℤ] ((c : ℤ) : Fin 2 → ℤ)) * (k ⊗ₜ[ℤ] x) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    _ = algebraMap ℤ (K ⊗[ℤ] (Fin 2 → ℤ)) c * (k ⊗ₜ[ℤ] x) := by
        rw [h1, ← Algebra.TensorProduct.includeRight_apply, AlgHom.commutes]
    _ = (algebraMap ℤ K c ⊗ₜ[ℤ] (1 : Fin 2 → ℤ)) * (k ⊗ₜ[ℤ] x) := by
        rw [Algebra.TensorProduct.algebraMap_apply]
    _ = (algebraMap ℤ K c * k) ⊗ₜ[ℤ] x := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private lemma exists_two_term (w : K ⊗[ℤ] (Fin 2 → ℤ)) :
    ∃ y₀ y₁ : K, w = y₀ ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) + y₁ ⊗ₜ[ℤ] Pi.single 1 1 := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul k p =>
    refine ⟨algebraMap ℤ K (p 0) * k, algebraMap ℤ K (p 1) * k, ?_⟩
    conv_lhs => rw [pi_decomp_mul p]
    rw [TensorProduct.tmul_add, tmul_intCast_mul, tmul_intCast_mul]
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨a₀, a₁, ha⟩ := h₁
    obtain ⟨b₀, b₁, hb⟩ := h₂
    exact ⟨a₀ + b₀, a₁ + b₁, by
      rw [ha, hb, TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩

private theorem exists_conv_idem (f : K ≃ₐ[ℤ] (Fin 2 → ℤ)) :
    ∃ u : K, IsIdempotentElem u ∧
      ∀ (R : Type) [CommRing R],
        (∀ φ ψ : WithConv (K →ₐ[ℤ] R),
          (φ * ψ) u = φ.ofConv u + ψ.ofConv u - 2 * (φ.ofConv u * ψ.ofConv u)) ∧
        ((1 : WithConv (K →ₐ[ℤ] R)) u = 0) ∧
        (∀ φ : K →ₐ[ℤ] R, IsIdempotentElem (φ u)) ∧
        (∀ φ ψ : K →ₐ[ℤ] R, φ u = ψ u → φ = ψ) ∧
        (∀ x : R, IsIdempotentElem x → ∃ φ : K →ₐ[ℤ] R, φ u = x) := by
  classical
  obtain ⟨i₀, i₁, hne, hε⟩ :=
    algHom_pi2_int_eq_eval ((counitAlgHom ℤ K).comp f.symm.toAlgHom)
  have hεap : ∀ p : Fin 2 → ℤ, counitAlgHom ℤ K (f.symm p) = p i₀ := by
    intro p
    have h := congrArg (fun g : (Fin 2 → ℤ) →ₐ[ℤ] ℤ => g p) hε
    simpa using h
  have hcompl : sVec f i₀ = 1 - sVec f i₁ := by
    rw [eq_sub_iff_add_eq, sVec, sVec, ← map_add, single_add_single hne, map_one]
  have hcu : counitAlgHom ℤ K (sVec f i₁) = 0 := by
    rw [sVec, hεap]
    exact Pi.single_eq_of_ne hne 1
  have hcu' : Coalgebra.counit (R := ℤ) (sVec f i₁) = (0 : ℤ) := hcu

  have hΔ : Bialgebra.comulAlgHom ℤ K (sVec f i₁)
      = sVec f i₁ ⊗ₜ[ℤ] (1 - sVec f i₁) + (1 - sVec f i₁) ⊗ₜ[ℤ] sVec f i₁ := by
    obtain ⟨y₀, y₁, hw⟩ := exists_two_term
      (LinearMap.lTensor K f.toLinearMap (Bialgebra.comulAlgHom ℤ K (sVec f i₁)))
    have hz : Bialgebra.comulAlgHom ℤ K (sVec f i₁)
        = y₀ ⊗ₜ[ℤ] sVec f 0 + y₁ ⊗ₜ[ℤ] sVec f 1 := by
      have h2 : f.symm.toLinearMap ∘ₗ f.toLinearMap = (LinearMap.id : K →ₗ[ℤ] K) := by
        ext k; simp
      have h1 := congrArg (LinearMap.lTensor K f.symm.toLinearMap) hw
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h2, LinearMap.lTensor_id,
        LinearMap.id_apply] at h1
      rw [h1, map_add, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
      simp only [AlgEquiv.toLinearMap_apply, sVec]

    have hone_mul := congrArg
      (fun θ : WithConv (K →ₐ[ℤ] K) => θ.ofConv (sVec f i₁))
      (one_mul (WithConv.toConv (AlgHom.id ℤ K)))
    have hmul_one := congrArg
      (fun θ : WithConv (K →ₐ[ℤ] K) => θ.ofConv (sVec f i₁))
      (mul_one (WithConv.toConv (AlgHom.id ℤ K)))
    simp only [AlgHom.convMul_apply] at hone_mul hmul_one
    rw [← Bialgebra.comulAlgHom_apply, hz] at hone_mul hmul_one
    simp only [map_add, Algebra.TensorProduct.lift_tmul, AlgHom.convOne_def,
      WithConv.ofConv_toConv, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply,
      Algebra.ofId_apply] at hone_mul hmul_one
    have hcs : ∀ b : Fin 2, counitAlgHom ℤ K (sVec f b) = (Pi.single b 1 : Fin 2 → ℤ) i₀ := by
      intro b; rw [sVec, hεap]
    rw [hcs, hcs] at hmul_one

    have hsq0 : Bialgebra.comulAlgHom ℤ K (sVec f i₁) * Bialgebra.comulAlgHom ℤ K (sVec f i₁)
        = Bialgebra.comulAlgHom ℤ K (sVec f i₁) := by
      rw [← map_mul, sVec_sq]
    have h01 : sVec f 0 * sVec f 1 = 0 := sVec_orth f (by omega)
    have h10 : sVec f 1 * sVec f 0 = 0 := sVec_orth f (by omega)
    rw [hz, add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, sVec_sq, sVec_sq, h01, h10,
      TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero, zero_add] at hsq0

    rcases (by omega : i₀ = 0 ∧ i₁ = 1 ∨ i₀ = 1 ∧ i₁ = 0) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · subst h0; subst h1
      have hs00 : (Pi.single 0 1 : Fin 2 → ℤ) 0 = 1 := Pi.single_eq_same _ _
      have hs10 : (Pi.single 1 1 : Fin 2 → ℤ) 0 = 0 := Pi.single_eq_of_ne (by decide) _
      have hs01 : (Pi.single 0 1 : Fin 2 → ℤ) 1 = 0 := Pi.single_eq_of_ne (by decide) _
      have hs11 : (Pi.single 1 1 : Fin 2 → ℤ) 1 = 1 := Pi.single_eq_same _ _
      rw [hs00, hs10, map_one, map_zero, mul_one, mul_zero, add_zero] at hmul_one

      have h1c := congrArg (fun k => f k 1) hone_mul
      simp only [map_add, map_mul, AlgEquiv.commutes, f_sVec, Pi.add_apply, Pi.mul_apply,
        hs01, hs11, mul_zero, mul_one, zero_add] at h1c

      have hy1sq := congrArg (fun t => (TensorProduct.rid ℤ K)
        ((LinearMap.lTensor K ((Pi.evalAlgHom ℤ (fun _ => ℤ) 1).toLinearMap))
          ((LinearMap.lTensor K f.toLinearMap) t))) hsq0
      simp only [map_add, LinearMap.lTensor_tmul, AlgEquiv.toLinearMap_apply,
        AlgHom.toLinearMap_apply, f_sVec, Pi.evalAlgHom_apply, hs01, hs11,
        TensorProduct.rid_tmul] at hy1sq

      have hfy10 : f y₁ 0 = 1 := by
        rw [← hεap (f y₁), f.symm_apply_apply]
        exact h1c
      have hcsq : f y₁ 1 * f y₁ 1 = f y₁ 1 := by
        have h := congrArg (fun w => f w 1) hy1sq
        simpa [map_mul] using h
      rcases int_idem hcsq with hc | hc
      · have hfy1 : f y₁ = Pi.single 0 1 := by
          ext j; fin_cases j
          · simpa using hfy10
          · simpa [Pi.single_apply] using hc
        have hy1 : y₁ = sVec f 0 := by
          rw [sVec, ← hfy1, f.symm_apply_apply]
        rw [hz, hmul_one, hy1, hcompl]
      · exfalso
        have hfy1 : f y₁ = 1 := by
          ext j; fin_cases j
          · simpa using hfy10
          · simpa using hc
        have hy1 : y₁ = 1 := by
          have h := congrArg f.symm hfy1
          rwa [f.symm_apply_apply, map_one] at h
        have hA3 := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := ℤ) (A := K) (sVec f 1)
        rw [← Bialgebra.comulAlgHom_apply, hz, hcu', hmul_one, hy1] at hA3
        simp only [map_add, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
          HopfAlgebra.antipode_one, one_mul, map_zero] at hA3

        have h3c := congrArg (fun k => f k 1) hA3
        simp only [map_add, map_mul, map_zero, f_sVec, Pi.add_apply, Pi.mul_apply,
          Pi.zero_apply, hs01, hs11, mul_zero, zero_add] at h3c
        exact one_ne_zero h3c
    · subst h0; subst h1
      have hs00 : (Pi.single 0 1 : Fin 2 → ℤ) 0 = 1 := Pi.single_eq_same _ _
      have hs10 : (Pi.single 1 1 : Fin 2 → ℤ) 0 = 0 := Pi.single_eq_of_ne (by decide) _
      have hs01 : (Pi.single 0 1 : Fin 2 → ℤ) 1 = 0 := Pi.single_eq_of_ne (by decide) _
      have hs11 : (Pi.single 1 1 : Fin 2 → ℤ) 1 = 1 := Pi.single_eq_same _ _
      rw [hs01, hs11, map_one, map_zero, mul_one, mul_zero, zero_add] at hmul_one

      have h0c := congrArg (fun k => f k 0) hone_mul
      simp only [map_add, map_mul, AlgEquiv.commutes, f_sVec, Pi.add_apply, Pi.mul_apply,
        hs00, hs10, mul_zero, mul_one, add_zero] at h0c

      have hy0sq := congrArg (fun t => (TensorProduct.rid ℤ K)
        ((LinearMap.lTensor K ((Pi.evalAlgHom ℤ (fun _ => ℤ) 0).toLinearMap))
          ((LinearMap.lTensor K f.toLinearMap) t))) hsq0
      simp only [map_add, LinearMap.lTensor_tmul, AlgEquiv.toLinearMap_apply,
        AlgHom.toLinearMap_apply, f_sVec, Pi.evalAlgHom_apply, hs00, hs10,
        TensorProduct.rid_tmul] at hy0sq

      have hfy01 : f y₀ 1 = 1 := by
        rw [← hεap (f y₀), f.symm_apply_apply]
        exact h0c
      have hcsq : f y₀ 0 * f y₀ 0 = f y₀ 0 := by
        have h := congrArg (fun w => f w 0) hy0sq
        simpa [map_mul] using h
      rcases int_idem hcsq with hc | hc
      · have hfy0 : f y₀ = Pi.single 1 1 := by
          ext j; fin_cases j
          · simpa [Pi.single_apply] using hc
          · simpa [Pi.single_apply] using hfy01
        have hy0 : y₀ = sVec f 1 := by
          rw [sVec, ← hfy0, f.symm_apply_apply]
        rw [hz, hmul_one, hy0, hcompl, add_comm]
      · exfalso
        have hfy0 : f y₀ = 1 := by
          ext j; fin_cases j
          · simpa using hc
          · simpa using hfy01
        have hy0 : y₀ = 1 := by
          have h := congrArg f.symm hfy0
          rwa [f.symm_apply_apply, map_one] at h
        have hA3 := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := ℤ) (A := K) (sVec f 0)
        rw [← Bialgebra.comulAlgHom_apply, hz, hcu', hmul_one, hy0] at hA3
        simp only [map_add, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
          HopfAlgebra.antipode_one, one_mul, map_zero] at hA3

        have h3c := congrArg (fun k => f k 0) hA3
        simp only [map_add, map_mul, map_zero, f_sVec, Pi.add_apply, Pi.mul_apply,
          Pi.zero_apply, hs00, hs10, mul_zero, add_zero] at h3c
        exact one_ne_zero h3c

  refine ⟨sVec f i₁, sVec_sq f i₁, fun R instR => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro φ ψ
    rw [AlgHom.convMul_apply, ← Bialgebra.comulAlgHom_apply, hΔ]
    simp only [map_add, Algebra.TensorProduct.lift_tmul, map_sub, map_one]
    ring
  · rw [AlgHom.convOne_apply, hcu', map_zero]
  · intro φ
    show φ (sVec f i₁) * φ (sVec f i₁) = φ (sVec f i₁)
    rw [← map_mul, sVec_sq]
  · intro φ ψ h
    have hφs : ∀ j : Fin 2, φ (sVec f j) = ψ (sVec f j) := by
      intro j
      rcases (by omega : j = i₀ ∨ j = i₁) with rfl | rfl
      · rw [hcompl, map_sub, map_sub, map_one, map_one, h]
      · exact h
    ext k
    rw [gen_decomp f k]
    simp only [map_add, map_mul, AlgHom.commutes, hφs]
  · intro x hx
    refine ⟨(pi2Hom i₀ i₁ x hx).comp f.toAlgHom, ?_⟩
    have hfu : (f : K →ₐ[ℤ] (Fin 2 → ℤ)) (sVec f i₁) = Pi.single i₁ 1 := f_sVec f i₁
    rw [AlgHom.comp_apply, hfu, pi2Hom_apply]
    simp only [Pi.single_eq_of_ne hne, Pi.single_eq_same, Int.cast_zero, Int.cast_one,
      zero_mul, one_mul, zero_add]

end Transport

end HopfPiTwo

end

section
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace Opposite

namespace IdemClopen

local instance instTopZMod (n : ℕ) : TopologicalSpace (ZMod n) := ⊥

local instance (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩

private theorem zmod_two_cases : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide

private theorem zmod_two_one_add_one : (1 + 1 : ZMod 2) = 0 := by decide

private theorem eq_one_of_isUnit {R : Type*} [Monoid R] {a : R} (ha : IsIdempotentElem a)
    (hu : IsUnit a) : a = 1 :=
  hu.mul_left_cancel (ha.eq.trans (mul_one a).symm)

private theorem eq_zero_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {a : R}
    (ha : IsIdempotentElem a) (hu : ¬ IsUnit a) : a = 0 := by
  have h1 : IsUnit (1 - a) := (IsLocalRing.isUnit_or_isUnit_one_sub_self a).resolve_left hu
  have h2 : (1 - a) * a = 0 := by rw [sub_mul, one_mul, ha.eq, sub_self]
  exact h1.mul_right_eq_zero.mp h2

private theorem not_isUnit_iff_isUnit_one_sub {R : Type*} [CommRing R] [IsLocalRing R] {a : R}
    (ha : IsIdempotentElem a) : ¬ IsUnit a ↔ IsUnit (1 - a) := by
  refine ⟨fun hu => (IsLocalRing.isUnit_or_isUnit_one_sub_self a).resolve_left hu, fun h1 hu => ?_⟩
  have : (1 : R) - a = 0 := by rw [eq_one_of_isUnit ha hu, sub_self]
  exact not_isUnit_zero (this ▸ h1)

variable (T : Scheme.{u})

private def piece (χ : C(↥T, ZMod 2)) (i : ZMod 2) : T.Opens :=
  ⟨χ ⁻¹' {i}, (isOpen_discrete {i}).preimage χ.continuous⟩

private theorem mem_piece {χ : C(↥T, ZMod 2)} {i : ZMod 2} {x : ↥T} : x ∈ piece T χ i ↔ χ x = i :=
  Iff.rfl

private theorem top_le_iSup_piece (χ : C(↥T, ZMod 2)) : (⊤ : T.Opens) ≤ ⨆ i, piece T χ i :=
  fun x _ => Opens.mem_iSup.mpr ⟨χ x, (mem_piece T).mpr rfl⟩

private def localVal (χ : C(↥T, ZMod 2)) (i : ZMod 2) : Γ(T, piece T χ i) := ((i.val : ℕ) : Γ(T, piece T χ i))

private theorem isCompatible_localVal (χ : C(↥T, ZMod 2)) :
    TopCat.Presheaf.IsCompatible T.presheaf (piece T χ) (localVal T χ) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rfl
  · apply TopCat.Presheaf.section_ext T.sheaf
    intro x hx
    exact absurd (((mem_piece T).mp hx.1).symm.trans ((mem_piece T).mp hx.2)) hij

private theorem existsUnique_idemOf (χ : C(↥T, ZMod 2)) :
    ∃! s : Γ(T, ⊤), ∀ i : ZMod 2,
      T.presheaf.map (homOfLE le_top : piece T χ i ⟶ ⊤).op s = localVal T χ i :=
  T.sheaf.existsUnique_gluing' (piece T χ) ⊤ (fun _ => homOfLE le_top) (top_le_iSup_piece T χ)
    (localVal T χ) (isCompatible_localVal T χ)

private noncomputable def idemOf (χ : C(↥T, ZMod 2)) : Γ(T, ⊤) :=
  (existsUnique_idemOf T χ).exists.choose

private theorem idemOf_spec (χ : C(↥T, ZMod 2)) (i : ZMod 2) :
    T.presheaf.map (homOfLE le_top : piece T χ i ⟶ ⊤).op (idemOf T χ) = localVal T χ i :=
  (existsUnique_idemOf T χ).exists.choose_spec i

private theorem germ_idemOf (χ : C(↥T, ZMod 2)) (x : ↥T) :
    T.presheaf.germ ⊤ x trivial (idemOf T χ) = (((χ x).val : ℕ) : T.presheaf.stalk x) := by
  have hx : x ∈ piece T χ (χ x) := (mem_piece T).mpr rfl
  have h := TopCat.Presheaf.germ_res_apply T.presheaf
    (homOfLE le_top : piece T χ (χ x) ⟶ ⊤) x hx (idemOf T χ)
  rw [idemOf_spec] at h
  exact h.symm.trans (map_natCast _ _)

private theorem germ_idemOf_of_eq_zero (χ : C(↥T, ZMod 2)) (x : ↥T) (h : χ x = 0) :
    T.presheaf.germ ⊤ x trivial (idemOf T χ) = 0 := by
  rw [germ_idemOf, h, ZMod.val_zero, Nat.cast_zero]

private theorem germ_idemOf_of_eq_one (χ : C(↥T, ZMod 2)) (x : ↥T) (h : χ x = 1) :
    T.presheaf.germ ⊤ x trivial (idemOf T χ) = 1 := by
  rw [germ_idemOf, h, ZMod.val_one, Nat.cast_one]

private theorem isIdempotentElem_idemOf (χ : C(↥T, ZMod 2)) : IsIdempotentElem (idemOf T χ) := by
  apply TopCat.Presheaf.section_ext T.sheaf
  intro x hx
  change T.presheaf.germ ⊤ x hx (idemOf T χ * idemOf T χ) = T.presheaf.germ ⊤ x hx (idemOf T χ)
  rw [map_mul]
  rcases zmod_two_cases (χ x) with h | h
  · rw [germ_idemOf_of_eq_zero T χ x h, mul_zero]
  · rw [germ_idemOf_of_eq_one T χ x h, mul_one]

private theorem idemOf_add (χ χ' : C(↥T, ZMod 2)) :
    idemOf T (χ + χ') = idemOf T χ + idemOf T χ' - 2 * (idemOf T χ * idemOf T χ') := by
  apply TopCat.Presheaf.section_ext T.sheaf
  intro x hx
  change T.presheaf.germ ⊤ x hx (idemOf T (χ + χ')) =
    T.presheaf.germ ⊤ x hx (idemOf T χ + idemOf T χ' - 2 * (idemOf T χ * idemOf T χ'))
  rw [map_sub, map_add, map_mul, map_mul, map_ofNat]
  have hadd : (χ + χ') x = χ x + χ' x := rfl
  rcases zmod_two_cases (χ x) with h | h <;> rcases zmod_two_cases (χ' x) with h' | h'
  · rw [germ_idemOf_of_eq_zero T χ x h, germ_idemOf_of_eq_zero T χ' x h',
      germ_idemOf_of_eq_zero T (χ + χ') x (by rw [hadd, h, h', add_zero])]
    ring
  · rw [germ_idemOf_of_eq_zero T χ x h, germ_idemOf_of_eq_one T χ' x h',
      germ_idemOf_of_eq_one T (χ + χ') x (by rw [hadd, h, h', zero_add])]
    ring
  · rw [germ_idemOf_of_eq_one T χ x h, germ_idemOf_of_eq_zero T χ' x h',
      germ_idemOf_of_eq_one T (χ + χ') x (by rw [hadd, h, h', add_zero])]
    ring
  · rw [germ_idemOf_of_eq_one T χ x h, germ_idemOf_of_eq_one T χ' x h',
      germ_idemOf_of_eq_zero T (χ + χ') x (by rw [hadd, h, h', zmod_two_one_add_one])]
    ring

private theorem idemOf_zero : idemOf T 0 = 0 := by
  apply TopCat.Presheaf.section_ext T.sheaf
  intro x hx
  change T.presheaf.germ ⊤ x hx (idemOf T 0) = T.presheaf.germ ⊤ x hx 0
  rw [map_zero, germ_idemOf_of_eq_zero T 0 x rfl]

private theorem compl_basicOpen_eq {e : Γ(T, ⊤)} (he : IsIdempotentElem e) :
    (T.basicOpen e : Set ↥T)ᶜ = (T.basicOpen (1 - e) : Set ↥T) := by
  ext x
  rw [Set.mem_compl_iff, SetLike.mem_coe, SetLike.mem_coe, Scheme.mem_basicOpen_top,
    Scheme.mem_basicOpen_top, map_sub, map_one]
  exact not_isUnit_iff_isUnit_one_sub (he.map (T.presheaf.germ ⊤ x trivial).hom)

open Classical in

private noncomputable def indFun (e : Γ(T, ⊤)) : ↥T → ZMod 2 := fun x => if x ∈ T.basicOpen e then 1 else 0

private theorem indFun_eq_one_iff (e : Γ(T, ⊤)) (x : ↥T) : indFun T e x = 1 ↔ x ∈ T.basicOpen e := by
  unfold indFun
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h01 => absurd h01 zero_ne_one, fun hx => absurd hx h⟩

private theorem indFun_eq_zero_iff (e : Γ(T, ⊤)) (x : ↥T) : indFun T e x = 0 ↔ x ∉ T.basicOpen e := by
  unfold indFun
  split_ifs with h
  · exact ⟨fun h10 => absurd h10 one_ne_zero, fun hx => absurd h hx⟩
  · exact ⟨fun _ => h, fun _ => rfl⟩

private theorem continuous_indFun {e : Γ(T, ⊤)} (he : IsIdempotentElem e) : Continuous (indFun T e) := by
  rw [continuous_discrete_rng]
  intro b
  rcases zmod_two_cases b with rfl | rfl
  · have : indFun T e ⁻¹' {0} = (T.basicOpen (1 - e) : Set ↥T) := by
      rw [← compl_basicOpen_eq T he]
      ext x
      exact indFun_eq_zero_iff T e x
    rw [this]
    exact (T.basicOpen (1 - e)).isOpen
  · have : indFun T e ⁻¹' {1} = (T.basicOpen e : Set ↥T) := by
      ext x
      exact indFun_eq_one_iff T e x
    rw [this]
    exact (T.basicOpen e).isOpen

private noncomputable def ind (e : Γ(T, ⊤)) (he : IsIdempotentElem e) : C(↥T, ZMod 2) :=
  ⟨indFun T e, continuous_indFun T he⟩

private theorem ind_apply (e : Γ(T, ⊤)) (he : IsIdempotentElem e) (x : ↥T) : ind T e he x = indFun T e x :=
  rfl

private theorem ind_idemOf (χ : C(↥T, ZMod 2)) : ind T (idemOf T χ) (isIdempotentElem_idemOf T χ) = χ := by
  ext x
  rw [ind_apply]
  rcases zmod_two_cases (χ x) with h | h
  · rw [h, indFun_eq_zero_iff, Scheme.mem_basicOpen_top, germ_idemOf_of_eq_zero T χ x h]
    exact not_isUnit_zero
  · rw [h, indFun_eq_one_iff, Scheme.mem_basicOpen_top, germ_idemOf_of_eq_one T χ x h]
    exact isUnit_one

private theorem idemOf_ind (e : Γ(T, ⊤)) (he : IsIdempotentElem e) : idemOf T (ind T e he) = e := by
  apply TopCat.Presheaf.section_ext T.sheaf
  intro x hx
  change T.presheaf.germ ⊤ x hx (idemOf T (ind T e he)) = T.presheaf.germ ⊤ x hx e
  have hex : IsIdempotentElem (T.presheaf.germ ⊤ x hx e) := he.map (T.presheaf.germ ⊤ x hx).hom
  by_cases hu : IsUnit (T.presheaf.germ ⊤ x hx e)
  · rw [eq_one_of_isUnit hex hu]
    exact germ_idemOf_of_eq_one T _ x
      ((indFun_eq_one_iff T e x).mpr ((Scheme.mem_basicOpen_top T e x).mpr hu))
  · rw [eq_zero_of_not_isUnit hex hu]
    exact germ_idemOf_of_eq_zero T _ x
      ((indFun_eq_zero_iff T e x).mpr (fun hm => hu ((Scheme.mem_basicOpen_top T e x).mp hm)))

private noncomputable def idemEquiv : C(↥T, ZMod 2) ≃ {e : Γ(T, ⊤) // IsIdempotentElem e} where
  toFun χ := ⟨idemOf T χ, isIdempotentElem_idemOf T χ⟩
  invFun e := ind T e.1 e.2
  left_inv χ := ind_idemOf T χ
  right_inv e := Subtype.ext (idemOf_ind T e.1 e.2)

private theorem idemOf_comp {T T' : Scheme.{u}} (g : T ⟶ T') (χ : C(↥T', ZMod 2)) :
    idemOf T (χ.comp g.base.hom) = g.appTop (idemOf T' χ) := by
  apply TopCat.Presheaf.section_ext T.sheaf
  intro x hx
  change T.presheaf.germ ⊤ x hx (idemOf T (χ.comp g.base.hom)) =
    T.presheaf.germ ⊤ x hx (g.appTop (idemOf T' χ))
  have h2 : T.presheaf.germ ⊤ x hx (g.appTop (idemOf T' χ)) =
      g.stalkMap x (T'.presheaf.germ ⊤ (g x) trivial (idemOf T' χ)) :=
    (Scheme.Hom.germ_stalkMap_apply g ⊤ x trivial (idemOf T' χ)).symm
  rw [h2, germ_idemOf, germ_idemOf, map_natCast]
  rfl

end IdemClopen

namespace SectionsAssembly

open IdemClopen

local instance : TopologicalSpace (ZMod 2) := ⊥

local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K] (u : K) (T : Scheme.{0})

private noncomputable def pt
    (hsurj : ∀ x : Γ(T, ⊤), IsIdempotentElem x → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x)
    (χ : C(↥T, ZMod 2)) : K →ₐ[ℤ] Γ(T, ⊤) :=
  Classical.choose (hsurj (idemOf T χ) (isIdempotentElem_idemOf T χ))

private theorem pt_apply_u
    (hsurj : ∀ x : Γ(T, ⊤), IsIdempotentElem x → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x)
    (χ : C(↥T, ZMod 2)) : pt u T hsurj χ u = idemOf T χ :=
  Classical.choose_spec (hsurj (idemOf T χ) (isIdempotentElem_idemOf T χ))

private noncomputable def ptEquiv
    (hidem : ∀ φ : K →ₐ[ℤ] Γ(T, ⊤), IsIdempotentElem (φ u))
    (hinj : ∀ φ ψ : K →ₐ[ℤ] Γ(T, ⊤), φ u = ψ u → φ = ψ)
    (hsurj : ∀ x : Γ(T, ⊤), IsIdempotentElem x → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x) :
    C(↥T, ZMod 2) ≃ (K →ₐ[ℤ] Γ(T, ⊤)) where
  toFun := pt u T hsurj
  invFun φ := ind T (φ u) (hidem φ)
  left_inv χ := by
    have key : ∀ (e : Γ(T, ⊤)) (he : IsIdempotentElem e), e = idemOf T χ → ind T e he = χ := by
      rintro e he rfl
      exact ind_idemOf T χ
    exact key _ _ (pt_apply_u u T hsurj χ)
  right_inv φ := hinj _ _ (by rw [pt_apply_u, idemOf_ind])

private noncomputable def secEquiv
    (hmul : ∀ φ ψ : WithConv (K →ₐ[ℤ] Γ(T, ⊤)),
      (φ * ψ) u = φ.ofConv u + ψ.ofConv u - 2 * (φ.ofConv u * ψ.ofConv u))
    (hidem : ∀ φ : K →ₐ[ℤ] Γ(T, ⊤), IsIdempotentElem (φ u))
    (hinj : ∀ φ ψ : K →ₐ[ℤ] Γ(T, ⊤), φ u = ψ u → φ = ψ)
    (hsurj : ∀ x : Γ(T, ⊤), IsIdempotentElem x → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x) :
    ((FppfKummerSES.sheafULift.{0}.obj
        (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj (Opposite.op T)) ≃+
      Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))) where
  toFun s := Additive.ofMul (WithConv.toConv (pt u T hsurj s.down))
  invFun x := ULift.up (ind T ((Additive.toMul x).ofConv u) (hidem _))
  left_inv s := by
    apply ULift.ext
    show ind T (pt u T hsurj s.down u) (hidem _) = s.down
    have key : ∀ (e : Γ(T, ⊤)) (he : IsIdempotentElem e), e = idemOf T s.down →
        ind T e he = s.down := by
      rintro e he rfl
      exact ind_idemOf T s.down
    exact key _ _ (pt_apply_u u T hsurj s.down)
  right_inv x := by
    have hx : pt u T hsurj (ind T ((Additive.toMul x).ofConv u) (hidem _)) =
        (Additive.toMul x).ofConv :=
      hinj _ _ (by rw [pt_apply_u, idemOf_ind])
    show Additive.ofMul (WithConv.toConv
      (pt u T hsurj (ind T ((Additive.toMul x).ofConv u) (hidem _)))) = x
    rw [hx]
    rfl
  map_add' s s' := by
    show Additive.ofMul (WithConv.toConv (pt u T hsurj (s + s').down)) =
      Additive.ofMul (WithConv.toConv (pt u T hsurj s.down)) +
        Additive.ofMul (WithConv.toConv (pt u T hsurj s'.down))
    rw [← ofMul_mul]
    apply congrArg Additive.ofMul
    apply WithConv.ext
    show pt u T hsurj (s.down + s'.down) =
      (WithConv.toConv (pt u T hsurj s.down) * WithConv.toConv (pt u T hsurj s'.down)).ofConv
    apply hinj
    rw [pt_apply_u]
    refine (idemOf_add T s.down s'.down).trans ?_
    have h := hmul (WithConv.toConv (pt u T hsurj s.down)) (WithConv.toConv (pt u T hsurj s'.down))
    change (WithConv.toConv (pt u T hsurj s.down) *
        WithConv.toConv (pt u T hsurj s'.down)).ofConv u =
      pt u T hsurj s.down u + pt u T hsurj s'.down u -
        2 * (pt u T hsurj s.down u * pt u T hsurj s'.down u) at h
    rw [pt_apply_u, pt_apply_u] at h
    exact h.symm

private theorem secEquiv_apply
    (hmul : ∀ φ ψ : WithConv (K →ₐ[ℤ] Γ(T, ⊤)),
      (φ * ψ) u = φ.ofConv u + ψ.ofConv u - 2 * (φ.ofConv u * ψ.ofConv u))
    (hidem : ∀ φ : K →ₐ[ℤ] Γ(T, ⊤), IsIdempotentElem (φ u))
    (hinj : ∀ φ ψ : K →ₐ[ℤ] Γ(T, ⊤), φ u = ψ u → φ = ψ)
    (hsurj : ∀ x : Γ(T, ⊤), IsIdempotentElem x → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x)
    (s : (FppfKummerSES.sheafULift.{0}.obj
        (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj (Opposite.op T))
    (k : K) :
    (Additive.toMul (secEquiv u T hmul hidem hinj hsurj s)) k = pt u T hsurj s.down k :=
  rfl

variable {T}

private theorem pt_comp {T T' : Scheme.{0}} (g : T ⟶ T')
    (hinj : ∀ φ ψ : K →ₐ[ℤ] Γ(T, ⊤), φ u = ψ u → φ = ψ)
    (hsurj : ∀ x : Γ(T, ⊤), IsIdempotentElem x → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x)
    (hsurj' : ∀ x : Γ(T', ⊤), IsIdempotentElem x → ∃ φ : K →ₐ[ℤ] Γ(T', ⊤), φ u = x)
    (χ : C(↥T', ZMod 2)) :
    pt u T hsurj (χ.comp g.base.hom) =
      ((Scheme.Γ.map g.op).hom.toIntAlgHom).comp (pt u T' hsurj' χ) := by
  apply hinj
  rw [pt_apply_u, idemOf_comp]
  show g.appTop (idemOf T' χ) = (Scheme.Γ.map g.op).hom (pt u T' hsurj' χ u)
  rw [pt_apply_u]
  rfl

variable (K)

private theorem exists_sectionsEquiv_of_conv
    (H : ∀ (R : Type) [CommRing R],
      (∀ φ ψ : WithConv (K →ₐ[ℤ] R),
        (φ * ψ) u = φ.ofConv u + ψ.ofConv u - 2 * (φ.ofConv u * ψ.ofConv u)) ∧
      ((1 : WithConv (K →ₐ[ℤ] R)) u = 0) ∧
      (∀ φ : K →ₐ[ℤ] R, IsIdempotentElem (φ u)) ∧
      (∀ φ ψ : K →ₐ[ℤ] R, φ u = ψ u → φ = ψ) ∧
      (∀ x : R, IsIdempotentElem x → ∃ φ : K →ₐ[ℤ] R, φ u = x)) :
    ∃ e : ∀ T : Scheme.{0},
      ((FppfKummerSES.sheafULift.{0}.obj
          (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj
        (Opposite.op T)) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))),
      ∀ {T T' : Scheme.{0}} (g : T ⟶ T')
        (s : (FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj
          (Opposite.op T')) (k : K),
        (Additive.toMul (e T ((FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.map g.op s))) k
          = (Scheme.Γ.map g.op) ((Additive.toMul (e T' s)) k) := by
  refine ⟨fun T => secEquiv u T (H _).1 (H _).2.2.1 (H _).2.2.2.1 (H _).2.2.2.2, ?_⟩
  intro T T' g s k
  dsimp only
  rw [secEquiv_apply, secEquiv_apply]
  show pt u T (H _).2.2.2.2 ((s.down).comp g.base.hom) k =
    (Scheme.Γ.map g.op) (pt u T' (H _).2.2.2.2 s.down k)
  rw [pt_comp u g (H _).2.2.2.1 (H _).2.2.2.2 (H _).2.2.2.2 s.down]
  rfl

end SectionsAssembly

end

section
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem solution
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (f : K ≃ₐ[ℤ] (Fin 2 → ℤ)) :
    ∃ e : ∀ T : Scheme.{0},
      ((FppfKummerSES.sheafULift.{0}.obj
          (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj
        (Opposite.op T)) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))),
      ∀ {T T' : Scheme.{0}} (g : T ⟶ T')
        (s : (FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj
          (Opposite.op T')) (k : K),
        (Additive.toMul (e T ((FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.map g.op s))) k
          = (Scheme.Γ.map g.op) ((Additive.toMul (e T' s)) k) := by
  obtain ⟨u, -, H⟩ := HopfPiTwo.exists_conv_idem f
  exact SectionsAssembly.exists_sectionsEquiv_of_conv K u H

end

end

end S_AlgebraicGeometry_exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two
end P2MW
export P2MW.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two (solution)
