-- Prove2me | solution 1 for Algebra.exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7b867edb-384d-5082-827c-5bf188b6458d

import Mathlib
import Theorems.Thm_MvPolynomial_exists_tmul_one_sub_one_tmul_eq_sum_mul
import Theorems.Thm_Algebra_bijective_rTensor_dual_bezoutian_of_square_presentation
import Theorems.Thm_Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul
import Theorems.Thm_Algebra_lmul_bezoutian_eq_jacobianDet
import Theorems.Thm_Algebra_trace_eq_dual_lmul_of_bijective_rTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped TensorProduct

theorem Ws47.DLB.lid_rTensor_comp_mulLeft
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (Δ : A ⊗[R] A) (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
    (φ : Module.Dual R A) (s : A) :
    Algebra.TensorProduct.lid R A (LinearMap.rTensor A (φ.comp (LinearMap.mulLeft R s)) Δ) =
      s * Algebra.TensorProduct.lid R A (LinearMap.rTensor A φ Δ) := by
  have h2 : ∀ z : A ⊗[R] A, LinearMap.rTensor A (LinearMap.mulLeft R s) z = (s ⊗ₜ[R] (1 : A)) * z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have h3 : ∀ z : A ⊗[R] A, ((1 : A) ⊗ₜ[R] s) * z = LinearMap.lTensor A (LinearMap.mulLeft R s) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have h4 : ∀ w : R ⊗[R] A, Algebra.TensorProduct.lid R A (LinearMap.lTensor R (LinearMap.mulLeft R s) w) =
      s * Algebra.TensorProduct.lid R A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [Algebra.TensorProduct.lid_tmul, mul_smul_comm]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]

  have h5 : LinearMap.rTensor A φ (LinearMap.lTensor A (LinearMap.mulLeft R s) Δ) =
      LinearMap.lTensor R (LinearMap.mulLeft R s) (LinearMap.rTensor A φ Δ) := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply, h2, hbal, h3, h5, h4]

theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    [Module.Finite R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    [Module.Free R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))] :
    ∃ τ : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) →ₗ[R] R,
      Function.Bijective (fun a : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f) =>
        τ.comp (LinearMap.mulLeft R a)) ∧
      ∀ a : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f),
        Algebra.trace R _ a =
          τ (Ideal.Quotient.mk (Ideal.span (Set.range f))
              (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i))) * a) := by
  classical

  choose a ha using fun i => MvPolynomial.exists_tmul_one_sub_one_tmul_eq_sum_mul R (f i)

  let A := MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)
  let Δ : A ⊗[R] A := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
      (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a))
  let θ : Module.Dual R A → A := fun φ => Algebra.TensorProduct.lid R A (LinearMap.rTensor A φ Δ)
  have hθ : Function.Bijective θ := Algebra.bijective_rTensor_dual_bezoutian_of_square_presentation R f a ha
  have hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ :=
    fun s => Algebra.tmul_one_mul_bezoutian_eq_one_tmul_mul R f a ha s
  have hlin : ∀ (φ : Module.Dual R A) (s : A), θ (φ.comp (LinearMap.mulLeft R s)) = s * θ φ :=
    fun φ s => Ws47.DLB.lid_rTensor_comp_mulLeft R A Δ hbal φ s

  obtain ⟨τ, hτ⟩ := hθ.2 1
  refine ⟨τ, ⟨?_, ?_⟩, ?_⟩
  ·
    intro s s' hss'
    have h := congrArg θ hss'
    simp only [hlin, hτ, mul_one] at h
    exact h
  ·
    intro φ
    refine ⟨θ φ, hθ.1 ?_⟩
    show θ (τ.comp (LinearMap.mulLeft R (θ φ))) = θ φ
    rw [hlin, hτ, mul_one]
  ·
    intro x
    have hmul : ∀ z : A ⊗[R] A, LinearMap.mul' R A z = Algebra.TensorProduct.lmul' (S := A) R z := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u v => simp
      | add u v hu hv => simp only [map_add, hu, hv]
    rw [Algebra.trace_eq_dual_lmul_of_bijective_rTensor R A τ Δ hbal hθ hτ x, hmul,
      Algebra.lmul_bezoutian_eq_jacobianDet R f a ha]

end S_Algebra_exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation
end P2MW
export P2MW.S_Algebra_exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation (solution)
