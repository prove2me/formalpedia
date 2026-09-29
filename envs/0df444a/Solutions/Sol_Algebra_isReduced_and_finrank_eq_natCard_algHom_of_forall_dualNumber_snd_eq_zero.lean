-- Prove2me | solution 1 for Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a04b3309-3e5a-5a5e-9c62-9ad74298071b

import Mathlib
import Theorems.Thm_Algebra_exists_algHom_dualNumber_snd_ne_zero_of_sq_ne
import Theorems.Thm_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
    (h : ∀ (φ : R →ₐ[F] DualNumber Ω) (r : R), (φ r).snd = 0) :
    IsReduced R ∧ Module.finrank F R = Nat.card (R →ₐ[F] Ω) := by
  classical

  have hFΩ : Function.Injective (algebraMap F Ω) := (algebraMap F Ω).injective

  have hS : ∀ 𝔪 : Ideal (Ω ⊗[F] R), 𝔪.IsMaximal → 𝔪 ^ 2 = 𝔪 := by
    intro 𝔪 h𝔪
    by_contra hne
    haveI := h𝔪
    haveI : Algebra.IsIntegral Ω ((Ω ⊗[F] R) ⧸ 𝔪) := Algebra.IsIntegral.of_finite Ω _
    have hres : Function.Surjective (algebraMap Ω ((Ω ⊗[F] R) ⧸ 𝔪)) :=
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := (Ω ⊗[F] R) ⧸ 𝔪)).2
    obtain ⟨φ, s, hφ⟩ := Algebra.exists_algHom_dualNumber_snd_ne_zero_of_sq_ne Ω (Ω ⊗[F] R) 𝔪 hres hne
    let ψ : R →ₐ[F] DualNumber Ω :=
      (φ.restrictScalars F).comp (Algebra.TensorProduct.includeRight (R := F) (A := Ω) (B := R))
    have hψ : ∀ r : R, ψ r = φ ((1 : Ω) ⊗ₜ[F] r) := fun r => rfl
    have hall : ∀ s : Ω ⊗[F] R, TrivSqZeroExt.snd (φ s) = 0 := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul ω r =>
          have : (ω ⊗ₜ[F] r : Ω ⊗[F] R) = ω • ((1 : Ω) ⊗ₜ[F] r) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [this, map_smul, TrivSqZeroExt.snd_smul, ← hψ, h ψ r, smul_zero]
      | add x y hx hy => rw [map_add, TrivSqZeroExt.snd_add, hx, hy, add_zero]
    exact hφ (hall s)

  obtain ⟨hredS, hrankS⟩ :=
    Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq Ω (Ω ⊗[F] R) hS
  refine ⟨?_, ?_⟩
  ·
    have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := F) (A := Ω) (B := R)) :=
      Algebra.TensorProduct.includeRight_injective hFΩ
    exact isReduced_of_injective _ hinj
  ·
    have h1 : Module.finrank Ω (Ω ⊗[F] R) = Module.finrank F R := Module.finrank_baseChange

    let toF : ((Ω ⊗[F] R) →ₐ[Ω] Ω) → (R →ₐ[F] Ω) := fun g =>
      (g.restrictScalars F).comp (Algebra.TensorProduct.includeRight (R := F) (A := Ω) (B := R))
    let toΩ : (R →ₐ[F] Ω) → ((Ω ⊗[F] R) →ₐ[Ω] Ω) := fun f =>
      Algebra.TensorProduct.lift (AlgHom.id Ω Ω) f (fun _ _ => Commute.all _ _)
    have e : ((Ω ⊗[F] R) →ₐ[Ω] Ω) ≃ (R →ₐ[F] Ω) :=
      { toFun := toF
        invFun := toΩ
        left_inv := fun g => by
          apply Algebra.TensorProduct.ext'
          intro a b
          simp only [toΩ, toF, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.coe_comp,
            AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply]
          have : (a ⊗ₜ[F] b : Ω ⊗[F] R) = a • ((1 : Ω) ⊗ₜ[F] b) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [this, map_smul, smul_eq_mul]
        right_inv := fun f => by
          apply AlgHom.ext
          intro r
          simp [toΩ, toF] }
    have h2 : Nat.card ((Ω ⊗[F] R) →ₐ[Ω] Ω) = Nat.card (R →ₐ[F] Ω) := Nat.card_congr e
    rw [← h1, hrankS, h2]

end S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero
end P2MW
export P2MW.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero (solution)
