-- Prove2me | solution 1 for AdicCompletion.exists_linearMap_forall_val_apply_eq_mk_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1a1d0310-92f8-5a8c-ba17-83f5aac85287

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply

set_option autoImplicit false

universe u

theorem solution
    {A : Type u} [CommRing A] (I : Ideal A)
    (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    ∃ θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N),
      ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
        Submodule.Quotient.mk g = x.val n →
          ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m) := by
  classical

  let β : ∀ n : ℕ, (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] N ⧸ (I ^ n • ⊤ : Submodule A N)) :=
    fun n => LinearMap.compRight A (Submodule.mkQ (I ^ n • ⊤ : Submodule A N))
  have hβ : ∀ n : ℕ, (I ^ n • ⊤ : Submodule A (M →ₗ[A] N)) ≤ LinearMap.ker (β n) := by
    intro n
    refine Submodule.smul_le.mpr fun a ha g _ => ?_
    rw [LinearMap.mem_ker]
    ext m
    simp only [β, LinearMap.compRight_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Submodule.mkQ_apply, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha Submodule.mem_top)
  let α : ∀ n : ℕ, (M →ₗ[A] N) ⧸ (I ^ n • ⊤ : Submodule A (M →ₗ[A] N)) →ₗ[A]
      (M →ₗ[A] N ⧸ (I ^ n • ⊤ : Submodule A N)) :=
    fun n => (I ^ n • ⊤ : Submodule A (M →ₗ[A] N)).liftQ (β n) (hβ n)
  have hα : ∀ (n : ℕ) (g : M →ₗ[A] N) (m : M),
      α n (Submodule.Quotient.mk g) m = Submodule.Quotient.mk (g m) := by
    intro n g m
    simp only [α, Submodule.liftQ_apply, β, LinearMap.compRight_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply]

  have hcompat : ∀ (x : AdicCompletion I (M →ₗ[A] N)) {m n : ℕ} (hle : m ≤ n),
      AdicCompletion.transitionMap I N hle ∘ₗ α n (x.val n) = α m (x.val m) := by
    intro x m n hle
    obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    have hm : x.val m = Submodule.Quotient.mk g := by
      rw [← x.property hle, ← hg]
      exact Submodule.factor_mk _ g
    ext v
    rw [LinearMap.comp_apply, ← hg, hm, hα, hα]
    exact Submodule.factor_mk _ (g v)

  let θfun : AdicCompletion I (M →ₗ[A] N) → (M →ₗ[A] AdicCompletion I N) :=
    fun x => AdicCompletion.lift I (fun n => α n (x.val n)) (fun hle => hcompat x hle)
  have hθfun : ∀ (x : AdicCompletion I (M →ₗ[A] N)) (m : M) (n : ℕ),
      (θfun x m).val n = α n (x.val n) m := fun x m n => rfl
  refine ⟨{ toFun := θfun, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    refine LinearMap.ext fun m => AdicCompletion.ext fun n => ?_
    simp only [hθfun, LinearMap.add_apply, AdicCompletion.val_add_apply, LinearMap.map_add]
  · intro a x
    refine LinearMap.ext fun m => AdicCompletion.ext fun n => ?_
    simp only [hθfun, RingHom.id_apply, LinearMap.smul_apply, AdicCompletion.val_smul_apply,
      LinearMap.map_smul]
  · intro x n g hg m
    show (θfun x m).val n = _
    rw [hθfun, ← hg, hα]

end S_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply
end P2MW
export P2MW.S_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply (solution)
