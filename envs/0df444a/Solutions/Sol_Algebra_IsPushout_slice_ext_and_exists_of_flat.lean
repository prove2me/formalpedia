-- Prove2me | solution 1 for Algebra.IsPushout.slice_ext_and_exists_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a8ed448f-d4c6-54d5-adac-52d467f653c7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsPushout_slice_ext_and_exists_of_flat

set_option autoImplicit false

open TensorProduct

universe u

theorem solution
    {B B₁ B' M N : Type u} [CommRing B] [CommRing B₁] [CommRing B'] [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B' B₁] [Algebra B B'] [Algebra B M] [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N] [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (hπ : Function.Surjective (algebraMap B B₁))
    (p : Fin 3 → (B' →ₐ[B] B))
    (hp : ∀ (i : Fin 3) (x : B'), algebraMap B B₁ (p i x) = algebraMap B' B₁ x)
    (hinj : ∀ x y : B', (∀ i, p i x = p i y) → x = y)
    (hsurj : ∀ b : Fin 3 → B, (∀ i j, algebraMap B B₁ (b i) = algebraMap B B₁ (b j)) → ∃ x : B', ∀ i, p i x = b i)
    (e : Fin 3 → (N →ₐ[B] M))
    (heM : ∀ (i : Fin 3) (m : M), e i (algebraMap M N m) = m)
    (heB : ∀ (i : Fin 3) (x : B'), e i (algebraMap B' N x) = algebraMap B M (p i x)) :
    (∀ n n' : N, (∀ i, e i n = e i n') → n = n') ∧
    (∀ m : Fin 3 → M, (∀ i j, m i - m j ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)) →
      ∃ n : N, ∀ i, e i n = m i) := by
  classical
  haveI : Algebra.IsPushout B M B' N := Algebra.IsPushout.symm inferInstance
  let E : M ⊗[B] B' ≃ₐ[M] N := Algebra.IsPushout.equiv B M B' N
  let Pl : B' →ₗ[B] (Fin 3 → B) := LinearMap.pi fun i => (p i).toLinearMap
  let Ψ : M ⊗[B] B' →ₗ[B] (Fin 3 → M) :=
    (TensorProduct.piScalarRight B B M (Fin 3)).toLinearMap ∘ₗ LinearMap.lTensor M Pl
  have hΨ_tmul : ∀ (m : M) (b : B') (i : Fin 3), Ψ (m ⊗ₜ b) i = p i b • m := by
    intro m b i
    simp only [Ψ, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    rfl
  have hE : ∀ (x : M ⊗[B] B') (i : Fin 3), e i (E x) = Ψ x i := by
    intro x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m b =>
      rw [hΨ_tmul]
      change e i (Algebra.IsPushout.equiv B M B' N (m ⊗ₜ b)) = _
      rw [Algebra.IsPushout.equiv_tmul, map_mul, heM, heB, Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hPl : Function.Injective Pl := fun x y h => hinj x y (fun i => congrFun h i)
  have hΨinj : Function.Injective Ψ :=
    (TensorProduct.piScalarRight B B M (Fin 3)).injective.comp (Module.Flat.lTensor_preserves_injective_linearMap Pl hPl)
  refine ⟨?_, ?_⟩
  ·
    intro n n' h
    obtain ⟨x, rfl⟩ := E.surjective n
    obtain ⟨x', rfl⟩ := E.surjective n'
    have : x = x' := hΨinj (funext fun i => by rw [← hE, ← hE, h i])
    rw [this]
  ·
    have hsingle : ∀ (k : Fin 3) (d : M), d ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M) →
        ∃ n : N, ∀ i, e i n = (Pi.single k d : Fin 3 → M) i := by
      intro k d hd
      refine Submodule.span_induction (p := fun d _ => ∃ n : N, ∀ i, e i n = (Pi.single k d : Fin 3 → M) i) ?_ ?_ ?_ ?_ hd
      · rintro _ ⟨j, hj, rfl⟩
        have hj0 : algebraMap B B₁ j = 0 := hj
        obtain ⟨x, hx⟩ := hsurj (Pi.single k j : Fin 3 → B) (fun i i' => by
          simp only [Pi.single_apply]
          split_ifs <;> simp [hj0])
        refine ⟨algebraMap B' N x, fun i => ?_⟩
        rw [heB, hx, Pi.single_apply, Pi.single_apply]
        split_ifs <;> simp
      · exact ⟨0, fun i => by simp⟩
      · rintro d₁ d₂ _ _ ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩
        exact ⟨n₁ + n₂, fun i => by rw [map_add, hn₁, hn₂, Pi.single_add, Pi.add_apply]⟩
      · rintro c d _ ⟨n, hn⟩
        refine ⟨algebraMap M N c * n, fun i => ?_⟩
        rw [map_mul, heM, hn, Pi.single_apply, Pi.single_apply, smul_eq_mul]
        split_ifs <;> simp
    intro m hm
    obtain ⟨n₁, hn₁⟩ := hsingle 1 (m 1 - m 0) (hm 1 0)
    obtain ⟨n₂, hn₂⟩ := hsingle 2 (m 2 - m 0) (hm 2 0)
    refine ⟨algebraMap M N (m 0) + n₁ + n₂, fun i => ?_⟩
    rw [map_add, map_add, heM, hn₁, hn₂]
    fin_cases i <;> simp

end S_Algebra_IsPushout_slice_ext_and_exists_of_flat
end P2MW
export P2MW.S_Algebra_IsPushout_slice_ext_and_exists_of_flat (solution)
