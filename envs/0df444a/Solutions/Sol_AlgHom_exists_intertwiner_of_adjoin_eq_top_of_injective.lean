-- Prove2me | solution 1 for AlgHom.exists_intertwiner_of_adjoin_eq_top_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/dec202ab-8098-5813-9907-9ae80b38c622

import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Algebra.Tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective

set_option autoImplicit false

theorem solution
    {R : Type} [CommRing R]
    {C₁ C₀ : Type} [CommRing C₁] [CommRing C₀] [Algebra R C₁] [Algebra R C₀]
    {M₁ M₀ : Type} [AddCommGroup M₁] [AddCommGroup M₀] [Module R M₁] [Module R M₀]
    [Module C₁ M₁] [Module C₀ M₀] [IsScalarTower R C₁ M₁] [IsScalarTower R C₀ M₀]
    (i : M₀ →ₗ[R] M₁) (hi : Function.Injective i)
    (hfaith : ∀ y : C₀, (∀ m : M₀, y • m = 0) → y = 0)
    (G : Set C₁) (hG : Algebra.adjoin R G = ⊤)
    (y : C₁ → C₀) (hy : ∀ g ∈ G, ∀ m : M₀, g • i m = i (y g • m)) :
    ∃ res : C₁ →ₐ[R] C₀,
      (∀ (t : C₁) (m : M₀), t • i m = i (res t • m)) ∧
      (∀ g ∈ G, res g = y g) ∧
      (∀ res' : C₁ →ₐ[R] C₀, (∀ (t : C₁) (m : M₀), t • i m = i (res' t • m)) → res' = res) := by
  classical

  have huniq : ∀ (t : C₁) (y₁ y₂ : C₀), (∀ m, t • i m = i (y₁ • m)) → (∀ m, t • i m = i (y₂ • m)) → y₁ = y₂ := by
    intro t y₁ y₂ h₁ h₂
    have hz : ∀ m : M₀, (y₁ - y₂) • m = (0 : M₀) := fun m => by
      have him : i ((y₁ - y₂) • m) = i 0 := by
        rw [map_zero, sub_smul, map_sub, ← h₁, ← h₂, sub_self]
      exact hi him
    exact sub_eq_zero.mp (hfaith _ hz)

  let A : Subalgebra R C₁ :=
    { carrier := {t | ∃ y : C₀, ∀ m, t • i m = i (y • m)}
      mul_mem' := by
        rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
        exact ⟨ya * yb, fun m => by rw [mul_smul, hb, ha, mul_smul]⟩
      one_mem' := ⟨1, fun m => by rw [one_smul, one_smul]⟩
      add_mem' := by
        rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
        exact ⟨ya + yb, fun m => by rw [add_smul, ha, hb, add_smul, map_add]⟩
      zero_mem' := ⟨0, fun m => by rw [zero_smul, zero_smul, map_zero]⟩
      algebraMap_mem' := fun r => ⟨algebraMap R C₀ r, fun m => by
        rw [algebraMap_smul, algebraMap_smul, LinearMap.map_smul]⟩ }
  have hGA : G ⊆ A := fun g hg => ⟨y g, hy g hg⟩
  have hA : ∀ t : C₁, t ∈ A := fun t => by
    have ht : t ∈ Algebra.adjoin R G := hG ▸ Algebra.mem_top
    exact Algebra.adjoin_le hGA ht
  have hall : ∀ t : C₁, ∃ y : C₀, ∀ m, t • i m = i (y • m) := fun t => hA t
  choose f hf using hall
  let res : C₁ →ₐ[R] C₀ :=
    { toFun := f
      map_one' := huniq 1 _ _ (hf 1) (fun m => by rw [one_smul, one_smul])
      map_mul' := fun a b => huniq (a * b) _ _ (hf _) (fun m => by rw [mul_smul, hf b, hf a, mul_smul])
      map_zero' := huniq 0 _ _ (hf 0) (fun m => by rw [zero_smul, zero_smul, map_zero])
      map_add' := fun a b => huniq (a + b) _ _ (hf _) (fun m => by rw [add_smul, hf a, hf b, add_smul, map_add])
      commutes' := fun r => huniq _ _ _ (hf _) (fun m => by
        rw [algebraMap_smul, algebraMap_smul, LinearMap.map_smul]) }
  refine ⟨res, fun t m => hf t m, fun g hg => huniq g _ _ (hf g) (hy g hg), fun res' hres' => ?_⟩
  ext t
  exact huniq t _ _ (hres' t) (hf t)

end S_AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective
end P2MW
export P2MW.S_AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective (solution)
