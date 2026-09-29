-- Prove2me | solution 1 for AddTorsor.bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/afd6f0d8-9723-552d-9e52-b02581206bf0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddTorsor_bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ

set_option autoImplicit false

universe u v w x y

theorem solution
    {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V] {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (τ : V →ₗ[k] W)
    {LA : Type x} [AddTorsor V LA] {LG : Type y} [AddAction W LG] [AddAction.IsPretransitive W LG]
    (f : LA → LG) (hf : ∀ (v : V) (a : LA), f (v +ᵥ a) = τ v +ᵥ f a) (hinj : Function.Injective f)
    (U : Submodule k V) [FiniteDimensional k ↥U] (hdim : Module.finrank k W ≤ Module.finrank k ↥U) :
    Function.Bijective τ ∧ Function.Surjective f := by
  classical
  obtain ⟨a⟩ := (AddTorsor.nonempty : Nonempty LA)

  have hτinj : Function.Injective τ := by
    intro v₁ v₂ h
    have : f (v₁ +ᵥ a) = f (v₂ +ᵥ a) := by rw [hf, hf, h]
    exact vadd_right_cancel a (hinj this)

  have hτsurj : Function.Surjective τ := by
    let τU : ↥U →ₗ[k] W := τ.comp U.subtype
    have hτU : Function.Injective τU := hτinj.comp Subtype.val_injective
    have h1 : Module.finrank k ↥(LinearMap.range τU) = Module.finrank k ↥U := LinearMap.finrank_range_of_inj hτU
    have h2 : Module.finrank k ↥(LinearMap.range τU) ≤ Module.finrank k W := Submodule.finrank_le _
    have htop : LinearMap.range τU = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm h2 (by rw [h1]; exact hdim))
    intro w
    have hw : w ∈ LinearMap.range τU := by rw [htop]; exact Submodule.mem_top
    obtain ⟨u, hu⟩ := hw
    exact ⟨(u : V), hu⟩
  refine ⟨⟨hτinj, hτsurj⟩, ?_⟩
  intro x
  obtain ⟨w, hw⟩ := AddAction.IsPretransitive.exists_vadd_eq (M := W) (f a) x
  obtain ⟨v, rfl⟩ := hτsurj w
  exact ⟨v +ᵥ a, by rw [hf, hw]⟩

end S_AddTorsor_bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ
end P2MW
export P2MW.S_AddTorsor_bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ (solution)
