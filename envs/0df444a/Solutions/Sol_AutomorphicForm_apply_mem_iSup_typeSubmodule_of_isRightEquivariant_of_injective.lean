-- Prove2me | solution 1 for AutomorphicForm.apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/155e5ef1-7e77-57fc-86d6-182f9bcf6c80

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective

set_option autoImplicit false

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective.AutomorphicForm"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant exists_isRightEquivariant_comp_subtype_eq_of_injective"
namespace TypePush
p2m_open "AutomorphicForm"

variable {H K G : Type*} [Group H] [Group K] [Group G]

def rightRegular (j : H →* K) : Representation ℂ H (K → ℂ) where
  toFun k :=
    { toFun := fun u κ => u (κ * j k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro u
    funext κ
    show u (κ * j 1) = u κ
    rw [map_one, mul_one]
  map_mul' k k' := by
    apply LinearMap.ext
    intro u
    funext κ
    show u (κ * j (k * k')) = u (κ * j k * j k')
    rw [map_mul, mul_assoc]

theorem rightRegular_apply (j : H →* K) (k : H) (u : K → ℂ) :
    rightRegular j k u = fun κ => u (κ * j k) :=
  rfl

theorem map_typeSubmodule_le_of_isRightEquivariant (j : H →* K) (ι' : H →* G)
    (Text : (K → ℂ) →ₗ[ℂ] (G → ℂ)) (hText : IsRightEquivariant ι' (rightRegular j) Text)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) :
    (typeSubmodule j ρ).map Text ≤ typeSubmodule ι' ρ := by
  show (Submodule.span ℂ _).map Text ≤ _
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, ⟨T, hT, v, rfl⟩, rfl⟩
  have hTT : IsRightEquivariant ι' ρ (Text ∘ₗ T) := by
    intro k v' x
    show Text (T (ρ k v')) x = Text (T v') (x * ι' k)
    have h1 : T (ρ k v') = rightRegular j k (T v') := funext fun κ => hT k v' κ
    rw [h1]
    exact hText k (T v') x
  exact mem_typeSubmodule_of_isRightEquivariant hTT v

end AutomorphicForm.TypePush

open AutomorphicForm.TypePush in
theorem solution
    {H K G : Type*} [Group H] [Group K] [Group G]
    (j : H →* K) (ι' : H →* G) (hι' : Function.Injective ι')
    (C : Submodule ℂ (K → ℂ)) (hC : ∀ (k : H) (u : K → ℂ), u ∈ C → (fun κ => u (κ * j k)) ∈ C)
    (A : ↥C →ₗ[ℂ] (G → ℂ))
    (hA : ∀ (k : H) (u : ↥C) (x : G),
      A ⟨fun κ => (u : K → ℂ) (κ * j k), hC k u u.2⟩ x = A u (x * ι' k))
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i)) (u : K → ℂ) (hu : u ∈ C)
    (hut : u ∈ ⨆ i, typeSubmodule j (ρ i)) :
    A ⟨u, hu⟩ ∈ ⨆ i, typeSubmodule ι' (ρ i) := by
  have hC' : ∀ (k : H) (u : K → ℂ), u ∈ C → rightRegular j k u ∈ C := fun k u h => hC k u h
  have hA' : ∀ (k : H) (u : ↥C) (x : G), A ⟨rightRegular j k u, hC' k u u.2⟩ x = A u (x * ι' k) :=
    fun k u x => hA k u x
  obtain ⟨Text, hText, hTextC⟩ :=
    AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective ι' hι' (rightRegular j) C hC' A hA'
  have hAu : A ⟨u, hu⟩ = Text u := by
    rw [← hTextC]
    rfl
  rw [hAu]
  have hle : (⨆ i, typeSubmodule j (ρ i)).map Text ≤ ⨆ i, typeSubmodule ι' (ρ i) := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun i => map_typeSubmodule_le_of_isRightEquivariant j ι' Text hText (ρ i)
  exact hle ⟨u, hut, rfl⟩

end S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
end P2MW
export P2MW.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective (solution)
