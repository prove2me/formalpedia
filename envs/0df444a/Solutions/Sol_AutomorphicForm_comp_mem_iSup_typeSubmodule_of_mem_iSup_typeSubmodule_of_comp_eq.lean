-- Prove2me | solution 1 for AutomorphicForm.comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b4728fe5-5f7e-5655-9659-122bd8b4732c

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq

set_option autoImplicit false

open AutomorphicForm

theorem solution
    {H P G : Type*} [Group H] [Group P] [Group G]
    (ι : H →* G) (j : H →* P) (θ : P →* G) (hθ : θ.comp j = ι)
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i))
    (f : G → ℂ) (hf : f ∈ ⨆ i, AutomorphicForm.typeSubmodule ι (ρ i)) :
    (fun p : P => f (θ p)) ∈ ⨆ i, AutomorphicForm.typeSubmodule j (ρ i) := by
  let L : (G → ℂ) →ₗ[ℂ] (P → ℂ) := LinearMap.funLeft ℂ ℂ θ
  have hι : ∀ k : H, θ (j k) = ι k := fun k => by rw [← hθ]; rfl
  have hle : ∀ i, (typeSubmodule ι (ρ i)).map L ≤ typeSubmodule j (ρ i) := by
    intro i
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro g ⟨T, hT, ⟨v, rfl⟩⟩
    show L (T v) ∈ typeSubmodule j (ρ i)
    refine Submodule.subset_span ⟨L.comp T, ?_, ⟨v, rfl⟩⟩
    intro k w x
    show T (ρ i k w) (θ x) = T w (θ (x * j k))
    rw [hT k w (θ x), map_mul, hι]
  have h1 : (⨆ i, typeSubmodule ι (ρ i)).map L ≤ ⨆ i, typeSubmodule j (ρ i) := by
    rw [Submodule.map_iSup]; exact iSup_mono hle
  exact h1 ⟨f, hf, rfl⟩

end S_AutomorphicForm_comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq
end P2MW
export P2MW.S_AutomorphicForm_comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq (solution)
