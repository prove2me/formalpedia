-- Prove2me | solution 1 for AlgebraicGeometry.exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/52b706c4-454e-5cb9-ae8c-ac8b5e3cdf1b

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}}
    (hAF : ∀ G : Finset X, ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ G, x ∈ W)
    (U O : X.Opens) (F : Finset ↥U) (hFO : ∀ x ∈ F, U.ι.base x ∈ O) :
    ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ U.ι ⁻¹ᵁ O ∧ ∀ x ∈ F, x ∈ W := by
  classical
  obtain ⟨W₁, hW₁, hFW₁⟩ := hAF (F.image fun x => U.ι.base x)
  obtain ⟨W₂, hW₂, hle, hFW₂⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_le_inf_forall_mem_of_finset W₁ hW₁ (U ⊓ O)
      (F.image fun x => U.ι.base x) hFW₁ (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨x.2, hFO x hx⟩)
  have hW₂U : W₂ ≤ U := (hle.trans inf_le_right).trans inf_le_left
  refine ⟨U.ι ⁻¹ᵁ W₂, hW₂.preimage_of_isOpenImmersion U.ι (by rwa [Scheme.Opens.opensRange_ι]), ?_, ?_⟩
  · exact Scheme.Hom.preimage_mono _ ((hle.trans inf_le_right).trans inf_le_right)
  · intro x hx
    exact hFW₂ _ (Finset.mem_image_of_mem _ hx)

end S_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset (solution)
