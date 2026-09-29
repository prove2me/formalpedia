-- Prove2me | solution 1 for AlgebraicGeometry.eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d71e209c-f4a6-5999-b3bc-d1f2e321445a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (s s' : T ⟶ X) (h : s ≫ f = s' ≫ f) (t₀ : ↥T) (ht₀ : ∀ t : ↥T, t ⤳ t₀)
    (hΔ : (pullback.lift s s' h).base t₀ ∈ Set.range (pullback.diagonal f).base) :
    s = s' := by

  have hrange : Set.range (pullback.lift s s' h).base ⊆ Set.range (pullback.diagonal f).base := by
    rintro _ ⟨t, rfl⟩
    exact ((ht₀ t).map (pullback.lift s s' h).continuous).mem_open
      (pullback.diagonal f).isOpenEmbedding.isOpen_range hΔ

  let l := IsOpenImmersion.lift (pullback.diagonal f) (pullback.lift s s' h) hrange
  have hl : l ≫ pullback.diagonal f = pullback.lift s s' h := IsOpenImmersion.lift_fac _ _ _
  have hs : s = l := by
    have := congrArg (· ≫ pullback.fst f f) hl
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at this
    exact this.symm
  have hs' : s' = l := by
    have := congrArg (· ≫ pullback.snd f f) hl
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at this
    exact this.symm
  rw [hs, hs']

end S_AlgebraicGeometry_eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal
end P2MW
export P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal (solution)
