-- Prove2me | solution 1 for AlgebraicGeometry.exists_isClosedImmersion_iff_comp_eq_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4b0b7f37-124a-5779-8bf6-1713865853d4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {H S T : Scheme.{u}} (q : H ⟶ S) [IsSeparated q] (t : T ⟶ S) (u v : T ⟶ H) (hu : u ≫ q = t) (hv : v ≫ q = t) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ T), IsClosedImmersion j ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T), ψ ≫ u = ψ ≫ v ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ := by
  refine ⟨pullback (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q),
    pullback.fst (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q), inferInstance, fun ψ => ⟨fun h => ?_, fun ⟨ψ', hψ'⟩ => ?_⟩⟩
  · refine ⟨pullback.lift ψ (ψ ≫ u) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
  · have hc := pullback.condition (f := pullback.lift u v (hu.trans hv.symm)) (g := pullback.diagonal q)
    have h1 := congrArg (fun φ => φ ≫ pullback.fst q q) hc
    have h2 := congrArg (fun φ => φ ≫ pullback.snd q q) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id] at h1 h2
    rw [← hψ', Category.assoc, Category.assoc, h1, h2]

end S_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated (solution)
