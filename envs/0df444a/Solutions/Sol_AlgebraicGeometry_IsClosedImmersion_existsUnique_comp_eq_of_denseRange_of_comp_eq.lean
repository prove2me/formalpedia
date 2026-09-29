-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_denseRange_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/95fdee69-c98a-55ab-8bb6-726df3fdeca0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {W X Y Z : Scheme.{u}} [IsReduced X] (g : W ⟶ X) (hg : DenseRange g.base)
    (ι : Z ⟶ Y) [IsClosedImmersion ι] (φ : X ⟶ Y)
    (ψ : W ⟶ Z) (hψ : ψ ≫ ι = g ≫ φ) :
    ∃! χ : X ⟶ Z, χ ≫ ι = φ := by
  classical

  let j : pullback ι φ ⟶ X := pullback.snd ι φ
  haveI : IsClosedImmersion j := inferInstance
  have hrange : Set.range g.base ⊆ Set.range j.base := by
    rintro _ ⟨w, rfl⟩

    obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := ι) (g := φ) (ψ.base w) (g.base w)
      (by
        change (ψ ≫ ι).base w = (g ≫ φ).base w
        rw [hψ])
    exact ⟨t, ht2⟩

  haveI : Surjective j := ⟨by
    rw [← Set.range_eq_univ]
    have hcl : IsClosed (Set.range j.base) := j.isClosedEmbedding.isClosed_range
    exact Set.eq_univ_of_univ_subset ((hg.closure_eq ▸ closure_minimal hrange hcl).ge)⟩
  haveI : IsIso j := isIso_of_isClosedImmersion_of_surjective j
  refine ⟨inv j ≫ pullback.fst ι φ, ?_, ?_⟩
  · show (inv j ≫ pullback.fst ι φ) ≫ ι = φ
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · intro χ hχ
    exact (cancel_mono ι).mp (by rw [hχ, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc])

end S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq (solution)
