-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/41db1011-5428-54a5-8d24-434e899d64e0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] [IsSeparated f]
    (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃! σ : Spec (CommRingCat.of R) ⟶ X,
      σ ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ = x := by
  let S : ValuativeCommSq f := ValuativeCommSq.mk R K x (𝟙 _) ⟨by rw [Category.comp_id]; exact hx⟩
  have hE : S.commSq.HasLift := by
    have h := UniversallyClosed.eq_valuativeCriterion
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := h ▸ (inferInstance : UniversallyClosed f)
    exact this.1 S
  have hU : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion f S
  refine ⟨S.commSq.lift, ⟨S.commSq.fac_right, S.commSq.fac_left⟩, ?_⟩
  rintro σ ⟨h1, h2⟩
  let l₁ : S.commSq.LiftStruct := ⟨σ, h2, h1⟩
  let l₂ : S.commSq.LiftStruct := ⟨S.commSq.lift, S.commSq.fac_left, S.commSq.fac_right⟩
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)

end S_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated (solution)
