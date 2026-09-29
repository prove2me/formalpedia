-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_refl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8a83d959-93da-5eee-8477-ef51550ba26b

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_refl

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S) :
    FramedPolarisedAbelianScheme.Iso X X := by
  refine ⟨Iso.refl X.A, by rw [Iso.refl_hom, Category.id_comp], ?_, ?_, ?_, ?_⟩
  · rw [Iso.refl_hom, Category.id_comp]
  · intro T t x y
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    simp only [Iso.refl_hom, Category.comp_id]
  · intro i
    rw [Iso.refl_hom, Category.comp_id]
  · intro s
    refine ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (X.f ⁻¹ᵁ ⊤).ι).mapIso ?_⟩⟩
    rw [Iso.refl_hom]
    exact (Scheme.Modules.pullbackId X.A).app X.pol

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_refl
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_refl (solution)
