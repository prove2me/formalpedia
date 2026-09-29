-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.universallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d4f97f6d-bdbe-509f-a8cc-cde1469e537a

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_universallyClosed

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ) :
    UniversallyClosed θ := by
  obtain ⟨N, 𝔓, h𝔓⟩ := hva

  haveI : UniversallyClosed 𝔓.toProj := by haveI := h𝔓; infer_instance
  haveI : UniversallyClosed f := by
    rw [← 𝔓.toProj_π]; infer_instance

  haveI : UniversallyClosed (θ ≫ (Proj.toSpecZero 𝓡 ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))) := by
    rw [hθ.comp_toSpecZero]; infer_instance
  exact UniversallyClosed.of_comp_of_isSeparated θ (Proj.toSpecZero 𝓡 ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_universallyClosed
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_universallyClosed (solution)
