-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.apply_eq_pullback_congr_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3c6785c0-4dbc-5db2-a890-2b1bec95b2a5

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_apply_eq_pullback_congr_hom

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"
open scoped TensorProduct

theorem solution
    {X X' : Scheme.{u}} (c c' : X' ⟶ X) (h : c = c') (L : X.Modules) (L' : X'.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L')
    {S S' : Type u} [CommRing S] [CommRing S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R)
    (R' : Type u) [CommRing R'] [Algebra S' R'] (𝓡' : ℕ → Submodule S' R')
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤))
    (ϑ : R →+* R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hϑ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x))) :
    ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c' L n ≪≫ Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackCongr h).app L).symm ≪≫ e) n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c').unit.app (L.tensorPow n)).app ⊤) (ι n x)) := by
  subst h
  intro n x
  rw [hϑ n x]
  have hI : ((Scheme.Modules.pullbackCongr (rfl : c = c)).app L).symm ≪≫ e = e := by
    ext : 1
    simp [Scheme.Modules.pullbackCongr]
  rw [hI]

end S_AlgebraicGeometry_GradedOAlgebra_apply_eq_pullback_congr_hom
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_apply_eq_pullback_congr_hom (solution)
