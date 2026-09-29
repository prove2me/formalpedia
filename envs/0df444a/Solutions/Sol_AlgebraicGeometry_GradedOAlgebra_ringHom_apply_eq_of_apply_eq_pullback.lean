-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.ringHom_apply_eq_of_apply_eq_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9cb7331d-3b72-5ea2-8c2b-560728cca1b8

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_ringHom_apply_eq_of_apply_eq_pullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"
open scoped TensorProduct

theorem solution
    {X X' : Scheme.{u}} (c : X' ⟶ X) (L : X.Modules) (L' : X'.Modules)
    (e e' : (Scheme.Modules.pullback c).obj L ≅ L') (he : e = e')
    {S S' : Type u} [CommRing S] [CommRing S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] (𝓡' : ℕ → Submodule S' R')
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤))
    (hι' : ∀ n, Function.Injective (ι' n))
    (ϑ : R →+* R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (ϑ' : R →+* R') (hϑ'deg : ∀ n, ∀ x ∈ 𝓡 n, ϑ' x ∈ 𝓡' n)
    (hϑ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)))
    (hϑ' : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ' x, hϑ'deg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e' n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x))) :
    ∀ x : R, ϑ x = ϑ' x := by
  classical
  subst he

  have hpiece : ∀ (n : ℕ) (x : 𝓡 n), ϑ x = ϑ' x := fun n x =>
    congrArg Subtype.val (hι' n ((hϑ n x).trans (hϑ' n x).symm))

  intro x
  rw [← DirectSum.sum_support_decompose 𝓡 x, map_sum, map_sum]
  exact Finset.sum_congr rfl fun n _ => hpiece n (DirectSum.decompose 𝓡 x n)

end S_AlgebraicGeometry_GradedOAlgebra_ringHom_apply_eq_of_apply_eq_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_ringHom_apply_eq_of_apply_eq_pullback (solution)
