-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.linMap_map_comp_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f00a9850-e540-54b4-a5ac-9dcfecc8f8fb

import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_linMap_map_comp_map

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

namespace K79BC

open AlgebraicGeometry.ProjSpace

theorem linSubst_comp_mvMapGraded {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (linSubst A n (M.map (algebraMap R A))).comp (mvMapGraded R A n) =
      (mvMapGraded R A n).comp (linSubst R n M) := by
  have h : ((linSubst A n (M.map (algebraMap R A))).comp (mvMapGraded R A n)).toRingHom =
      ((mvMapGraded R A n).comp (linSubst R n M)).toRingHom :=
    MvPolynomial.ringHom_ext
      (fun r => by
        change linSubst A n (M.map (algebraMap R A)) (MvPolynomial.map (algebraMap R A) (C r)) =
          MvPolynomial.map (algebraMap R A) (linSubst R n M (C r))
        rw [map_C, linSubst_C, linSubst_C, map_C])
      (fun i => by
        change linSubst A n (M.map (algebraMap R A)) (MvPolynomial.map (algebraMap R A) (X i)) =
          MvPolynomial.map (algebraMap R A) (linSubst R n M (X i))
        rw [map_X, linSubst_X, linSubst_X]
        simp only [linForm, map_sum, map_mul, map_C, map_X, Matrix.map_apply])
  exact GradedRingHom.ext fun x => RingHom.congr_fun h x

end K79BC

theorem solution {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) (hMA : IsUnit (M.map (algebraMap R A))) :
    ProjSpace.linMap A n (M.map (algebraMap R A)) hMA ≫ ProjSpace.map R A n =
      ProjSpace.map R A n ≫ ProjSpace.linMap R n M hM := by
  rw [ProjSpace.linMap_eq, ProjSpace.linMap_eq, ProjSpace.map_eq, ← Proj.map_comp, ← Proj.map_comp]
  have key : ∀ (k₁ k₂ : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R →+*ᵍ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
      (hk₁ : HomogeneousIdeal.irrelevant _ ≤ (HomogeneousIdeal.irrelevant _).map k₁)
      (hk₂ : HomogeneousIdeal.irrelevant _ ≤ (HomogeneousIdeal.irrelevant _).map k₂),
      k₁ = k₂ → Proj.map k₁ hk₁ = Proj.map k₂ hk₂ := by
    rintro k₁ k₂ hk₁ hk₂ rfl
    rfl
  exact key _ _ _ _ (K79BC.linSubst_comp_mvMapGraded n M)

end S_AlgebraicGeometry_ProjSpace_linMap_map_comp_map
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_linMap_map_comp_map (solution)
