-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_isClosedImmersion_comp_pi_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/25a37948-2a60-5c36-8e9c-53355a54f383

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_comp_pi_eq_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (R : Type u) [CommRing R] (r : ℕ) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R),
      IsClosedImmersion σ ∧ σ ≫ ProjSpace.π R r = 𝟙 _ := by
  classical

  let ev : MvPolynomial (Fin (r + 1)) R →+* R :=
    (MvPolynomial.eval fun j : Fin (r + 1) => if j = 0 then (1 : R) else 0)
  have hev0 : ev (MvPolynomial.X 0) = 1 := by
    simp [ev]
  have hunit : IsUnit (ev (MvPolynomial.X 0)) := by rw [hev0]; exact isUnit_one
  let evL : Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin (r + 1)) R) →+* R :=
    Localization.awayLift ev (MvPolynomial.X 0) hunit
  let φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R) (MvPolynomial.X 0) →+* R :=
    evL.comp (algebraMap _ (Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin (r + 1)) R)))

  have hφ : φ.comp (algebraMap R _) = RingHom.id R := by
    ext x
    change evL ((algebraMap R (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)
      (MvPolynomial.X 0)) x).val) = x
    rw [ProjSpace.val_algebraMap]
    change Localization.awayLift ev (MvPolynomial.X 0) hunit (algebraMap _ _ (MvPolynomial.C x)) = x
    rw [Localization.awayLift, IsLocalization.Away.lift_eq]
    simp [ev]
  let σ : Spec (CommRingCat.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R) :=
    Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R) (MvPolynomial.X 0) (ProjSpace.X_mem_one R r 0) one_pos
  have hσ : σ ≫ ProjSpace.π R r = 𝟙 _ := by
    simp only [σ, Category.assoc]
    rw [ProjSpace.awayι_comp_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ, CommRingCat.ofHom_id, Spec.map_id]
  refine ⟨σ, ?_, hσ⟩
  have : IsClosedImmersion (σ ≫ ProjSpace.π R r) := by rw [hσ]; infer_instance
  exact IsClosedImmersion.of_comp σ (ProjSpace.π R r)

end S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_comp_pi_eq_id
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_comp_pi_eq_id (solution)
