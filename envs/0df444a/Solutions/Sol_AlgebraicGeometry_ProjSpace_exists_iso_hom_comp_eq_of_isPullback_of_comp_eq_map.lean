-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fa6331fe-622a-50bd-968b-8852dc2b5f8a

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (Z : Scheme.{0})
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (Z₁ : Scheme.{0}) (ι₁ : Z₁ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₁ : Z₁ ⟶ Z)
    (h₁ : IsPullback e₁ (ι₁ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (h₁' : e₁ ≫ ι = ι₁ ≫ ProjSpace.map A B n)
    (Z₂ : Scheme.{0}) (ι₂ : Z₂ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₂ : Z₂ ⟶ Z)
    (h₂ : IsPullback e₂ (ι₂ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (h₂' : e₂ ≫ ι = ι₂ ≫ ProjSpace.map A B n) :
    ∃ φ : Z₁ ≅ Z₂, φ.hom ≫ ι₂ = ι₁ ∧ φ.hom ≫ e₂ = e₁ := by
  refine ⟨h₁.isoIsPullback _ _ h₂, ?_, by simp⟩
  apply (AlgebraicGeometry.ProjSpace.isPullback_map A B n).hom_ext
  · rw [Category.assoc, ← h₂', ← Category.assoc, IsPullback.isoIsPullback_hom_fst, h₁']
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd]

end S_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map (solution)
