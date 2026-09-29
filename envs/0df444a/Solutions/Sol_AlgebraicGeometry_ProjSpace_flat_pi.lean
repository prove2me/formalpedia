-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.flat_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/de7bcc73-6877-5556-9129-d0985df76a4f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

import Theorems.Thm_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_flat_pi

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry

universe u

theorem solution (R : Type u) [CommRing R] (n : ℕ) : Flat (ProjSpace.π R n) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

  have hflat : ∀ d : ℕ, Module.Flat R (𝒜 d) := by
    intro d
    refine Module.Flat.of_retract (Submodule.subtype (𝒜 d))
      ((DirectSum.component R ℕ (fun i => 𝒜 i) d).comp (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap) ?_
    refine LinearMap.ext fun x => ?_
    obtain ⟨x, hx⟩ := x
    show (DirectSum.component R ℕ (fun i => 𝒜 i) d) (DirectSum.decompose 𝒜 x) = ⟨x, hx⟩
    rw [← DirectSum.apply_eq_component]
    exact Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 hx)

  apply HasRingHomProperty.of_source_openCover (P := @Flat) (ProjSpace.affineOpenCover R n).openCover
  intro i
  change Fin (n + 1) at i
  have hi : (ProjSpace.affineOpenCover R n).openCover.f i ≫ ProjSpace.π R n =
      Spec.map (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)))) := ProjSpace.awayι_comp_π R n i
  rw [hi]
  apply HasRingHomProperty.appTop (P := @Flat)
  refine (HasRingHomProperty.Spec_iff (P := @Flat) (R := CommRingCat.of R) (S := CommRingCat.of (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)))).mpr ?_
  show (algebraMap R (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))).Flat

  have heq : (algebraMap R (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))) =
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (MvPolynomial.X i))).comp
        ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap R (MvPolynomial (Fin (n + 1)) R))) := by
    refine RingHom.ext fun r => ?_
    show (HomogeneousLocalization.fromZeroRingHom 𝒜 _) (ProjSpace.grad0Equiv R n r) =
      (HomogeneousLocalization.fromZeroRingHom 𝒜 _) (GradedRing.projZeroRingHom' 𝒜 (algebraMap R _ r))
    congr 1
    apply Subtype.ext
    have hC : (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) ∈ 𝒜 0 := (ProjSpace.grad0Equiv R n r).2
    show MvPolynomial.C r = ((GradedRing.projZeroRingHom' 𝒜) (MvPolynomial.C r) : MvPolynomial (Fin (n + 1)) R)
    first
      | (show MvPolynomial.C r = ((DirectSum.decompose 𝒜 (MvPolynomial.C r)) 0 : MvPolynomial (Fin (n + 1)) R)
         rw [DirectSum.decompose_of_mem_same 𝒜 hC])
      | (simp only [GradedRing.projZeroRingHom', RingHom.codRestrict_apply, GradedRing.projZeroRingHom_apply,
           GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hC])
      | (simp [GradedRing.projZeroRingHom', GradedRing.projZeroRingHom, DirectSum.decompose_of_mem_same 𝒜 hC])
  rw [heq]
  exact HomogeneousLocalization.Away.flat_fromZeroRingHom_comp_algebraMap_of_forall_flat 𝒜 hflat (MvPolynomial.X i)
    (ProjSpace.X_mem_one R n i)

end S_AlgebraicGeometry_ProjSpace_flat_pi
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_flat_pi (solution)
