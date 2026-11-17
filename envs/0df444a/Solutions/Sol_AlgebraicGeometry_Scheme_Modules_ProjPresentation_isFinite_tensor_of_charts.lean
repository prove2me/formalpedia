-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_tensor_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:45.691782+00:00
-- url     : https://prove2.me/submissions/f9f2f6d3-2864-43b2-9ec1-c67206bfbf1f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- Product charts retain finiteness when the first presentation is finite. -/
theorem _root_.solution
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N*N'+N+N'+1) ≃ Fin (N+1) × Fin (N'+1))
    (R : (L ⊗ M).ProjPresentation f (N*N'+N+N'))
    (hchart : ∀ k, R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) =
      (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
        (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)))
    (hP : IsFinite P.toProj) : IsFinite R.toProj := by
  haveI : IsProper f := by rw [← P.toProj_π]; infer_instance
  have hDD (d : ℕ) (i : Fin (d+1)) :
      IsAffineOpen (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (d+1)) K) (MvPolynomial.X i)) :=
    Proj.isAffineOpen_basicOpen _ _ (ProjSpace.X_mem_one K d i) one_pos
  rw [IsFinite.iff_isProper_and_isAffineHom]
  constructor
  · haveI : IsProper (R.toProj ≫ ProjSpace.π K (N*N'+N+N')) := by rw [R.toProj_π]; infer_instance
    exact IsProper.of_comp R.toProj (ProjSpace.π K (N*N'+N+N'))
  · rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom)
      (fun k => (⟨Proj.basicOpen _ (MvPolynomial.X k), hDD (N*N'+N+N') k⟩ :
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (N*N'+N+N'+1)) K)).affineOpens))
      (Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X K (N*N'+N+N')))]
    intro k
    change IsAffineOpen (R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k))
    rw [hchart k]
    let U := P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)
    have hU : IsAffineOpen U := (hDD N (idx k).1).preimage P.toProj
    haveI : IsAffine U := hU
    haveI : IsAffineHom ((U.ι ≫ Q.toProj) ≫ ProjSpace.π K N') := inferInstance
    haveI : IsAffineHom (U.ι ≫ Q.toProj) := IsAffineHom.of_comp _ (ProjSpace.π K N')
    have h1 := (hDD N' (idx k).2).preimage (U.ι ≫ Q.toProj)
    have h2 := h1.image_of_isOpenImmersion U.ι
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι] at h2
    exact h2

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
