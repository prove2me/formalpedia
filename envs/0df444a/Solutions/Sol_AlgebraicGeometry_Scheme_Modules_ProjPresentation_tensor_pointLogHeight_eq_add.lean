-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.tensor_pointLogHeight_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:10.167336+00:00
-- url     : https://prove2.me/submissions/a6c429e2-a635-439f-aaed-3e195c1f4198

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_surjective
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointEquivProjectivization_kPointOfVec
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pointProjectivization_tensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- The full tensor tuple has exactly the sum of the two projective heights. -/
theorem _root_.solution
    {K : Type} [Field K] [NumberField K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
    (R : (L ⊗ M).ProjPresentation f (N * N' + N + N'))
    (hσ : ∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2))
    (hU : ∀ k, (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
      (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) ≤
      R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k))
    (x : Scheme.KPoint f) :
    R.pointLogHeight x = P.pointLogHeight x + Q.pointLogHeight x := by
  obtain ⟨a,ha,hap⟩ := ProjSpace.kPointOfVec_surjective K N
    ⟨x.1 ≫ P.toProj, by rw [Category.assoc,P.toProj_π]; exact x.2⟩
  obtain ⟨b,hb,hbp⟩ := ProjSpace.kPointOfVec_surjective K N'
    ⟨x.1 ≫ Q.toProj, by rw [Category.assoc,Q.toProj_π]; exact x.2⟩
  obtain ⟨hc,hR⟩ := P.pointProjectivization_tensor Q idx R hσ hU x a ha b hb
    (congrArg Subtype.val hap) (congrArg Subtype.val hbp)
  have hP : P.pointProjectivization x = Projectivization.mk K a ha := by
    change ProjSpace.kPointEquivProjectivization K N _ = _
    rw [← hap]
    exact ProjSpace.kPointEquivProjectivization_kPointOfVec K N a ha
  have hQ : Q.pointProjectivization x = Projectivization.mk K b hb := by
    change ProjSpace.kPointEquivProjectivization K N' _ = _
    rw [← hbp]
    exact ProjSpace.kPointEquivProjectivization_kPointOfVec K N' b hb
  simp only [pointLogHeight,hP,hQ,hR,Projectivization.logHeight_mk]
  exact (Height.logHeight_comp_equiv idx (fun t => a t.1 * b t.2)).trans (Height.logHeight_fun_mul_eq ha hb)

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
