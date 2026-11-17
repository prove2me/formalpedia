-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensor_pointLogHeight_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:10.836655+00:00
-- url     : https://prove2.me/submissions/c575bd17-3583-4768-a41d-dd2ebe27b013

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensor_sections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_tensor_pointLogHeight_eq_add
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- A full Segre presentation adds point heights exactly. -/
theorem _root_.solution
    {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N') :
    ∃ (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
      (R : (L ⊗ M).ProjPresentation f (N * N' + N + N')),
      (∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2)) ∧
      ∀ x, R.pointLogHeight x = P.pointLogHeight x + Q.pointLogHeight x := by
  obtain ⟨idx,R,hσ,hU⟩ := P.exists_tensor_sections Q
  exact ⟨idx,R,hσ,P.tensor_pointLogHeight_eq_add Q idx R hσ hU⟩

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
