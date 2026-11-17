-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensor_pointLogHeight_eq_add_and_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:11.925361+00:00
-- url     : https://prove2.me/submissions/5c978743-6e72-4f0e-9403-9e1d3406b1e6

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
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_tensor_chart_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_tensor_of_charts

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- The Segre presentation remains finite when the first presentation is finite. -/
theorem _root_.solution
    {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (hP : IsFinite P.toProj) :
    ∃ (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
      (R : (L ⊗ M).ProjPresentation f (N * N' + N + N')), IsFinite R.toProj ∧
      (∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2)) ∧
      ∀ x, R.pointLogHeight x = P.pointLogHeight x + Q.pointLogHeight x := by
  obtain ⟨idx,R,hσ,hU⟩ := P.exists_tensor_sections Q
  exact ⟨idx,R,P.isFinite_tensor_of_charts Q idx R
    (P.tensor_chart_eq Q idx R hσ hU) hP,hσ,P.tensor_pointLogHeight_eq_add Q idx R hσ hU⟩

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
