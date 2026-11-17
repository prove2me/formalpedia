-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_externalTensor_pointLogHeight_eq_add_and_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:58.84911+00:00
-- url     : https://prove2.me/submissions/b8c0a445-847e-449a-9a37-52e4ba1df2d1

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_pullback_pointLogHeight_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensor_sections
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_tensor_chart_eq
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_tensor_pointLogHeight_eq_add
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_of_external_charts

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- The external full tensor frame is finite and adds the two projected heights exactly. -/
theorem _root_.solution
    {K : Type} [Field K] [NumberField K]
    {X Y : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)}
    {g : Y ⟶ Spec (CommRingCat.of K)}
    {L : X.Modules} {M : Y.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation g N')
    (hP : IsFinite P.toProj) (hQ : IsFinite Q.toProj) :
    ∃ R :
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L ⊗
        (Scheme.Modules.pullback (pullback.snd f g)).obj M).ProjPresentation
        (pullback.fst f g ≫ f) (N * N' + N + N'),
      IsFinite R.toProj ∧
      ∀ z : Scheme.KPoint (pullback.fst f g ≫ f),
        R.pointLogHeight z =
          P.pointLogHeight
            ⟨z.1 ≫ pullback.fst f g,
              by rw [Category.assoc, z.2]⟩ +
          Q.pointLogHeight
            ⟨z.1 ≫ pullback.snd f g,
              by rw [Category.assoc, ← pullback.condition, z.2]⟩  := by
  obtain ⟨P', hPσ, hPto, hPh⟩ := P.exists_pullback_pointLogHeight_eq (pullback.fst f g)
  obtain ⟨Q₀, hQσ, hQto, hQh⟩ := Q.exists_pullback_pointLogHeight_eq (pullback.snd f g)
  let Q' : ((Scheme.Modules.pullback (pullback.snd f g)).obj M).ProjPresentation
      (pullback.fst f g ≫ f) N' :=
    { σ := Q₀.σ
      toProj := Q₀.toProj
      toProj_π := Q₀.toProj_π.trans pullback.condition.symm
      frame := Q₀.frame
      app_ratio_smul := Q₀.app_ratio_smul }
  obtain ⟨idx, R, hσ, hU⟩ := P'.exists_tensor_sections Q'
  refine ⟨R, ?_, fun z => ?_⟩
  · apply isFinite_of_external_charts P Q hP hQ R idx
    intro k
    rw [tensor_chart_eq P' Q' idx R hσ hU k]
    change P'.toProj ⁻¹ᵁ _ ⊓ Q₀.toProj ⁻¹ᵁ _ = _
    rw [hPto, hQto]
    rfl
  · rw [tensor_pointLogHeight_eq_add P' Q' idx R hσ hU z, hPh z]
    congr 1
    exact hQh ⟨z.1, by rw [← pullback.condition]; exact z.2⟩

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
