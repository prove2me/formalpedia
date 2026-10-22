-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceLabels_Defs
-- name    : LPCA_Solutions_LPCA_RelativeFaceLabels_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:51:35.452268+00:00
-- url     : https://prove2.me/theorems/efb1642d-6436-40e0-a3d4-9ceb6b116c78
-- title:
--   Relabelling the actual relative cochain kernels
-- statement:
--   This bundle supplies relabelling the actual relative cochain kernels. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Reindex both absolute cochain complexes in the actual restriction square, then take its actual kernel.
--   - Removing unused labels is a natural relative-cohomology equivalence for a whole monotone pair family, not only an equality of dimensions.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_RelativeFaceLabels.lean, selected declarations in lines 17–174; source SHA-256 f9ea0533b5704ba3bda62acccd9e83c6fa4fe78f8c21bbc15ebc26f164dd0b86; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_redRestrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_restrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceLabelNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCohomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterIncidence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterLinkTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterNonfaceVanishing_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterSigns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
variable (k : Type u) [Field k]

/-- Reindex both absolute cochain complexes in the actual restriction square,
then take its actual kernel. -/
noncomputable def relativeFaceLabelComplexIso (rank : V ↪ ℕ)
    {B A : Complex V} (h : B.faces ⊆ A.faces) (e : W ↪ V)
    (hB : ∀ F ∈ B.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hA : ∀ F ∈ A.faces, ∀ v ∈ F, v ∈ Set.range e) :
    relativeFaceComplex k rank h ≅
      relativeFaceComplex k (e.trans rank) (restrictComplex_faces_mono h e) :=
  kernel.mapIso (reducedFaceRestriction k rank h)
    (reducedFaceRestriction k (e.trans rank) (restrictComplex_faces_mono h e))
    (offsetFaceLabelComplexIso k rank A e hA (-1))
    (offsetFaceLabelComplexIso k rank B e hB (-1))
    (offsetFaceLabelComplexIso_restriction k rank h e hB hA (-1))

@[reassoc] theorem relativeFaceLabelComplexIso_toAbsolute (rank : V ↪ ℕ)
    {B A : Complex V} (h : B.faces ⊆ A.faces) (e : W ↪ V)
    (hB : ∀ F ∈ B.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hA : ∀ F ∈ A.faces, ∀ v ∈ F, v ∈ Set.range e) :
    (relativeFaceLabelComplexIso k rank h e hB hA).hom ≫
        kernel.ι (reducedFaceRestriction k (e.trans rank) (restrictComplex_faces_mono h e)) =
      kernel.ι (reducedFaceRestriction k rank h) ≫
        (offsetFaceLabelComplexIso k rank A e hA (-1)).hom :=
  kernel.lift_ι _ _ _



@[reassoc] theorem relativeFaceLabelComplexIso_restriction (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ : Complex V} (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces)
    (hB : B₀.faces ⊆ B₁.faces) (hA : A₀.faces ⊆ A₁.faces) (e : W ↪ V)
    (hB₀ : ∀ F ∈ B₀.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hA₀ : ∀ F ∈ A₀.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hB₁ : ∀ F ∈ B₁.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hA₁ : ∀ F ∈ A₁.faces, ∀ v ∈ F, v ∈ Set.range e) :
    relativeFaceRestriction k rank h₀ h₁ hB hA ≫
        (relativeFaceLabelComplexIso k rank h₀ e hB₀ hA₀).hom =
      (relativeFaceLabelComplexIso k rank h₁ e hB₁ hA₁).hom ≫
        relativeFaceRestriction k (e.trans rank)
          (restrictComplex_faces_mono h₀ e) (restrictComplex_faces_mono h₁ e)
          (restrictComplex_faces_mono hB e) (restrictComplex_faces_mono hA e) := by
  apply (cancel_mono (kernel.ι (reducedFaceRestriction k (e.trans rank)
    (restrictComplex_faces_mono h₀ e)))).mp
  calc
    _ = relativeFaceRestriction k rank h₀ h₁ hB hA ≫
        (kernel.ι (reducedFaceRestriction k rank h₀) ≫
          (offsetFaceLabelComplexIso k rank A₀ e hA₀ (-1)).hom) := by
      rw [Category.assoc, relativeFaceLabelComplexIso_toAbsolute]
    _ = (kernel.ι (reducedFaceRestriction k rank h₁) ≫
        reducedFaceRestriction k rank hA) ≫
          (offsetFaceLabelComplexIso k rank A₀ e hA₀ (-1)).hom := by
      rw [← Category.assoc, relativeFaceRestriction_toAbsolute]
    _ = kernel.ι (reducedFaceRestriction k rank h₁) ≫
        ((offsetFaceLabelComplexIso k rank A₁ e hA₁ (-1)).hom ≫
          reducedFaceRestriction k (e.trans rank) (restrictComplex_faces_mono hA e)) := by
      rw [Category.assoc]
      exact congrArg (fun a => kernel.ι (reducedFaceRestriction k rank h₁) ≫ a)
        (offsetFaceLabelComplexIso_restriction k rank hA e hA₀ hA₁ (-1))
    _ = ((relativeFaceLabelComplexIso k rank h₁ e hB₁ hA₁).hom ≫
        kernel.ι (reducedFaceRestriction k (e.trans rank) (restrictComplex_faces_mono h₁ e))) ≫
          reducedFaceRestriction k (e.trans rank) (restrictComplex_faces_mono hA e) := by
      rw [relativeFaceLabelComplexIso_toAbsolute, Category.assoc]
    _ = _ := by
      symm
      calc
        _ = (relativeFaceLabelComplexIso k rank h₁ e hB₁ hA₁).hom ≫
            (relativeFaceRestriction k (e.trans rank)
              (restrictComplex_faces_mono h₀ e) (restrictComplex_faces_mono h₁ e)
              (restrictComplex_faces_mono hB e) (restrictComplex_faces_mono hA e) ≫
                kernel.ι (reducedFaceRestriction k (e.trans rank)
                  (restrictComplex_faces_mono h₀ e))) := Category.assoc _ _ _
        _ = (relativeFaceLabelComplexIso k rank h₁ e hB₁ hA₁).hom ≫
            (kernel.ι (reducedFaceRestriction k (e.trans rank) (restrictComplex_faces_mono h₁ e)) ≫
              reducedFaceRestriction k (e.trans rank) (restrictComplex_faces_mono hA e)) :=
          congrArg (fun a => (relativeFaceLabelComplexIso k rank h₁ e hB₁ hA₁).hom ≫ a)
            (relativeFaceRestriction_toAbsolute k (e.trans rank)
              (restrictComplex_faces_mono h₀ e) (restrictComplex_faces_mono h₁ e)
              (restrictComplex_faces_mono hB e) (restrictComplex_faces_mono hA e))
        _ = _ := (Category.assoc _ _ _).symm

noncomputable def relativeFaceLabelCohomologyIso (rank : V ↪ ℕ)
    {B A : Complex V} (h : B.faces ⊆ A.faces) (e : W ↪ V)
    (hB : ∀ F ∈ B.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hA : ∀ F ∈ A.faces, ∀ v ∈ F, v ∈ Set.range e) (r : ℤ) :
    relativeFaceCohomology k rank h r ≅
      relativeFaceCohomology k (e.trans rank) (restrictComplex_faces_mono h e) r :=
  (homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) r).mapIso
    (relativeFaceLabelComplexIso k rank h e hB hA)





@[reassoc] theorem relativeFaceLabelCohomologyIso_restriction (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ : Complex V} (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces)
    (hB : B₀.faces ⊆ B₁.faces) (hA : A₀.faces ⊆ A₁.faces) (e : W ↪ V)
    (hB₀ : ∀ F ∈ B₀.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hA₀ : ∀ F ∈ A₀.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hB₁ : ∀ F ∈ B₁.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hA₁ : ∀ F ∈ A₁.faces, ∀ v ∈ F, v ∈ Set.range e) (r : ℤ) :
    relativeFaceCohomologyRestriction k rank h₀ h₁ hB hA r ≫
        (relativeFaceLabelCohomologyIso k rank h₀ e hB₀ hA₀ r).hom =
      (relativeFaceLabelCohomologyIso k rank h₁ e hB₁ hA₁ r).hom ≫
        relativeFaceCohomologyRestriction k (e.trans rank)
          (restrictComplex_faces_mono h₀ e) (restrictComplex_faces_mono h₁ e)
          (restrictComplex_faces_mono hB e) (restrictComplex_faces_mono hA e) r := by
  change homologyMap _ r ≫ homologyMap _ r = homologyMap _ r ≫ homologyMap _ r
  rw [← homologyMap_comp, ← homologyMap_comp, relativeFaceLabelComplexIso_restriction]

/-- Removing unused labels is a natural relative-cohomology equivalence for a
whole monotone pair family, not only an equality of dimensions. -/
noncomputable def relativeFaceLabelPersistenceIso (rank : V ↪ ℕ)
    (A B : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces))
    (hB : Monotone (fun t => (B t).faces)) (h : ∀ t, (B t).faces ⊆ (A t).faces)
    (e : W ↪ V)
    (hBe : ∀ t F, F ∈ (B t).faces → ∀ v ∈ F, v ∈ Set.range e)
    (hAe : ∀ t F, F ∈ (A t).faces → ∀ v ∈ F, v ∈ Set.range e) (r : ℤ) :
    relativeFacePersistence k rank A B hA hB h r ≅
      relativeFacePersistence k (e.trans rank)
        (fun t => restrictComplex (A t) e) (fun t => restrictComplex (B t) e)
        (fun _s _t hst => restrictComplex_faces_mono (hA hst) e)
        (fun _s _t hst => restrictComplex_faces_mono (hB hst) e)
        (fun t => restrictComplex_faces_mono (h t) e) r :=
  NatIso.ofComponents
    (fun t => relativeFaceLabelCohomologyIso k rank (h (OrderDual.ofDual t)) e
      (hBe (OrderDual.ofDual t)) (hAe (OrderDual.ofDual t)) r)
    (fun _f => relativeFaceLabelCohomologyIso_restriction k rank _ _ _ _ e _ _ _ _ r)

end LPCA


