-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceNaturality_Defs
-- name    : LPCA_Solutions_LPCA_RelativeFaceNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:45:04.252415+00:00
-- url     : https://prove2.me/theorems/ce7a15be-8033-4e66-b09f-137b768a0800
-- title:
--   Functorial pair restrictions and relative connecting maps
-- statement:
--   This bundle supplies functorial pair restrictions and relative connecting maps. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The relative map of pairs is induced on the actual kernel cochain complex by ordinary restriction on both absolute cochain complexes.
--   - Naturality of the connecting map of the ordinary reduced relative long exact sequence, with the same restriction maps on the actual pair.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_RelativeFaceNaturality.lean, selected declarations in lines 16–122; source SHA-256 7fd21f12e05cd1376825bcc16f5651f207d5df7410a022b467398630220db21f; source certificate Sapelo2 job 49172236.

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
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
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

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem reducedFaceRestriction_pair_square (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ : Complex V} (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces)
    (hB : B₀.faces ⊆ B₁.faces) (hA : A₀.faces ⊆ A₁.faces) :
    reducedFaceRestriction k rank h₁ ≫ reducedFaceRestriction k rank hB =
      reducedFaceRestriction k rank hA ≫ reducedFaceRestriction k rank h₀ := by
  change offsetFaceRestriction k rank h₁ (-1) ≫ offsetFaceRestriction k rank hB (-1) =
    offsetFaceRestriction k rank hA (-1) ≫ offsetFaceRestriction k rank h₀ (-1)
  rw [offsetFaceRestriction_comp, offsetFaceRestriction_comp]

/-- The relative map of pairs is induced on the actual kernel cochain
complex by ordinary restriction on both absolute cochain complexes. -/
noncomputable def relativeFaceRestriction (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ : Complex V} (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces)
    (hB : B₀.faces ⊆ B₁.faces) (hA : A₀.faces ⊆ A₁.faces) :
    relativeFaceComplex k rank h₁ ⟶ relativeFaceComplex k rank h₀ :=
  kernel.map (reducedFaceRestriction k rank h₁) (reducedFaceRestriction k rank h₀)
    (reducedFaceRestriction k rank hA) (reducedFaceRestriction k rank hB)
    (reducedFaceRestriction_pair_square k rank h₀ h₁ hB hA)

theorem relativeFaceRestriction_toAbsolute (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ : Complex V} (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces)
    (hB : B₀.faces ⊆ B₁.faces) (hA : A₀.faces ⊆ A₁.faces) :
    relativeFaceRestriction k rank h₀ h₁ hB hA ≫ kernel.ι (reducedFaceRestriction k rank h₀) =
      kernel.ι (reducedFaceRestriction k rank h₁) ≫ reducedFaceRestriction k rank hA :=
  kernel.lift_ι _ _ _

noncomputable def relativeFaceShortComplexRestriction (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ : Complex V} (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces)
    (hB : B₀.faces ⊆ B₁.faces) (hA : A₀.faces ⊆ A₁.faces) :
    relativeFaceShortComplex k rank h₁ ⟶ relativeFaceShortComplex k rank h₀ where
  τ₁ := relativeFaceRestriction k rank h₀ h₁ hB hA
  τ₂ := reducedFaceRestriction k rank hA
  τ₃ := reducedFaceRestriction k rank hB
  comm₁₂ := relativeFaceRestriction_toAbsolute k rank h₀ h₁ hB hA
  comm₂₃ := (reducedFaceRestriction_pair_square k rank h₀ h₁ hB hA).symm

theorem relativeFaceRestriction_refl (rank : V ↪ ℕ)
    {B A : Complex V} (h : B.faces ⊆ A.faces) :
    relativeFaceRestriction k rank h h (Finset.Subset.refl B.faces) (Finset.Subset.refl A.faces) =
      𝟙 (relativeFaceComplex k rank h) := by
  apply (cancel_mono (kernel.ι (reducedFaceRestriction k rank h))).mp
  rw [relativeFaceRestriction_toAbsolute, Category.id_comp]
  change kernel.ι _ ≫ offsetFaceRestriction k rank (Finset.Subset.refl A.faces) (-1) = _
  rw [offsetFaceRestriction_refl, Category.comp_id]

theorem relativeFaceRestriction_comp (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ B₂ A₂ : Complex V}
    (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces) (h₂ : B₂.faces ⊆ A₂.faces)
    (hB₀₁ : B₀.faces ⊆ B₁.faces) (hA₀₁ : A₀.faces ⊆ A₁.faces)
    (hB₁₂ : B₁.faces ⊆ B₂.faces) (hA₁₂ : A₁.faces ⊆ A₂.faces) :
    relativeFaceRestriction k rank h₁ h₂ hB₁₂ hA₁₂ ≫ relativeFaceRestriction k rank h₀ h₁ hB₀₁ hA₀₁ =
      relativeFaceRestriction k rank h₀ h₂ (Finset.Subset.trans hB₀₁ hB₁₂)
        (Finset.Subset.trans hA₀₁ hA₁₂) := by
  apply (cancel_mono (kernel.ι (reducedFaceRestriction k rank h₀))).mp
  rw [Category.assoc, relativeFaceRestriction_toAbsolute, ← Category.assoc,
    relativeFaceRestriction_toAbsolute, Category.assoc, relativeFaceRestriction_toAbsolute]
  change kernel.ι _ ≫ (offsetFaceRestriction k rank hA₁₂ (-1) ≫
    offsetFaceRestriction k rank hA₀₁ (-1)) = _
  rw [offsetFaceRestriction_comp]
  rfl

noncomputable def relativeFaceCohomologyRestriction (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ : Complex V} (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces)
    (hB : B₀.faces ⊆ B₁.faces) (hA : A₀.faces ⊆ A₁.faces) (r : ℤ) :
    relativeFaceCohomology k rank h₁ r ⟶ relativeFaceCohomology k rank h₀ r :=
  homologyMap (relativeFaceRestriction k rank h₀ h₁ hB hA) r

theorem relativeFaceCohomologyRestriction_refl (rank : V ↪ ℕ)
    {B A : Complex V} (h : B.faces ⊆ A.faces) (r : ℤ) :
    relativeFaceCohomologyRestriction k rank h h (Finset.Subset.refl B.faces)
      (Finset.Subset.refl A.faces) r = 𝟙 (relativeFaceCohomology k rank h r) := by
  unfold relativeFaceCohomologyRestriction
  rw [relativeFaceRestriction_refl, homologyMap_id]
  rfl

theorem relativeFaceCohomologyRestriction_comp (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ B₂ A₂ : Complex V}
    (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces) (h₂ : B₂.faces ⊆ A₂.faces)
    (hB₀₁ : B₀.faces ⊆ B₁.faces) (hA₀₁ : A₀.faces ⊆ A₁.faces)
    (hB₁₂ : B₁.faces ⊆ B₂.faces) (hA₁₂ : A₁.faces ⊆ A₂.faces) (r : ℤ) :
    relativeFaceCohomologyRestriction k rank h₁ h₂ hB₁₂ hA₁₂ r ≫
        relativeFaceCohomologyRestriction k rank h₀ h₁ hB₀₁ hA₀₁ r =
      relativeFaceCohomologyRestriction k rank h₀ h₂ (Finset.Subset.trans hB₀₁ hB₁₂)
        (Finset.Subset.trans hA₀₁ hA₁₂) r := by
  unfold relativeFaceCohomologyRestriction
  rw [← homologyMap_comp, relativeFaceRestriction_comp]

theorem relativeFaceCohomologyToAbsolute_naturality (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ : Complex V} (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces)
    (hB : B₀.faces ⊆ B₁.faces) (hA : A₀.faces ⊆ A₁.faces) (r : ℤ) :
    relativeFaceCohomologyRestriction k rank h₀ h₁ hB hA r ≫
        relativeFaceCohomologyToAbsolute k rank h₀ r =
      relativeFaceCohomologyToAbsolute k rank h₁ r ≫ reducedFaceCohomologyRestriction k rank hA r := by
  unfold relativeFaceCohomologyRestriction relativeFaceCohomologyToAbsolute reducedFaceCohomologyRestriction
  rw [← homologyMap_comp, ← homologyMap_comp]
  exact congrArg (fun f => homologyMap f r) (relativeFaceRestriction_toAbsolute k rank h₀ h₁ hB hA)

/-- Naturality of the connecting map of the ordinary reduced relative
long exact sequence, with the same restriction maps on the actual pair. -/
theorem relativeFaceConnecting_naturality (rank : V ↪ ℕ)
    {B₀ A₀ B₁ A₁ : Complex V} (h₀ : B₀.faces ⊆ A₀.faces) (h₁ : B₁.faces ⊆ A₁.faces)
    (hB : B₀.faces ⊆ B₁.faces) (hA : A₀.faces ⊆ A₁.faces) (r : ℤ) :
    relativeFaceConnecting k rank h₁ r ≫ relativeFaceCohomologyRestriction k rank h₀ h₁ hB hA (r + 1) =
      reducedFaceCohomologyRestriction k rank hB r ≫ relativeFaceConnecting k rank h₀ r :=
  HomologicalComplex.HomologySequence.δ_naturality
    (relativeFaceShortComplexRestriction k rank h₀ h₁ hB hA)
    (relativeFaceShortExact k rank h₁) (relativeFaceShortExact k rank h₀) r (r + 1) (by simp)

end LPCA


