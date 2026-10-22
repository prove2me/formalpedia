-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceCochains_Defs
-- name    : LPCA_Solutions_LPCA_RelativeFaceCochains_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:42:33.288045+00:00
-- url     : https://prove2.me/theorems/ffaae045-199e-4fb0-a1f7-78caf3ae2f1e
-- title:
--   Actual kernels of augmented reduced-cochain restriction
-- statement:
--   This bundle supplies actual kernels of augmented reduced-cochain restriction. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Ordinary restriction of reduced face cochains is surjective in every integer degree: a function on the smaller face set extends to the larger one.
--   - Relative reduced cochains of the actual pair (L,K): the kernel of ordinary restriction C-tilde(L) to C-tilde(K), with the full reduced augmentation.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_RelativeFaceCochains.lean, selected declarations in lines 18–93; source SHA-256 146a6d945226431105867a91008cd226f960ac0cff88e15123e606b12bfff633; source certificate Sapelo2 job 49172236.

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

/-- Ordinary restriction of reduced face cochains is surjective in every
integer degree: a function on the smaller face set extends to the larger one. -/
theorem reducedFaceRestriction_component_surjective (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (r : ℤ) :
    Function.Surjective ((reducedFaceRestriction k rank h).f r) := by
  classical
  letI : LinearOrder V := rankLinearOrder rank
  let e : Proofs.BassLyubeznik.BassStatic.Signed.Idx
      (Proofs.BassLyubeznik.SrFamily.faceFamily (toSignedComplex K)) (-1) r →
        Proofs.BassLyubeznik.BassStatic.Signed.Idx
          (Proofs.BassLyubeznik.SrFamily.faceFamily (toSignedComplex L)) (-1) r :=
    fun F => ⟨F.1, h F.2.1, F.2.2⟩
  have he : Function.Injective e := by
    intro F G hFG
    apply Subtype.ext
    exact congrArg (fun J : Proofs.BassLyubeznik.BassStatic.Signed.Idx
      (Proofs.BassLyubeznik.SrFamily.faceFamily (toSignedComplex L)) (-1) r => J.1) hFG
  change Function.Surjective (LinearMap.funLeft k k e)
  exact he.surjective_comp_right

theorem reducedFaceRestriction_epi (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) : Epi (reducedFaceRestriction k rank h) := by
  apply HomologicalComplex.epi_of_epi_f
  intro r
  exact (ModuleCat.epi_iff_surjective _).mpr
    (reducedFaceRestriction_component_surjective k rank h r)

/-- Relative reduced cochains of the actual pair (L,K): the kernel of
ordinary restriction C-tilde(L) to C-tilde(K), with the full reduced augmentation. -/
noncomputable def relativeFaceComplex (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) : CochainComplex (ModuleCat.{u} k) ℤ :=
  kernel (reducedFaceRestriction k rank h)

noncomputable def relativeFaceShortComplex (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) :
    ShortComplex (CochainComplex (ModuleCat.{u} k) ℤ) :=
  ShortComplex.kernelSequence (reducedFaceRestriction k rank h)

theorem relativeFaceShortExact (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) : (relativeFaceShortComplex k rank h).ShortExact := by
  haveI := reducedFaceRestriction_epi k rank h
  refine { exact := ShortComplex.kernelSequence_exact _, mono_f := ?_, epi_g := ?_ }
  · change Mono (kernel.ι (reducedFaceRestriction k rank h))
    infer_instance
  · change Epi (reducedFaceRestriction k rank h)
    exact reducedFaceRestriction_epi k rank h

noncomputable def relativeFaceCohomology (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (r : ℤ) : ModuleCat.{u} k :=
  (relativeFaceComplex k rank h).homology r

noncomputable def relativeFaceCohomologyToAbsolute (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (r : ℤ) :
    relativeFaceCohomology k rank h r ⟶ reducedFaceCohomology k rank L r :=
  homologyMap (kernel.ι (reducedFaceRestriction k rank h)) r

noncomputable def relativeFaceConnecting (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (r : ℤ) :
    reducedFaceCohomology k rank K r ⟶ relativeFaceCohomology k rank h (r + 1) :=
  (relativeFaceShortExact k rank h).δ r (r + 1) (by simp)

theorem relativeFaceCohomologyToAbsolute_restriction_zero (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (r : ℤ) :
    relativeFaceCohomologyToAbsolute k rank h r ≫ reducedFaceCohomologyRestriction k rank h r = 0 := by
  rw [relativeFaceCohomologyToAbsolute, reducedFaceCohomologyRestriction,
    ← homologyMap_comp, kernel.condition, homologyMap_zero]

theorem relativeFaceRestriction_connecting_zero (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (r : ℤ) :
    reducedFaceCohomologyRestriction k rank h r ≫ relativeFaceConnecting k rank h r = 0 :=
  (relativeFaceShortExact k rank h).comp_δ r (r + 1) (by simp)

theorem relativeFaceConnecting_toAbsolute_zero (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (r : ℤ) :
    relativeFaceConnecting k rank h r ≫ relativeFaceCohomologyToAbsolute k rank h (r + 1) = 0 :=
  (relativeFaceShortExact k rank h).δ_comp r (r + 1) (by simp)







end LPCA


