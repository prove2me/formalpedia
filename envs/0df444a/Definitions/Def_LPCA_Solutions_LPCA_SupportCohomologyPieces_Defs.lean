-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
-- name    : LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:17:18.085296+00:00
-- url     : https://prove2.me/theorems/8a47cd72-d61f-436e-b4e5-50d01726ea8d
-- title:
--   Actual homogeneous subspaces of support local cohomology
-- statement:
--   This bundle supplies actual homogeneous subspaces of support local cohomology. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The degree-a subspace of the original Ext-colimit object is the range of the actual homogeneous Cech inclusion under the proved comparison.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_SupportCohomologyPieces.lean, selected declarations in lines 16–69; source SHA-256 d89e01c9a42d03e080901f1c156f230ea4c03502bf86ed5f3ae176040945c557; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
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
import Definitions.Def_LPCA
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
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

noncomputable abbrev supportCohomologyField (K : Complex V) (T : Finset V) (q : ℕ) :
    ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
    (supportCohomology k K T q)

noncomputable def supportCohomologyDegreeInclusion (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    localizedCechCohomology k rank K T a q ⟶ supportCohomologyField k K T q :=
  ModuleCat.ofHom (DirectSum.lof k (V → ℤ)
    (fun b => localizedCechCohomology k rank K T b q) a) ≫
      (supportCohomologyDirectSumIso k rank K T q).inv

theorem supportCohomologyDegreeInclusion_actual
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) (q : ℕ) :
    supportCohomologyDegreeInclusion k rank K T a q =
      HomologicalComplex.homologyMap (localizedCechDegreeInclusion k rank K T a) q ≫
        (supportCohomologyFieldCechIso k rank K T q).inv :=
  supportCohomologyDirectSumIso_ι_inv k rank K T q a

theorem supportCohomologyDegreeInclusion_injective
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) (q : ℕ) :
    Function.Injective (supportCohomologyDegreeInclusion k rank K T a q) := by
  intro x y h
  change (supportCohomologyDirectSumIso k rank K T q).inv
      (DirectSum.lof k (V → ℤ) (fun b => localizedCechCohomology k rank K T b q) a x) =
    (supportCohomologyDirectSumIso k rank K T q).inv
      (DirectSum.lof k (V → ℤ) (fun b => localizedCechCohomology k rank K T b q) a y) at h
  have hh := (supportCohomologyDirectSumIso k rank K T q).symm.toLinearEquiv.injective h
  simpa only [DirectSum.lof_apply] using congrArg (fun z => z a) hh

/-- The degree-a subspace of the original Ext-colimit object is the range
of the actual homogeneous Cech inclusion under the proved comparison. -/
noncomputable def supportCohomologyPiece (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    Submodule k (supportCohomologyField k K T q) :=
  LinearMap.range (supportCohomologyDegreeInclusion k rank K T a q).hom

noncomputable def supportCohomologyPieceIso (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    ModuleCat.of k (supportCohomologyPiece k rank K T a q) ≅
      localizedCechCohomology k rank K T a q :=
  (LinearEquiv.ofInjective (supportCohomologyDegreeInclusion k rank K T a q).hom
    (supportCohomologyDegreeInclusion_injective k rank K T a q)).toModuleIso.symm

@[reassoc] theorem supportCohomologyPieceIso_hom_inclusion
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) (q : ℕ) :
    (supportCohomologyPieceIso k rank K T a q).hom ≫
        supportCohomologyDegreeInclusion k rank K T a q =
      ModuleCat.ofHom (supportCohomologyPiece k rank K T a q).subtype := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearEquiv.ofInjective_symm_apply
    (supportCohomologyDegreeInclusion k rank K T a q).hom x



end LPCA


