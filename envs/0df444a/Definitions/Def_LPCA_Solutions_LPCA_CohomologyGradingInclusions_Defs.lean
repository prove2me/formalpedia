-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
-- name    : LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:16:17.493678+00:00
-- url     : https://prove2.me/theorems/8f65af88-5f9c-47d0-a594-5b5b7259bd86
-- title:
--   Cohomology Grading Inclusions for localized persistent commutative algebra
-- statement:
--   This bundle supplies cohomology Grading Inclusions for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The support object retains its original ambient-polynomial action; this is the canonical comparison after restricting that action to constants.
--   - Each concrete direct-sum injection is precisely the homology of the actual homogeneous-subcomplex inclusion, transported to the original Ext colimit. In particular the abstract comparison has no arbitrary summand maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CohomologyGradingInclusions.lean, selected declarations in lines 17–78; source SHA-256 b5961781724559ebfe74ba3da1c6862e1a30cd025acb3f28be58986b593106b8; source certificate Sapelo2 job 49172236.

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

@[reassoc] theorem degreeCohomologyColimitIso_ι
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (q : ℕ) (a : V → ℤ) :
    colimit.ι (cechDegreeDiagram k rank K T ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) q)
        (Discrete.mk a) ≫ (degreeCohomologyColimitIso k rank K T q).hom =
      ModuleCat.ofHom (DirectSum.lof k (V → ℤ)
        (fun b => localizedCechCohomology k rank K T b q) a) := by
  classical
  dsimp only [degreeCohomologyColimitIso, Iso.trans_hom]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  change 𝟙 _ ≫ (colimit.ι
      (Discrete.functor (fun b => localizedCechCohomology k rank K T b q))
      (Discrete.mk a) ≫ _) = _
  rw [Category.id_comp]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) (moduleDirectSumIsColimit k
      (fun b => localizedCechCohomology k rank K T b q)) (Discrete.mk a)

@[reassoc] theorem degreeCohomologyColimitIso_ι_inv
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (q : ℕ) (a : V → ℤ) :
    ModuleCat.ofHom (DirectSum.lof k (V → ℤ)
        (fun b => localizedCechCohomology k rank K T b q) a) ≫
        (degreeCohomologyColimitIso k rank K T q).inv =
      colimit.ι (cechDegreeDiagram k rank K T ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) q)
        (Discrete.mk a) := by
  apply (cancel_mono (degreeCohomologyColimitIso k rank K T q).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    degreeCohomologyColimitIso_ι]

/-- The support object retains its original ambient-polynomial action; this
is the canonical comparison after restricting that action to constants. -/
noncomputable def supportCohomologyFieldCechIso (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (q : ℕ) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
        (supportCohomology k K T q) ≅ (ambientCechFieldComplex k rank K T).homology q :=
  (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).mapIso
      (supportCohomologyCechIso k rank K T q) ≪≫
    (ambientCechHomologyFieldIso k rank K T q).symm

/-- Each concrete direct-sum injection is precisely the homology of the
actual homogeneous-subcomplex inclusion, transported to the original Ext
colimit. In particular the abstract comparison has no arbitrary summand maps. -/
@[reassoc] theorem supportCohomologyDirectSumIso_ι_inv
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (q : ℕ) (a : V → ℤ) :
    ModuleCat.ofHom (DirectSum.lof k (V → ℤ)
        (fun b => localizedCechCohomology k rank K T b q) a) ≫
        (supportCohomologyDirectSumIso k rank K T q).inv =
      HomologicalComplex.homologyMap (localizedCechDegreeInclusion k rank K T a) q ≫
        (supportCohomologyFieldCechIso k rank K T q).inv := by
  simp only [supportCohomologyDirectSumIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [degreeCohomologyColimitIso_ι_inv_assoc, exactColimitHomologyIso_ι_assoc]
  simp only [← Category.assoc]
  change ((HomologicalComplex.homologyMap
      (colimit.ι (cechDegreeDiagram k rank K T) (Discrete.mk a)) q ≫
      HomologicalComplex.homologyMap (cechDegreeColimitIso k rank K T).hom q) ≫
      (ambientCechHomologyFieldIso k rank K T q).hom) ≫
      ((ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).mapIso
        (supportCohomologyCechIso k rank K T q)).inv = _
  rw [← HomologicalComplex.homologyMap_comp, cechDegreeColimitIso_ι]
  simp only [Category.assoc]
  rfl

end LPCA


