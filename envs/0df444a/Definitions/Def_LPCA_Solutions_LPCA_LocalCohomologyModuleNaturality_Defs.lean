-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyModuleNaturality_Defs
-- name    : LPCA_Solutions_LPCA_LocalCohomologyModuleNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:59:45.339974+00:00
-- url     : https://prove2.me/theorems/9c801207-602e-4f65-be1f-b977e01caefb
-- title:
--   Local Cohomology Module Naturality for localized persistent commutative algebra
-- statement:
--   This bundle supplies local Cohomology Module Naturality for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Naturality of the unchanged original legacy-Ext/coordinate-Koszul colimit comparison in its actual module argument.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalCohomologyModuleNaturality.lean, selected declarations in lines 17–58; source SHA-256 1bca00c79e30664759ad7279288486f72862fb0c24afcae62b775987422a8484; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
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
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite HomologicalComplex

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- Naturality of the unchanged original legacy-Ext/coordinate-Koszul
colimit comparison in its actual module argument. -/
@[reassoc] theorem coordinateLocalCohomologyKoszulColimitIso_module_naturality
    (rank : V ↪ ℕ) (T : Finset V) (q : ℕ)
    {M N : ModuleCat.{u} (MvPolynomial V k)} (f : M ⟶ N) :
    (localCohomology (coordinateIdeal k T) q).map f ≫
        (coordinateLocalCohomologyKoszulColimitIso k rank T q N).hom =
      (coordinateLocalCohomologyKoszulColimitIso k rank T q M).hom ≫
        homologyMap (colim.map (coordinateKoszulYonedaModuleMap k rank T f)) q := by
  let D := localCohomology.diagram (coordinatePowersDiagram k T) q
  let a := whiskerLeft D
    ((evaluation (ModuleCat.{u} (MvPolynomial V k))
      (ModuleCat.{u} (MvPolynomial V k))).map f)
  let e₀ (A : ModuleCat.{u} (MvPolynomial V k)) :
      (localCohomology (coordinateIdeal k T) q).obj A ⟶ (colimit D).obj A :=
    ((coordinatePowersLocalCohomologyIso k T q).app A).inv
  let e₁ (A : ModuleCat.{u} (MvPolynomial V k)) :
      (colimit D).obj A ⟶ colimit (D ⋙
        (evaluation (ModuleCat.{u} (MvPolynomial V k))
          (ModuleCat.{u} (MvPolynomial V k))).obj A) :=
    (colimitObjIsoColimitCompEvaluation D A).hom
  let e₂ (A : ModuleCat.{u} (MvPolynomial V k)) :
      colimit (D ⋙ (evaluation (ModuleCat.{u} (MvPolynomial V k))
          (ModuleCat.{u} (MvPolynomial V k))).obj A) ⟶
        colimit (coordinateKoszulExtDiagram k T q A) :=
    (Functor.Final.colimitIso (opOpEquivalence ℕ).inverse
      (D ⋙ (evaluation (ModuleCat.{u} (MvPolynomial V k))
        (ModuleCat.{u} (MvPolynomial V k))).obj A)).inv
  have h₀ : (localCohomology (coordinateIdeal k T) q).map f ≫ e₀ N =
      e₀ M ≫ (colimit D).map f :=
    (coordinatePowersLocalCohomologyIso k T q).inv.naturality f
  have h₁ : (colimit D).map f ≫ e₁ N = e₁ M ≫ colim.map a :=
    colimit_map_colimitObjIsoColimitCompEvaluation_hom D f
  have h₂ : colim.map a ≫ e₂ N =
      e₂ M ≫ colim.map (coordinateKoszulExtModuleMap k T q f) :=
    (Functor.Final.colimIso (opOpEquivalence ℕ).inverse).inv.naturality a
  change (localCohomology (coordinateIdeal k T) q).map f ≫
      e₀ N ≫ e₁ N ≫ e₂ N ≫ (coordinateKoszulExtColimitIso k rank T q N).hom =
    (e₀ M ≫ e₁ M ≫ e₂ M ≫ (coordinateKoszulExtColimitIso k rank T q M).hom) ≫ _
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂]
  simp only [Category.assoc]
  rw [coordinateKoszulExtColimitIso_module_naturality]

end LPCA


