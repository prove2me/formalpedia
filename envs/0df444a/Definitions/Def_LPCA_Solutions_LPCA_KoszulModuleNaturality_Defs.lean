-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_KoszulModuleNaturality_Defs
-- name    : LPCA_Solutions_LPCA_KoszulModuleNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:57:00.869472+00:00
-- url     : https://prove2.me/theorems/82b571f6-ed02-4547-a0ec-94e33888a364
-- title:
--   Koszul Module Naturality for localized persistent commutative algebra
-- statement:
--   This bundle supplies koszul Module Naturality for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual Koszul Hom diagrams are covariant by postcomposition in the module argument. Their exponent transitions are unchanged.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_KoszulModuleNaturality.lean, selected declarations in lines 18–83; source SHA-256 9ebaa11c633c186cf802a59b83eb8ead05e9458a53893ec6071e550a47e12178; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
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

/-- The actual Koszul Hom diagrams are covariant by postcomposition in
the module argument. Their exponent transitions are unchanged. -/
noncomputable def coordinateKoszulYonedaModuleMap
    (rank : V ↪ ℕ) (T : Finset V)
    {M N : ModuleCat.{u} (MvPolynomial V k)} (f : M ⟶ N) :
    coordinateKoszulYonedaDiagram k rank T M ⟶
      coordinateKoszulYonedaDiagram k rank T N where
  app n := linearYonedaModuleMap (MvPolynomial V k) (coordinateKoszulComplex k rank n T) f
  naturality n m g := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

noncomputable def coordinateKoszulExtModuleMap
    (T : Finset V) (q : ℕ)
    {M N : ModuleCat.{u} (MvPolynomial V k)} (f : M ⟶ N) :
    coordinateKoszulExtDiagram k T q M ⟶ coordinateKoszulExtDiagram k T q N :=
  whiskerLeft ((opOpEquivalence ℕ).inverse ⋙
    localCohomology.diagram (coordinatePowersDiagram k T) q)
      ((evaluation (ModuleCat.{u} (MvPolynomial V k))
        (ModuleCat.{u} (MvPolynomial V k))).map f)

theorem coordinateKoszulExtDiagramIso_module_naturality
    (rank : V ↪ ℕ) (T : Finset V) (q : ℕ)
    {M N : ModuleCat.{u} (MvPolynomial V k)} (f : M ⟶ N) :
    coordinateKoszulExtModuleMap k T q f ≫ (coordinateKoszulExtDiagramIso k rank T q N).hom =
      (coordinateKoszulExtDiagramIso k rank T q M).hom ≫
        whiskerRight (coordinateKoszulYonedaModuleMap k rank T f)
          (homologyFunctor (ModuleCat.{u} (MvPolynomial V k)) (ComplexShape.up ℕ) q) := by
  apply NatTrans.ext
  funext n
  exact legacyIsoExt_module_naturality (MvPolynomial V k)
    (coordinateKoszulResolution k rank n T) f q



@[reassoc] theorem coordinateKoszulExtColimitIso_module_naturality
    (rank : V ↪ ℕ) (T : Finset V) (q : ℕ)
    {M N : ModuleCat.{u} (MvPolynomial V k)} (f : M ⟶ N) :
    colim.map (coordinateKoszulExtModuleMap k T q f) ≫
        (coordinateKoszulExtColimitIso k rank T q N).hom =
      (coordinateKoszulExtColimitIso k rank T q M).hom ≫
        homologyMap (colim.map (coordinateKoszulYonedaModuleMap k rank T f)) q := by
  change colim.map (coordinateKoszulExtModuleMap k T q f) ≫
      (colim.map (coordinateKoszulExtDiagramIso k rank T q N).hom ≫
        (filteredColimitHomologyIso (MvPolynomial V k)
          (coordinateKoszulYonedaDiagram k rank T N) q).hom) =
    (colim.map (coordinateKoszulExtDiagramIso k rank T q M).hom ≫
        (filteredColimitHomologyIso (MvPolynomial V k)
          (coordinateKoszulYonedaDiagram k rank T M) q).hom) ≫ _
  rw [← Category.assoc, ← Functor.map_comp,
    coordinateKoszulExtDiagramIso_module_naturality, Functor.map_comp]
  simp only [Category.assoc]
  rw [filteredColimitHomologyIso_naturality]

end LPCA


