-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_PersistenceArrowInterleaving_Defs
-- name    : LPCA_Solutions_LPCA_PersistenceArrowInterleaving_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T01:06:55.968222+00:00
-- url     : https://prove2.me/theorems/ff756402-ac2a-402b-912e-ab71636bba25
-- title:
--   Interleavings in the arrow category of persistence functors
-- statement:
--   This bundle supplies interleavings in the arrow category of persistence functors. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Shift a literal commuting square of persistence natural transformations.
--   - An interleaving literally in Arrow of the persistence functor category. The shifted squares and both triangles are equalities of its actual morphisms.
--   - Bundle the specified diagram-of-arrows interleaving as literal shifted squares of persistence natural transformations. No component is changed.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_PersistenceArrowInterleaving.lean, selected declarations in lines 15–119; source SHA-256 b66d70f92546ec80eef9851f620b7989fbdfc97c009bb1ea4cc1f246ec43fd86; source certificate Sapelo2 job 49172236.

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
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
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
import Definitions.Def_LPCA_Solutions_LPCA_ArrowRangeFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CanonicalFaceOffset_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_FaceOffsetNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCoordinates_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FamilyHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCohomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterIncidence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterLinkTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterNonfaceVanishing_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterSigns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ImagePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyModuleNaturality_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReversedInterleaving_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Functor

universe u

def reversedShiftIndex (ε : ℝ) : OrderDual ℝ ⥤ OrderDual ℝ where
  obj t := OrderDual.toDual (OrderDual.ofDual t + ε)
  map {s t} h := homOfLE (show OrderDual.ofDual t + ε ≤ OrderDual.ofDual s + ε from
    add_le_add (leOfHom h) (le_refl ε))

variable (k : Type u) [Field k]

def reversedDoubleShiftIndexHom (ε : ℝ) (hε : 0 ≤ ε) (t : OrderDual ℝ) :
    (reversedShiftIndex ε).obj ((reversedShiftIndex ε).obj t) ⟶ t :=
  homOfLE (show OrderDual.toDual ((OrderDual.ofDual t + ε) + ε) ≤ t from
    twiceShift_le (OrderDual.ofDual t) ε hε)

/-- Shift a literal commuting square of persistence natural transformations. -/
def shiftedPersistenceSquare (ε : ℝ)
    {A B : Arrow (OrderDual ℝ ⥤ ModuleCat.{u} k)} (φ : A ⟶ B) :
    Arrow.mk (whiskerLeft (reversedShiftIndex ε) A.hom) ⟶
      Arrow.mk (whiskerLeft (reversedShiftIndex ε) B.hom) :=
  Arrow.homMk (whiskerLeft (reversedShiftIndex ε) φ.left)
    (whiskerLeft (reversedShiftIndex ε) φ.right) (by
      change whiskerLeft (reversedShiftIndex ε) φ.left ≫
          whiskerLeft (reversedShiftIndex ε) B.hom =
        whiskerLeft (reversedShiftIndex ε) A.hom ≫
          whiskerLeft (reversedShiftIndex ε) φ.right
      simpa only [whiskerLeft_comp] using
        congrArg (fun a => whiskerLeft (reversedShiftIndex ε) a) (Arrow.w φ))

def persistenceDoubleTransition (F : OrderDual ℝ ⥤ ModuleCat.{u} k)
    (ε : ℝ) (hε : 0 ≤ ε) :
    reversedShiftIndex ε ⋙ (reversedShiftIndex ε ⋙ F) ⟶ F where
  app t := F.map (reversedDoubleShiftIndexHom ε hε t)
  naturality s t h := by
    exact (F.map_comp ((reversedShiftIndex ε).map ((reversedShiftIndex ε).map h))
      (reversedDoubleShiftIndexHom ε hε t)).symm.trans
        ((congrArg (fun a => F.map a) (Subsingleton.elim _ _)).trans
          (F.map_comp (reversedDoubleShiftIndexHom ε hε s) h))

def persistenceDoubleTransitionSquare
    {F G : OrderDual ℝ ⥤ ModuleCat.{u} k} (τ : F ⟶ G) (ε : ℝ) (hε : 0 ≤ ε) :
    Arrow.mk (whiskerLeft (reversedShiftIndex ε) (whiskerLeft (reversedShiftIndex ε) τ)) ⟶
      Arrow.mk τ :=
  Arrow.homMk (persistenceDoubleTransition k F ε hε)
    (persistenceDoubleTransition k G ε hε) (by
      apply NatTrans.ext
      funext t
      exact τ.naturality (reversedDoubleShiftIndexHom ε hε t))

/-- An interleaving literally in Arrow of the persistence functor category.
The shifted squares and both triangles are equalities of its actual morphisms. -/
structure PersistenceArrowInterleaving
    {F₀ F₁ G₀ G₁ : OrderDual ℝ ⥤ ModuleCat.{u} k}
    (τ : F₀ ⟶ F₁) (σ : G₀ ⟶ G₁) (ε : ℝ) where
  nonneg : 0 ≤ ε
  forward : Arrow.mk (whiskerLeft (reversedShiftIndex ε) τ) ⟶ Arrow.mk σ
  backward : Arrow.mk (whiskerLeft (reversedShiftIndex ε) σ) ⟶ Arrow.mk τ
  left_triangle : shiftedPersistenceSquare k ε forward ≫ backward =
    persistenceDoubleTransitionSquare k τ ε nonneg
  right_triangle : shiftedPersistenceSquare k ε backward ≫ forward =
    persistenceDoubleTransitionSquare k σ ε nonneg

/-- Bundle the specified diagram-of-arrows interleaving as literal shifted
squares of persistence natural transformations. No component is changed. -/
noncomputable def PersistenceArrowInterleaving.ofDiagram
    {F₀ F₁ G₀ G₁ : OrderDual ℝ ⥤ ModuleCat.{u} k}
    {τ : F₀ ⟶ F₁} {σ : G₀ ⟶ G₁} {ε : ℝ}
    (α : ReversedInterleaving (arrowPersistence k τ) (arrowPersistence k σ) ε) :
    PersistenceArrowInterleaving k τ σ ε where
  nonneg := α.nonneg
  forward := Arrow.homMk
    { app := fun t => (α.forward (OrderDual.ofDual t)).left
      naturality := fun s t h => congrArg (fun φ => φ.left)
        (α.forward_naturality (OrderDual.ofDual t) (OrderDual.ofDual s) (leOfHom h)) }
    { app := fun t => (α.forward (OrderDual.ofDual t)).right
      naturality := fun s t h => congrArg (fun φ => φ.right)
        (α.forward_naturality (OrderDual.ofDual t) (OrderDual.ofDual s) (leOfHom h)) }
    (by
      apply NatTrans.ext
      funext t
      exact Arrow.w (α.forward (OrderDual.ofDual t)))
  backward := Arrow.homMk
    { app := fun t => (α.backward (OrderDual.ofDual t)).left
      naturality := fun s t h => congrArg (fun φ => φ.left)
        (α.backward_naturality (OrderDual.ofDual t) (OrderDual.ofDual s) (leOfHom h)) }
    { app := fun t => (α.backward (OrderDual.ofDual t)).right
      naturality := fun s t h => congrArg (fun φ => φ.right)
        (α.backward_naturality (OrderDual.ofDual t) (OrderDual.ofDual s) (leOfHom h)) }
    (by
      apply NatTrans.ext
      funext t
      exact Arrow.w (α.backward (OrderDual.ofDual t)))
  left_triangle := by
    apply Arrow.hom_ext
    · apply NatTrans.ext
      funext t
      exact congrArg (fun φ => φ.left) (α.left_triangle (OrderDual.ofDual t))
    · apply NatTrans.ext
      funext t
      exact congrArg (fun φ => φ.right) (α.left_triangle (OrderDual.ofDual t))
  right_triangle := by
    apply Arrow.hom_ext
    · apply NatTrans.ext
      funext t
      exact congrArg (fun φ => φ.left) (α.right_triangle (OrderDual.ofDual t))
    · apply NatTrans.ext
      funext t
      exact congrArg (fun φ => φ.right) (α.right_triangle (OrderDual.ofDual t))

end LPCA


