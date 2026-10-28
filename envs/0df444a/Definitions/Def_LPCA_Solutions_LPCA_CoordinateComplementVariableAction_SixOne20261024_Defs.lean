-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateComplementVariableAction_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateComplementVariableAction_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T21:15:46.419465+00:00
-- url     : https://prove2.me/theorems/19f5b25e-586b-48f5-bb5a-e80ce94c2565
-- title:
--   Coordinate Complement Variable Action — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for coordinate complement variable action used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Fixed-support charts preserve actual multiplication by every native
--   complement variable, including transitions between negative, zero and positive
--   complement degrees.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CoordinateComplementVariableAction.lean, selected declarations in lines 18–124; source SHA-256 22cb5e3dc639c4f9311c451f0261d8a824f5fe50d45409596242b6cb93181da7; exact-source certificate Sapelo2 job 49296539.

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
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Ideal
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
import Definitions.Def_LPCA_Solutions_LPCA_CanonicalFaceOffset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableMaps_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCechVariables_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateBasis_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateBooleanDiagram_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCechComparison_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateComplementComparison_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedSupportComparison_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceOffsetNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCoordinates_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_LinkIdentities_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexAttachmentNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplementAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexPiecePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexTensorTarget_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

theorem eraseCoordinateDegree_increment_not_mem (U : Finset V) (a b : V → ℤ) (j : V)
    (hj : j ∉ U) (hab : ∀ v, b v = a v + if v = j then 1 else 0) :
    ∀ v, eraseCoordinateDegree U b v = eraseCoordinateDegree U a v + if v = j then 1 else 0 := by
  intro v
  by_cases hv : v ∈ U
  · have hne : v ≠ j := fun he => hj (he ▸ hv)
    simp [eraseCoordinateDegree, hv, hne]
  · simpa only [eraseCoordinateDegree, if_neg hv] using hab v

variable (k : Type u) [Field k]

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

noncomputable local instance (priority := 3000) coordinateComplementVariableTermAddCommMonoid
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    AddCommMonoid (LocalizedCechTerm k K T a p) :=
  (localizedTermAddCommGroup k K T a p).toAddCommMonoid

/-- Fixed-support charts preserve actual multiplication by every native
complement variable, including transitions between negative, zero and positive
complement degrees. -/
theorem coordinateFixedSupport_actualVariable_compatibility (K : Complex V)
    (U A T : Finset V) (a b : V → ℤ) (j : V) (p : ℕ)
    (hj : j ∉ U) (hTU : Disjoint T U)
    (ha : ∀ v ∈ U, 0 ≤ a v) (hb : ∀ v ∈ U, 0 ≤ b v)
    (hA : coordinatePositivePart U a = A) (hB : coordinatePositivePart U b = A)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0)
    (y : LocalizedCechTerm k K T a p) :
    coordinateFixedSupportActualTermEquiv k K U A T b p hTU hb hB
        (actualTermVariableMap k K T a b j p hab y) =
      actualTermVariableMap k (coordinateLink K U A) T
        (eraseCoordinateDegree U a) (eraseCoordinateDegree U b) j p
        (eraseCoordinateDegree_increment_not_mem U a b j hj hab)
        (coordinateFixedSupportActualTermEquiv k K U A T a p hTU ha hA y) := by
  classical
  apply (actualTermEquivModel k (coordinateLink K U A) T (eraseCoordinateDegree U b) p).injective
  change actualToModel k (coordinateLink K U A) T (eraseCoordinateDegree U b) p _ =
    actualToModel k (coordinateLink K U A) T (eraseCoordinateDegree U b) p _
  rw [coordinateFixedSupportActualTermEquiv_coordinates]
  funext G
  change actualToModel k K T b p (actualTermVariableMap k K T a b j p hab y)
    ((coordinateFixedSupportBasisEquiv K U A T b p hTU hb hB).symm G) = _
  rw [actualTermVariableMap_coordinates, actualTermVariableMap_coordinates]
  change (if hc : LocalizationCriterion K G.1 a then
    (pieceCoordinateEquiv k K G.1 a hc).symm (y ⟨G.1, G.2.1, G.2.2.1⟩) else 0) = _
  have he : LocalizationCriterion K G.1 a ↔
      LocalizationCriterion (coordinateLink K U A) G.1 (eraseCoordinateDegree U a) := by
    have ht := criterion_coordinate_degree K U T G.1 a hTU G.2.1 ha
    rw [hA] at ht
    exact ht
  by_cases hc : LocalizationCriterion K G.1 a
  · have hc' := he.mp hc
    simp only [dif_pos hc, dif_pos hc']
    exact (congrFun (coordinateFixedSupportActualTermEquiv_coordinates k K U A T a p hTU ha hA y)
      ⟨G.1, G.2.1, G.2.2.1, hc'⟩).symm
  · have hc' : ¬ LocalizationCriterion (coordinateLink K U A) G.1 (eraseCoordinateDegree U a) :=
      fun h => hc (he.mpr h)
    simp only [dif_neg hc, dif_neg hc']

theorem coordinateFixedSupportCechComplexIso_variable (rank : V ↪ ℕ) (K : Complex V)
    (U A T : Finset V) (a b : V → ℤ) (j : V)
    (hj : j ∉ U) (hTU : Disjoint T U)
    (ha : ∀ v ∈ U, 0 ≤ a v) (hb : ∀ v ∈ U, 0 ≤ b v)
    (hA : coordinatePositivePart U a = A) (hB : coordinatePositivePart U b = A)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0) :
    localizedCechVariableMap k rank K T a b j hab ≫
        (coordinateFixedSupportCechComplexIso k rank K U A T b hTU hb hB).hom =
      (coordinateFixedSupportCechComplexIso k rank K U A T a hTU ha hA).hom ≫
        localizedCechVariableMap k rank (coordinateLink K U A) T
          (eraseCoordinateDegree U a) (eraseCoordinateDegree U b) j
          (eraseCoordinateDegree_increment_not_mem U a b j hj hab) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact coordinateFixedSupport_actualVariable_compatibility k K U A T a b j p hj hTU ha hb hA hB hab y

theorem coordinateFixedSupportComplementCechComplexIso_variable (rank : V ↪ ℕ) (K : Complex V)
    (U A : Finset V) (a b : V → ℤ) (j : {v : V // v ∉ U})
    (ha : ∀ v ∈ U, 0 ≤ a v) (hb : ∀ v ∈ U, 0 ≤ b v)
    (hA : coordinatePositivePart U a = A) (hB : coordinatePositivePart U b = A)
    (hab : ∀ v, b v = a v + if v = j.1 then 1 else 0) :
    localizedCechVariableMap k rank K (coordinateCechSupport U) a b j.1 hab ≫
        (coordinateFixedSupportComplementCechComplexIso k rank K U A b hb hB).hom =
      (coordinateFixedSupportComplementCechComplexIso k rank K U A a ha hA).hom ≫
        localizedCechVariableMap k ((coordinateComplementEmbedding U).trans rank)
          (coordinateComplementComplex K U A) Finset.univ
          (a ∘ coordinateComplementEmbedding U) (b ∘ coordinateComplementEmbedding U) j
          (increment_restrict (coordinateComplementEmbedding U) a b j hab) := by
  let e := coordinateComplementEmbedding U
  have hu := eraseCoordinateDegree_increment_not_mem U a b j.1 j.property hab
  have hs := coordinateFixedSupportCechComplexIso_variable k rank K U A (coordinateCechSupport U)
    a b j.1 j.property (coordinateCechSupport_disjoint U) ha hb hA hB hab
  have hr := restrictionCechComplexIso_variable k rank (coordinateLink K U A) e
    (coordinateLink_faces_in_complement K U A) Finset.univ
    (eraseCoordinateDegree U a) (eraseCoordinateDegree U b) j
    (eraseCoordinateDegree_zero_outside_complement U a)
    (eraseCoordinateDegree_zero_outside_complement U b) hu
  have ht := localizedCechVariableMap_transport k (e.trans rank)
    (coordinateComplementComplex K U A) Finset.univ
    (eraseCoordinateDegree U a ∘ e) (eraseCoordinateDegree U b ∘ e)
    (a ∘ e) (b ∘ e) j (eraseCoordinateDegree_complement U a) (eraseCoordinateDegree_complement U b)
    (increment_restrict e _ _ j hu) (increment_restrict e a b j hab)
  simp only [coordinateFixedSupportComplementCechComplexIso, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% hs]
  erw [reassoc_of% hr, ht]



end LPCA


