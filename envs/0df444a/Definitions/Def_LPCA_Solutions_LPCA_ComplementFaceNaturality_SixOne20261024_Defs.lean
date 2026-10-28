-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_ComplementFaceNaturality_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:11:11.305305+00:00
-- url     : https://prove2.me/theorems/16e653c6-9e75-47c8-997c-2c874bfc01c3
-- title:
--   Complement Face Naturality — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for complement face naturality used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_ComplementFaceNaturality.lean, selected declarations in lines 23–116; source SHA-256 7bb81eba43b7ff4c5af8547c6065eea903758ce2ea7c5f868818a214d4a426ee; exact-source certificate Sapelo2 job 49296539.

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
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.CategoryTheory.Abelian.Ext
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
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableMaps_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W]
variable (k : Type u) [Field k]



theorem faceRingRename_restriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (e : W ↪ V) (r : FaceRing k (restrictComplex L e)) :
    faceRingRename k K e (faceRingRestriction k (restrictComplex_faces_mono h e) r) =
      faceRingRestriction k h (faceRingRename k L e r) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

theorem localizedRestrictionRingEquiv_restriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hL : ∀ F ∈ L.faces, ∀ v ∈ F, v ∈ Set.range e)
    (F : Finset W) (z : LocalizedFaceRing k (restrictComplex L e) F) :
    localizedRestrictionRingEquiv k K e hK F
        (localizedFaceRestriction k (restrictComplex_faces_mono h e) F z) =
      localizedFaceRestriction k h (F.map e)
        (localizedRestrictionRingEquiv k L e hL F z) := by
  have hn : (localizedRestrictionRingEquiv k K e hK F).toRingHom.comp
        (localizedFaceRestriction k (restrictComplex_faces_mono h e) F).toRingHom =
      (localizedFaceRestriction k h (F.map e)).toRingHom.comp
        (localizedRestrictionRingEquiv k L e hL F).toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (invertedMonomial k (restrictComplex L e) F))
    apply RingHom.ext
    intro r
    change localizedRestrictionRingEquiv k K e hK F
        (localizedFaceRestriction k (restrictComplex_faces_mono h e) F
          (algebraMap (FaceRing k (restrictComplex L e))
            (LocalizedFaceRing k (restrictComplex L e) F) r)) =
      localizedFaceRestriction k h (F.map e)
        (localizedRestrictionRingEquiv k L e hL F
          (algebraMap (FaceRing k (restrictComplex L e))
            (LocalizedFaceRing k (restrictComplex L e) F) r))
    rw [localizedFaceRestriction_base, localizedRestrictionRingEquiv_base,
      localizedRestrictionRingEquiv_base, localizedFaceRestriction_base]
    exact congrArg (algebraMap (FaceRing k K) (LocalizedFaceRing k K (F.map e)))
      (faceRingRename_restriction k h e r)
  exact RingHom.congr_fun hn z

variable [Fintype V] [Fintype W]

theorem localizedPieceRestrictionEquiv_restriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hL : ∀ F ∈ L.faces, ∀ v ∈ F, v ∈ Set.range e)
    (F : Finset W) (a : V → ℤ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0)
    (z : localizedPiece k (restrictComplex L e) F (a ∘ e)) :
    localizedPieceRestrictionEquiv k K e hK F a ha
        (pieceFaceRestriction k (restrictComplex_faces_mono h e) F (a ∘ e) z) =
      pieceFaceRestriction k h (F.map e) a
        (localizedPieceRestrictionEquiv k L e hL F a ha z) := by
  apply Subtype.ext
  exact localizedRestrictionRingEquiv_restriction k h e hK hL F z.1

theorem restrictionActualTermEquiv_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hL : ∀ F ∈ L.faces, ∀ v ∈ F, v ∈ Set.range e)
    (T : Finset W) (a : V → ℤ) (p : ℕ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0)
    (y : (localizedCechComplex k rank L (T.map e) a).X p) :
    restrictionActualTermEquiv k K e hK T a p ha
        (localizedCechTermRestriction k rank h (T.map e) a p y) =
      localizedCechTermRestriction k (e.trans rank) (restrictComplex_faces_mono h e)
        T (a ∘ e) p (restrictionActualTermEquiv k L e hL T a p ha y) := by
  funext F
  rw [restrictionActualTermEquiv_apply]
  apply (localizedPieceRestrictionEquiv k K e hK F.1 a ha).injective
  rw [LinearEquiv.apply_symm_apply]
  change pieceFaceRestriction k h (F.1.map e) a
      (y (restrictionCechSlotEquiv e T p F)) =
    localizedPieceRestrictionEquiv k K e hK F.1 a ha
      (pieceFaceRestriction k (restrictComplex_faces_mono h e) F.1 (a ∘ e)
        ((localizedPieceRestrictionEquiv k L e hL F.1 a ha).symm
          (y (restrictionCechSlotEquiv e T p F))))
  rw [localizedPieceRestrictionEquiv_restriction k h e hK hL F.1 a ha,
    LinearEquiv.apply_symm_apply]

@[reassoc] theorem restrictionCechComplexIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hL : ∀ F ∈ L.faces, ∀ v ∈ F, v ∈ Set.range e)
    (T : Finset W) (a : V → ℤ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0) :
    localizedCechRestriction k rank h (T.map e) a ≫
        (restrictionCechComplexIso k rank K e hK T a ha).hom =
      (restrictionCechComplexIso k rank L e hL T a ha).hom ≫
        localizedCechRestriction k (e.trans rank) (restrictComplex_faces_mono h e) T (a ∘ e) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact restrictionActualTermEquiv_restriction k rank h e hK hL T a p ha y

end LPCA


