-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ReducedNegativeOne_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_ReducedNegativeOne_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:36:16.92999+00:00
-- url     : https://prove2.me/theorems/4e7e363d-fda3-4fb5-8570-ad8d7307a971
-- title:
--   Reduced Negative One — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for reduced negative one, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   A scalar comparison at every complex, including void and ghost cases.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_ReducedNegativeOne.lean, selected declarations in lines 18–160; source SHA-256 eef5dc91fafa2c828b997a534da6f8b9522095e33b52cef5caa0c61b9fda37fb; exact-source certificate Sapelo2 job 49311470.

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
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.WithBot
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
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableMaps_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_FaceCofaceIntervals_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LinkIdentities_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem offsetFaceIndex_negOne_eq_empty (K : Complex V)
    (F : OffsetFaceIndex K (-1) (-1)) : F.1 = ∅ := by
  have hc := F.property.2
  exact Finset.card_eq_zero.mp (by omega)

instance offsetFaceIndexNegOne_subsingleton (K : Complex V) :
    Subsingleton (OffsetFaceIndex K (-1) (-1)) :=
  ⟨fun F G => Subtype.ext ((offsetFaceIndex_negOne_eq_empty K F).trans
    (offsetFaceIndex_negOne_eq_empty K G).symm)⟩

noncomputable def reducedNegativeOneTermIso (rank : V ↪ ℕ) (K : Complex V)
    (he : ∅ ∈ K.faces) :
    (reducedFaceComplex k rank K).X (-1) ≅ ModuleCat.of k k := by
  letI : Unique (OffsetFaceIndex K (-1) (-1)) :=
    { default := ⟨∅, he, by norm_num⟩
      uniq := fun _ => Subsingleton.elim _ _ }
  exact (LinearEquiv.funUnique (OffsetFaceIndex K (-1) (-1)) k k).toModuleIso

theorem reducedNegativeOneIncoming_zero (rank : V ↪ ℕ) (K : Complex V) :
    (reducedFaceComplex k rank K).d (-2) (-1) = 0 :=
  (reducedFaceComplexComponent_isZero_below k rank K (-2) (by omega)).eq_of_src _ _

theorem reducedNegativeOneDifferential_injective (rank : V ↪ ℕ) (K : Complex V)
    (v : V) (hv : {v} ∈ K.faces) :
    Function.Injective (offsetFaceDifferential k rank K (-1) (-1)) := by
  classical
  letI : LinearOrder V := rankLinearOrder rank
  have he : ∅ ∈ K.faces := K.down_closed hv (Finset.empty_subset _)
  let E : OffsetFaceIndex K (-1) (-1) := ⟨∅, he, by norm_num⟩
  let J : OffsetFaceIndex K (-1) 0 := ⟨{v}, hv, by simp⟩
  letI : Unique (OffsetFaceIndex K (-1) (-1)) :=
    { default := E, uniq := fun _ => Subsingleton.elim _ _ }
  have h_eval (x : OffsetFaceIndex K (-1) (-1) → k) :
      offsetFaceDifferential k rank K (-1) (-1) x J = x E := by
    change (∑ G : OffsetFaceIndex K (-1) (-1),
      Proofs.BassLyubeznik.SignedCore.inc k G.1 J.1 * x G) = x E
    rw [Fintype.sum_unique]
    change Proofs.BassLyubeznik.SignedCore.inc k ∅ {v} * x E = x E
    simp [Proofs.BassLyubeznik.SignedCore.inc, Proofs.BassLyubeznik.SignedCore.nu]
  intro x y hxy
  have heq : x E = y E := by
    rw [← h_eval x, ← h_eval y, hxy]
  funext F
  simpa only [Subsingleton.elim F E] using heq

theorem reducedNegativeOne_isZero_of_vertex (rank : V ↪ ℕ) (K : Complex V)
    (v : V) (hv : {v} ∈ K.faces) :
    IsZero (reducedFaceCohomology k rank K (-1)) := by
  let C := reducedFaceComplex k rank K
  have hinj : Function.Injective (C.d (-1) 0) := by
    have hd := offsetFaceComplex_d k rank K (-1) (-1)
    change C.d (-1) 0 = ModuleCat.ofHom
      (offsetFaceDifferential k rank K (-1) (-1)) at hd
    rw [hd]
    exact reducedNegativeOneDifferential_injective k rank K v hv
  apply ((C.sc (-1)).exact_iff_isZero_homology).mp
  apply (C.sc (-1)).moduleCat_exact_iff.mpr
  intro x hx
  have hn : (ComplexShape.up ℤ).next (-1) = 0 := by
    apply ComplexShape.next_eq'
    change (-1 : ℤ) + 1 = 0
    norm_num
  change (C.d (-1) ((ComplexShape.up ℤ).next (-1))) x = 0 at hx
  rw [hn] at hx
  have hx0 : x = 0 := hinj (by simpa using hx)
  exact ⟨0, by simp [hx0]⟩

theorem reducedNegativeOne_isZero_of_no_empty (rank : V ↪ ℕ) (K : Complex V)
    (he : ∅ ∉ K.faces) : IsZero (reducedFaceCohomology k rank K (-1)) := by
  haveI : IsEmpty (ReducedFaceIndex K (-1)) := ⟨fun F =>
    he ((reducedFaceIndex_negOne_iff K F.1).mp F.property).2⟩
  have hm : IsZero ((reducedFaceComplex k rank K).X (-1)) :=
    (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).of_iso
      (reducedFaceComplexComponentIso k rank K (-1))
  exact (((reducedFaceComplex k rank K).sc (-1)).exact_iff_isZero_homology).mp
    (ShortComplex.exact_of_isZero_X₂ _ hm)

theorem reducedNegativeOne_isZero_of_not_emptyFaceOnly (rank : V ↪ ℕ)
    (K : Complex V) (h : ¬ EmptyFaceOnly K) :
    IsZero (reducedFaceCohomology k rank K (-1)) := by
  classical
  by_cases he : ∅ ∈ K.faces
  · have hv : ∃ v : V, {v} ∈ K.faces := by
      by_contra hn
      exact h ((emptyFaceOnly_iff K).mpr ⟨he, by simpa using hn⟩)
    obtain ⟨v, hv⟩ := hv
    exact reducedNegativeOne_isZero_of_vertex k rank K v hv
  · exact reducedNegativeOne_isZero_of_no_empty k rank K he

theorem reducedNegativeOneOutgoing_zero_of_emptyFaceOnly (rank : V ↪ ℕ)
    (K : Complex V) (h : EmptyFaceOnly K) :
    (reducedFaceComplex k rank K).d (-1) 0 = 0 := by
  haveI : IsEmpty (ReducedFaceIndex K 0) := by
    refine ⟨fun F => ?_⟩
    have hF : F.1 = ∅ := Finset.mem_singleton.mp (h ▸ F.property.1)
    have hc := F.property.2
    rw [hF] at hc
    norm_num at hc
  have ht : IsZero ((reducedFaceComplex k rank K).X 0) :=
    (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).of_iso
      (reducedFaceComplexComponentIso k rank K 0)
  exact ht.eq_of_tgt _ _

noncomputable def reducedNegativeOneScalarIso (rank : V ↪ ℕ) (K : Complex V)
    (h : EmptyFaceOnly K) : reducedFaceCohomology k rank K (-1) ≅ ModuleCat.of k k :=
  ((reducedFaceComplex k rank K).isoHomologyπ (-2) (-1) (by
    apply ComplexShape.prev_eq'
    change (-2 : ℤ) + 1 = -1
    norm_num)
    (reducedNegativeOneIncoming_zero k rank K)).symm ≪≫
  (reducedFaceComplex k rank K).iCyclesIso (-1) 0 (by
    apply ComplexShape.next_eq'
    change (-1 : ℤ) + 1 = 0
    norm_num)
    (reducedNegativeOneOutgoing_zero_of_emptyFaceOnly k rank K h) ≪≫
  reducedNegativeOneTermIso k rank K ((emptyFaceOnly_iff K).mp h).1

/-- A scalar comparison at every complex, including void and ghost cases. -/
noncomputable def reducedNegativeOneIndicatorIso (rank : V ↪ ℕ) (K : Complex V) :
    reducedFaceCohomology k rank K (-1) ≅
      ModuleCat.of k (intervalScalarSpace k (EmptyFaceOnly K)) := by
  classical
  by_cases h : EmptyFaceOnly K
  · exact reducedNegativeOneScalarIso k rank K h ≪≫
      (intervalScalarEquivOfTrue k _ h).toModuleIso
  · exact (reducedNegativeOne_isZero_of_not_emptyFaceOnly k rank K h).iso
      (intervalScalarSpace_isZero k _ h)

theorem reducedNegativeOneIndicatorIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) :
    reducedFaceCohomologyRestriction k rank h (-1) ≫
        (reducedNegativeOneIndicatorIso k rank K).hom =
      (reducedNegativeOneIndicatorIso k rank L).hom ≫ ModuleCat.ofHom
        (intervalScalarMap k (EmptyFaceOnly L) (EmptyFaceOnly K)) := by
  classical
  by_cases hL : EmptyFaceOnly L
  · by_cases hK : EmptyFaceOnly K
    · have heq : K = L := Complex.ext_faces (hK.trans hL.symm)
      subst L
      rw [reducedFaceCohomologyRestriction_refl, intervalScalarMap_self]
      simp
    · exact (intervalScalarSpace_isZero k _ hK).eq_of_tgt _ _
  · exact (reducedNegativeOne_isZero_of_not_emptyFaceOnly k rank L hL).eq_of_src _ _

end LPCA


