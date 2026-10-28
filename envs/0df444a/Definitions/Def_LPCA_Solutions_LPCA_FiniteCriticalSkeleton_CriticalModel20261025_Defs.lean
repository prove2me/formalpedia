-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FiniteCriticalSkeleton_CriticalModel20261025_Defs
-- name    : LPCA_Solutions_LPCA_FiniteCriticalSkeleton_CriticalModel20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T02:24:33.79586+00:00
-- url     : https://prove2.me/theorems/8ca342c2-5bab-4c90-b4d1-34258e686f04
-- title:
--   Finite Critical Skeleton — finite critical-level dependencies
-- statement:
--   Selected constructions and proved compatibility results for finite critical skeleton, used in the exact finite critical-level model of original homogeneous Ext persistence. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   The finite ordered set of initial subsets of the actual critical values.
--
--   A real level determines its literal lower subset of critical weights.
--
--   The same original face family selected by a finite critical cut.
--
--   Actual homogeneous Ext persistence over the finite critical-cut order.
--
--   Exact factorization of the original real-indexed functor through a finite
--   linear order, with every original quotient-induced map retained.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Theorem3.10, its finite-critical-value part, with formalization dependencies. Certified Lean source: Solutions/LPCA_FiniteCriticalSkeleton.lean, selected declarations in lines 17–141; source SHA-256 06c053bbd44eb615d76f9d49a3e8f1e1d5911776d384599132b31138ec60000b; exact-source certificate Sapelo2 job 49311704.

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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.UpperLower.CompleteLattice
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
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFiniteLevels_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteCochainHomology_CriticalModel20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_MinusOne20261025_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V]

abbrev CriticalWeight (K : Complex V) (f : Finset V → ℝ) :=
  {r : ℝ // r ∈ filtrationCriticalValues K f}

/-- The finite ordered set of initial subsets of the actual critical values. -/
abbrev CriticalCut (K : Complex V) (f : Finset V → ℝ) :=
  LowerSet (CriticalWeight K f)

noncomputable instance criticalCutFintype (K : Complex V) (f : Finset V → ℝ) :
    Fintype (CriticalCut K f) := by
  classical
  exact Fintype.ofInjective (fun D : CriticalCut K f => (D : Set (CriticalWeight K f)))
    SetLike.coe_injective

def faceCriticalWeight (K : Complex V) (f : Finset V → ℝ)
    (F : Finset V) (hF : F ∈ K.faces) : CriticalWeight K f :=
  ⟨f F, Finset.mem_image.mpr ⟨F, hF, rfl⟩⟩

/-- A real level determines its literal lower subset of critical weights. -/
def criticalCutAt (K : Complex V) (f : Finset V → ℝ) (t : ℝ) : CriticalCut K f :=
  ⟨{r | r.1 ≤ t}, by
    intro a b hab ha
    change b.1 ≤ t
    change a.1 ≤ t at ha
    exact (show b.1 ≤ a.1 from hab).trans ha⟩

theorem criticalCutAt_mono (K : Complex V) (f : Finset V → ℝ) :
    Monotone (criticalCutAt K f) := by
  intro s t hst r hr
  change r.1 ≤ t
  change r.1 ≤ s at hr
  exact hr.trans hst

/-- The same original face family selected by a finite critical cut. -/
noncomputable def criticalCutComplex (K : Complex V) (f : Finset V → ℝ)
    (hf : FiltrationMonotone K f) (D : CriticalCut K f) : Complex V := by
  classical
  exact
    { faces := K.faces.filter (fun F => ∃ hF : F ∈ K.faces, faceCriticalWeight K f F hF ∈ D)
      down_closed := by
        intro F G hF hGF
        obtain ⟨hFK, hFK', hFD⟩ := Finset.mem_filter.mp hF
        have hGK : G ∈ K.faces := K.down_closed hFK hGF
        refine Finset.mem_filter.mpr ⟨hGK, hGK, ?_⟩
        exact D.lower (show faceCriticalWeight K f G hGK ≤ faceCriticalWeight K f F hFK'
          from hf hFK hGF) hFD }

theorem mem_criticalCutComplex (K : Complex V) (f : Finset V → ℝ)
    (hf : FiltrationMonotone K f) (D : CriticalCut K f) (F : Finset V) :
    F ∈ (criticalCutComplex K f hf D).faces ↔
      ∃ hF : F ∈ K.faces, faceCriticalWeight K f F hF ∈ D := by
  classical
  simp only [criticalCutComplex, Finset.mem_filter]
  exact ⟨fun h => h.2, fun ⟨hF, hFD⟩ => ⟨hF, hF, hFD⟩⟩

theorem criticalCutComplex_mono (K : Complex V) (f : Finset V → ℝ)
    (hf : FiltrationMonotone K f) : Monotone (fun D => (criticalCutComplex K f hf D).faces) := by
  intro D E hDE F hF
  obtain ⟨hFK, hFD⟩ := (mem_criticalCutComplex K f hf D F).mp hF
  exact (mem_criticalCutComplex K f hf E F).mpr ⟨hFK, hDE hFD⟩

theorem criticalCutComplex_at (K : Complex V) (f : Finset V → ℝ)
    (hf : FiltrationMonotone K f) (t : ℝ) :
    criticalCutComplex K f hf (criticalCutAt K f t) = level K f hf t := by
  apply Complex.ext_faces
  ext F
  rw [mem_criticalCutComplex]
  constructor
  · rintro ⟨hF, hFt⟩
    change f F ≤ t at hFt
    exact Finset.mem_filter.mpr ⟨hF, hFt⟩
  · intro hF
    obtain ⟨hFK, hFt⟩ := Finset.mem_filter.mp hF
    refine ⟨hFK, ?_⟩
    change f F ≤ t
    exact hFt

noncomputable def criticalCutFunctor (K : Complex V) (f : Finset V → ℝ) :
    OrderDual ℝ ⥤ OrderDual (CriticalCut K f) where
  obj t := OrderDual.toDual (criticalCutAt K f (OrderDual.ofDual t))
  map h := homOfLE (criticalCutAt_mono K f (leOfHom h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable (k : Type u) [Field k] [Fintype V]

/-- Actual homogeneous Ext persistence over the finite critical-cut order. -/
noncomputable def criticalCutPiecePersistence (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    OrderDual (CriticalCut K f) ⥤ ModuleCat.{u} k where
  obj D := ModuleCat.of k
    (supportCohomologyPiece k rank (criticalCutComplex K f hf (OrderDual.ofDual D)) T a q)
  map h := supportCohomologyPieceRestriction k rank (criticalCutComplex_mono K f hf (leOfHom h)) T a q
  map_id _ := supportCohomologyPieceRestriction_refl k rank _ T a q
  map_comp _ _ := (supportCohomologyPieceRestriction_comp k rank _ _ T a q).symm

theorem supportPieceRestriction_congr (rank : V ↪ ℕ)
    {K K' L L' : Complex V} (h : K.faces ⊆ L.faces) (h' : K'.faces ⊆ L'.faces)
    (hK : K = K') (hL : L = L') (T : Finset V) (a : V → ℤ) (q : ℕ) :
    supportCohomologyPieceRestriction k rank h T a q ≫
        (eqToIso (congrArg (fun C => ModuleCat.of k (supportCohomologyPiece k rank C T a q)) hK)).hom =
      (eqToIso (congrArg (fun C => ModuleCat.of k (supportCohomologyPiece k rank C T a q)) hL)).hom ≫
        supportCohomologyPieceRestriction k rank h' T a q := by
  subst K'
  subst L'
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- Exact factorization of the original real-indexed functor through a finite
linear order, with every original quotient-induced map retained. -/
noncomputable def criticalCutPiecePersistenceIso (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    supportCohomologyPiecePersistence k rank K f hf T a q ≅
      criticalCutFunctor K f ⋙ criticalCutPiecePersistence k rank K f hf T a q :=
  NatIso.ofComponents
    (fun t => eqToIso (congrArg (fun C => ModuleCat.of k (supportCohomologyPiece k rank C T a q))
      (criticalCutComplex_at K f hf (OrderDual.ofDual t)).symm))
    (fun h => supportPieceRestriction_congr k rank _ _
      (criticalCutComplex_at K f hf _).symm (criticalCutComplex_at K f hf _).symm T a q)

theorem criticalCutPiecePersistence_pointwise_finite (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f)
    (T : Finset V) (a : V → ℤ) (q : ℕ) (D : OrderDual (CriticalCut K f)) :
    FiniteDimensional k ((criticalCutPiecePersistence k rank K f hf T a q).obj D) :=
  finiteDimensional_supportCohomologyPiece k rank _ T a q



end LPCA


