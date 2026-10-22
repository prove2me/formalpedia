-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FaceLabelNaturality_Defs
-- name    : LPCA_Solutions_LPCA_FaceLabelNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:50:15.235448+00:00
-- url     : https://prove2.me/theorems/f63d0954-100c-4f81-8797-16c605b1ecba
-- title:
--   Face Label Naturality for localized persistent commutative algebra
-- statement:
--   This bundle supplies face Label Naturality for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Remove unused ambient vertex labels from the actual face indices.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FaceLabelNaturality.lean, selected declarations in lines 17–106; source SHA-256 074dec945d7f1672e16258a34c8ff76b02dda11e41b774ae7b603c61f57e3920; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
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

open CategoryTheory HomologicalComplex

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]

/-- Remove unused ambient vertex labels from the actual face indices. -/
noncomputable abbrev offsetFaceLabelEquiv (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (m n : ℤ) :
    OffsetFaceIndex (restrictComplex K e) m n ≃ OffsetFaceIndex K m n :=
  { Equiv.ofBijective
      (fun F : OffsetFaceIndex (restrictComplex K e) m n =>
        (⟨F.1.map e, (mem_restrictComplex K e F.1).mp F.property.1,
          by simpa only [Finset.card_map] using F.property.2⟩ : OffsetFaceIndex K m n)) (by
      constructor
      · intro F G h
        apply Subtype.ext
        exact Finset.map_injective e (congrArg Subtype.val h)
      · intro G
        let F := G.1.preimage e e.injective.injOn
        have hmap : F.map e = G.1 := by
          ext v
          constructor
          · intro hv
            obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
            exact Finset.mem_preimage.mp hw
          · intro hv
            obtain ⟨w, rfl⟩ := hK G.1 G.property.1 v hv
            exact Finset.mem_map.mpr ⟨w, Finset.mem_preimage.mpr hv, rfl⟩
        have hF : F ∈ (restrictComplex K e).faces :=
          (mem_restrictComplex K e F).mpr (hmap ▸ G.property.1)
        have hc : (F.card : ℤ) = n - m := by
          rw [← Finset.card_map e, hmap]
          exact G.property.2
        exact ⟨⟨F, hF, hc⟩, Subtype.ext hmap⟩) with
    toFun := fun F => ⟨F.1.map e, (mem_restrictComplex K e F.1).mp F.property.1,
      by simpa only [Finset.card_map] using F.property.2⟩ }

variable (k : Type u) [Field k]

noncomputable def offsetFaceLabelTermEquiv (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (m n : ℤ) :
    (OffsetFaceIndex K m n → k) ≃ₗ[k]
      (OffsetFaceIndex (restrictComplex K e) m n → k) :=
  LinearEquiv.funCongrLeft k k (offsetFaceLabelEquiv K e hK m n)

theorem offsetFaceLabelTermEquiv_differential (rank : V ↪ ℕ)
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (m n : ℤ)
    (x : OffsetFaceIndex K m n → k) :
    offsetFaceLabelTermEquiv k K e hK m (n + 1)
        (offsetFaceDifferential k rank K m n x) =
      offsetFaceDifferential k (e.trans rank) (restrictComplex K e) m n
        (offsetFaceLabelTermEquiv k K e hK m n x) := by
  classical
  funext H
  change (∑ F : OffsetFaceIndex K m n,
      cechCoefficient k rank F.1 (H.1.map e) * x F) =
    ∑ G : OffsetFaceIndex (restrictComplex K e) m n,
      cechCoefficient k (e.trans rank) G.1 H.1 *
        x (offsetFaceLabelEquiv K e hK m n G)
  rw [← Equiv.sum_comp (offsetFaceLabelEquiv K e hK m n)]
  apply Finset.sum_congr rfl
  intro G _
  rw [show (offsetFaceLabelEquiv K e hK m n G).1 = G.1.map e from rfl,
    cechCoefficient_map]

noncomputable def offsetFaceLabelComplexIso (rank : V ↪ ℕ)
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (m : ℤ) :
    offsetFaceComplex k rank K m ≅
      offsetFaceComplex k (e.trans rank) (restrictComplex K e) m := by
  refine Hom.isoOfComponents
    (fun n => (offsetFaceLabelTermEquiv k K e hK m n).toModuleIso) ?_
  intro p q hpq
  change p + 1 = q at hpq
  subst q
  rw [offsetFaceComplex_d, offsetFaceComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (offsetFaceLabelTermEquiv_differential k rank K e hK m p x).symm

@[reassoc] theorem offsetFaceLabelComplexIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (hL : ∀ F ∈ L.faces, ∀ v ∈ F, v ∈ Set.range e) (m : ℤ) :
    offsetFaceRestriction k rank h m ≫ (offsetFaceLabelComplexIso k rank K e hK m).hom =
      (offsetFaceLabelComplexIso k rank L e hL m).hom ≫
        offsetFaceRestriction k (e.trans rank) (restrictComplex_faces_mono h e) m := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl





end LPCA


