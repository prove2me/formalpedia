-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
-- name    : LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:29:37.521044+00:00
-- url     : https://prove2.me/theorems/ab8298bd-6e77-4000-9da0-732196363f90
-- title:
--   Hochster Cochain Comparison for localized persistent commutative algebra
-- statement:
--   This bundle supplies hochster Cochain Comparison for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The same intrinsic face indices with an arbitrary integer offset.
--   - Intrinsic signed reduced face cochains with a degree offset. No categorical shift functor, and hence no extra differential sign, is used.
--   - The signed link comparison on scalar coordinates.
--   - The ordinary signed face differential in these coordinates.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_HochsterCochainComparison.lean, selected declarations in lines 16–99; source SHA-256 bf5572cadf5fba5d3e344b3daeb70ecba398393dfb45e898b4cca3cba2139ed5; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Embedding.Restriction
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
import Mathlib.Tactic.Ring
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- The same intrinsic face indices with an arbitrary integer offset. -/
abbrev OffsetFaceIndex (K : Complex V) (m n : ℤ) : Type u :=
  {G : Finset V // G ∈ K.faces ∧ (G.card : ℤ) = n - m}

def hochsterOffsetBasisEquiv (K : Complex V) (a : V → ℤ) (q : ℕ)
    (ha : positiveSupport a = ∅) :
    CechBasis K Finset.univ a q ≃
      OffsetFaceIndex (link K (negativeSupport a)) (negativeSupport a).card (q : ℤ) :=
  (hochsterLinkBasisEquiv K a q ha).trans
    (Equiv.subtypeEquivRight (fun G => by
      change (G ∈ (link K (negativeSupport a)).faces ∧
          (G.card : ℤ) = ((q : ℤ) - ((negativeSupport a).card : ℤ) - 1) + 1) ↔
        (G ∈ (link K (negativeSupport a)).faces ∧
          (G.card : ℤ) = (q : ℤ) - ((negativeSupport a).card : ℤ))
      simp only [sub_add_cancel]))

variable (k : Type u) [Field k]

/-- Intrinsic signed reduced face cochains with a degree offset. No
categorical shift functor, and hence no extra differential sign, is used. -/
noncomputable def offsetFaceComplex (rank : V ↪ ℕ) (K : Complex V) (m : ℤ) :
    CochainComplex (ModuleCat.{u} k) ℤ := by
  letI : LinearOrder V := rankLinearOrder rank
  exact Proofs.BassLyubeznik.BassStatic.redCochain k (toSignedComplex K) m

/-- The signed link comparison on scalar coordinates. -/
noncomputable def hochsterModelLinkEquiv (rank : V ↪ ℕ) (K : Complex V)
    (a : V → ℤ) (q : ℕ) (ha : positiveSupport a = ∅) :
    (CechBasis K Finset.univ a q → k) ≃ₗ[k]
      (OffsetFaceIndex (link K (negativeSupport a)) (negativeSupport a).card (q : ℤ) → k) :=
  (LinearEquiv.funCongrLeft k k (hochsterOffsetBasisEquiv K a q ha).symm).trans
    { toFun := fun x G => hochsterSign k rank (negativeSupport a) G.1 * x G
      invFun := fun x G => hochsterSign k rank (negativeSupport a) G.1 * x G
      left_inv := fun x => by
        funext G
        change hochsterSign k rank (negativeSupport a) G.1 *
          (hochsterSign k rank (negativeSupport a) G.1 * x G) = x G
        rw [← mul_assoc, hochsterSign_mul_self, one_mul]
      right_inv := fun x => by
        funext G
        change hochsterSign k rank (negativeSupport a) G.1 *
          (hochsterSign k rank (negativeSupport a) G.1 * x G) = x G
        rw [← mul_assoc, hochsterSign_mul_self, one_mul]
      map_add' := fun x y => by funext G; exact mul_add _ _ _
      map_smul' := fun c x => by
        funext G
        change hochsterSign k rank (negativeSupport a) G.1 * (c * x G) =
          c * (hochsterSign k rank (negativeSupport a) G.1 * x G)
        ring }

/-- The ordinary signed face differential in these coordinates. -/
noncomputable def offsetFaceDifferential (rank : V ↪ ℕ) (K : Complex V) (m n : ℤ) :
    (OffsetFaceIndex K m n → k) →ₗ[k] (OffsetFaceIndex K m (n + 1) → k) := by
  letI : LinearOrder V := rankLinearOrder rank
  exact Proofs.BassLyubeznik.BassStatic.Signed.dLin k
    (Proofs.BassLyubeznik.SrFamily.faceFamily (toSignedComplex K)) m n

theorem hochsterModelLinkEquiv_differential (rank : V ↪ ℕ) (K : Complex V)
    (a : V → ℤ) (q : ℕ) (ha : positiveSupport a = ∅)
    (f : CechBasis K Finset.univ a q → k) :
    hochsterModelLinkEquiv k rank K a (q + 1) ha
        (basisDifferential k (cechCoefficient k rank) K Finset.univ a q f) =
      offsetFaceDifferential k rank (link K (negativeSupport a))
        (negativeSupport a).card (q : ℤ)
        (hochsterModelLinkEquiv k rank K a q ha f) := by
  classical
  funext H
  change hochsterSign k rank (negativeSupport a) H.1 *
      (∑ F : CechBasis K Finset.univ a q,
        cechCoefficient k rank F.1 (negativeSupport a ∪ H.1) * f F) =
    ∑ G : OffsetFaceIndex (link K (negativeSupport a)) (negativeSupport a).card (q : ℤ),
      cechCoefficient k rank G.1 H.1 *
        (hochsterSign k rank (negativeSupport a) G.1 *
          f ((hochsterOffsetBasisEquiv K a q ha).symm G))
  rw [← Equiv.sum_comp (hochsterOffsetBasisEquiv K a q ha).symm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G _
  change hochsterSign k rank (negativeSupport a) H.1 *
      (cechCoefficient k rank (negativeSupport a ∪ G.1) (negativeSupport a ∪ H.1) *
        f ((hochsterOffsetBasisEquiv K a q ha).symm G)) = _
  have hG := (Finset.mem_filter.mp G.property.1).2.1.symm
  have hH := (Finset.mem_filter.mp H.property.1).2.1.symm
  rw [← mul_assoc, hochsterSign_incidence k rank (negativeSupport a) G.1 H.1 hG hH]
  ring

end LPCA


