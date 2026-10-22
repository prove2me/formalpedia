-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
-- name    : LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:13:51.586566+00:00
-- url     : https://prove2.me/theorems/6ca963f7-16bf-45ac-a57e-535f6527dad2
-- title:
--   Face Restriction Čech for localized persistent commutative algebra
-- statement:
--   This bundle supplies face Restriction Čech for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The quotient-induced map of the actual full ambient-linear Cech complexes, with the original signed localization differential.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FaceRestrictionCech.lean, selected declarations in lines 17–74; source SHA-256 500dec0c43aa70286c2ace05445a0ed097397df1d00af113b165b02f47d12090; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
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
import Mathlib.CategoryTheory.Category.Preorder
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
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
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

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem ambientFaceRestriction_entry (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F G : Finset V) :
    (ambientFaceRestriction k h G).hom.comp (ambientCechEntry k rank L F G) =
      (ambientCechEntry k rank K F G).comp (ambientFaceRestriction k h F).hom := by
  classical
  apply LinearMap.ext
  intro x
  by_cases hFG : F ⊆ G
  · simp only [LinearMap.comp_apply, ambientCechEntry, ambientLocalizationEntry,
      dif_pos hFG, LinearMap.smul_apply, map_smul]
    apply congrArg (fun z : ambientLocalizedModule k K G =>
      (MvPolynomial.C (cechCoefficient k rank F G) : MvPolynomial V k) • z)
    exact (congrArg (fun g => g x)
      (localizedFaceRestriction_localization k h F G hFG)).symm
  · simp only [LinearMap.comp_apply, ambientCechEntry, ambientLocalizationEntry,
      dif_neg hFG, LinearMap.zero_apply, smul_zero, map_zero]

noncomputable def ambientCechTermRestriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) (p : ℕ) :
    AmbientCechTerm k L T p →ₗ[MvPolynomial V k] AmbientCechTerm k K T p where
  toFun y F := ambientFaceRestriction k h F.1 (y F)
  map_add' x y := by
    funext F
    exact (ambientFaceRestriction k h F.1).hom.map_add (x F) (y F)
  map_smul' c x := by
    funext F
    exact (ambientFaceRestriction k h F.1).hom.map_smul c (x F)

theorem ambientCechTermRestriction_differential (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) (p : ℕ) (y : AmbientCechTerm k L T p) :
    ambientCechTermRestriction k h T (p + 1) (ambientCechDifferential k rank L T p y) =
      ambientCechDifferential k rank K T p (ambientCechTermRestriction k h T p y) := by
  classical
  funext G
  change ambientFaceRestriction k h G.1
      (∑ F : CechSlot T p, ambientCechEntry k rank L F.1 G.1 (y F)) =
    ∑ F : CechSlot T p, ambientCechEntry k rank K F.1 G.1
      (ambientFaceRestriction k h F.1 (y F))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F _
  exact congrArg (fun f => f (y F)) (ambientFaceRestriction_entry k rank h F.1 G.1)

/-- The quotient-induced map of the actual full ambient-linear Cech
complexes, with the original signed localization differential. -/
noncomputable def ambientCechRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) :
    ambientCechComplex k rank L T ⟶ ambientCechComplex k rank K T where
  f p := ModuleCat.ofHom (ambientCechTermRestriction k h T p)
  comm' := by
    intro p q hpq
    change p + 1 = q at hpq
    subst q
    rw [ambientCechComplex_d, ambientCechComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact (ambientCechTermRestriction_differential k rank h T p y).symm





end LPCA


