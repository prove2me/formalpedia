-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
-- name    : LPCA_Solutions_LPCA_CechGradedInclusions_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T22:03:59.778752+00:00
-- url     : https://prove2.me/theorems/368c5dd9-4801-4a72-8021-0a9e1f95694f
-- title:
--   Čech Graded Inclusions for localized persistent commutative algebra
-- statement:
--   This bundle supplies čech Graded Inclusions for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The full ambient differential restricts to the existing fixed-degree differential, with its actual localized homogeneous subspaces and signs.
--   - The homogeneous pieces embed as actual subcomplexes of the full Cech complex after canonical scalar restriction to the field.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CechGradedInclusions.lean, selected declarations in lines 20–102; source SHA-256 6ef51326282844ca61831ed938a60102308207f92e024afc8529a4973ff9e4e9; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
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
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

noncomputable local instance (priority := 3000) cechInclusionTermAddCommMonoid
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    AddCommMonoid (LocalizedCechTerm k K T a p) :=
  (localizedTermAddCommGroup k K T a p).toAddCommMonoid

theorem ambientConstant_smul (K : Complex V) (F : Finset V) (c : k)
    (z : LocalizedFaceRing k K F) :
    (show LocalizedFaceRing k K F from
      (MvPolynomial.C c : MvPolynomial V k) • (show ambientLocalizedModule k K F from z)) =
        c • z := by
  exact (ambientLocalizationFieldIso k K F).hom.hom.map_smul c
    (show (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
      (ambientLocalizedModule k K F) from z)

noncomputable def localizedCechTermForget (K : Complex V) (T : Finset V)
    (a : V → ℤ) (p : ℕ) :
    LocalizedCechTerm k K T a p →ₗ[k] (∀ F : CechSlot T p, LocalizedFaceRing k K F.1) where
  toFun y F := (y F).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def localizedCechTermInclusion (K : Complex V) (T : Finset V)
    (a : V → ℤ) (p : ℕ) :
    ModuleCat.of k (LocalizedCechTerm k K T a p) ⟶
      (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
        (ModuleCat.of (MvPolynomial V k) (AmbientCechTerm k K T p)) :=
  ModuleCat.ofHom (localizedCechTermForget k K T a p) ≫ (ambientCechTermFieldIso k K T p).inv



/-- The full ambient differential restricts to the existing fixed-degree
differential, with its actual localized homogeneous subspaces and signs. -/
theorem ambientCechDifferential_homogeneous (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (a : V → ℤ) (p : ℕ) (y : LocalizedCechTerm k K T a p) :
    ambientCechDifferential k rank K T p (fun F => (y F).1) =
      fun G => (actualDifferential k (cechCoefficient k rank) K T a p y G).1 := by
  classical
  funext G
  have hc := congrArg (fun z : localizedPiece k K G.1 a => z.1)
    (actualDifferential_apply_full k (cechCoefficient k rank) K T a p y G)
  simp only [Submodule.coe_sum] at hc
  rw [hc]
  change (∑ F : CechSlot T p, ambientCechEntry k rank K F.1 G.1 (y F).1) = _
  apply Finset.sum_congr rfl
  intro F _
  by_cases hFG : F.1 ⊆ G.1
  · simp only [ambientCechEntry, ambientLocalizationEntry, dif_pos hFG,
      LinearMap.smul_apply, Submodule.coe_smul]
    exact ambientConstant_smul k K G.1 (cechCoefficient k rank F.1 G.1)
      (localizationMap k K F.1 G.1 hFG (y F).1)
  · simp [ambientCechEntry, ambientLocalizationEntry, hFG]
    rfl

noncomputable def ambientCechFieldComplex (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) :
    CochainComplex (ModuleCat k) ℕ :=
  ((ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (ambientCechComplex k rank K T)

/-- The homogeneous pieces embed as actual subcomplexes of the full Cech
complex after canonical scalar restriction to the field. -/
noncomputable def localizedCechDegreeInclusion (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (a : V → ℤ) :
    localizedCechComplex k rank K T a ⟶ ambientCechFieldComplex k rank K T where
  f p := localizedCechTermInclusion k K T a p
  comm' := by
    intro p q hpq
    change p + 1 = q at hpq
    subst q
    change localizedCechTermInclusion k K T a p ≫
        (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).map
          ((ambientCechComplex k rank K T).d p (p + 1)) =
      (localizedCechComplex k rank K T a).d p (p + 1) ≫
        localizedCechTermInclusion k K T a (p + 1)
    rw [ambientCechComplex_d, localizedCechComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact ambientCechDifferential_homogeneous k rank K T a p

end LPCA


