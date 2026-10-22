-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:46:12.133305+00:00
-- url     : https://prove2.me/theorems/f35aff6c-bef1-4595-8582-c57b4e7bf3a2
-- title:
--   Coordinate Koszul Resolution for localized persistent commutative algebra
-- statement:
--   This bundle supplies coordinate Koszul Resolution for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual coordinate-power quotient has this finite free resolution. Its exactness was proved by the polynomial multidegree decomposition.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CoordinateKoszulResolution.lean, selected declarations in lines 17–62; source SHA-256 36a5c91d2568395e7ec2a89342e61ac47eb30019635378ae8dcd52d50afbece9; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory HomologicalComplex

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

set_option backward.isDefEq.respectTransparency false in
theorem coordinateKoszulComplex_exactAt_succ
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ) :
    (coordinateKoszulComplex k rank n T).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (p + 1 + 1) (p + 1) p (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    coordinateKoszulComplex_d]
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    (coordinateKoszulDifferential_range_eq_ker k rank n T p)

set_option backward.isDefEq.respectTransparency false in
theorem coordinateKoszulAugmentationMap_quasiIso
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) :
    QuasiIso (coordinateKoszulAugmentationMap k rank n T) := by
  refine ⟨fun p => ?_⟩
  cases p with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    refine (ShortComplex.quasiIso_iff_of_zeros' _ ?_ ?_ ?_).mpr ?_
    · change (coordinateKoszulComplex k rank n T).d 0 0 = 0
      simp
    · exact HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 _ 1 0
    · exact HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 _ 0 0
    · constructor
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro y hy
        change (coordinateKoszulAugmentationMap k rank n T).f 0 y = 0 at hy
        rw [coordinateKoszulAugmentationMap_zero] at hy
        exact coordinateKoszulAugmentation_exact k rank n T y hy
      · change Epi ((coordinateKoszulAugmentationMap k rank n T).f 0)
        rw [coordinateKoszulAugmentationMap_zero, ModuleCat.epi_iff_surjective]
        exact coordinateKoszulAugmentation_surjective k n T
  | succ p =>
    rw [quasiIsoAt_iff_exactAt']
    · exact coordinateKoszulComplex_exactAt_succ k rank n T p
    · apply ChainComplex.exactAt_succ_single_obj

/-- The actual coordinate-power quotient has this finite free resolution.
Its exactness was proved by the polynomial multidegree decomposition. -/
noncomputable def coordinateKoszulResolution
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) :
    ProjectiveResolution
      (ModuleCat.of (MvPolynomial V k) (MvPolynomial V k ⧸ coordinatePowerIdeal k T n)) where
  complex := coordinateKoszulComplex k rank n T
  π := coordinateKoszulAugmentationMap k rank n T
  quasiIso := coordinateKoszulAugmentationMap_quasiIso k rank n T

end LPCA


