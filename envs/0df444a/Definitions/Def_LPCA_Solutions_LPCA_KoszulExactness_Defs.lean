-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
-- name    : LPCA_Solutions_LPCA_KoszulExactness_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:44:58.943556+00:00
-- url     : https://prove2.me/theorems/c2ba0f19-8e4e-4fee-8db4-05f5bcaeb2db
-- title:
--   Koszul Exactness for localized persistent commutative algebra
-- statement:
--   This bundle supplies koszul Exactness for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Choose the simplex contraction only in degrees having an eligible vertex. This map is k-linear; no polynomial-linear contraction is asserted.
--   - Positive-degree exactness in the actual finite free polynomial complex.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_KoszulExactness.lean, selected declarations in lines 13–120; source SHA-256 bac98aa74d331d0134ab1f4c365244fa59683c304e71a110e61b40b83bf22acf; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
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

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- Choose the simplex contraction only in degrees having an eligible vertex.
This map is k-linear; no polynomial-linear contraction is asserted. -/
noncomputable def gradedCoordinateKoszulInsertion
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ) :
    GradedCoordinateKoszulTerm k n T p →ₗ[k] GradedCoordinateKoszulTerm k n T (p + 1) := by
  classical
  exact DirectSum.lmap (fun d =>
    if h : (eligibleVertices n T d).Nonempty then
      simplexDegreeInsertion k rank (eligibleVertices n T d) h.choose p else 0)

theorem gradedCoordinateKoszulContraction_succ
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ)
    (y : GradedCoordinateKoszulTerm k n T (p + 1)) :
    gradedCoordinateKoszulInsertion k rank n T p (gradedCoordinateKoszulDifferential k rank n T p y) +
      gradedCoordinateKoszulDifferential k rank n T (p + 1)
        (gradedCoordinateKoszulInsertion k rank n T (p + 1) y) = y := by
  classical
  ext d F
  by_cases h : (eligibleVertices n T d).Nonempty
  · have hc := congrFun (simplexDegreeContraction_identity k rank
      (eligibleVertices n T d) h.choose h.choose_spec p (y d)) F
    change ((if h : (eligibleVertices n T d).Nonempty then
        simplexDegreeInsertion k rank (eligibleVertices n T d) h.choose p else 0)
          (simplexDegreeBoundary k rank (eligibleVertices n T d) p (y d))) F +
      (simplexDegreeBoundary k rank (eligibleVertices n T d) (p + 1)
        ((if h : (eligibleVertices n T d).Nonempty then
          simplexDegreeInsertion k rank (eligibleVertices n T d) h.choose (p + 1) else 0)
            (y d))) F = y d F
    simpa only [dif_pos h, Pi.add_apply] using hc
  · have he : eligibleVertices n T d = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hh := Finset.card_le_card F.2.1
    rw [F.2.2, he, Finset.card_empty] at hh
    omega

/-- Positive-degree exactness in the actual finite free polynomial complex. -/
theorem coordinateKoszulDifferential_exact
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ)
    (y : CoordinateKoszulTerm k T (p + 1))
    (hy : coordinateKoszulDifferential k rank n T p y = 0) :
    ∃ z : CoordinateKoszulTerm k T (p + 1 + 1),
      coordinateKoszulDifferential k rank n T (p + 1) z = y := by
  let yg := coordinateKoszulGradingEquiv k n T (p + 1) y
  have hdy : gradedCoordinateKoszulDifferential k rank n T p yg = 0 := by
    rw [← coordinateKoszulGradingEquiv_differential, hy, map_zero]
  have hh := gradedCoordinateKoszulContraction_succ k rank n T p yg
  rw [hdy, map_zero, zero_add] at hh
  refine ⟨(coordinateKoszulGradingEquiv k n T (p + 1 + 1)).symm
    (gradedCoordinateKoszulInsertion k rank n T (p + 1) yg), ?_⟩
  apply (coordinateKoszulGradingEquiv k n T (p + 1)).injective
  rw [coordinateKoszulGradingEquiv_differential, LinearEquiv.apply_symm_apply]
  exact hh

theorem coordinateKoszulAugmentation_exact
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (y : CoordinateKoszulTerm k T 0)
    (hy : coordinateKoszulAugmentation k n T y = 0) :
    ∃ z : CoordinateKoszulTerm k T 1,
      coordinateKoszulDifferential k rank n T 0 z = y := by
  classical
  have hp : y ⟨∅, Finset.empty_subset T, by simp⟩ ∈ coordinatePowerIdeal k T n := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hy
  let yg := coordinateKoszulGradingEquiv k n T 0 y
  have hh : gradedCoordinateKoszulDifferential k rank n T 0
      (gradedCoordinateKoszulInsertion k rank n T 0 yg) = yg := by
    ext d F
    by_cases h : (eligibleVertices n T d).Nonempty
    · have hc := congrFun (simplexDegreeContraction_zero k rank
        (eligibleVertices n T d) h.choose h.choose_spec (yg d)) F
      change (simplexDegreeBoundary k rank (eligibleVertices n T d) 0
        ((if h : (eligibleVertices n T d).Nonempty then
          simplexDegreeInsertion k rank (eligibleVertices n T d) h.choose 0 else 0)
            (yg d))) F = yg d F
      simpa only [dif_pos h] using hc
    · have he : eligibleVertices n T d = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hzero := coordinatePowerIdeal_coeff_zero_of_no_eligible k n T
        (y ⟨∅, Finset.empty_subset T, by simp⟩) hp d he
      have hF : F.1 = ∅ := Finset.card_eq_zero.mp F.2.2
      have hcoord : yg d F = 0 := by
        change coordinateKoszulGradingEquiv k n T 0 y d F = 0
        rw [coordinateKoszulGradingEquiv_apply]
        have hw : coordinateWeight n F.1 = 0 := by
          ext j
          rw [coordinateWeight_apply, hF]
          simp
        have he : normalizedKoszulExponent n d F.1 = d := by
          rw [normalizedKoszulExponent, hw, tsub_zero]
        have hs : (⟨F.1, (fun j hj => (Finset.mem_filter.mp (F.2.1 hj)).1), F.2.2⟩ :
            CechSlot T 0) = ⟨∅, Finset.empty_subset T, by simp⟩ := Subtype.ext hF
        rw [he, hs]
        exact hzero
      change (simplexDegreeBoundary k rank (eligibleVertices n T d) 0
        ((if h : (eligibleVertices n T d).Nonempty then
          simplexDegreeInsertion k rank (eligibleVertices n T d) h.choose 0 else 0) (yg d))) F = _
      rw [dif_neg h, LinearMap.zero_apply, map_zero, Pi.zero_apply, hcoord]
  refine ⟨(coordinateKoszulGradingEquiv k n T 1).symm
    (gradedCoordinateKoszulInsertion k rank n T 0 yg), ?_⟩
  apply (coordinateKoszulGradingEquiv k n T 0).injective
  rw [coordinateKoszulGradingEquiv_differential, LinearEquiv.apply_symm_apply]
  exact hh

theorem coordinateKoszulDifferential_range_eq_ker
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ) :
    LinearMap.range (coordinateKoszulDifferential k rank n T (p + 1)) =
      LinearMap.ker (coordinateKoszulDifferential k rank n T p) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact coordinateKoszulDifferential_square k rank n T p z
  · exact coordinateKoszulDifferential_exact k rank n T p y



end LPCA


