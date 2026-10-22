-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
-- name    : LPCA_Solutions_LPCA_SimplexContraction_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:41:07.645622+00:00
-- url     : https://prove2.me/theorems/55e68949-b6aa-4e7f-8d07-0b772fdefee9
-- title:
--   Simplex Contraction for localized persistent commutative algebra
-- statement:
--   This bundle supplies simplex Contraction for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The transposed insertion/contraction identity on all subsets of a simplex. The insertion-invariant family contains all cardinalities.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_SimplexContraction.lean, selected declarations in lines 13–116; source SHA-256 f1b89da9b9b5baab525f4b139665184773db56e0dbef5420efaa3913e51c3fc8; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
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
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

abbrev SubsetIndex (E : Finset V) : Type u := {F : Finset V // F ⊆ E}

noncomputable def insertionCoefficient (rank : V ↪ ℕ) (j : V) (A F : Finset V) : k := by
  classical
  exact if j ∈ A ∧ F = A.erase j then
    (-1 : k) ^ (F.filter (fun v => rank v < rank j)).card else 0

/-- The transposed insertion/contraction identity on all subsets of a simplex.
The insertion-invariant family contains all cardinalities. -/
theorem simplexContraction_coefficients
    (rank : V ↪ ℕ) (E : Finset V) (j : V) (hj : j ∈ E)
    (A F : SubsetIndex E) :
    ∑ B : SubsetIndex E,
      (insertionCoefficient k rank j A.1 B.1 * cechCoefficient k rank B.1 F.1 +
        cechCoefficient k rank A.1 B.1 * insertionCoefficient k rank j B.1 F.1) =
      if A = F then 1 else 0 := by
  let decV : DecidableEq V := inferInstance
  let orderV : LinearOrder V := LinearOrder.lift' rank rank.injective
  letI : LinearOrder V := {
    orderV with
    toDecidableEq := decV
    compare := fun v w => @compareOfLessAndEq V v w orderV.toLT (orderV.toDecidableLT v w) decV
    compare_eq_compareOfLessAndEq := by intro v w; rfl }
  classical
  have hinc : ∀ B C : Finset V, cechCoefficient k rank B C =
      Proofs.BassLyubeznik.SignedCore.inc k B C := fun _ _ => rfl
  have hins : ∀ B C : Finset V, insertionCoefficient k rank j B C =
      Proofs.BassLyubeznik.SignedCore.hc k j B C := fun _ _ => rfl
  have hmem : ∀ B : Finset V,
      B ∈ (Finset.univ.filter (fun B : Finset V => B ⊆ E)) ↔ B ⊆ E := by
    intro B
    simp
  have hsum := Proofs.BassLyubeznik.SignedCore.hc_inc_sum
    (k := k) (j := j) (𝓕 := fun B : Finset V => B ⊆ E)
    (by intro B; simp only [Finset.insert_subset_iff, hj, true_and]) A.2 F.2
  rw [Finset.sum_subtype _ hmem] at hsum
  simpa only [← hinc, ← hins, Subtype.ext_iff] using hsum

noncomputable def simplexBoundaryMatrix (rank : V ↪ ℕ) (E : Finset V) :
    Matrix (SubsetIndex E) (SubsetIndex E) k :=
  fun A F => cechCoefficient k rank A.1 F.1

noncomputable def simplexInsertionMatrix (rank : V ↪ ℕ) (E : Finset V) (j : V) :
    Matrix (SubsetIndex E) (SubsetIndex E) k :=
  fun A F => insertionCoefficient k rank j A.1 F.1

theorem simplexContraction_matrix
    (rank : V ↪ ℕ) (E : Finset V) (j : V) (hj : j ∈ E) :
    simplexInsertionMatrix k rank E j * simplexBoundaryMatrix k rank E +
        simplexBoundaryMatrix k rank E * simplexInsertionMatrix k rank E j = 1 := by
  classical
  ext A F
  change (∑ B : SubsetIndex E, insertionCoefficient k rank j A.1 B.1 *
      cechCoefficient k rank B.1 F.1) +
    (∑ B : SubsetIndex E, cechCoefficient k rank A.1 B.1 *
      insertionCoefficient k rank j B.1 F.1) = if A = F then 1 else 0
  rw [← Finset.sum_add_distrib, simplexContraction_coefficients k rank E j hj A F]

noncomputable def simplexBoundary (rank : V ↪ ℕ) (E : Finset V) :
    (SubsetIndex E → k) →ₗ[k] (SubsetIndex E → k) :=
  (simplexBoundaryMatrix k rank E).mulVecLin

noncomputable def simplexInsertion (rank : V ↪ ℕ) (E : Finset V) (j : V) :
    (SubsetIndex E → k) →ₗ[k] (SubsetIndex E → k) :=
  (simplexInsertionMatrix k rank E j).mulVecLin

theorem simplexContraction_identity
    (rank : V ↪ ℕ) (E : Finset V) (j : V) (hj : j ∈ E)
    (y : SubsetIndex E → k) :
    simplexInsertion k rank E j (simplexBoundary k rank E y) +
      simplexBoundary k rank E (simplexInsertion k rank E j y) = y := by
  have hmap : (simplexInsertion k rank E j).comp (simplexBoundary k rank E) +
      (simplexBoundary k rank E).comp (simplexInsertion k rank E j) = LinearMap.id := by
    unfold simplexInsertion simplexBoundary
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_add,
      simplexContraction_matrix k rank E j hj, Matrix.mulVecLin_one]
  exact LinearMap.congr_fun hmap y



theorem simplexInsertion_supported_card
    (rank : V ↪ ℕ) (E : Finset V) (j : V) (p : ℕ) (y : SubsetIndex E → k)
    (hy : ∀ F : SubsetIndex E, F.1.card ≠ p → y F = 0)
    (A : SubsetIndex E) (hA : A.1.card ≠ p + 1) :
    simplexInsertion k rank E j y A = 0 := by
  classical
  change (∑ F : SubsetIndex E, insertionCoefficient k rank j A.1 F.1 * y F) = 0
  apply Finset.sum_eq_zero
  intro F _
  by_cases hF : F.1.card = p
  · have hzero : insertionCoefficient k rank j A.1 F.1 = 0 := by
      unfold insertionCoefficient
      split_ifs with h
      · have hcard := Finset.card_erase_add_one h.1
        rw [← h.2, hF] at hcard
        exact False.elim (hA hcard.symm)
      · rfl
    rw [hzero, zero_mul]
  · rw [hy F hF, mul_zero]

end LPCA


