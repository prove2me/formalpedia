-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
-- name    : LPCA_Solutions_LPCA_LocalizedBasis_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:18:43.615436+00:00
-- url     : https://prove2.me/theorems/16490551-f227-4100-b367-a2499c3d649b
-- title:
--   Localized Basis for localized persistent commutative algebra
-- statement:
--   This bundle supplies localized Basis for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalizedBasis.lean, selected declarations in lines 31–89; source SHA-256 9bd2846d69a2906bf4dda03bf8df4d632239f2b0c8123fc08b5d371e8688feab; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

private noncomputable def indicatorExponent (F : Finset V) : V →₀ ℕ :=
  Finsupp.indicator F (fun _ _ => 1)

private theorem invertedMonomial_eq (K : Complex V) (F : Finset V) :
    invertedMonomial k K F = Ideal.Quotient.mk (srIdeal k K)
      (MvPolynomial.monomial (indicatorExponent F) (1 : k)) := by
  unfold invertedMonomial variableClass
  rw [← map_prod]
  congr 1
  simpa only [indicatorExponent, pow_one] using
    MvPolynomial.prod_X_pow (R := k) (fun _ : V => 1) F

private theorem invertedMonomial_pow (K : Complex V) (F : Finset V) (N : ℕ) :
    invertedMonomial k K F ^ N = Ideal.Quotient.mk (srIdeal k K)
      (MvPolynomial.monomial (N • indicatorExponent F) (1 : k)) := by
  rw [invertedMonomial_eq, ← map_pow, MvPolynomial.monomial_pow, one_pow]

theorem localizedMonomial_eq_of_degree
    (K : Complex V) (F : Finset V) (a : V → ℤ)
    (m m' : V →₀ ℕ) (N N' : ℕ)
    (hm : ∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j)
    (hm' : ∀ j : V, (m' j : ℤ) - (if j ∈ F then (N' : ℤ) else 0) = a j) :
    localizedMonomial k K F m N = localizedMonomial k K F m' N' := by
  have hexponents : m + N' • indicatorExponent F = m' + N • indicatorExponent F := by
    ext j
    have h := hm j
    have h' := hm' j
    by_cases hj : j ∈ F
    · simp only [if_pos hj] at h h'
      simp only [Finsupp.add_apply, Finsupp.smul_apply, indicatorExponent,
        Finsupp.indicator_of_mem hj, smul_eq_mul, mul_one]
      omega
    · simp only [if_neg hj, sub_zero] at h h'
      simp only [Finsupp.add_apply, Finsupp.smul_apply, indicatorExponent,
        Finsupp.indicator_of_notMem hj, smul_zero, add_zero]
      omega
  unfold localizedMonomial
  apply IsLocalization.mk'_eq_iff_eq'.mpr
  apply congrArg (algebraMap (FaceRing k K) (LocalizedFaceRing k K F))
  dsimp only [Subtype.coe_mk]
  rw [invertedMonomial_pow, invertedMonomial_pow, ← map_mul, ← map_mul,
    MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, one_mul, hexponents]

theorem localizedPiece_eq_span_of_rep
    (K : Complex V) (F : Finset V) (a : V → ℤ) (m : V →₀ ℕ) (N : ℕ)
    (hm : ∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j) :
    localizedPiece k K F a = Submodule.span k {localizedMonomial k K F m N} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨m', N', hm', rfl⟩
    rw [localizedMonomial_eq_of_degree k K F a m' m N' N hm' hm]
    exact Submodule.subset_span (Set.mem_singleton _)
  · apply Submodule.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact Submodule.subset_span ⟨m, N, hm, rfl⟩

theorem localizedPiece_finite_finrank_le_one
    (K : Complex V) (F : Finset V) (a : V → ℤ) :
    Module.Finite k (localizedPiece k K F a) ∧
      Module.finrank k (localizedPiece k K F a) ≤ 1 := by
  classical
  by_cases h : ∃ (m : V →₀ ℕ) (N : ℕ),
      ∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j
  · obtain ⟨m, N, hm⟩ := h
    rw [localizedPiece_eq_span_of_rep k K F a m N hm]
    exact ⟨Module.Finite.span_of_finite k (Set.finite_singleton _),
      by simpa using (finrank_span_le_card (R := k)
        ({localizedMonomial k K F m N} : Set (LocalizedFaceRing k K F)))⟩
  · have hzero : localizedPiece k K F a = ⊥ := by
      apply le_antisymm ?_ bot_le
      apply Submodule.span_le.mpr
      rintro z ⟨m, N, hm, _⟩
      exact False.elim (h ⟨m, N, hm⟩)
    rw [hzero]
    exact ⟨inferInstance, by simp⟩

end LPCA


