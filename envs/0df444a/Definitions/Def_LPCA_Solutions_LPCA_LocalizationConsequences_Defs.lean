-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
-- name    : LPCA_Solutions_LPCA_LocalizationConsequences_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:20:22.605015+00:00
-- url     : https://prove2.me/theorems/ae30f9d5-4466-4e84-bb1e-621f2bc52650
-- title:
--   Localization Consequences for localized persistent commutative algebra
-- statement:
--   This bundle supplies localization Consequences for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - An explicit coefficient-to-fraction equivalence; its value at 1 is the actual coefficient-one monomial fraction, rather than an arbitrary basis vector.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalizationConsequences.lean, selected declarations in lines 12–64; source SHA-256 cb2e65ba606c95953eb12a6c192189747fdf5e198f9641c84eb24a17f95ddaaf; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem localizedPiece_eq_bot_iff
    (K : Complex V) (F : Finset V) (a : V → ℤ) :
    localizedPiece k K F a = ⊥ ↔ ¬ LocalizationCriterion K F a := by
  classical
  have h := localization_piece_dimension_proved k K F a
  letI := h.1
  constructor
  · intro hzero hcriterion
    have hdim : Module.finrank k (localizedPiece k K F a) = 0 := by
      rw [hzero]
      simp
    rw [h.2, if_pos hcriterion] at hdim
    exact Nat.one_ne_zero hdim
  · intro hcriterion
    apply Submodule.finrank_eq_zero.mp
    rw [h.2, if_neg hcriterion]

theorem localizedPiece_nonzero_generator
    (K : Complex V) (F : Finset V) (a : V → ℤ)
    (hcriterion : LocalizationCriterion K F a) :
    ∃ (m : V →₀ ℕ) (N : ℕ),
      (∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j) ∧
      localizedMonomial k K F m N ≠ 0 ∧
      localizedPiece k K F a = Submodule.span k {localizedMonomial k K F m N} := by
  obtain ⟨m, N, hm, hsupp⟩ := exists_positive_denominator_rep F a hcriterion.1
  refine ⟨m, N, hm, ?_, localizedPiece_eq_span_of_rep k K F a m N hm⟩
  apply localizedMonomial_ne_zero_of_face k K F m N
  · exact hsupp.symm ▸ hcriterion.2
  · rw [hsupp]
    exact Finset.subset_union_right

/-- An explicit coefficient-to-fraction equivalence; its value at 1 is the
actual coefficient-one monomial fraction, rather than an arbitrary basis vector. -/
noncomputable def localizedPieceEquivOfRep
    (K : Complex V) (F : Finset V) (a : V → ℤ) (m : V →₀ ℕ) (N : ℕ)
    (hm : ∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j)
    (hne : localizedMonomial k K F m N ≠ 0) :
    k ≃ₗ[k] localizedPiece k K F a := by
  let z : localizedPiece k K F a :=
    ⟨localizedMonomial k K F m N, Submodule.subset_span ⟨m, N, hm, rfl⟩⟩
  let f : k →ₗ[k] localizedPiece k K F a :=
    LinearMap.toSpanSingleton k (localizedPiece k K F a) z
  apply LinearEquiv.ofBijective f
  constructor
  · apply smul_left_injective k
    intro hz
    exact hne (congrArg Subtype.val hz)
  · intro y
    have hy : y.1 ∈ Submodule.span k {localizedMonomial k K F m N} := by
      rw [← localizedPiece_eq_span_of_rep k K F a m N hm]
      exact y.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨c, Subtype.ext hc⟩



end LPCA


