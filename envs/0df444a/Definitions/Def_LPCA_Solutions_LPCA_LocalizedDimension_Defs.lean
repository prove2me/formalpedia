-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
-- name    : LPCA_Solutions_LPCA_LocalizedDimension_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:19:18.561985+00:00
-- url     : https://prove2.me/theorems/9726534f-b606-4bc4-be8e-6196832145c4
-- title:
--   Localized Dimension for localized persistent commutative algebra
-- statement:
--   This bundle supplies localized Dimension for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalizedDimension.lean, selected declarations in lines 57–185; source SHA-256 0c74e1526994d050c415f7d9beffbe4a146297b09c18e94825422381996def28; source certificate Sapelo2 job 49172236.

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

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

private noncomputable def faceEvaluation
    (K : Complex V) (G : Finset V) (hG : G ∈ K.faces) : FaceRing k K →+* k := by
  classical
  let evaluation : MvPolynomial V k →+* k :=
    MvPolynomial.eval (fun j => if j ∈ G then 1 else 0)
  have hkernel : srIdeal k K ≤ RingHom.ker evaluation := by
    apply Ideal.span_le.mpr
    rintro p ⟨H, hH, rfl⟩
    change evaluation (∏ j ∈ H, MvPolynomial.X j) = 0
    have hnsub : ¬ H ⊆ G := fun hHG => hH (K.down_closed hG hHG)
    obtain ⟨j, hjH, hjG⟩ := Finset.not_subset.mp hnsub
    rw [map_prod]
    apply Finset.prod_eq_zero hjH
    simp [evaluation, hjG]
  exact Ideal.Quotient.lift (srIdeal k K) evaluation
    (fun p hp => RingHom.mem_ker.mp (hkernel hp))

private theorem faceEvaluation_monomial
    (K : Complex V) (G : Finset V) (hG : G ∈ K.faces)
    (m : V →₀ ℕ) (hm : m.support ⊆ G) :
    faceEvaluation k K G hG
      (Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k))) = 1 := by
  classical
  change MvPolynomial.eval (fun j => if j ∈ G then (1 : k) else 0)
    (MvPolynomial.monomial m 1) = 1
  rw [MvPolynomial.eval_monomial, one_mul]
  apply Finset.prod_eq_one
  intro j hj
  simp [hm hj]

private theorem faceEvaluation_inverted
    (K : Complex V) (G : Finset V) (hG : G ∈ K.faces)
    (F : Finset V) (hF : F ⊆ G) :
    faceEvaluation k K G hG (invertedMonomial k K F) = 1 := by
  classical
  unfold invertedMonomial
  rw [map_prod]
  apply Finset.prod_eq_one
  intro j hj
  change MvPolynomial.eval (fun j => if j ∈ G then (1 : k) else 0)
    (MvPolynomial.X j) = 1
  simp [hF hj]

theorem localizedMonomial_ne_zero_of_face
    (K : Complex V) (F : Finset V) (m : V →₀ ℕ) (N : ℕ)
    (hface : m.support ∈ K.faces) (hF : F ⊆ m.support) :
    localizedMonomial k K F m N ≠ 0 := by
  intro hz
  unfold localizedMonomial at hz
  rw [IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨r, hr⟩ := hz
  obtain ⟨r, rN, rfl⟩ := r
  have heval := congrArg (faceEvaluation k K m.support hface) hr
  simp only [map_mul, map_pow, map_zero,
    faceEvaluation_inverted k K m.support hface F hF,
    faceEvaluation_monomial k K m.support hface m (Finset.Subset.refl _),
    one_pow, one_mul] at heval
  exact one_ne_zero heval

theorem monomial_zero_of_nonface
    (K : Complex V) (m : V →₀ ℕ) (hface : m.support ∉ K.faces) :
    Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k)) = 0 := by
  classical
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  let e : V →₀ ℕ := Finsupp.indicator m.support (fun _ _ => 1)
  have hproduct : (∏ j ∈ m.support, (MvPolynomial.X j : MvPolynomial V k)) =
      MvPolynomial.monomial e 1 := by
    simpa only [e, pow_one] using
      MvPolynomial.prod_X_pow (R := k) (fun _ : V => 1) m.support
  have hgen : MvPolynomial.monomial e (1 : k) ∈ srIdeal k K := by
    rw [← hproduct]
    exact Ideal.subset_span ⟨m.support, hface, rfl⟩
  have hle : e ≤ m := by
    intro j
    by_cases hj : j ∈ m.support
    · simpa only [e, Finsupp.indicator_of_mem hj] using
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
    · simp [e, Finsupp.indicator_of_notMem hj]
  have hdiv : MvPolynomial.monomial e (1 : k) ∣ MvPolynomial.monomial m (1 : k) :=
    MvPolynomial.monomial_dvd_monomial.mpr ⟨Or.inr hle, dvd_refl 1⟩
  obtain ⟨p, hp⟩ := hdiv
  rw [hp]
  exact Ideal.mul_mem_right _ _ hgen

section FiniteVertices

variable [Fintype V]

theorem exists_positive_denominator_rep
    (F : Finset V) (a : V → ℤ) (hnonnegative : ∀ j : V, j ∉ F → 0 ≤ a j) :
    ∃ (m : V →₀ ℕ) (N : ℕ),
      (∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j) ∧
      m.support = positiveSupport a ∪ F := by
  classical
  let N : ℕ := (∑ j : V, (-a j).toNat) + 1
  have hpositive : ∀ j : V, 0 < a j + (N : ℤ) := by
    intro j
    have hsum : (-a j).toNat ≤ ∑ v : V, (-a v).toNat :=
      Finset.single_le_sum (f := fun v : V => (-a v).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hcast : (-a j) ≤ ((-a j).toNat : ℤ) := Int.self_le_toNat _
    dsimp only [N]
    omega
  let m : V →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun j => (a j + if j ∈ F then (N : ℤ) else 0).toNat)
  have hcast : ∀ j : V, (m j : ℤ) = a j + if j ∈ F then (N : ℤ) else 0 := by
    intro j
    have hz : 0 ≤ a j + if j ∈ F then (N : ℤ) else 0 := by
      by_cases hj : j ∈ F
      · simpa only [if_pos hj] using le_of_lt (hpositive j)
      · simpa only [if_neg hj, add_zero] using hnonnegative j hj
    simpa [m] using Int.toNat_of_nonneg hz
  refine ⟨m, N, ?_, ?_⟩
  · intro j
    rw [hcast]
    omega
  · ext j
    simp only [Finsupp.mem_support_iff, positiveSupport, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    have hc := hcast j
    by_cases hj : j ∈ F
    · have hp := hpositive j
      simp only [if_pos hj] at hc
      simp only [hj, or_true, iff_true]
      have hmpositive : 0 < (m j : ℤ) := by simpa only [← hc] using hp
      exact_mod_cast ne_of_gt hmpositive
    · simp only [if_neg hj, add_zero] at hc
      simp only [hj, or_false]
      omega

attribute [local instance] Classical.propDecidable

theorem localization_piece_dimension_proved
    (K : Complex V) (F : Finset V) (a : V → ℤ) :
    Module.Finite k (localizedPiece k K F a) ∧
      Module.finrank k (localizedPiece k K F a) =
        (if LocalizationCriterion K F a then 1 else 0) := by
  classical
  refine ⟨(localizedPiece_finite_finrank_le_one k K F a).1, ?_⟩
  by_cases hnonnegative : ∀ j : V, j ∉ F → 0 ≤ a j
  · obtain ⟨m, N, hm, hsupp⟩ := exists_positive_denominator_rep F a hnonnegative
    rw [localizedPiece_eq_span_of_rep k K F a m N hm]
    by_cases hface : m.support ∈ K.faces
    · have hcriterion : LocalizationCriterion K F a := ⟨hnonnegative, hsupp ▸ hface⟩
      rw [if_pos hcriterion]
      apply finrank_span_singleton
      apply localizedMonomial_ne_zero_of_face k K F m N hface
      rw [hsupp]
      exact Finset.subset_union_right
    · have hcriterion : ¬ LocalizationCriterion K F a := by
        intro hc
        exact hface (hsupp.symm ▸ hc.2)
      rw [if_neg hcriterion]
      have hzero : localizedMonomial k K F m N = 0 := by
        unfold localizedMonomial
        rw [monomial_zero_of_nonface k K m hface, IsLocalization.mk'_zero]
      rw [hzero]
      simp
  · have hcriterion : ¬ LocalizationCriterion K F a := fun h => hnonnegative h.1
    rw [if_neg hcriterion]
    have hzero : localizedPiece k K F a = ⊥ := by
      apply le_antisymm ?_ bot_le
      apply Submodule.span_le.mpr
      rintro z ⟨m, N, hm, _⟩
      apply False.elim
      apply hnonnegative
      intro j hj
      have hd := hm j
      rw [if_neg hj, sub_zero] at hd
      exact hd ▸ Int.natCast_nonneg (m j)
    rw [hzero]
    simp

end FiniteVertices
end LPCA


