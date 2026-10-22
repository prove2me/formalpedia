-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
-- name    : LPCA_Solutions_LPCA_KoszulMultidegree_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:39:30.702542+00:00
-- url     : https://prove2.me/theorems/a4d73cd8-ea14-455c-9ef6-211c24f90988
-- title:
--   Koszul Multidegree for localized persistent commutative algebra
-- statement:
--   This bundle supplies koszul Multidegree for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The multidegree shift of the F-basis vector at coordinate-power stage n.
--   - Exact ambient-polynomial ideal membership, including the empty support.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_KoszulMultidegree.lean, selected declarations in lines 13–145; source SHA-256 50f8a251af650b4e879bd2998d4320212908d8863183da97226ff003be34d8e6; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
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

/-- The multidegree shift of the F-basis vector at coordinate-power stage n. -/
noncomputable def coordinateWeight (n : ℕ) (F : Finset V) : V →₀ ℕ :=
  Finsupp.indicator F (fun _ _ => n + 1)

@[simp] theorem coordinateWeight_apply (n : ℕ) (F : Finset V) (j : V) :
    coordinateWeight n F j = if j ∈ F then n + 1 else 0 := by
  classical
  simp [coordinateWeight]

abbrev eligibleVertices (n : ℕ) (T : Finset V) (d : V →₀ ℕ) : Finset V :=
  T.filter (fun j => n + 1 ≤ d j)

theorem coordinateWeight_le_iff
    (n : ℕ) (T F : Finset V) (hFT : F ⊆ T) (d : V →₀ ℕ) :
    coordinateWeight n F ≤ d ↔ F ⊆ eligibleVertices n T d := by
  constructor
  · intro h j hj
    apply Finset.mem_filter.mpr
    refine ⟨hFT hj, ?_⟩
    simpa only [coordinateWeight_apply, if_pos hj] using h j
  · intro h j
    by_cases hj : j ∈ F
    · simpa only [coordinateWeight_apply, if_pos hj] using (Finset.mem_filter.mp (h hj)).2
    · simp only [coordinateWeight_apply, if_neg hj]
      exact Nat.zero_le _



theorem coordinateWeight_product (n : ℕ) (F : Finset V) :
    (∏ j ∈ F, (MvPolynomial.X j : MvPolynomial V k) ^ (n + 1)) =
      MvPolynomial.monomial (coordinateWeight n F) (1 : k) := by
  simpa only [coordinateWeight] using
    MvPolynomial.prod_X_pow (R := k) (fun _ : V => n + 1) F

theorem coordinateKoszulCoefficient_monomial
    (rank : V ↪ ℕ) (n : ℕ) (F G : Finset V) :
    coordinateKoszulCoefficient k rank n F G =
      MvPolynomial.monomial (coordinateWeight n (G \ F)) (cechCoefficient k rank F G) := by
  unfold coordinateKoszulCoefficient
  rw [coordinateWeight_product, MvPolynomial.C_mul_monomial, mul_one]

theorem degree_eligible_of_subset
    (n : ℕ) (T G : Finset V) (hGT : G ⊆ T) (m : V →₀ ℕ) :
    G ⊆ eligibleVertices n T (m + coordinateWeight n G) :=
  (coordinateWeight_le_iff n T G hGT _).mp (le_add_left le_rfl)

noncomputable def normalizedKoszulExponent (n : ℕ) (d : V →₀ ℕ) (F : Finset V) : V →₀ ℕ :=
  d - coordinateWeight n F

theorem normalizedKoszulExponent_add_weight
    (n : ℕ) (T : Finset V) (d : V →₀ ℕ) (F : Finset V)
    (hF : F ⊆ eligibleVertices n T d) :
    normalizedKoszulExponent n d F + coordinateWeight n F = d := by
  apply tsub_add_cancel_of_le
  exact (coordinateWeight_le_iff n T F
    (fun j hj => (Finset.mem_filter.mp (hF hj)).1) d).mpr hF

theorem normalizedKoszulExponent_difference
    (n : ℕ) (T : Finset V) (d : V →₀ ℕ) (F G : Finset V)
    (hFG : F ⊆ G) (hG : G ⊆ eligibleVertices n T d) :
    coordinateWeight n (G \ F) + normalizedKoszulExponent n d G =
      normalizedKoszulExponent n d F := by
  ext j
  have hN : j ∈ G → n + 1 ≤ d j := fun hj => (Finset.mem_filter.mp (hG hj)).2
  by_cases hjF : j ∈ F
  · have hjG := hFG hjF
    simp only [normalizedKoszulExponent, Finsupp.add_apply, Finsupp.tsub_apply,
      coordinateWeight_apply, Finset.mem_sdiff, hjF, hjG, not_true_eq_false,
      and_false, if_false, if_true, zero_add]
  · by_cases hjG : j ∈ G
    · have h := hN hjG
      simp only [normalizedKoszulExponent, Finsupp.add_apply, Finsupp.tsub_apply,
        coordinateWeight_apply, Finset.mem_sdiff, hjF, hjG, not_false_eq_true,
        and_self, if_true, if_false, Nat.sub_zero]
      omega
    · simp [normalizedKoszulExponent, hjF, hjG]



private theorem coordinatePowerIdeal_monomial_span (n : ℕ) (T : Finset V) :
    coordinatePowerIdeal k T n = Ideal.span
      ((fun m : V →₀ ℕ => MvPolynomial.monomial m (1 : k)) ''
        ((fun j => Finsupp.single j (n + 1)) '' (T : Set V))) := by
  simp only [coordinatePowerIdeal, Set.image_image, Function.comp_def,
    MvPolynomial.X_pow_eq_monomial]

/-- Exact ambient-polynomial ideal membership, including the empty support. -/
theorem mem_coordinatePowerIdeal_iff (n : ℕ) (T : Finset V) (p : MvPolynomial V k) :
    p ∈ coordinatePowerIdeal k T n ↔
      ∀ d ∈ p.support, (eligibleVertices n T d).Nonempty := by
  rw [coordinatePowerIdeal_monomial_span, MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h d hd
    obtain ⟨s, ⟨j, hj, rfl⟩, hsd⟩ := h d hd
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
    simpa only [Finsupp.single_eq_same] using hsd j
  · intro h d hd
    obtain ⟨j, hj⟩ := h d hd
    obtain ⟨hjT, hjN⟩ := Finset.mem_filter.mp hj
    refine ⟨Finsupp.single j (n + 1), ⟨j, hjT, rfl⟩, ?_⟩
    intro v
    by_cases hv : v = j
    · subst v
      simpa only [Finsupp.single_eq_same] using hjN
    · simp only [Finsupp.single_eq_of_ne hv]
      exact Nat.zero_le _

theorem coordinatePowerIdeal_coeff_zero_of_no_eligible
    (n : ℕ) (T : Finset V) (p : MvPolynomial V k)
    (hp : p ∈ coordinatePowerIdeal k T n) (d : V →₀ ℕ)
    (hd : eligibleVertices n T d = ∅) : p.coeff d = 0 := by
  by_contra h
  have hnonempty := (mem_coordinatePowerIdeal_iff k n T p).mp hp d
    (MvPolynomial.mem_support_iff.mpr h)
  rw [hd] at hnonempty
  exact Finset.not_nonempty_empty hnonempty

end LPCA


