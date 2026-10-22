-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:40:22.158367+00:00
-- url     : https://prove2.me/theorems/d75904bf-2f82-473c-abf2-94528cdb4495
-- title:
--   Coordinate Koszul Transitions for localized persistent commutative algebra
-- statement:
--   This bundle supplies coordinate Koszul Transitions for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The transition from exponent m+1 to n+1 multiplies the F-basis vector by x_F^(m-n), so adjacent stages multiply it by x_F.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CoordinateKoszulTransitions.lean, selected declarations in lines 14–102; source SHA-256 725ed26dcc4e31666a7ef999af8101fe7ddfea735d80589cf64b7ca8cfba7b86; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

noncomputable def polynomialFaceMonomial (F : Finset V) : MvPolynomial V k :=
  ∏ j ∈ F, MvPolynomial.X j

private theorem polynomialFaceMonomial_factor (F G : Finset V) (hFG : F ⊆ G) :
    polynomialFaceMonomial k F * polynomialFaceMonomial k (G \ F) =
      polynomialFaceMonomial k G := by
  have hd : Disjoint F (G \ F) := by
    apply Finset.disjoint_left.mpr
    intro j hjF hjG
    exact (Finset.mem_sdiff.mp hjG).2 hjF
  unfold polynomialFaceMonomial
  rw [← Finset.prod_union hd, Finset.union_sdiff_of_subset hFG]

theorem coordinateKoszulCoefficient_transition
    (rank : V ↪ ℕ) (n m : ℕ) (hnm : n ≤ m) (F G : Finset V) :
    coordinateKoszulCoefficient k rank n F G * polynomialFaceMonomial k G ^ (m - n) =
      polynomialFaceMonomial k F ^ (m - n) * coordinateKoszulCoefficient k rank m F G := by
  by_cases hFG : F ⊆ G
  · have hG : polynomialFaceMonomial k G =
        polynomialFaceMonomial k F * polynomialFaceMonomial k (G \ F) :=
      (polynomialFaceMonomial_factor k F G hFG).symm
    have hn : (∏ j ∈ G \ F, (MvPolynomial.X j : MvPolynomial V k) ^ (n + 1)) =
        polynomialFaceMonomial k (G \ F) ^ (n + 1) := Finset.prod_pow _ _ _
    have hm : (∏ j ∈ G \ F, (MvPolynomial.X j : MvPolynomial V k) ^ (m + 1)) =
        polynomialFaceMonomial k (G \ F) ^ (m + 1) := Finset.prod_pow _ _ _
    have hexp : m + 1 = n + 1 + (m - n) := by omega
    unfold coordinateKoszulCoefficient
    rw [hn, hm, hG, mul_pow, hexp, pow_add]
    ring
  · simp [coordinateKoszulCoefficient, cechCoefficient_zero_of_not_subset k rank F G hFG]

/-- The transition from exponent m+1 to n+1 multiplies the F-basis vector
by x_F^(m-n), so adjacent stages multiply it by x_F. -/
noncomputable def coordinateKoszulTransition (n m : ℕ) (T : Finset V) (p : ℕ) :
    CoordinateKoszulTerm k T p →ₗ[MvPolynomial V k] CoordinateKoszulTerm k T p where
  toFun y F := polynomialFaceMonomial k F.1 ^ (m - n) * y F
  map_add' x y := by funext F; exact mul_add _ _ _
  map_smul' c y := by
    funext F
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem coordinateKoszulTransition_differential
    (rank : V ↪ ℕ) (n m : ℕ) (hnm : n ≤ m) (T : Finset V) (p : ℕ)
    (y : CoordinateKoszulTerm k T (p + 1)) :
    coordinateKoszulDifferential k rank n T p (coordinateKoszulTransition k n m T (p + 1) y) =
      coordinateKoszulTransition k n m T p (coordinateKoszulDifferential k rank m T p y) := by
  classical
  funext F
  change (∑ G : CechSlot T (p + 1), coordinateKoszulCoefficient k rank n F.1 G.1 *
      (polynomialFaceMonomial k G.1 ^ (m - n) * y G)) =
    polynomialFaceMonomial k F.1 ^ (m - n) *
      ∑ G : CechSlot T (p + 1), coordinateKoszulCoefficient k rank m F.1 G.1 * y G
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G _
  rw [← mul_assoc, coordinateKoszulCoefficient_transition k rank n m hnm F.1 G.1, mul_assoc]

noncomputable def coordinateKoszulTransitionMap
    (rank : V ↪ ℕ) (n m : ℕ) (hnm : n ≤ m) (T : Finset V) :
    coordinateKoszulComplex k rank m T ⟶ coordinateKoszulComplex k rank n T where
  f p := ModuleCat.ofHom (coordinateKoszulTransition k n m T p)
  comm' := by
    intro p q hpq
    change q + 1 = p at hpq
    subst p
    rw [coordinateKoszulComplex_d, coordinateKoszulComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact coordinateKoszulTransition_differential k rank n m hnm T q y

theorem coordinateKoszulTransition_self (n : ℕ) (T : Finset V) (p : ℕ) :
    coordinateKoszulTransition k n n T p = LinearMap.id := by
  ext y F
  simp [coordinateKoszulTransition]

theorem coordinateKoszulTransition_comp
    (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) (T : Finset V) (p : ℕ) :
    (coordinateKoszulTransition k n m T p).comp (coordinateKoszulTransition k m l T p) =
      coordinateKoszulTransition k n l T p := by
  apply LinearMap.ext
  intro y
  funext F
  change polynomialFaceMonomial k F.1 ^ (m - n) *
      (polynomialFaceMonomial k F.1 ^ (l - m) * y F) =
    polynomialFaceMonomial k F.1 ^ (l - n) * y F
  have hexp : (m - n) + (l - m) = l - n := by omega
  rw [← mul_assoc, ← pow_add, hexp]

end LPCA


