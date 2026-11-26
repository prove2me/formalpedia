-- Prove2me | solution 1 for AME125.reduced_graphState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:56.228682+00:00
-- url     : https://prove2.me/submissions/e37a909c-0346-486a-ac9e-2c90a86b18a9

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
public import Theorems.Thm_P2M_AME125_sum___dot_53c9426ac755
public import Theorems.Thm_AME125_quad_add
public import Theorems.Thm_AME125_sum_split
public import Theorems.Thm_AME125_toZ_combineFirst_left
public import Theorems.Thm_AME125_toZ_combineFirst_right
public import Theorems.Thm_AME125_toZ_combineFirst_eq
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.diagonalState_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply



set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix
namespace AME125
theorem _root_.solution {n m : ℕ} (hm : m ≤ n) (U : Matrix (Fin n) (Fin n) (ZMod 5))
    (a b : Config m 5) :
    ∃ K : ZMod 5, (toZ a = toZ b → K = 0) ∧ reducedDensityFirst m hm (graphState U) a b =
      ((5 : ℂ) ^ (n / 2))⁻¹ ^ 2 * χ K *
        (if coeff hm (U + Uᵀ) (toZ a - toZ b) = 0 then (5 : ℂ) ^ (n - m) else 0) := by
  set d := toZ a - toZ b
  refine ⟨quad U (lift d) + ∑ i : Fin m, (∑ l, lift d l * (U + Uᵀ) l (leftIndex hm i)) * toZ b i,
    fun hab ↦ ?_, ?_⟩
  · have hd : d = 0 := sub_eq_zero.mpr hab
    have hl : lift (n := n) d = 0 := by
      funext i
      simp [lift, hd]
    simp [hl, quad]
  have hdiff : ∀ z : Config (n - m) 5,
      quad U (toZ (combineFirst m hm a z)) - quad U (toZ (combineFirst m hm b z)) =
        (quad U (lift d) + ∑ i : Fin m, (∑ l, lift d l * (U + Uᵀ) l (leftIndex hm i)) * toZ b i) +
          ∑ k, toZ z k * coeff hm (U + Uᵀ) d k := by
    intro z
    rw [toZ_combineFirst_eq hm a b z, quad_add, sum_split hm]
    simp only [toZ_combineFirst_left, toZ_combineFirst_right, coeff]
    rw [Finset.sum_congr rfl fun k _ ↦ mul_comm (∑ l, lift d l * (U + Uᵀ) l (rightIndex hm k))
      (toZ z k)]
    ring
  have hterm : ∀ z : Config (n - m) 5,
      graphState U (combineFirst m hm a z) * star (graphState U (combineFirst m hm b z)) =
        ((5 : ℂ) ^ (n / 2))⁻¹ ^ 2 *
          χ ((quad U (lift d) +
              ∑ i : Fin m, (∑ l, lift d l * (U + Uᵀ) l (leftIndex hm i)) * toZ b i) +
            ∑ k, toZ z k * coeff hm (U + Uᵀ) d k) := by
    intro z
    rw [← hdiff z, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
    simp only [graphState, mkStateVector_apply, star_mul', starRingEnd_apply]
    have hc : star ((5 : ℂ) ^ (n / 2))⁻¹ = ((5 : ℂ) ^ (n / 2))⁻¹ := by simp
    rw [hc]
    ring
  have hsum : ∑ z : Config (n - m) 5, χ (∑ k, toZ z k * coeff hm (U + Uᵀ) d k) =
      ∑ v : Fin (n - m) → ZMod 5, χ (∑ k, v k * coeff hm (U + Uᵀ) d k) :=
    Fintype.sum_equiv (configEquiv (n - m)) _ _ fun _ ↦ rfl
  rw [reducedDensityFirst]
  simp_rw [hterm, AddChar.map_add_eq_mul, ← Finset.mul_sum]
  rw [hsum, sum_χ_dot]
  ring
end AME125
