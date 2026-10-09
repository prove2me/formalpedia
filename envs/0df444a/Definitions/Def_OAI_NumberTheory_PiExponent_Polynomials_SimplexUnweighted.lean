-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted
-- name    : OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T13:38:08.387984+00:00
-- url     : https://prove2.me/theorems/30610836-78a0-4b0b-92e7-bbe4d6ff4312
-- title:
--   Counting and asymptotics of unweighted integer simplices
-- statement:
--   unweightedSimplex d N is the finite set of functions Fin d → ℕ whose coordinate sum is at most N. Its cardinality is (N + d).choose d. For fixed d, both that cardinality divided by N^d and the cardinality after replacing N by N + c divided by N^d tend to 1 / d! as N tends to infinity; the bundle also records the corresponding normalized binomial-coefficient limits.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexUnweighted.lean#L10-L102

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic


namespace OAI

open scoped BigOperators

namespace PiExponent

def unweightedSimplex (d N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, a i ≤ N)

@[simp] theorem mem_unweightedSimplex {d N : ℕ} {a : Fin d → ℕ} :
    a ∈ unweightedSimplex d N ↔ ∑ i, a i ≤ N := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    omega

theorem card_unweightedSimplex (d N : ℕ) :
    (unweightedSimplex d N).card = (N + d).choose d := by
  classical
  let target : Finset (Fin (d + 1) →₀ ℕ) := Finset.univ.finsuppAntidiag N
  have hc : target.card = (N + d).choose d := by
    rw [Finset.card_finsuppAntidiag_nat_eq_choose]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show d + 1 + N - 1 = N + d by omega, Nat.choose_symm_add]
  rw [← hc]
  let f : (Fin d → ℕ) → (Fin (d + 1) →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm (Fin.cons (N - ∑ i, a i) a)
  apply Finset.card_bij (fun a _ => f a)
  · intro a ha
    apply Finset.mem_finsuppAntidiag.mpr
    constructor
    · simp only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      exact Nat.sub_add_cancel (mem_unweightedSimplex.mp ha)
    · exact Finset.subset_univ _
  · intro a ha b hb hab
    funext i
    have h := congrArg (fun g : Fin (d + 1) →₀ ℕ => g i.succ) hab
    simpa only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.cons_succ] using h
  · intro b hb
    obtain ⟨hs, _⟩ := Finset.mem_finsuppAntidiag.mp hb
    have hs' : b 0 + ∑ i : Fin d, b i.succ = N := by
      simpa only [Fin.sum_univ_succ] using hs
    refine ⟨fun i => b i.succ, mem_unweightedSimplex.mpr (by omega), ?_⟩
    apply Finsupp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change N - ∑ j : Fin d, b j.succ = b 0
      omega
    · change b j.succ = b j.succ
      rfl

open Filter Topology Asymptotics

theorem tendsto_choose_normalized (d : ℕ) :
    Tendsto (fun N : ℕ => (N.choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h := (isEquivalent_choose d).div
    (IsEquivalent.refl : (fun N : ℕ => (N : ℝ) ^ d) ~[atTop]
      (fun N : ℕ => (N : ℝ) ^ d))
  apply h.symm.tendsto_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  change 1 / (d.factorial : ℝ) = ((N : ℝ) ^ d / (d.factorial : ℝ)) / (N : ℝ) ^ d
  field_simp

theorem tendsto_choose_add_normalized (d c : ℕ) :
    Tendsto (fun N : ℕ => ((N + c).choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h₁ := (tendsto_choose_normalized d).comp (tendsto_add_atTop_nat c)
  have h₂ : Tendsto (fun N : ℕ => ((N + c : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (c : ℝ) 0 1 (d := 1) (by norm_num))
  have h := h₁.mul (h₂.pow d)
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : ((N + c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N + c ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem tendsto_card_unweightedSimplex (d : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex] using tendsto_choose_add_normalized d d

theorem tendsto_card_unweightedSimplex_add (d c : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d (N + c)).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex, Nat.add_assoc] using
    tendsto_choose_add_normalized d (c + d)

end PiExponent

end OAI


