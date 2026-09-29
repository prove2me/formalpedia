-- Prove2me | solution 1 for AGT.swap_regret_correlated_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-12T16:36:23.889613+00:00
-- url     : https://prove2.me/submissions/907ac0fd-b8a3-4a4c-a0dd-85bd2208cf88

import Definitions.Def_agt_regret
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic

namespace AGT

open Finset

end AGT

open AGT Finset in
theorem solution {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    (cost : ι → (∀ i, S i) → ℝ) (T : ℕ) (hT : 0 < T)
    (σ : ℕ → ∀ i, S i → ℝ) (hσ : ∀ t, t < T → IsMixedProfile (σ t)) (R : ℝ)
    (hswap : ∀ i (F : S i → S i),
      ∑ t ∈ Finset.range T, ∑ s, profileProb (σ t) s * cost i s ≤
        (∑ t ∈ Finset.range T, ∑ s,
          profileProb (σ t) s * cost i (Function.update s i (F (s i)))) + R) :
    IsCorrelatedEquilibrium (R / T) cost
      (fun s => (∑ t ∈ Finset.range T, profileProb (σ t) s) / T) := by
  classical
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  -- At each of the first `T` steps the product distribution is a lottery on
  -- joint action vectors.
  have hpp_nonneg : ∀ t ∈ range T, ∀ s : ∀ i, S i, 0 ≤ profileProb (σ t) s := by
    intro t ht s
    exact Finset.prod_nonneg fun i _ => (hσ t (mem_range.mp ht) i).1 (s i)
  have hpp_sum : ∀ t ∈ range T, ∑ s : ∀ i, S i, profileProb (σ t) s = 1 := by
    intro t ht
    have hprod : ∏ i, ∑ j, σ t i j = ∑ s : ∀ i, S i, ∏ i, σ t i (s i) := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    have hone : ∏ i, ∑ j, σ t i j = 1 :=
      Finset.prod_eq_one fun i _ => (hσ t (mem_range.mp ht) i).2
    simpa [profileProb, hprod] using hone
  -- Averaging identity: the empirical distribution averages the per-step ones.
  have key : ∀ g : (∀ i, S i) → ℝ,
      ∑ s : ∀ i, S i, (∑ t ∈ range T, profileProb (σ t) s) / T * g s
        = (∑ t ∈ range T, ∑ s : ∀ i, S i, profileProb (σ t) s * g s) / T := by
    intro g
    simp only [div_mul_eq_mul_div, Finset.sum_mul]
    rw [← Finset.sum_div, Finset.sum_comm]
  refine ⟨⟨fun s => div_nonneg (Finset.sum_nonneg fun t ht => hpp_nonneg t ht s)
      hTpos.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, Finset.sum_comm, Finset.sum_congr rfl hpp_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      div_self hTpos.ne']
  · intro i F
    rw [key (fun s => cost i s), key (fun s => cost i (Function.update s i (F (s i)))),
      ← add_div, div_le_div_iff_of_pos_right hTpos]
    exact hswap i F
