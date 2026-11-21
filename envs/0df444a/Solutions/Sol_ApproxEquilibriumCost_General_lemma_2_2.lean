-- Prove2me | solution 1 for ApproxEquilibriumCost.General.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:34.264633+00:00
-- url     : https://prove2.me/submissions/fb5a9e9f-bffb-4896-b13a-9c0d21aa2ac7

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts

section
set_option autoImplicit false
namespace ApproxEquilibriumCost.Dev.L22
open ApproxEquilibriumCost.General

variable {n k : ℕ}

theorem cross_eq (G : Game n k) (g g' : Flow G) :
    crossCost G g g' = ∑ r, g' r * strategyLatency G g r := by
  unfold crossCost strategyLatency load KellyStochasticNetworks.linkFlow
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro e _; ring

theorem cost_eq (G : Game n k) (g : Flow G) : cost G g = crossCost G g g := by
  unfold cost crossCost; rfl

theorem fiber_sum (G : Game n k) (g : Flow G) (hg : IsFeasible G g) (m : Fin k → ℝ) :
    ∑ r, g r * m (population G r) = ∑ i, G.demand i * m i := by
  rw [← Finset.sum_fiberwise Finset.univ (population G)]
  apply Finset.sum_congr rfl
  intro i _
  have h := hg.2 i
  calc ∑ r ∈ Finset.univ.filter (fun r => population G r = i), g r * m (population G r)
      = ∑ r ∈ Finset.univ.filter (fun r => population G r = i), g r * m i := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [(Finset.mem_filter.1 hr).2]
    _ = G.demand i * m i := by rw [← Finset.sum_mul, h]

theorem exists_min (G : Game n k) (h : Flow G) (i : Fin k) :
    ∃ r, population G r = i ∧ ∀ r', population G r' = i →
      strategyLatency G h r ≤ strategyLatency G h r' := by
  obtain ⟨S, hS⟩ := G.strategies_nonempty i
  have hne : (Finset.univ.filter (fun r : Fin (routeCount G) => population G r = i)).Nonempty := by
    exact ⟨Fintype.equivFin (StrategyIndex G) ⟨i, ⟨S, hS⟩⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by unfold population route; simp⟩⟩
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image _ (strategyLatency G h) hne
  exact ⟨r, (Finset.mem_filter.1 hr).2, fun r' hr' => hmin r' (by simp [hr'])⟩

theorem nash_cost (G : Game n k) (f : Flow G) (hf : IsNash G f) :
    cost G f = ∑ i, G.demand i *
      strategyLatency G f (Classical.choose (exists_min G f i)) := by
  have hfeas : IsFeasible G f := hf.1
  rw [cost_eq, cross_eq, ← fiber_sum G f hfeas (fun i =>
    strategyLatency G f (Classical.choose (exists_min G f i)))]
  apply Finset.sum_congr rfl
  intro r _
  rcases (hf.1.1 r).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · congr 1
    obtain ⟨hp, -⟩ := Classical.choose_spec (exists_min G f (population G r))
    exact le_antisymm (hf.2 r _ hp hpos) (by
      obtain ⟨-, hm⟩ := Classical.choose_spec (exists_min G f (population G r))
      exact hm r rfl)

theorem part1 (G : Game n k) (f f' : Flow G) (hf' : IsFeasible G f') (hf : IsNash G f) :
    0 ≤ crossCost G f f' - cost G f := by
  rw [nash_cost G f hf, cross_eq, ← fiber_sum G f' hf']
  rw [sub_nonneg]
  apply Finset.sum_le_sum
  intro r _
  obtain ⟨-, hm⟩ := Classical.choose_spec (exists_min G f (population G r))
  exact mul_le_mul_of_nonneg_left (hm r rfl) (hf'.1 r)

theorem part2 (G : Game n k) (f f' : Flow G) (hf : IsFeasible G f) (ε : ℝ) (hε : 0 ≤ ε)
    (hf' : IsApproxNash G ε f') : cost G f' ≤ (1 + ε) * crossCost G f' f := by
  set m : Fin k → ℝ := fun i => strategyLatency G f' (Classical.choose (exists_min G f' i)) with hm
  have h1 : cost G f' ≤ ∑ r, f' r * ((1 + ε) * m (population G r)) := by
    rw [cost_eq, cross_eq]
    apply Finset.sum_le_sum
    intro r _
    rcases (hf'.1.1 r).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · apply mul_le_mul_of_nonneg_left _ hpos.le
      exact hf'.2 r _ (Classical.choose_spec (exists_min G f' (population G r))).1 hpos
  have h2 : ∑ r, f' r * ((1 + ε) * m (population G r)) = (1 + ε) * ∑ r, f r * m (population G r) := by
    rw [fiber_sum G f' hf'.1 (fun i => (1 + ε) * m i), fiber_sum G f hf m, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  have h3 : ∑ r, f r * m (population G r) ≤ crossCost G f' f := by
    rw [cross_eq]
    apply Finset.sum_le_sum
    intro r _
    obtain ⟨-, hmin⟩ := Classical.choose_spec (exists_min G f' (population G r))
    exact mul_le_mul_of_nonneg_left (hmin r rfl) (hf.1 r)
  calc cost G f' ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by linarith)

end ApproxEquilibriumCost.Dev.L22

namespace ApproxEquilibriumCost.General

theorem chk_lemma_2_2 {n k : ℕ} (G : Game n k) (f f' : Flow G)
    (hf : IsFeasible G f) (hf' : IsFeasible G f') (ε : ℝ) (hε : 0 ≤ ε) :
    (IsNash G f → 0 ≤ crossCost G f f' - cost G f) ∧
    (IsApproxNash G ε f' → cost G f' ≤ (1 + ε) * crossCost G f' f) ∧
    (IsNash G f → IsApproxNash G ε f' →
      (∑ e, (load G f' e - load G f e) *
        (G.latency e (load G f' e) - G.latency e (load G f e))) ≤
          ε * crossCost G f' f) := by
  refine ⟨fun h => Dev.L22.part1 G f f' hf' h, fun h => Dev.L22.part2 G f f' hf ε hε h, ?_⟩
  intro hN hA
  have p1 := Dev.L22.part1 G f f' hf' hN
  have p2 := Dev.L22.part2 G f f' hf ε hε hA
  have key : (∑ e, (load G f' e - load G f e) *
        (G.latency e (load G f' e) - G.latency e (load G f e))) =
      (cost G f' - crossCost G f' f) + (cost G f - crossCost G f f') := by
    unfold cost crossCost
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _; ring
  rw [key]; linarith

end ApproxEquilibriumCost.General
end

theorem solution : type_of% @ApproxEquilibriumCost.General.chk_lemma_2_2 := @ApproxEquilibriumCost.General.chk_lemma_2_2
