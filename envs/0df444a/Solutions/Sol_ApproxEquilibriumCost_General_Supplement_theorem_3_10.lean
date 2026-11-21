-- Prove2me | solution 1 for ApproxEquilibriumCost.General.Supplement.theorem_3_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:34.972677+00:00
-- url     : https://prove2.me/submissions/e4829303-3681-4554-bfcb-7c468a3f4848

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_RoutingGame
import Theorems.Thm_ApproxEquilibriumCost_General_Supplement_lemma_3_8

section
set_option autoImplicit false
namespace ApproxEquilibriumCost.Dev.SP
open ApproxEquilibriumCost.General ApproxEquilibriumCost.General.Supplement

set_option allowUnsafeReducibility true in
attribute [local reducible] edgeCount

/-! Parallel -/

/-! Arc -/

/-! Reduction from the game model to path flows -/

theorem cost_eq_sum {n : ℕ} (G : Game n 1) (g : Flow G) :
    cost G g = ∑ r, g r * strategyLatency G g r := by
  unfold cost strategyLatency load KellyStochasticNetworks.linkFlow
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem feas_facts {n : ℕ} (G : Game n 1) {f : Flow G} (h : IsFeasible G f) :
    (∀ r, 0 ≤ f r) ∧ ∑ r, f r = G.demand 0 := by
  refine ⟨h.1, ?_⟩
  have := h.2 0
  rwa [Finset.filter_true_of_mem (fun r _ => Subsingleton.elim _ _)] at this

theorem exists_pos_flow {n : ℕ} (G : Game n 1) {f : Flow G} (h : IsFeasible G f) :
    ∃ r, 0 < f r := by
  by_contra hc
  push Not at hc
  have h1 := (feas_facts G h).2
  have h2 := Finset.sum_nonpos (s := Finset.univ) (fun r _ => hc r)
  linarith [G.demand_pos 0]

theorem cost_nash {n : ℕ} (G : Game n 1) {f : Flow G} (hf : IsNash G f) {P0 : Fin (routeCount G)}
    (hP0 : 0 < f P0) : cost G f = G.demand 0 * strategyLatency G f P0 := by
  have hfe := feas_facts G hf.1
  rw [cost_eq_sum, ← hfe.2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rcases (hfe.1 r).eq_or_lt with h | h
  · rw [← h]; simp
  · have a : strategyLatency G f r ≤ strategyLatency G f P0 := hf.2 r P0 (Subsingleton.elim _ _) h
    have b : strategyLatency G f P0 ≤ strategyLatency G f r := hf.2 P0 r (Subsingleton.elim _ _) hP0
    rw [le_antisymm a b]

theorem le_cost {n : ℕ} (G : Game n 1) {g : Flow G} (hg : IsFeasible G g) (c : ℝ)
    (h : ∀ r, c ≤ strategyLatency G g r) : G.demand 0 * c ≤ cost G g := by
  have hfe := feas_facts G hg
  rw [cost_eq_sum, ← hfe.2, Finset.sum_mul]
  exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (h r) (hfe.1 r)

end ApproxEquilibriumCost.Dev.SP
end

section
set_option autoImplicit false
namespace ApproxEquilibriumCost.Dev.T310
open ApproxEquilibriumCost.General ApproxEquilibriumCost.General.Supplement ApproxEquilibriumCost.Dev.SP

theorem main (N : SPNetwork) (G : Game (edgeCount N) 1)
    (f : Flow G) (hf : IsNash G f)
    (hcost : 0 < cost G f) (ε : ℝ) (hε : 0 ≤ ε)
    (f' : Flow G) (hf' : IsApproxNash G ε f')
    (L38 : ∀ (P Q : Fin (routeCount G)), 0 < f P →
      strategyLatency G f P / (1 + (depth N : ℝ) * ε) ≤ strategyLatency G f' Q) :
    1 / (1 + (depth N : ℝ) * ε) ≤ cost G f' / cost G f := by
  obtain ⟨P0, hP0⟩ := exists_pos_flow G hf.1
  have hc := cost_nash G hf hP0
  have h1 := le_cost G hf'.1 (strategyLatency G f P0 / (1 + (depth N : ℝ) * ε))
    (fun Q => L38 P0 Q hP0)
  have hpos : 0 < 1 + (depth N : ℝ) * ε := by positivity
  rw [le_div_iff₀ hcost, hc]
  calc 1 / (1 + (depth N : ℝ) * ε) * (G.demand 0 * strategyLatency G f P0)
      = G.demand 0 * (strategyLatency G f P0 / (1 + (depth N : ℝ) * ε)) := by ring
    _ ≤ cost G f' := h1

end ApproxEquilibriumCost.Dev.T310

namespace ApproxEquilibriumCost.General.Supplement
theorem chk_theorem_3_10 (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (hcost : 0 < cost G f) (ε : ℝ) (hε : 0 ≤ ε)
    (f' : Flow G) (hf' : IsApproxNash G ε f') :
    1 / (1 + (depth N : ℝ) * ε) ≤ cost G f' / cost G f :=
  ApproxEquilibriumCost.Dev.T310.main N G f hf hcost ε hε f' hf'
    (fun P Q hP => ApproxEquilibriumCost.General.Supplement.lemma_3_8 N G hG f hf ε hε f' hf' P Q hP)
end ApproxEquilibriumCost.General.Supplement
end

theorem solution : type_of% @ApproxEquilibriumCost.General.Supplement.chk_theorem_3_10 := @ApproxEquilibriumCost.General.Supplement.chk_theorem_3_10
