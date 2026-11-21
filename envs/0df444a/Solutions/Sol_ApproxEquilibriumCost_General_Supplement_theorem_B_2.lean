-- Prove2me | solution 1 for ApproxEquilibriumCost.General.Supplement.theorem_B_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:34.781194+00:00
-- url     : https://prove2.me/submissions/33dc8c77-4b7a-4046-b532-49e2d30235e3

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_RoutingGame
import Theorems.Thm_ApproxEquilibriumCost_General_Supplement_lemma_B_1

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

theorem cost_le {n : ℕ} (G : Game n 1) {g : Flow G} (hg : IsFeasible G g) (c : ℝ)
    (h : ∀ r, 0 < g r → strategyLatency G g r ≤ c) : cost G g ≤ G.demand 0 * c := by
  have hfe := feas_facts G hg
  rw [cost_eq_sum, ← hfe.2, Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ => ?_
  rcases (hfe.1 r).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · exact mul_le_mul_of_nonneg_left (h r h0) h0.le

end ApproxEquilibriumCost.Dev.SP
end

section
set_option autoImplicit false
namespace ApproxEquilibriumCost.Dev.B2
open ApproxEquilibriumCost.General ApproxEquilibriumCost.General.Supplement ApproxEquilibriumCost.Dev.SP

theorem main (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (hcost : 0 < cost G f) (ε : ℝ) (hε : 0 ≤ ε)
    (f' : Flow G) (hf' : IsApproxNash G ε f')
    (B1 : ∀ P : Fin (routeCount G), 0 < f P →
      ∃ Q : Fin (routeCount G), strategyLatency G f' Q ≤ strategyLatency G f P) :
    cost G f' / cost G f ≤ 1 + ε := by
  obtain ⟨P0, hP0⟩ := exists_pos_flow G hf.1
  have hc := cost_nash G hf hP0
  obtain ⟨Q0, hQ0⟩ := B1 P0 hP0
  have h1 : cost G f' ≤ G.demand 0 * ((1 + ε) * strategyLatency G f P0) := by
    refine cost_le G hf'.1 _ fun r hr => ?_
    have := hf'.2 r Q0 (Subsingleton.elim _ _) hr
    calc strategyLatency G f' r ≤ (1 + ε) * strategyLatency G f' Q0 := this
      _ ≤ (1 + ε) * strategyLatency G f P0 :=
        mul_le_mul_of_nonneg_left hQ0 (by linarith)
  rw [div_le_iff₀ hcost, hc]
  linarith

end ApproxEquilibriumCost.Dev.B2

namespace ApproxEquilibriumCost.General.Supplement
theorem chk_theorem_B_2 (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (hcost : 0 < cost G f) (ε : ℝ) (hε : 0 ≤ ε)
    (f' : Flow G) (hf' : IsApproxNash G ε f') :
    cost G f' / cost G f ≤ 1 + ε :=
  ApproxEquilibriumCost.Dev.B2.main N G hG f hf hcost ε hε f' hf'
    (fun P hP => ApproxEquilibriumCost.General.Supplement.lemma_B_1 N G hG f hf f' hf'.1 P hP)
end ApproxEquilibriumCost.General.Supplement
end

theorem solution : type_of% @ApproxEquilibriumCost.General.Supplement.chk_theorem_B_2 := @ApproxEquilibriumCost.General.Supplement.chk_theorem_B_2
