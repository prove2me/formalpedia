-- Prove2me | Definitions.Def_CSL_Shared_Programs_StatefulControlCost
-- name    : CSL_Shared_Programs_StatefulControlCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:16:43.208795+00:00
-- url     : https://prove2.me/theorems/74623829-5ff3-4919-b2cb-c5d1063ddccf
-- title:
--   Coded sorting library: Shared / Programs / StatefulControlCost
-- statement:
--   Module `CodedSorting.Shared.Programs.StatefulControlCost` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Costs of the actual sequential, state-threaded edge evaluator. The
--   measure below is read from the returned state; it is not a second tree walk.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.StatefulControlCost

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_StatefulRecursiveExchange

/-! Costs of the actual sequential, state-threaded edge evaluator. The
measure below is read from the returned state; it is not a second tree walk. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace CSL.StatefulControlCost
open StatefulRecursiveExchange RecursiveExchange Circuit CircuitProgram ProgramNetwork
open Address CodedSimulation MatrixFactorization TensorLabels
open scoped BigOperators
noncomputable section

variable {σ α ι : Type}

theorem sequence_cost (step : α → ι → σ → α × σ)
    (Safe : σ → Prop) (measure : σ → ℕ) (cost : ι → ℕ)
    (hstep : ∀ value i state, Safe state → Safe (step value i state).2 ∧
      measure (step value i state).2 = measure state + cost i)
    (is : List ι) (value : α) (state : σ) (hs : Safe state) :
    Safe (sequence step is value state).2 ∧
      measure (sequence step is value state).2 = measure state + (is.map cost).sum := by
  induction is generalizing value state with
  | nil => exact ⟨hs,by simp [StatefulRecursiveExchange.sequence]⟩
  | cons i is ih =>
    obtain ⟨hs',hc⟩ := hstep value i state hs
    obtain ⟨hsout,hcout⟩ := ih (step value i state).1 (step value i state).2 hs'
    refine ⟨hsout,?_⟩
    simpa only [StatefulRecursiveExchange.sequence,List.map_cons,List.sum_cons,hc,Nat.add_assoc] using hcout

theorem tabulate_cost {Key Value : Type} [DecidableEq Key]
    (keys : List Key) (run : Key → σ → Value × σ) (initial : Key → Value)
    (Safe : σ → Prop) (measure : σ → ℕ) (cost : Key → ℕ)
    (hrun : ∀ key state, Safe state → Safe (run key state).2 ∧
      measure (run key state).2 = measure state + cost key)
    (state : σ) (hs : Safe state) :
    Safe (tabulate keys run initial state).2 ∧
      measure (tabulate keys run initial state).2 = measure state + (keys.map cost).sum :=
  sequence_cost (fun table key st =>
    (Function.update table key (run key st).1,(run key st).2))
    Safe measure cost (fun _ key st h => hrun key st h) keys initial state hs

variable {Prefix Gap Suffix : Type}

theorem edge_cost (f : ℕ) (e : Edge)
    (child : ChildAction (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) σ f)
    (Safe : σ → Prop) (measure : σ → ℕ) (C : ℕ)
    (hchild : ∀ c F state, Safe state → Safe (child c F state).2 ∧
      measure (child c F state).2 = measure state + C)
    (F : Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) (state : σ)
    (hs : Safe state) :
    Safe (edgeProgram f e child F state).2 ∧
      measure (edgeProgram f e child F state).2 = measure state + (edgePivots e).length*C := by
  have hstep : ∀ stream (p : EdgeChild e) s, Safe s →
      Safe (shortStep f child stream ⟨e,p⟩ s).2 ∧
      measure (shortStep f child stream ⟨e,p⟩ s).2 = measure s + C := by
    intro stream p s hsafe
    exact hchild ⟨e,p⟩ _ s hsafe
  obtain ⟨hvalid,hcost⟩ := sequence_cost
    (fun stream p => shortStep f child stream ⟨e,p⟩) Safe measure (fun _ => C)
    hstep (edgePivots e) (transport (coordinatePermutation f e) F) state hs
  refine ⟨hvalid, ?_⟩
  first
  | exact hcost
  | (have h_sx := hcost; simp only [List.map_const',List.sum_replicate] at h_sx ⊢; exact h_sx)
  | (have h_sx := hcost; simp only [List.map_const',List.sum_replicate] at h_sx; exact h_sx)
  | (simp only [List.map_const',List.sum_replicate]; exact hcost)

theorem layer_cost (f : ℕ)
    (input : Reg → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (stored : DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (move : Edge → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → σ →
      Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f × σ)
    (Safe : σ → Prop) (measure : σ → ℕ) (cost : Edge → ℕ)
    (hmove : ∀ e F state, Safe state → Safe (move e F state).2 ∧
      measure (move e F state).2 = measure state + cost e)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ) (hs : Safe state) :
    Safe (layer f input stored move t state).2 ∧
      measure (layer f input stored move t state).2 = measure state + ∑ r : Reg, cost (t,r) := by
  try dsimp only [layer]
  obtain ⟨hvalid,hcost⟩ := tabulate_cost (Finset.univ : Finset Reg).toList
    (fun r => move (t,r) (gateInput f input stored (t,r))) (fun _ _ => 0)
    Safe measure (fun r => cost (t,r)) (fun r s h => hmove (t,r) _ s h) state hs
  exact ⟨hvalid,by simpa only [Finset.sum_map_toList] using hcost⟩

def prefixCost (cost : Edge → ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => prefixCost cost t + if ht : t < (globalProgram Parameters.d).length+1
      then ∑ r : Reg, cost (⟨t,ht⟩,r) else 0

theorem execute_cost (f : ℕ)
    (input : Reg → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (move : Edge → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → σ →
      Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f × σ)
    (Safe : σ → Prop) (measure : σ → ℕ) (cost : Edge → ℕ)
    (hmove : ∀ e F state, Safe state → Safe (move e F state).2 ∧
      measure (move e F state).2 = measure state + cost e)
    (t : ℕ) (state : σ) (hs : Safe state) :
    Safe (execute f input move t state).2 ∧
      measure (execute f input move t state).2 = measure state + prefixCost cost t := by
  induction t with
  | zero => exact ⟨hs,by simp [execute,prefixCost]⟩
  | succ t ih =>
    by_cases ht : t < (globalProgram Parameters.d).length+1
    · obtain ⟨hv,hcost⟩ := layer_cost f input (execute f input move t state).1 move
        Safe measure cost hmove ⟨t,ht⟩ (execute f input move t state).2 ih.1
      refine ⟨by simpa only [execute,dif_pos ht] using hv,?_⟩
      simpa only [execute,dif_pos ht,prefixCost,ih.2,Nat.add_assoc] using hcost
    · simpa only [execute,dif_neg ht,prefixCost,Nat.add_zero] using ih

theorem prefixCost_eq (cost : Edge → ℕ) (t : ℕ)
    (ht : t ≤ (globalProgram Parameters.d).length+1) :
    prefixCost cost t = ∑ i : Fin t, ∑ r : Reg, cost (⟨i.val,lt_of_lt_of_le i.isLt ht⟩,r) := by
  induction t with
  | zero => simp [prefixCost]
  | succ t ih =>
    have hprev : t ≤ (globalProgram Parameters.d).length+1 := by omega
    have hlt : t < (globalProgram Parameters.d).length+1 := by omega
    rw [prefixCost,dif_pos hlt,ih hprev,Fin.sum_univ_castSucc]
    rfl

theorem full_cost {Rows : ℕ} (f : ℕ)
    (child : ChildAction (Prefix := Fin Rows) (Gap := Gap) (Suffix := Suffix) σ f)
    (Safe : σ → Prop) (measure : σ → ℕ) (C : ℕ)
    (hchild : ∀ c F state, Safe state → Safe (child c F state).2 ∧
      measure (child c F state).2 = measure state + C)
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit)
    (state : σ) (hs : Safe state) :
    Safe (full f child F state).2 ∧
      measure (full f child F state).2 = measure state + Parameters.S*C := by
  try dsimp only [full,middle]
  obtain ⟨hvalid,hcost⟩ := execute_cost f
    (splitInput f (transport (mapPairEquiv lowerSubtractEquiv) F))
    (fun e => edgeProgram f e child) Safe measure (fun e => (edgePivots e).length*C)
    (fun e stream s h => edge_cost f e child Safe measure C hchild stream s h)
    ((globalProgram Parameters.d).length+1) state hs
  refine ⟨hvalid,?_⟩
  rw [prefixCost_eq _ _ (Nat.le_refl _)] at hcost
  simp_rw [← Finset.sum_mul] at hcost
  simpa only [eager_child_count] using hcost

end
end CSL.StatefulControlCost


