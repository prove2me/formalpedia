-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Recursion_PhysicalRecursiveCost
-- name    : CSL_Interchange_Framework_Recursion_PhysicalRecursiveCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:56:09.978802+00:00
-- url     : https://prove2.me/theorems/68d30fb5-7500-4f8c-b663-6f07c25e6d78
-- title:
--   Coded sorting library: Interchange / Framework / Recursion / PhysicalRecursiveCost
-- statement:
--   Module `CodedSorting.Interchange.Framework.Recursion.PhysicalRecursiveCost` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Costs extracted from the same physical short/sparse/edge executions.
--   All intermediate source files are the actual preceding output files in the
--   relations defined by `PhysicalRecursiveExchange`.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Recursion.PhysicalRecursiveCost

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_PhysicalRecursiveExchange
import Definitions.Def_CSL_Shared_Memory_PhysicalLayerCost

/-! Costs extracted from the same physical short/sparse/edge executions.
All intermediate source files are the actual preceding output files in the
relations defined by `PhysicalRecursiveExchange`. -/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace CSL.PhysicalRecursiveCost
open RecursiveExchange RecursiveExchangeCost PhysicalRecursiveExchange PhysicalLayerCost ScanProgram
open Circuit CircuitProgram ProgramNetwork
open scoped BigOperators
noncomputable section

variable {σ : Type} {f P G S : ℕ} {hG : 0 < G} {hS : 0 < S}

theorem shortRun_local_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (c : Child) (F : EdgeStream f P G S) (state : σ) (source : File)
    (out : Output σ) (h : ShortRun L B hB child runChild c F state source out) :
    out.localCost ≤ 30*(longVolume f P G S/B+1) := by
  obtain ⟨preFile,cb,result,ca,hb,hc,ha,hs,hl,hr⟩ := h
  have hbefore := scalarBefore_cost_bound f P G S c B hB hb.execution
  have hafter := scalarAfter_cost_bound f P G S result.returned hS B hB ha.execution
  rw [hl]
  omega

theorem sparseRun_local_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (e : Edge)
    (ps : List (EdgeChild e)) (F : EdgeStream f P G S) (state : σ) (source : File)
    (out : Output σ) (h : SparseRun L B hB child runChild e ps F state source out) :
    out.localCost ≤ 30*ps.length*(longVolume f P G S/B+1) := by
  induction h with
  | nil => simp
  | cons p ps F state source head tail hh ht ih =>
    have hhcost := shortRun_local_cost L B hB child runChild ⟨e,p⟩ F state source head hh
    change head.localCost+tail.localCost ≤ _
    calc
      _ ≤ 30*(longVolume f P G S/B+1)+30*ps.length*(longVolume f P G S/B+1) :=
        Nat.add_le_add hhcost ih
      _ = _ := by simp only [List.length_cons]; ring

theorem totalConstant_append {V : ℕ} (xs ys : List (Pass V)) :
    totalConstant (xs++ys) = totalConstant xs+totalConstant ys := by
  simp only [totalConstant,List.map_append,List.sum_append]

def beforeConstant (e : Edge) : ℕ := factorConstant e .leftInverse+factorConstant e .right
def afterConstant (e : Edge) : ℕ := factorConstant e .left+factorConstant e .rightInverse
def edgeConstant (e : Edge) : ℕ := beforeConstant e+30*(edgePivots e).length+afterConstant e

theorem beforeProgram_constant (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S) (e : Edge) :
    totalConstant (beforeProgram f P G S hG hS e) ≤ beforeConstant e := by
  rw [beforeProgram,totalConstant_append]
  exact Nat.add_le_add (coordinateProgram_constant f e .leftInverse P G S hG hS)
    (coordinateProgram_constant f e .right P G S hG hS)

theorem afterProgram_constant (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S) (e : Edge) :
    totalConstant (afterProgram f P G S hG hS e) ≤ afterConstant e := by
  rw [afterProgram,totalConstant_append]
  exact Nat.add_le_add (coordinateProgram_constant f e .left P G S hG hS)
    (coordinateProgram_constant f e .rightInverse P G S hG hS)

theorem edgeRun_local_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (e : Edge) (F : EdgeStream f P G S) (state : σ) (source : File) (out : Output σ)
    (h : EdgeRun L B hB child runChild e F state source out) :
    out.localCost ≤ edgeConstant e*(longVolume f P G S/B+1) := by
  obtain ⟨preFile,cb,middle,ca,hb,hm,ha,hs,hl,hr⟩ := h
  have hbefore := (execution_cost_bound B hB hb.execution).trans
    (Nat.mul_le_mul_right _ (beforeProgram_constant f P G S hG hS e))
  have hmiddle := sparseRun_local_cost L B hB child runChild e (edgePivots e)
    _ state preFile middle hm
  have hafter := (execution_cost_bound B hB ha.execution).trans
    (Nat.mul_le_mul_right _ (afterProgram_constant f P G S hG hS e))
  rw [hl]
  calc
    _ ≤ beforeConstant e*(longVolume f P G S/B+1)+
        30*(edgePivots e).length*(longVolume f P G S/B+1)+
        afterConstant e*(longVolume f P G S/B+1) :=
      Nat.add_le_add (Nat.add_le_add hbefore hmiddle) hafter
    _ = _ := by unfold edgeConstant; ring

/-- This is the induction hypothesis for the concrete smaller file runner.
It applies only to its genuine successful child executions. -/
def ChildCostBound (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ) : Prop :=
  ∀ c F state source result,
    ChildRun L.layout B hB child runChild c F state source result → result.cost ≤ C

theorem shortRun_recursive_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ)
    (hcost : ChildCostBound L B hB child runChild C)
    (c : Child) (F : EdgeStream f P G S) (state : σ) (source : File)
    (out : Output σ) (h : ShortRun L B hB child runChild c F state source out) :
    out.recursiveCost ≤ C := by
  obtain ⟨preFile,cb,result,ca,hb,hc,ha,hs,hl,hr⟩ := h
  rw [hr]
  exact hcost c _ state preFile result hc

theorem sparseRun_recursive_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ)
    (hcost : ChildCostBound L B hB child runChild C) (e : Edge)
    (ps : List (EdgeChild e)) (F : EdgeStream f P G S) (state : σ) (source : File)
    (out : Output σ) (h : SparseRun L B hB child runChild e ps F state source out) :
    out.recursiveCost ≤ ps.length*C := by
  induction h with
  | nil => simp
  | cons p ps F state source head tail hh ht ih =>
    have hhcost := shortRun_recursive_cost L B hB child runChild C hcost
      ⟨e,p⟩ F state source head hh
    change head.recursiveCost+tail.recursiveCost ≤ _
    calc
      _ ≤ C+ps.length*C := Nat.add_le_add hhcost ih
      _ = _ := by simp only [List.length_cons]; ring

theorem edgeRun_recursive_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ)
    (hcost : ChildCostBound L B hB child runChild C)
    (e : Edge) (F : EdgeStream f P G S) (state : σ) (source : File) (out : Output σ)
    (h : EdgeRun L B hB child runChild e F state source out) :
    out.recursiveCost ≤ (edgePivots e).length*C := by
  obtain ⟨preFile,cb,middle,ca,hb,hm,ha,hs,hl,hr⟩ := h
  rw [hr]
  exact sparseRun_recursive_cost L B hB child runChild C hcost e (edgePivots e)
    _ state preFile middle hm

theorem factor_sum (c : Factor → ℕ) :
    (∑ a : Factor,c a) = c .leftInverse+c .right+c .left+c .rightInverse := by
  have hu : (Finset.univ : Finset Factor) =
      {.left,.right,.leftInverse,.rightInverse} := by decide
  rw [hu]
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,
    reduceCtorEq,or_self,not_false_eq_true,Finset.sum_singleton]
  omega

theorem edgeConstant_eq (e : Edge) :
    edgeConstant e = (∑ a : Factor,factorConstant e a)+30*(edgePivots e).length := by
  rw [factor_sum]
  unfold edgeConstant beforeConstant afterConstant
  ring

/-- The sum contains exactly the actual pivot budget S from the network,
including the final wires entering sinks. -/
theorem edgeConstant_sum :
    (∑ e : Edge,edgeConstant e) =
      (∑ e : Edge,∑ a : Factor,factorConstant e a)+30*Parameters.S := by
  simp_rw [edgeConstant_eq]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  simp_rw [edgePivots_length]
  rw [edge_rank_sum]

/-- One fixed construction-dependent coefficient for an entire eager layer,
using the exact edge schedule, not a maximum multiplied by unknown work. -/
def wholeConstant : ℕ := ∑ e : Edge,(edgeConstant e+3*edgeGateScans e)

theorem sum_cost_bound (B V : ℕ) (edgeCosts gateCosts : Edge → ℕ)
    (he : ∀ e,edgeCosts e ≤ edgeConstant e*(V/B+1))
    (hg : ∀ e,gateCosts e ≤ 3*edgeGateScans e*(V/B+1)) :
    (∑ e : Edge,(edgeCosts e+gateCosts e)) ≤
      (∑ e : Edge,(edgeConstant e+3*edgeGateScans e))*(V/B+1) := by
  calc
    _ ≤ ∑ e : Edge,(edgeConstant e+3*edgeGateScans e)*(V/B+1) := by
      apply Finset.sum_le_sum
      intro e _
      rw [Nat.add_mul]
      exact Nat.add_le_add (he e) (hg e)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem gateRun_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File) (e : Edge)
    (result : GateStreamMachine.Result)
    (h : GateRun L B hB input stored inputFiles storedFiles e result) :
    result.cost ≤ 3*edgeGateScans e*(longVolume f P G S/B+1) := by
  rw [h.cost_eq]
  change edgeGateScans e*(3*((longVolume f P G S+B-1)/B)) ≤ _
  calc
    _ ≤ edgeGateScans e*(3*(longVolume f P G S/B+1)) := Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left 3 (ceil_le_floor_add_one _ B hB))
    _ = _ := by ring

theorem rowsRun_local_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (rs : List Reg)
    (table : Reg → EdgeStream f P G S) (files : Reg → File) (state : σ) (out : RowsOutput σ)
    (h : RowsRun L B hB child runChild input stored inputFiles storedFiles t rs table files state out) :
    out.localCost ≤ ((rs.map (fun r => edgeConstant (t,r)+3*edgeGateScans (t,r))).sum)*
      (longVolume f P G S/B+1) := by
  induction h with
  | nil => simp
  | cons r rs table files state gate head tail hg he ht ih =>
    have hgate := gateRun_cost L B hB input stored inputFiles storedFiles (t,r) gate hg
    have hedge := edgeRun_local_cost L B hB child runChild (t,r) _ state gate.disk head he
    change gate.cost+head.localCost+tail.localCost ≤ _
    calc
      _ ≤ 3*edgeGateScans (t,r)*(longVolume f P G S/B+1)+
          edgeConstant (t,r)*(longVolume f P G S/B+1)+
          ((rs.map (fun r => edgeConstant (t,r)+3*edgeGateScans (t,r))).sum)*
            (longVolume f P G S/B+1) := Nat.add_le_add (Nat.add_le_add hgate hedge) ih
      _ = _ := by simp only [List.map_cons,List.sum_cons]; ring

theorem rowsRun_recursive_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ)
    (hcost : ChildCostBound L B hB child runChild C)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (rs : List Reg)
    (table : Reg → EdgeStream f P G S) (files : Reg → File) (state : σ) (out : RowsOutput σ)
    (h : RowsRun L B hB child runChild input stored inputFiles storedFiles t rs table files state out) :
    out.recursiveCost ≤ ((rs.map (fun r => (edgePivots (t,r)).length)).sum)*C := by
  induction h with
  | nil => simp
  | cons r rs table files state gate head tail hg he ht ih =>
    have hedge := edgeRun_recursive_cost L B hB child runChild C hcost
      (t,r) _ state gate.disk head he
    change head.recursiveCost+tail.recursiveCost ≤ _
    calc
      _ ≤ (edgePivots (t,r)).length*C+
          ((rs.map (fun r => (edgePivots (t,r)).length)).sum)*C := Nat.add_le_add hedge ih
      _ = _ := by simp only [List.map_cons,List.sum_cons]; ring

theorem layerRun_local_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ) (out : LayerOutput σ)
    (h : LayerRun L B hB child runChild input stored inputFiles storedFiles t state out) :
    out.localCost ≤ (∑ r : Reg,(edgeConstant (t,r)+3*edgeGateScans (t,r)))*
      (longVolume f P G S/B+1) := by
  obtain ⟨rows,hr,hf,hs,hl,hc⟩ := h
  rw [hl]
  simpa only [Finset.sum_map_toList] using rowsRun_local_cost L B hB child runChild
    input stored inputFiles storedFiles t (Finset.univ : Finset Reg).toList
      input inputFiles state rows hr

theorem layerRun_recursive_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ)
    (hcost : ChildCostBound L B hB child runChild C)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ) (out : LayerOutput σ)
    (h : LayerRun L B hB child runChild input stored inputFiles storedFiles t state out) :
    out.recursiveCost ≤ (∑ r : Reg,(edgePivots (t,r)).length)*C := by
  obtain ⟨rows,hr,hf,hs,hl,hc⟩ := h
  rw [hc]
  simpa only [Finset.sum_map_toList] using rowsRun_recursive_cost L B hB child runChild
    C hcost input stored inputFiles storedFiles t (Finset.univ : Finset Reg).toList
      input inputFiles state rows hr

end
end CSL.PhysicalRecursiveCost


