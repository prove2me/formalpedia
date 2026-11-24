-- Prove2me | Definitions.Def_CSL_Shared_Memory_PhysicalLayerCost
-- name    : CSL_Shared_Memory_PhysicalLayerCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:20:25.862984+00:00
-- url     : https://prove2.me/theorems/78c39649-8042-4505-ad42-48c5aa07e17d
-- title:
--   Coded sorting library: Shared / Memory / PhysicalLayerCost
-- statement:
--   Module `CodedSorting.Shared.Memory.PhysicalLayerCost` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Costs of the executions that actually occur in a physical layer.
--   The bounds below apply to any recorded execution, rather than selecting a
--   second family of independently executed primitive calls.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.PhysicalLayerCost

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchangeCost
import Definitions.Def_CSL_Shared_Programs_NodeStreamMachine

/-! Costs of the executions that actually occur in a physical layer.
The bounds below apply to any recorded execution, rather than selecting a
second family of independently executed primitive calls. -/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace CSL.PhysicalLayerCost
open ScanProgram RecursiveExchange RecursiveExchangeCost
open scoped BigOperators

variable {V : ℕ} {Value : Type*} [Inhabited Value]

/-- A primitive's recorded transfer count is determined by its input file. -/
theorem step_cost_unique (p : Pass V) (F : Fin V → Value)
    (B : ℕ) (hB : 0 < B) {c d : ℕ}
    (hc : StepEvidence p F B hB c) (hd : StepEvidence p F B hB d) : c = d := by
  cases p with
  | streams K e key hi =>
    obtain ⟨r,hr,_,hcr,_,_⟩ := hc
    obtain ⟨s,hs,_,hds,_,_⟩ := hd
    have he : r = s := Option.some.inj (hr.symm.trans hs)
    exact hcr.trans (he ▸ hds.symm)
  | reverse T L hL hV =>
    let source : BlockReflection.Disk Value :=
      fun i => if h : i < V then F ⟨i,h⟩ else default
    have hs : ∀ y : Fin V, source y.val = F y := by intro y; simp [source,y.isLt]
    exact (hc source source hs).1.trans (hd source source hs).1.symm

theorem step_cost_bound (p : Pass V) (F : Fin V → Value)
    (B : ℕ) (hB : 0 < B) {c : ℕ} (hc : StepEvidence p F B hB c) :
    c ≤ p.constant * (V / B + 1) := by
  obtain ⟨d,hd,hbound⟩ := pass_correct p F B hB
  exact (step_cost_unique p F B hB hc hd) ▸ hbound

/-- The same sequential execution supplies both the intermediate arrays and
the bounded cost. No fresh execution is substituted into this statement. -/
theorem execution_cost_bound (B : ℕ) (hB : 0 < B)
    {ps : List (Pass V)} {F : Fin V → Value} {cost : ℕ}
    (h : Execution B hB ps F cost) :
    cost ≤ totalConstant ps * (V / B + 1) := by
  induction h with
  | nil F => simp [totalConstant]
  | cons p ps F c d hc hd ih =>
    simpa only [totalConstant,List.map_cons,List.sum_cons,Nat.add_mul] using
      Nat.add_le_add (step_cost_bound p F B hB hc) ih

theorem coordinate_cost_bound (f : ℕ) (e : Edge) (a : Factor)
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (B : ℕ) (hB : 0 < B)
    {input : Fin (longVolume f P G S) → Value} {cost : ℕ}
    (h : Execution B hB (coordinateProgram f e a P G S hG hS) input cost) :
    cost ≤ factorConstant e a * (longVolume f P G S / B + 1) :=
  (execution_cost_bound B hB h).trans
    (Nat.mul_le_mul_right _ (coordinateProgram_constant f e a P G S hG hS))

theorem scalarBefore_cost_bound (f P G S : ℕ) (c : Child)
    (B : ℕ) (hB : 0 < B)
    {input : Fin (longVolume f P G S) → Value} {cost : ℕ}
    (h : Execution B hB (scalarBefore f P G S c) input cost) :
    cost ≤ 10 * (longVolume f P G S / B + 1) := by
  simpa only [scalarBefore_constant] using execution_cost_bound B hB h

theorem scalarAfter_cost_bound (f P G S : ℕ) (c : Child) (hS : 0 < S)
    (B : ℕ) (hB : 0 < B)
    {input : Fin (longVolume f P G S) → Value} {cost : ℕ}
    (h : Execution B hB (scalarAfter f P G S c hS) input cost) :
    cost ≤ 20 * (longVolume f P G S / B + 1) := by
  simpa only [scalarAfter_constant] using execution_cost_bound B hB h

/-- The address evidence supplied by the enclosing evaluator is sufficient:
there is no existential replacement of any of its intermediate inputs. -/
theorem addressWork_cost_bound (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (factorInputs : Edge → Factor → Fin (longVolume f P G S) → Value)
    (beforeInputs afterInputs : Child → Fin (longVolume f P G S) → Value)
    (B : ℕ) (hB : 0 < B) {cost : ℕ}
    (h : AddressWork f P G S hG hS factorInputs beforeInputs afterInputs B hB cost) :
    cost ≤ addressLocalConstant * (longVolume f P G S / B + 1) := by
  obtain ⟨factors,before,after,hf,hb,ha,rfl⟩ := h
  have hfactor : (∑ e,∑ a,factors e a) ≤
      allCoordinateConstant * (longVolume f P G S / B + 1) := by
    calc
      _ ≤ ∑ e,∑ a,factorConstant e a * (longVolume f P G S / B + 1) :=
        Finset.sum_le_sum (fun e _ => Finset.sum_le_sum
          (fun a _ => coordinate_cost_bound f e a P G S hG hS B hB (hf e a)))
      _ = _ := by simp only [allCoordinateConstant,Finset.sum_mul]
  have hscalar : (∑ c : Child,(before c+after c)) ≤
      30*Parameters.S*(longVolume f P G S/B+1) := by
    calc
      _ ≤ ∑ _c : Child,30*(longVolume f P G S/B+1) := by
        apply Finset.sum_le_sum
        intro c _
        have hb' := scalarBefore_cost_bound f P G S c B hB (hb c)
        have ha' := scalarAfter_cost_bound f P G S c hS B hB (ha c)
        omega
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul]
        ring
  simpa only [addressLocalConstant,Nat.add_mul] using Nat.add_le_add hfactor hscalar

noncomputable section
open Circuit CircuitProgram ProgramNetwork NodeStreamMachine BucketMachine

def edgeGateScans (e : Edge) : ℕ :=
  nodeScans (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) e) ⟨e,rfl⟩

def gateLocalConstant : ℕ := ∑ e : Edge,3*edgeGateScans e

def physicalLocalConstant : ℕ := addressLocalConstant+gateLocalConstant

/-- The output file is the result of the actual port-restricted node machine;
the exact cost follows from equality of the same deterministic run. -/
theorem edgeGate_cost (e : Edge) (B V : ℕ) (hB : 0 < B)
    (values : InputPort (globalProgram Parameters.d)
      (wireTail (globalProgram Parameters.d) e) → Fin V → Bit)
    (result : GateStreamMachine.Result)
    (hr : nodeOutput B V (globalProgram Parameters.d)
      (wireTail (globalProgram Parameters.d) e)
      (fun port => pack B hB (List.ofFn (values port))) ⟨e,rfl⟩ = some result) :
    result.cost = edgeGateScans e*(3*((V+B-1)/B)) := by
  have he := nodeOutput_correct B V hB (globalProgram Parameters.d)
    (wireTail (globalProgram Parameters.d) e) values ⟨e,rfl⟩
  exact congrArg GateStreamMachine.Result.cost (Option.some.inj (hr.symm.trans he))

theorem edgeGate_cost_bound (e : Edge) (B V : ℕ) (hB : 0 < B)
    (values : InputPort (globalProgram Parameters.d)
      (wireTail (globalProgram Parameters.d) e) → Fin V → Bit)
    (result : GateStreamMachine.Result)
    (hr : nodeOutput B V (globalProgram Parameters.d)
      (wireTail (globalProgram Parameters.d) e)
      (fun port => pack B hB (List.ofFn (values port))) ⟨e,rfl⟩ = some result) :
    result.cost ≤ 3*edgeGateScans e*(V/B+1) := by
  rw [edgeGate_cost e B V hB values result hr]
  calc
    _ ≤ edgeGateScans e*(3*(V/B+1)) := Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ (ceil_le_floor_add_one V B hB))
    _ = _ := by ring

/-- Sum of the node runs actually recorded by a whole-layer execution. -/
theorem allGates_cost_bound (B V : ℕ) (hB : 0 < B)
    (values : (e : Edge) → InputPort (globalProgram Parameters.d)
      (wireTail (globalProgram Parameters.d) e) → Fin V → Bit)
    (results : Edge → GateStreamMachine.Result)
    (hr : ∀ e,nodeOutput B V (globalProgram Parameters.d)
      (wireTail (globalProgram Parameters.d) e)
      (fun port => pack B hB (List.ofFn (values e port))) ⟨e,rfl⟩ = some (results e)) :
    (∑ e,(results e).cost) ≤ gateLocalConstant*(V/B+1) := by
  calc
    _ ≤ ∑ e : Edge,3*edgeGateScans e*(V/B+1) := Finset.sum_le_sum
      (fun e _ => edgeGate_cost_bound e B V hB (values e) (results e) (hr e))
    _ = _ := by simp only [gateLocalConstant,Finset.sum_mul]

/-- Arithmetic combination used after extracting the actual address and node
cost bounds above from a single physical-layer run. -/
theorem add_local_cost_bounds (B V addressCost gateCost : ℕ)
    (ha : addressCost ≤ addressLocalConstant*(V/B+1))
    (hg : gateCost ≤ gateLocalConstant*(V/B+1)) :
    addressCost+gateCost ≤ (addressLocalConstant+gateLocalConstant)*(V/B+1) :=
  (Nat.add_le_add ha hg).trans
    (le_of_eq (Nat.add_mul addressLocalConstant gateLocalConstant (V/B+1)).symm)

theorem local_cost_outside_cutoff (B V cost : ℕ) (hV : B ≤ V)
    (hc : cost ≤ physicalLocalConstant*(V/B+1)) :
    cost*B ≤ 2*physicalLocalConstant*V :=
  absorb_startup V B physicalLocalConstant cost hV hc

end

end CSL.PhysicalLayerCost


