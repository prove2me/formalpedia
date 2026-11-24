-- Prove2me | Definitions.Def_CSL_Circuit_NetworkModel_Framework_PhysicalNetworkCost
-- name    : CSL_Circuit_NetworkModel_Framework_PhysicalNetworkCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T16:14:36.097989+00:00
-- url     : https://prove2.me/theorems/13a9672a-3586-41a4-a709-f5924b7060b3
-- title:
--   Coded sorting library: Circuit / NetworkModel / Framework / PhysicalNetworkCost
-- statement:
--   Module `CodedSorting.Circuit.NetworkModel.Framework.PhysicalNetworkCost` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   The complete eager circuit on external files. Empty future-wire slots
--   are never read: every node's actual incoming wires have smaller stage index.
--   No zero-filled payload file is manufactured during initialization.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.NetworkModel.Framework.PhysicalNetworkCost

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_PhysicalEdgeProgramCounter
import Definitions.Def_CSL_Interchange_Framework_Recursion_PhysicalRecursiveCost
import Definitions.Def_CSL_Shared_Programs_StatefulControlCost

section PhysicalNetwork
/-! The complete eager circuit on external files. Empty future-wire slots
are never read: every node's actual incoming wires have smaller stage index.
No zero-filled payload file is manufactured during initialization. -/

set_option maxRecDepth 4096
namespace CSL.PhysicalNetwork
open PhysicalRecursiveExchange RecursiveExchange RecursiveExchangeCost
open Circuit CircuitProgram ProgramNetwork
noncomputable section

variable {σ : Type} {f P G S : ℕ} {hG : 0 < G} {hS : 0 < S}

def execute (B : ℕ) (hB : 0 < B) (runChild : FileChild σ)
    (inputFiles : Reg → File) : ℕ → σ → Option (LayerOutput σ)
  | 0,state => some ⟨fun _ => [],state,0,0⟩
  | n+1,state => do
      let before ← execute B hB runChild inputFiles n state
      if hn : n < (globalProgram Parameters.d).length+1 then
        let after ← executeLayer (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
          B hB runChild inputFiles before.files ⟨n,hn⟩ before.state
        return ⟨after.files,after.state,before.localCost+after.localCost,
          before.recursiveCost+after.recursiveCost⟩
      else some before

inductive NetworkRun (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (inputFiles : Reg → File) (state : σ) :
    ℕ → LayerOutput σ → Prop
  | zero : NetworkRun L B hB child runChild input inputFiles state 0
      ⟨fun _ => [],state,0,0⟩
  | succ (n : ℕ) (hn : n < (globalProgram Parameters.d).length+1)
      (before after : LayerOutput σ)
      (hb : NetworkRun L B hB child runChild input inputFiles state n before)
      (ha : LayerRun L B hB child runChild input
        (StatefulRecursiveExchange.execute f input
          (fun e => StatefulRecursiveExchange.edgeProgram f e child) n state).1
        inputFiles before.files ⟨n,hn⟩ before.state after) :
      NetworkRun L B hB child runChild input inputFiles state (n+1)
        ⟨after.files,after.state,before.localCost+after.localCost,
          before.recursiveCost+after.recursiveCost⟩

theorem NetworkRun.actual (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (inputFiles : Reg → File) (state : σ)
    (n : ℕ) (out : LayerOutput σ)
    (h : NetworkRun L B hB child runChild input inputFiles state n out) :
    execute (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB runChild inputFiles n state = some out := by
  induction h with
  | zero => rfl
  | succ n hn before after hb ha ih =>
    simp [execute,ih,hn,LayerRun.actual L B hB child runChild _ _ _ _ _ _ _ ha]

theorem NetworkRun.projection (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (inputFiles : Reg → File) (state : σ)
    (n : ℕ) (out : LayerOutput σ)
    (h : NetworkRun L B hB child runChild input inputFiles state n out) :
    let expected := StatefulRecursiveExchange.execute f input
      (fun e => StatefulRecursiveExchange.edgeProgram f e child) n state
    (∀ e,e.1.val<n → out.files e = represented L.layout B hB (expected.1 e)) ∧
      out.state = expected.2 := by
  induction h with
  | zero => exact ⟨fun e he => (Nat.not_lt_zero _ he).elim,rfl⟩
  | succ n hn before after hb ha ih =>
    have hp := LayerRun.projection L B hB child runChild _ _ _ _ _ _ _ ha
    rw [ih.2] at hp
    constructor
    · intro e he
      by_cases hstage : e.1 = (⟨n,hn⟩ : Fin ((globalProgram Parameters.d).length+1))
      · simpa only [StatefulRecursiveExchange.execute,dif_pos hn] using hp.1 e hstage
      · have hlt : e.1.val<n := by
          have hne : e.1.val ≠ n := fun h => hstage (Fin.ext h)
          omega
        rw [hp.2.2 e hstage,ih.1 e hlt]
        congr 1
        simp only [StatefulRecursiveExchange.execute,dif_pos hn,StatefulRecursiveExchange.layer,
          if_neg hstage]
    · simpa only [StatefulRecursiveExchange.execute,dif_pos hn] using hp.2.1

theorem networkRun_exists (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (hc : ChildAvailable L.layout B hB child runChild)
    (input : Reg → EdgeStream f P G S) (inputFiles : Reg → File) (state : σ)
    (hi : ∀ r,inputFiles r = represented L.layout B hB (input r))
    (n : ℕ) (hn : n ≤ (globalProgram Parameters.d).length+1) :
    ∃ out, NetworkRun L B hB child runChild input inputFiles state n out := by
  induction n with
  | zero => exact ⟨_,.zero⟩
  | succ n ih =>
    obtain ⟨before,hb⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
    have hp := NetworkRun.projection L B hB child runChild _ _ _ _ _ hb
    have hlt : n < (globalProgram Parameters.d).length+1 := hn
    obtain ⟨after,ha⟩ := layerRun_exists L B hB child runChild hc input _ inputFiles before.files
      ⟨n,hlt⟩ before.state hi hp.1
    exact ⟨_,.succ n hlt before after hb ha⟩

/-- The concrete codec removes every address-layout premise. The only
remaining premise is the smaller recursive child's actual file execution. -/
theorem actual_network_execution (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (hc : ChildAvailable (actualLayouts f P G S hG hS).layout B hB child runChild)
    (input : Reg → EdgeStream f P G S) (inputFiles : Reg → File) (state : σ)
    (hi : ∀ r,inputFiles r = represented (actualLayouts f P G S hG hS).layout B hB (input r)) :
    ∃ out, NetworkRun (actualLayouts f P G S hG hS) B hB child runChild input inputFiles state
        ((globalProgram Parameters.d).length+1) out ∧
      execute (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
        B hB runChild inputFiles ((globalProgram Parameters.d).length+1) state = some out ∧
      (∀ e,out.files e = represented (actualLayouts f P G S hG hS).layout B hB
        ((StatefulRecursiveExchange.execute f input
          (fun e => StatefulRecursiveExchange.edgeProgram f e child)
          ((globalProgram Parameters.d).length+1) state).1 e)) := by
  obtain ⟨out,hout⟩ := networkRun_exists (actualLayouts f P G S hG hS) B hB child runChild hc
    input inputFiles state hi _ le_rfl
  exact ⟨out,hout,NetworkRun.actual _ _ _ _ _ _ _ _ _ _ hout,
    fun e => (NetworkRun.projection _ _ _ _ _ _ _ _ _ _ hout).1 e e.1.isLt⟩

end
end CSL.PhysicalNetwork
end PhysicalNetwork

section PhysicalNetworkContinuation
/-! Chronological, defunctionalized code for the actual network evaluator.
The incoming directory stays frozen throughout a layer. A separate outgoing
directory is committed at the end of that layer, exactly as in executeRows.
Directories below describe external files; their finite resident handles
and physical allocation are a separate representation obligation. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace CSL.PhysicalNetworkContinuation
open PhysicalRecursiveExchange RecursiveExchange RecursiveExchangeCost
open Circuit CircuitProgram
noncomputable section

abbrev EdgeInstruction := PhysicalEdgeContinuation.Instruction
abbrev Active := PhysicalEdgeContinuation.State

inductive Instruction where
  | gate (edge : Edge)
  | edge (op : EdgeInstruction)
  | store (reg : Reg)
  | beginLayer
  | commit (stage : Fin ((globalProgram Parameters.d).length+1))

structure State (σ : Type) where
  inputs : Reg → File
  wires : Edge → File
  rows : Reg → File
  active : Active σ

def step {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) : Instruction → State σ → Option (State σ)
  | .gate e,s => (executeGate B (longVolume f P G S) s.inputs s.wires e).map fun out =>
      {s with active := {s.active with file := out.disk,localCost := s.active.localCost+out.cost}}
  | .edge op,s => (PhysicalEdgeContinuation.step f P G S B hG hS hB child op s.active).map
      fun active => {s with active := active}
  | .store r,s => some {s with rows := Function.update s.rows r s.active.file}
  | .beginLayer,s => some {s with rows := s.inputs}
  | .commit t,s => some {s with wires := fun e => if e.1=t then s.rows e.2 else s.wires e}

def run {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) : List Instruction → State σ → Option (State σ)
  | [],s => some s
  | op::ops,s => (step f P G S B hG hS hB child op s).bind
      (run f P G S B hG hS hB child ops)

def rowCode (t : Fin ((globalProgram Parameters.d).length+1)) (r : Reg) : List Instruction :=
  [.gate (t,r)] ++ (PhysicalEdgeContinuation.edgeCode (t,r)).map .edge ++ [.store r]
def rowsCode (t : Fin ((globalProgram Parameters.d).length+1)) (rs : List Reg) : List Instruction :=
  rs.flatMap (rowCode t)
def layerCode (t : Fin ((globalProgram Parameters.d).length+1)) : List Instruction :=
  [.beginLayer] ++ rowsCode t (Finset.univ : Finset Reg).toList ++ [.commit t]
def networkCode : ℕ → List Instruction
  | 0 => []
  | n+1 => networkCode n ++ if hn : n < (globalProgram Parameters.d).length+1
      then layerCode ⟨n,hn⟩ else []

theorem run_append {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (a b : List Instruction) (s : State σ) :
    run f P G S B hG hS hB child (a++b) s =
      (run f P G S B hG hS hB child a s).bind
        (run f P G S B hG hS hB child b) := by
  induction a generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [List.cons_append,run,ih,Option.bind_assoc]

theorem run_edges {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (ops : List EdgeInstruction) (s : State σ) :
    run f P G S B hG hS hB child (ops.map .edge) s =
      (PhysicalEdgeContinuation.run f P G S B hG hS hB child ops s.active).map
        fun active => {s with active := active} := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      simp only [List.map_cons,run,step,PhysicalEdgeContinuation.run]
      cases hs : PhysicalEdgeContinuation.step f P G S B hG hS hB child op s.active with
      | none => rfl
      | some active =>
          simpa only [Option.map_some,Option.some_bind,Option.map_map] using
            ih {s with active := active}

def rowsResult {σ : Type} (s : State σ) (out : RowsOutput σ) (file : File) (ret : Child) : State σ :=
  {s with rows := out.files, active :=
    ⟨file,ret,out.state,s.active.localCost+out.localCost,s.active.recursiveCost+out.recursiveCost⟩}

/-- A row's gate, complete real edge program, and write-back occur in that
order, with the gate's transfer charge counted exactly once. -/
theorem row_execution {σ : Type} (f P G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (t : Fin ((globalProgram Parameters.d).length+1)) (r : Reg)
    (s : State σ) (gate : GateStreamMachine.Result) (out : Output σ)
    (hg : executeGate B (longVolume f P G S) s.inputs s.wires (t,r)=some gate)
    (he : executeEdge (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB child (t,r) gate.disk s.active.user=some out) :
    ∃ ret,run f P G S B hG hS hB child (rowCode t r) s=some
      {s with rows := Function.update s.rows r out.output,active :=
        ⟨out.output,ret,out.state,s.active.localCost+gate.cost+out.localCost,
          s.active.recursiveCost+out.recursiveCost⟩} := by
  let active : Active σ := {s.active with file := gate.disk,localCost := s.active.localCost+gate.cost}
  obtain ⟨ret,hr⟩ := PhysicalEdgeContinuation.edge_execution f P G S B hG hS hB child (t,r) active out he
  have hgate : run f P G S B hG hS hB child [.gate (t,r)] s=
      some {s with active := active} := by simp [run,step,hg,active]
  refine ⟨ret,?_⟩
  rw [rowCode,run_append,run_append,hgate,Option.some_bind,run_edges]
  change ((PhysicalEdgeContinuation.run f P G S B hG hS hB child
    (PhysicalEdgeContinuation.edgeCode (t,r)) active).map _).bind _ = _
  rw [hr]
  simp [run,step,PhysicalEdgeContinuation.appendOutput,active]

theorem rows_execution {σ : Type} (f P G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (t : Fin ((globalProgram Parameters.d).length+1)) (rs : List Reg)
    (s : State σ) (out : RowsOutput σ)
    (h : executeRows (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB child s.inputs s.wires t rs s.rows s.active.user=some out) :
    ∃ file ret,run f P G S B hG hS hB child (rowsCode t rs) s=some (rowsResult s out file ret) := by
  induction rs generalizing s out with
  | nil =>
      simp only [executeRows,Option.some.injEq] at h
      subst out
      exact ⟨s.active.file,s.active.returned,by simp [rowsCode,run,rowsResult]⟩
  | cons r rs ih =>
      cases hg : executeGate B (longVolume f P G S) s.inputs s.wires (t,r) with
      | none => simp [executeRows,hg] at h
      | some gate =>
        cases he : executeEdge (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
            B hB child (t,r) gate.disk s.active.user with
        | none => simp [executeRows,hg,he] at h
        | some head =>
          cases ht : executeRows (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
              B hB child s.inputs s.wires t rs (Function.update s.rows r head.output) head.state with
          | none => simp [executeRows,hg,he,ht] at h
          | some tail =>
            simp [executeRows,hg,he,ht] at h
            cases h
            obtain ⟨ret,hr⟩ := row_execution f P G S B hG hS hB child t r s gate head hg he
            let mid : State σ := {s with rows := Function.update s.rows r head.output,active :=
              ⟨head.output,ret,head.state,s.active.localCost+gate.cost+head.localCost,
                s.active.recursiveCost+head.recursiveCost⟩}
            obtain ⟨file,ret',hr'⟩ := ih mid tail ht
            refine ⟨file,ret',?_⟩
            rw [rowsCode,List.flatMap_cons,run_append,hr,Option.some_bind]
            first
            | exact hr'
            | (have h_sx := hr'; simp only [rowsResult,mid,Nat.add_assoc] at h_sx ⊢; exact h_sx)
            | (have h_sx := hr'; simp only [rowsResult,mid,Nat.add_assoc] at h_sx; exact h_sx)
            | (simp only [rowsResult,mid,Nat.add_assoc]; exact hr')

def layerResult {σ : Type} (s : State σ) (out : LayerOutput σ)
    (rowFiles : Reg → File) (file : File) (ret : Child) : State σ :=
  {s with wires := out.files, rows := rowFiles,active :=
    ⟨file,ret,out.state,s.active.localCost+out.localCost,s.active.recursiveCost+out.recursiveCost⟩}

theorem layer_execution {σ : Type} (f P G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (t : Fin ((globalProgram Parameters.d).length+1)) (s : State σ) (out : LayerOutput σ)
    (h : executeLayer (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB child s.inputs s.wires t s.active.user=some out) :
    ∃ rows file ret,run f P G S B hG hS hB child (layerCode t) s=
      some (layerResult s out rows file ret) := by
  cases hr : executeRows (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB child s.inputs s.wires t (Finset.univ : Finset Reg).toList s.inputs s.active.user with
  | none => simp [executeLayer,hr] at h
  | some rows =>
      simp [executeLayer,hr] at h
      cases h
      obtain ⟨file,ret,hrows⟩ := rows_execution f P G S B hG hS hB child t
        (Finset.univ : Finset Reg).toList {s with rows := s.inputs} rows hr
      have hbegin : run f P G S B hG hS hB child [.beginLayer] s=
          some {s with rows := s.inputs} := rfl
      refine ⟨rows.files,file,ret,?_⟩
      rw [layerCode,run_append,run_append,hbegin,Option.some_bind,hrows]
      simp [run,step,rowsResult,layerResult]

/-- This is a single fixed chronological network program: each layer is
completed and committed before the next layer starts. -/
theorem network_execution {σ : Type} (f P G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (n : ℕ) (s : State σ) (out : LayerOutput σ)
    (hzero : s.wires=fun _ => [])
    (h : PhysicalNetwork.execute (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB child s.inputs n s.active.user=some out) :
    ∃ rows file ret,run f P G S B hG hS hB child (networkCode n) s=
      some (layerResult s out rows file ret) := by
  induction n generalizing out with
  | zero =>
      simp only [PhysicalNetwork.execute,Option.some.injEq] at h
      subst out
      exact ⟨s.rows,s.active.file,s.active.returned,by simp [networkCode,run,layerResult,← hzero]⟩
  | succ n ih =>
      cases hb : PhysicalNetwork.execute (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
          B hB child s.inputs n s.active.user with
      | none => simp [PhysicalNetwork.execute,hb] at h
      | some before =>
          obtain ⟨rows,file,ret,hr⟩ := ih before hb
          by_cases hn : n < (globalProgram Parameters.d).length+1
          · cases ha : executeLayer (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
                B hB child s.inputs before.files ⟨n,hn⟩ before.state with
            | none => simp [PhysicalNetwork.execute,hb,hn,ha] at h
            | some after =>
                simp [PhysicalNetwork.execute,hb,hn,ha] at h
                cases h
                obtain ⟨rows',file',ret',hl⟩ := layer_execution f P G S B hG hS hB child ⟨n,hn⟩
                  (layerResult s before rows file ret) after ha
                refine ⟨rows',file',ret',?_⟩
                rw [networkCode,dif_pos hn,run_append,hr,Option.some_bind]
                simpa only [layerResult,Nat.add_assoc] using hl
          · simp [PhysicalNetwork.execute,hb,hn] at h
            subst out
            refine ⟨rows,file,ret,?_⟩
            simpa only [networkCode,dif_neg hn,List.append_nil] using hr

attribute [irreducible] networkCode

end
end CSL.PhysicalNetworkContinuation
end PhysicalNetworkContinuation

section PhysicalNetworkCost
/-! Actual whole-network costs, obtained by induction on the physical
network run whose successive layers share their external files and state. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CSL.PhysicalNetworkCost
open RecursiveExchange RecursiveExchangeCost PhysicalRecursiveExchange PhysicalLayerCost
open PhysicalRecursiveCost PhysicalNetwork StatefulControlCost
open Circuit CircuitProgram ProgramNetwork
open scoped BigOperators
noncomputable section

variable {σ : Type} {f P G S : ℕ} {hG : 0 < G} {hS : 0 < S}

def networkCoefficient (e : Edge) : ℕ := edgeConstant e+3*edgeGateScans e

theorem networkRun_local_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (inputFiles : Reg → File) (state : σ)
    (n : ℕ) (out : LayerOutput σ)
    (h : NetworkRun L B hB child runChild input inputFiles state n out) :
    out.localCost ≤ prefixCost networkCoefficient n*(longVolume f P G S/B+1) := by
  induction h with
  | zero => simp only [prefixCost,Nat.zero_mul,le_refl]
  | succ n hn before after hb ha ih =>
    have hafter := layerRun_local_cost L B hB child runChild input _ inputFiles before.files
      ⟨n,hn⟩ before.state after ha
    change before.localCost+after.localCost ≤ _
    rw [prefixCost,dif_pos hn,Nat.add_mul]
    exact Nat.add_le_add ih hafter

theorem networkRun_recursive_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ)
    (hcost : ChildCostBound L B hB child runChild C)
    (input : Reg → EdgeStream f P G S) (inputFiles : Reg → File) (state : σ)
    (n : ℕ) (out : LayerOutput σ)
    (h : NetworkRun L B hB child runChild input inputFiles state n out) :
    out.recursiveCost ≤ prefixCost (fun e => (edgePivots e).length) n*C := by
  induction h with
  | zero => simp only [prefixCost,Nat.zero_mul,le_refl]
  | succ n hn before after hb ha ih =>
    have hafter := layerRun_recursive_cost L B hB child runChild C hcost input _
      inputFiles before.files ⟨n,hn⟩ before.state after ha
    change before.recursiveCost+after.recursiveCost ≤ _
    rw [prefixCost,dif_pos hn,Nat.add_mul]
    exact Nat.add_le_add ih hafter

theorem full_prefixCost (cost : Edge → ℕ) :
    prefixCost cost ((globalProgram Parameters.d).length+1) = ∑ e : Edge,cost e := by
  simpa only [Edge,Wire,Fintype.sum_prod_type] using
    prefixCost_eq cost ((globalProgram Parameters.d).length+1) le_rfl

/-- One complete physical eager execution has precisely the fixed network
local overhead plus S copies of the smaller successful-child bound. -/
theorem full_network_cost (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ)
    (hcost : ChildCostBound L B hB child runChild C)
    (input : Reg → EdgeStream f P G S) (inputFiles : Reg → File) (state : σ)
    (out : LayerOutput σ)
    (h : NetworkRun L B hB child runChild input inputFiles state
      ((globalProgram Parameters.d).length+1) out) :
    out.localCost ≤ (∑ e : Edge,networkCoefficient e)*(longVolume f P G S/B+1) ∧
      out.recursiveCost ≤ Parameters.S*C := by
  have hl := networkRun_local_cost L B hB child runChild input inputFiles state _ out h
  have hr := networkRun_recursive_cost L B hB child runChild C hcost input inputFiles state _ out h
  rw [full_prefixCost] at hl hr
  have hp : (∑ e : Edge,(edgePivots e).length) = Parameters.S := by
    simp_rw [edgePivots_length]
    exact edge_rank_sum
  exact ⟨hl,by simpa only [hp] using hr⟩

/-- Functional correctness and both cost bounds refer to the very same
returned file bank. Every layout law is discharged by the concrete codec. -/
theorem actual_network_execution_cost (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ)
    (hc : ChildAvailable (actualLayouts f P G S hG hS).layout B hB child runChild)
    (hcost : ChildCostBound (actualLayouts f P G S hG hS) B hB child runChild C)
    (input : Reg → EdgeStream f P G S) (inputFiles : Reg → File) (state : σ)
    (hi : ∀ r,inputFiles r = represented (actualLayouts f P G S hG hS).layout B hB (input r)) :
    ∃ out, NetworkRun (actualLayouts f P G S hG hS) B hB child runChild input inputFiles state
        ((globalProgram Parameters.d).length+1) out ∧
      execute (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
        B hB runChild inputFiles ((globalProgram Parameters.d).length+1) state = some out ∧
      (∀ e,out.files e = represented (actualLayouts f P G S hG hS).layout B hB
        ((StatefulRecursiveExchange.execute f input
          (fun e => StatefulRecursiveExchange.edgeProgram f e child)
          ((globalProgram Parameters.d).length+1) state).1 e)) ∧
      out.localCost ≤ (∑ e : Edge,networkCoefficient e)*(longVolume f P G S/B+1) ∧
      out.recursiveCost ≤ Parameters.S*C := by
  obtain ⟨out,hrun,hactual,hfiles⟩ := actual_network_execution B hB child runChild hc
    input inputFiles state hi
  have hbound := full_network_cost (actualLayouts f P G S hG hS) B hB child runChild C
    hcost input inputFiles state out hrun
  exact ⟨out,hrun,hactual,hfiles,hbound⟩

end
end CSL.PhysicalNetworkCost
end PhysicalNetworkCost


