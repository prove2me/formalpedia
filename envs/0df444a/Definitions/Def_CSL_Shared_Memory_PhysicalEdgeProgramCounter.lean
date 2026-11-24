-- Prove2me | Definitions.Def_CSL_Shared_Memory_PhysicalEdgeProgramCounter
-- name    : CSL_Shared_Memory_PhysicalEdgeProgramCounter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:56:19.282681+00:00
-- url     : https://prove2.me/theorems/8ca31ec4-0f10-4109-88db-f796f129f39f
-- title:
--   Coded sorting library: Shared / Memory / PhysicalEdgeProgramCounter
-- statement:
--   Module `CodedSorting.Shared.Memory.PhysicalEdgeProgramCounter` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   An explicit instruction counter for the *actual* edge interpreter.  Calls
--   occur in `edgePivots` order; the postscan uses the returned child identifier.
--   The instructions contain no function-valued return continuation.  Payload
--   files in `State` are external files, not an assertion of resident storage.
--   This compilation preserves the actual local and recursive charges exactly.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.PhysicalEdgeProgramCounter

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_PhysicalRecursiveExchange

section PhysicalEdgeContinuation
/-!
An explicit instruction counter for the *actual* edge interpreter.  Calls
occur in `edgePivots` order; the postscan uses the returned child identifier.
The instructions contain no function-valued return continuation.  Payload
files in `State` are external files, not an assertion of resident storage.
This compilation preserves the actual local and recursive charges exactly.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace CSL.PhysicalEdgeContinuation
open PhysicalRecursiveExchange RecursiveExchange RecursiveExchangeCost
noncomputable section

inductive Instruction where
  | before (edge : Edge)
  | pre (child : Child)
  | call (child : Child)
  | post
  | after (edge : Edge)

structure State (σ : Type) where
  file : File
  returned : Child
  user : σ
  localCost : ℕ
  recursiveCost : ℕ

def appendOutput {σ : Type} (s : State σ) (out : Output σ) (returned : Child) : State σ :=
  ⟨out.output,returned,out.state,s.localCost+out.localCost,s.recursiveCost+out.recursiveCost⟩

def scan {σ : Type} {V : ℕ} (B : ℕ) (hB : 0 < B)
    (program : List (ScanProgram.Pass V)) (s : State σ) : Option (State σ) :=
  (executeProgram B hB program s.file).map fun out =>
    {s with file := out.1,localCost := s.localCost+out.2}

/-- The return boundary only copies the child's actual output, identifier
and charge.  It retains no selected scan or caller closure. -/
def returned {σ : Type} (s : State σ) (out : ChildOutput σ) : State σ :=
  ⟨out.output,out.returned,out.state,s.localCost,s.recursiveCost+out.cost⟩

def localStep {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    : Instruction → State σ → Option (State σ)
  | .before e,s => scan B hB (beforeProgram f P G S hG hS e) s
  | .pre c,s => scan B hB (scalarBefore f P G S c) s
  | .call _,_ => none
  | .post,s => scan B hB (scalarAfter f P G S s.returned hS) s
  | .after e,s => scan B hB (afterProgram f P G S hG hS e) s

def step {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (op : Instruction) (s : State σ) : Option (State σ) :=
  match op with
  | .call c => (child c s.file s.user).map (returned s)
  | _ => localStep f P G S B hG hS hB op s

def run {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) : List Instruction → State σ → Option (State σ)
  | [],s => some s
  | op::ops,s => (step f P G S B hG hS hB child op s).bind
      (run f P G S B hG hS hB child ops)

def shortCode (c : Child) : List Instruction := [.pre c,.call c,.post]
def sparseCode (e : Edge) (ps : List (EdgeChild e)) : List Instruction :=
  ps.flatMap fun p => shortCode ⟨e,p⟩
def edgeCode (e : Edge) : List Instruction :=
  [.before e] ++ sparseCode e (edgePivots e) ++ [.after e]

theorem run_append {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (a b : List Instruction) (s : State σ) :
    run f P G S B hG hS hB child (a++b) s =
      (run f P G S B hG hS hB child a s).bind
        (run f P G S B hG hS hB child b) := by
  induction a generalizing s with
  | nil => rfl
  | cons op ops ih =>
      simp only [List.cons_append,run,ih,Option.bind_assoc]

/-- Every successful callback execution has the same straight-line
three-instruction execution, including its postscan and exact costs. -/
theorem short_execution {σ : Type} (f P G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (c : Child) (s : State σ) (out : Output σ)
    (h : executeShort (f := f) (P := P) (G := G) (S := S) (hS := hS)
      B hB child c s.file s.user=some out) :
    ∃ ret,run f P G S B hG hS hB child (shortCode c) s=some (appendOutput s out ret) := by
  cases hb : executeProgram B hB (scalarBefore f P G S c) s.file with
  | none => simp [executeShort,hb] at h
  | some pre =>
    cases hc : child c pre.1 s.user with
    | none => simp [executeShort,hb,hc] at h
    | some result =>
      cases ha : executeProgram B hB (scalarAfter f P G S result.returned hS) result.output with
      | none => simp [executeShort,hb,hc,ha] at h
      | some post =>
        simp [executeShort,hb,hc,ha] at h
        cases h
        refine ⟨result.returned,?_⟩
        simp [shortCode,run,step,localStep,scan,hb,hc,returned,ha,appendOutput,Nat.add_assoc]

theorem sparse_execution {σ : Type} (f P G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (e : Edge) (ps : List (EdgeChild e)) (s : State σ) (out : Output σ)
    (h : executeSparse (f := f) (P := P) (G := G) (S := S) (hS := hS)
      B hB child e ps s.file s.user=some out) :
    ∃ ret,run f P G S B hG hS hB child (sparseCode e ps) s=some (appendOutput s out ret) := by
  induction ps generalizing s out with
  | nil =>
      simp only [executeSparse,Option.some.injEq] at h
      subst out
      exact ⟨s.returned,by simp [sparseCode,run,appendOutput]⟩
  | cons p ps ih =>
      cases hh : executeShort (f := f) (P := P) (G := G) (S := S) (hS := hS)
          B hB child ⟨e,p⟩ s.file s.user with
      | none => simp [executeSparse,hh] at h
      | some head =>
        cases ht : executeSparse (f := f) (P := P) (G := G) (S := S) (hS := hS)
            B hB child e ps head.output head.state with
        | none => simp [executeSparse,hh,ht] at h
        | some tail =>
          simp [executeSparse,hh,ht] at h
          cases h
          obtain ⟨ret,hr⟩ := short_execution f P G S B hG hS hB child ⟨e,p⟩ s head hh
          obtain ⟨ret',hr'⟩ := ih (appendOutput s head ret) tail ht
          refine ⟨ret',?_⟩
          rw [sparseCode,List.flatMap_cons,run_append,hr,Option.some_bind]
          first
          | exact hr'
          | (have h_sx := hr'; simp only [appendOutput,Nat.add_assoc] at h_sx ⊢; exact h_sx)
          | (have h_sx := hr'; simp only [appendOutput,Nat.add_assoc] at h_sx; exact h_sx)
          | (simp only [appendOutput,Nat.add_assoc]; exact hr')

/-- The compiled instruction order is the edge interpreter's actual order,
not an arbitrary enumeration of all recursive children. -/
theorem edge_execution {σ : Type} (f P G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (e : Edge) (s : State σ) (out : Output σ)
    (h : executeEdge (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB child e s.file s.user=some out) :
    ∃ ret,run f P G S B hG hS hB child (edgeCode e) s=some (appendOutput s out ret) := by
  cases hb : executeProgram B hB (beforeProgram f P G S hG hS e) s.file with
  | none => simp [executeEdge,hb] at h
  | some pre =>
    cases hm : executeSparse (f := f) (P := P) (G := G) (S := S) (hS := hS)
        B hB child e (edgePivots e) pre.1 s.user with
    | none => simp [executeEdge,hb,hm] at h
    | some middle =>
      cases ha : executeProgram B hB (afterProgram f P G S hG hS e) middle.output with
      | none => simp [executeEdge,hb,hm,ha] at h
      | some post =>
        simp [executeEdge,hb,hm,ha] at h
        cases h
        let start : State σ := {s with file := pre.1,localCost := s.localCost+pre.2}
        obtain ⟨ret,hr⟩ := sparse_execution f P G S B hG hS hB child e (edgePivots e) start middle hm
        have hstart : run f P G S B hG hS hB child [.before e] s=some start := by
          simp [run,step,localStep,scan,hb,start]
        refine ⟨ret,?_⟩
        rw [edgeCode,run_append,run_append,hstart,Option.some_bind,hr]
        simp [run,step,localStep,scan,appendOutput,ha,start,Nat.add_assoc]

end
end CSL.PhysicalEdgeContinuation
end PhysicalEdgeContinuation

section PhysicalEdgeProgramCounter
/-! Counter-based suspension of the real edge code.  In contrast to a host
recursive list evaluator, each transition selects the instruction from the
same fixed program using its numerical pc.  No list of pending operations
is part of the active state.  A call emits a request and can only progress
by receiving its child's actual result. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace CSL.PhysicalEdgeProgramCounter
open PhysicalRecursiveExchange RecursiveExchange PhysicalEdgeContinuation
noncomputable section

/-- These are specification requests, not payload stored in the control
counter. The file is the same external working file as before the call. -/
inductive Event (σ : Type) where
  | halt
  | local (next : State σ)
  | call (child : Child)

def dispatch {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (code : List Instruction) (pc : ℕ) (s : State σ) : Option (Event σ) :=
  match code[pc]? with
  | none => some .halt
  | some (.call c) => some (.call c)
  | some op => (localStep f P G S B hG hS hB op s).map Event.local

def advance {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (code : List Instruction) (pc : ℕ) (s : State σ) :
    Option (ℕ × State σ) := do
  let event ← dispatch f P G S B hG hS hB code pc s
  match event with
  | .halt => some (pc,s)
  | .local next => some (pc+1,next)
  | .call c => (child c s.file s.user).map fun result => (pc+1,returned s result)

def execute {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (code : List Instruction) : ℕ → ℕ → State σ → Option (ℕ × State σ)
  | 0,pc,s => some (pc,s)
  | n+1,pc,s => (advance f P G S B hG hS hB child code pc s).bind fun next =>
      execute f P G S B hG hS hB child code n next.1 next.2

theorem advance_at {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (code : List Instruction) (pc : ℕ) (s : State σ)
    (op : Instruction) (h : code[pc]?=some op) :
    advance f P G S B hG hS hB child code pc s =
      (step f P G S B hG hS hB child op s).map fun next => (pc+1,next) := by
  cases op <;> simp [advance,dispatch,h,step,Option.bind_map,Function.comp_def]
  all_goals exact Option.map_eq_bind.symm

theorem advance_halted {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (code : List Instruction) (s : State σ) :
    advance f P G S B hG hS hB child code code.length s=some (code.length,s) := by
  simp [advance,dispatch]

theorem execute_suffix {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (pref suffix : List Instruction) (s : State σ) :
    execute f P G S B hG hS hB child (pref++suffix) suffix.length pref.length s =
      (run f P G S B hG hS hB child suffix s).map fun out => ((pref++suffix).length,out) := by
  induction suffix generalizing pref s with
  | nil => simp [execute,run]
  | cons op ops ih =>
      have lookup : (pref++op::ops)[pref.length]?=some op := by simp
      rw [List.length_cons,execute,advance_at f P G S B hG hS hB child _ _ _ _ lookup]
      cases hs : step f P G S B hG hS hB child op s with
      | none => simp [run,hs]
      | some next =>
        simp only [Option.map_some,Option.some_bind,run,hs]
        have htail := ih (pref++[op]) next
        first
        | exact htail
        | (have h_sx := htail; simp only [List.append_assoc,List.singleton_append,List.length_append,
          List.length_singleton,List.length_cons,Option.map_some,Option.some_bind,Nat.add_assoc] at h_sx ⊢; exact h_sx)
        | (have h_sx := htail; simp only [List.append_assoc,List.singleton_append,List.length_append,
          List.length_singleton,List.length_cons,Option.map_some,Option.some_bind,Nat.add_assoc] at h_sx; exact h_sx)
        | (simp only [List.append_assoc,List.singleton_append,List.length_append,
          List.length_singleton,List.length_cons,Option.map_some,Option.some_bind,Nat.add_assoc]; exact htail)

/-- The very same fixed code and counter program work for every initial
payload. The output and both charges are those of the previous interpreter. -/
theorem execute_edge {σ : Type} (f P G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (e : Edge) (s : State σ) (out : Output σ)
    (h : executeEdge (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB child e s.file s.user=some out) :
    ∃ ret,execute f P G S B hG hS hB child (edgeCode e) (edgeCode e).length 0 s=
      some ((edgeCode e).length,appendOutput s out ret) := by
  obtain ⟨ret,hr⟩ := edge_execution f P G S B hG hS hB child e s out h
  refine ⟨ret,?_⟩
  have he := execute_suffix f P G S B hG hS hB child [] (edgeCode e) s
  simpa only [List.nil_append,List.length_nil,hr,Option.map_some] using he

end
end CSL.PhysicalEdgeProgramCounter
end PhysicalEdgeProgramCounter


