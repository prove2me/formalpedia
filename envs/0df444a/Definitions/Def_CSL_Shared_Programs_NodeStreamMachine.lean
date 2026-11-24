-- Prove2me | Definitions.Def_CSL_Shared_Programs_NodeStreamMachine
-- name    : CSL_Shared_Programs_NodeStreamMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:22:54.21824+00:00
-- url     : https://prove2.me/theorems/fd8cc359-3df9-4e83-88c7-00db85bad562
-- title:
--   Coded sorting library: Shared / Programs / NodeStreamMachine
-- statement:
--   Module `CodedSorting.Shared.Programs.NodeStreamMachine` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # A real two-reader, one-writer pointwise gate scan
--
--   The runtime only obtains inputs through `Reader.pop` and immediately pushes
--   the computed payload into its output writer. The generic operation below
--   specializes to both Bool.xor and the circuit's addition on ZMod 2.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.NodeStreamMachine

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_DiskStreamPass
import Definitions.Def_CSL_Circuit_NetworkModel_Framework_ProgramNetwork

section XorStreamMachine
/-!
# A real two-reader, one-writer pointwise gate scan

The runtime only obtains inputs through `Reader.pop` and immediately pushes
the computed payload into its output writer. The generic operation below
specializes to both Bool.xor and the circuit's addition on ZMod 2.
-/

namespace CSL.XorStreamMachine

open BucketMachine BucketReader
variable {α : Type*}

structure State (α : Type*) where
  left : Reader α
  right : Reader α
  output : Writer α

def State.Valid (B : ℕ) (s : State α) :=
  s.left.Valid B ∧ s.right.Valid B ∧ s.output.Valid B

def State.memory (s : State α) :=
  s.left.pending.length + s.right.pending.length + s.output.pending.length

/-- The two temporary payload values are discarded immediately after push;
unread blocks and completed blocks are external disk objects. -/
def step (B : ℕ) (op : α → α → α) (s : State α) : Option (State α) := do
  let (a,left) ← s.left.pop
  let (b,right) ← s.right.pop
  return ⟨left,right,s.output.push B (op a b)⟩

def run (B : ℕ) (op : α → α → α) : ℕ → State α → Option (State α)
  | 0,s => some s
  | n+1,s => (step B op s).bind (run B op n)

theorem valid_memory (B : ℕ) (s : State α) (hs : s.Valid B) : s.memory ≤ 3*B := by
  have hl := hs.1.2
  have hr := hs.2.1.2
  have hw := hs.2.2.2
  unfold State.memory
  omega

theorem step_valid (B : ℕ) (op : α → α → α) (s t : State α)
    (hs : s.Valid B) (ht : step B op s = some t) : t.Valid B := by
  unfold step at ht
  cases hl : s.left.pop with
  | none => simp [hl] at ht
  | some leftPair =>
    obtain ⟨a,left⟩ := leftPair
    cases hr : s.right.pop with
    | none => simp [hl,hr] at ht
    | some rightPair =>
      obtain ⟨b,right⟩ := rightPair
      simp [hl,hr] at ht
      subst t
      exact ⟨Reader.pop_valid B _ _ _ hs.1 hl,
        Reader.pop_valid B _ _ _ hs.2.1 hr,Writer.push_valid B _ _ hs.2.2⟩

theorem run_valid (B n : ℕ) (op : α → α → α) (s t : State α)
    (hs : s.Valid B) (ht : run B op n s = some t) : t.Valid B := by
  induction n generalizing s with
  | zero => exact (Option.some.inj ht) ▸ hs
  | succ n ih =>
    simp only [run] at ht
    cases hstep : step B op s with
    | none => simp [hstep] at ht
    | some next =>
      simp only [hstep,Option.bind_some] at ht
      exact ih next (step_valid B op s next hs hstep) ht

/-- The bound applies to every successful prefix, not merely the final
empty-reader state. Adding the two transient operands gives 3B+2 bits. -/
theorem run_memory (B n : ℕ) (op : α → α → α) (s t : State α)
    (hs : s.Valid B) (ht : run B op n s = some t) : t.memory+2 ≤ 3*B+2 := by
  have := valid_memory B t (run_valid B n op s t hs ht)
  omega

theorem run_prefix (B : ℕ) (op : α → α → α) (xs ys tail₁ tail₂ : List α)
    (hlen : xs.length = ys.length) (s : State α) (hs : s.Valid B)
    (hx : s.left.contents = xs++tail₁) (hy : s.right.contents = ys++tail₂) :
    ∃ t, run B op xs.length s = some t ∧ t.Valid B ∧
      t.left.contents = tail₁ ∧ t.right.contents = tail₂ ∧
      t.output.contents = s.output.contents ++ List.zipWith op xs ys ∧
      t.left.reads+t.left.disk.length = s.left.reads+s.left.disk.length ∧
      t.right.reads+t.right.disk.length = s.right.reads+s.right.disk.length := by
  induction xs generalizing ys s with
  | nil =>
    have hyNil : ys=[] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    exact ⟨s,rfl,hs,by simpa using hx,by simpa using hy,by simp,rfl,rfl⟩
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hx' : s.left.contents = a::(xs++tail₁) := by simpa using hx
      have hy' : s.right.contents = b::(ys++tail₂) := by simpa using hy
      obtain ⟨left,hl⟩ := Reader.pop_exists B s.left hs.1 a _ hx'
      obtain ⟨right,hr⟩ := Reader.pop_exists B s.right hs.2.1 b _ hy'
      let next : State α := ⟨left,right,s.output.push B (op a b)⟩
      have hn : step B op s = some next := by simp [step,hl,hr,next]
      have hv := step_valid B op s next hs hn
      have hleft : next.left.contents = xs++tail₁ := by
        have h := Reader.pop_contents _ _ _ hl
        rw [hx'] at h
        exact (List.cons.inj h).2.symm
      have hright : next.right.contents = ys++tail₂ := by
        have h := Reader.pop_contents _ _ _ hr
        rw [hy'] at h
        exact (List.cons.inj h).2.symm
      obtain ⟨t,ht,hv',htl,htr,ho,hcl,hcr⟩ :=
        ih ys (by simpa using hlen) next hv hleft hright
      refine ⟨t,?_,hv',htl,htr,?_,?_,?_⟩
      · simpa only [List.length_cons,run,hn,Option.bind_some] using ht
      · rw [ho]
        simp [next,Writer.push_contents,List.append_assoc]
      · exact hcl.trans (Reader.pop_conservation _ _ _ hl)
      · exact hcr.trans (Reader.pop_conservation _ _ _ hr)

def initial (leftDisk rightDisk : List (List α)) : State α :=
  ⟨Reader.fromDisk leftDisk,Reader.fromDisk rightDisk,Writer.empty⟩

def transfers (s : State α) : ℕ :=
  s.left.reads+s.right.reads+s.output.finish.length

/-- Canonical output blocks and exact transfer count of the real scan.
Both sources are read once and the output is written once, including the
partially filled final block. -/
theorem run_packed (B : ℕ) (hB : 0<B) (op : α → α → α) (xs ys : List α)
    (hlen : xs.length=ys.length) :
    ∃ t, run B op xs.length (initial (pack B hB xs) (pack B hB ys)) = some t ∧
      t.output.finish = pack B hB (List.zipWith op xs ys) ∧
      transfers t = 3*((xs.length+B-1)/B) ∧
      t.Valid B ∧ t.memory+2 ≤ 3*B+2 := by
  let start := initial (pack B hB xs) (pack B hB ys)
  have hv : start.Valid B :=
    ⟨StreamCopy.pack_reader_valid B hB xs,StreamCopy.pack_reader_valid B hB ys,
      Writer.empty_valid B hB⟩
  have hx : start.left.contents = xs++[] := by
    simp [start,initial,Reader.contents,Reader.fromDisk,flatten_pack]
  have hy : start.right.contents = ys++[] := by
    simp [start,initial,Reader.contents,Reader.fromDisk,flatten_pack]
  obtain ⟨t,ht,hvt,hleft,hright,hout,hcl,hcr⟩ :=
    run_prefix B op xs ys [] [] hlen start hv hx hy
  have hld := Reader.empty_contents_disk B t.left hvt.1 hleft
  have hrd := Reader.empty_contents_disk B t.right hvt.2.1 hright
  have hlcount : t.left.reads = (xs.length+B-1)/B := by
    simpa [hld,start,initial,Reader.fromDisk,pack_count] using hcl
  have hrcount : t.right.reads = (xs.length+B-1)/B := by
    simpa [hrd,start,initial,Reader.fromDisk,pack_count,← hlen] using hcr
  have hout' : t.output.contents = List.zipWith op xs ys := by
    simpa [start,initial,Writer.contents,Writer.empty] using hout
  have hcanonical : t.output.finish = pack B hB (List.zipWith op xs ys) := by
    rw [DiskStreamPass.writer_finish_eq_pack B hB _ hvt.2.2,hout']
  refine ⟨t,ht,hcanonical,?_,hvt,run_memory B _ op start t hv ht⟩
  unfold transfers
  rw [hlcount,hrcount,hcanonical,pack_count,List.length_zipWith,hlen,min_self]
  omega

def xorDisk (B n : ℕ) (leftDisk rightDisk : List (List Bool)) : Option (State Bool) :=
  run B Bool.xor n (initial leftDisk rightDisk)

theorem xorDisk_correct (B : ℕ) (hB : 0<B) (xs ys : List Bool)
    (hlen : xs.length=ys.length) :
    ∃ t, xorDisk B xs.length (pack B hB xs) (pack B hB ys) = some t ∧
      t.output.finish = pack B hB (List.zipWith Bool.xor xs ys) ∧
      transfers t = 3*((xs.length+B-1)/B) ∧
      t.Valid B ∧ t.memory+2 ≤ 3*B+2 :=
  run_packed B hB Bool.xor xs ys hlen

end CSL.XorStreamMachine
end XorStreamMachine

section GateStreamMachine
/-! Physical realization of an actual finite XOR gate. All controls are read
from the original external files. A fresh output file is built for each target,
so even overlapping target/control names have the simultaneous gate semantics. -/

namespace CSL.GateStreamMachine
open BucketMachine BucketReader Circuit CircuitProgram
open scoped BigOperators
noncomputable section
variable {R : Type} [DecidableEq R] {V : ℕ}

abbrev Disk := List (List Bit)
abbrev Bank (R : Type) := R → Disk

structure Result where
  disk : Disk
  cost : ℕ

/-- One disk-to-disk XOR scan, with the actual read/write count. -/
def xorScan (B V : ℕ) (a b : Disk) : Option Result := do
  let t ← XorStreamMachine.run B (· + ·) V (XorStreamMachine.initial a b)
  return ⟨t.output.finish,XorStreamMachine.transfers t⟩

private theorem zipWith_ofFn {α β γ : Type*} {n : ℕ} (op : α → β → γ)
    (a : Fin n → α) (b : Fin n → β) :
    List.zipWith op (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => op (a i) (b i)) := by
  apply List.ext_getElem <;> simp

theorem xorScan_correct (B V : ℕ) (hB : 0 < B) (a b : Fin V → Bit) :
    xorScan B V (pack B hB (List.ofFn a)) (pack B hB (List.ofFn b)) =
      some ⟨pack B hB (List.ofFn (fun i => a i+b i)),3*((V+B-1)/B)⟩ := by
  obtain ⟨t,ht,ho,hc,_,_⟩ := XorStreamMachine.run_packed B hB (· + ·)
    (List.ofFn a) (List.ofFn b) (by simp)
  simp only [List.length_ofFn] at ht hc
  simp [xorScan,ht,ho,hc,zipWith_ofFn]

/-- The accumulator is a disk file; after each scan its old version can be
reclaimed. Source control files remain available for all later targets. -/
def controls (B V : ℕ) (source : Bank R) : List R → Disk → Option Result
  | [], acc => some ⟨acc,0⟩
  | c::cs,acc => do
      let next ← xorScan B V acc (source c)
      let out ← controls B V source cs next.disk
      return ⟨out.disk,next.cost+out.cost⟩

def controlValue (source : R → Fin V → Bit) (cs : List R) (acc : Fin V → Bit) : Fin V → Bit :=
  fun i => acc i + (cs.map (fun c => source c i)).sum

theorem controls_correct (B V : ℕ) (hB : 0 < B)
    (source : R → Fin V → Bit) (cs : List R) (acc : Fin V → Bit) :
    controls B V (fun r => pack B hB (List.ofFn (source r))) cs
        (pack B hB (List.ofFn acc)) =
      some ⟨pack B hB (List.ofFn (controlValue source cs acc)),
        cs.length*(3*((V+B-1)/B))⟩ := by
  induction cs generalizing acc with
  | nil =>
    have hz : controlValue source [] acc = acc := by funext i; simp [controlValue]
    simp [controls,hz]
  | cons c cs ih =>
    rw [controls,xorScan_correct B V hB acc (source c)]
    have he : controlValue source cs (fun i => acc i+source c i) =
        controlValue source (c::cs) acc := by
      funext i
      simp [controlValue,add_assoc]
    simp [ih,he,Nat.succ_mul,Nat.add_comm]

structure GateResult (R : Type) where
  bank : Bank R
  cost : ℕ

/-- Separate original and accumulating banks implement simultaneous writes. -/
def targets (B V : ℕ) (g : XorGate R) (source : Bank R) :
    List R → Bank R → Option (GateResult R)
  | [], out => some ⟨out,0⟩
  | r::rs,out => do
      let fresh ← controls B V source (g.controls r).toList (source r)
      let rest ← targets B V g source rs (Function.update out r fresh.disk)
      return ⟨rest.bank,fresh.cost+rest.cost⟩

def targetValue (g : XorGate R) (source : R → Fin V → Bit) (r : R) : Fin V → Bit :=
  fun i => source r i+∑ c ∈ g.controls r,source c i

def updateValues (g : XorGate R) (source : R → Fin V → Bit)
    (rs : List R) (out : R → Fin V → Bit) : R → Fin V → Bit :=
  fun r => if r∈rs then targetValue g source r else out r

private theorem controls_targetValue (g : XorGate R) (source : R → Fin V → Bit) (r : R) :
    controlValue source (g.controls r).toList (source r) = targetValue g source r := by
  funext i
  simp [controlValue,targetValue,← Finset.sum_toList]

private theorem updateValues_cons (g : XorGate R) (source : R → Fin V → Bit)
    (r : R) (rs : List R) (out : R → Fin V → Bit) :
    updateValues g source rs (Function.update out r (targetValue g source r)) =
      updateValues g source (r::rs) out := by
  funext j
  by_cases hm : j∈rs
  · simp [updateValues,hm]
  · by_cases he : j=r <;> simp [updateValues,hm,he,Function.update_apply]

private theorem pack_update (B : ℕ) (hB : 0 < B) (out : R → Fin V → Bit)
    (r : R) (value : Fin V → Bit) :
    Function.update (fun j => pack B hB (List.ofFn (out j))) r (pack B hB (List.ofFn value)) =
      fun j => pack B hB (List.ofFn (Function.update out r value j)) := by
  funext j
  by_cases he : j=r <;> simp [he,Function.update_apply]

theorem targets_correct (B V : ℕ) (hB : 0 < B) (g : XorGate R)
    (source out : R → Fin V → Bit) (rs : List R) :
    targets B V g (fun r => pack B hB (List.ofFn (source r))) rs
        (fun r => pack B hB (List.ofFn (out r))) =
      some ⟨(fun r => pack B hB (List.ofFn (updateValues g source rs out r))),
        ((rs.map (fun r => (g.controls r).card)).sum)*(3*((V+B-1)/B))⟩ := by
  induction rs generalizing out with
  | nil => simp [targets,updateValues]
  | cons r rs ih =>
    rw [targets,controls_correct B V hB source (g.controls r).toList (source r)]
    simp only [controls_targetValue]
    simp [pack_update,ih,updateValues_cons,Nat.add_mul]

def runGate (B V : ℕ) (g : XorGate R) (source : Bank R) : Option (GateResult R) :=
  targets B V g source g.targets.toList source

def scanCount (g : XorGate R) : ℕ := ∑ r ∈ g.targets,(g.controls r).card

/-- Every actual finite XOR gate, with its declared read/write ports. No
functional gate oracle is used: the RHS is obtained by the explicit scans. -/
theorem runGate_correct (B V : ℕ) (hB : 0 < B) (g : XorGate R)
    (source : R → Fin V → Bit) :
    runGate B V g (fun r => pack B hB (List.ofFn (source r))) =
      some ⟨(fun r => pack B hB (List.ofFn (fun i => g.eval (fun c => source c i) r))),
        scanCount g*(3*((V+B-1)/B))⟩ := by
  unfold runGate
  rw [targets_correct B V hB g source source]
  have hv : (fun r => pack B hB (List.ofFn (updateValues g source g.targets.toList source r))) =
      (fun r => pack B hB (List.ofFn (fun i => g.eval (fun c => source c i) r))) := by
    funext r
    congr 2
    funext i
    by_cases hr : r ∈ g.targets <;> simp [updateValues,targetValue,XorGate.eval,hr]
  have hc : (g.targets.toList.map (fun r => (g.controls r).card)).sum = scanCount g := by
    simp [scanCount,← Finset.sum_toList]
  rw [hv,hc]


/-- Per-output version used by the physical network's eager wire loop. -/
def runOutput (B V : ℕ) (g : XorGate R) (r : R) (source : Bank R) : Option Result :=
  if r ∈ g.targets then controls B V source (g.controls r).toList (source r)
  else some ⟨source r,0⟩

def outputScans (g : XorGate R) (r : R) : ℕ :=
  if r ∈ g.targets then (g.controls r).card else 0

theorem runOutput_correct (B V : ℕ) (hB : 0 < B) (g : XorGate R)
    (r : R) (source : R → Fin V → Bit) :
    runOutput B V g r (fun c => pack B hB (List.ofFn (source c))) =
      some ⟨pack B hB (List.ofFn (fun i => g.eval (fun c => source c i) r)),
        outputScans g r*(3*((V+B-1)/B))⟩ := by
  by_cases hr : r ∈ g.targets
  · simp only [runOutput,if_pos hr]
    rw [controls_correct B V hB source (g.controls r).toList (source r)]
    simp only [controls_targetValue,Finset.length_toList]
    simp only [XorGate.eval,outputScans,if_pos hr]
    rfl
  · simp [runOutput,hr,outputScans,XorGate.eval]

theorem controls_congr (B V : ℕ) (first second : Bank R) (cs : List R)
    (he : ∀ c ∈ cs,first c=second c) (acc : Disk) :
    controls B V first cs acc=controls B V second cs acc := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [controls,he c (by simp)]
    congr 1
    funext next
    rw [ih (fun r hr => he r (by simp [hr]))]

theorem runOutput_congr (B V : ℕ) (g : XorGate R) (r : R)
    (hr : r∈g.ports) (first second : Bank R)
    (he : ∀ c∈g.ports,first c=second c) :
    runOutput B V g r first=runOutput B V g r second := by
  unfold runOutput
  by_cases ht : r∈g.targets
  · simp only [if_pos ht,he r hr]
    exact controls_congr B V first second _ (fun c hc =>
      he c (g.controls_subset r ht (Finset.mem_toList.mp hc))) _
  · simp [ht,he r hr]

theorem outputScans_le_ports (g : XorGate R) (r : R) :
    outputScans g r ≤ g.ports.card := by
  by_cases hr : r∈g.targets
  · simp only [outputScans,if_pos hr]
    exact Finset.card_le_card (g.controls_subset r hr)
  · simp [outputScans,hr]


end
end CSL.GateStreamMachine
end GateStreamMachine

section NodeStreamMachine
/-! The real file scan for each outgoing physical network wire. Source and
pass vertices forward an immutable file reference; XOR nodes allocate a fresh
file by the explicit control scans. No unavailable nonlocal input is read. -/

namespace CSL.NodeStreamMachine
open Circuit CircuitProgram ProgramNetwork GateStreamMachine BucketMachine
variable {R : Type} [DecidableEq R]
noncomputable section

/-- Only actual incoming ports are given files. Off-port placeholders are
never read by the implementation (`runOutput_congr`). -/
def gateBank (p : List (XorGate R)) (t : Fin p.length)
    (files : InputPort p (.gate t) → Disk) : Bank R :=
  fun r => if hr : r∈(p.get t).ports then
    files (.inr ⟨incomingWire p t r,
      (incomingWire_head p t r).trans (stageVertex_gate p t r hr)⟩)
  else []

def nodeOutput (B V : ℕ) (p : List (XorGate R)) :
    (v : Vertex R p.length) → (InputPort p v → Disk) → OutputPort p v → Option Result
  | .source r,files,_ => some ⟨files (.inl ⟨r,rfl⟩),0⟩
  | .gate t,files,out => runOutput B V (p.get t) out.val.2 (gateBank p t files)
  | .pass t r,files,_ => if hr : r∈(p.get t).ports then none else
      some ⟨files (.inr ⟨incomingWire p t r,
        (incomingWire_head p t r).trans (stageVertex_pass p t r hr)⟩),0⟩
  | .sink _,_,_ => none

def nodeScans (p : List (XorGate R)) :
    (v : Vertex R p.length) → OutputPort p v → ℕ
  | .gate t,out => outputScans (p.get t) out.val.2
  | _,_ => 0

/-- Exactly the same `localMap` as the operational network code, now
realized by the disk interpreter with an exact transfer count. -/
theorem nodeOutput_correct (B V : ℕ) (hB : 0 < B) (p : List (XorGate R))
    (v : Vertex R p.length) (values : InputPort p v → Fin V → Bit)
    (out : OutputPort p v) :
    nodeOutput B V p v (fun port => pack B hB (List.ofFn (values port))) out =
      some ⟨pack B hB (List.ofFn (fun i => localMap p v (fun port => values port i) out)),
        nodeScans p v out*(3*((V+B-1)/B))⟩ := by
  cases v with
  | source r => simp only [nodeOutput,nodeScans,Nat.zero_mul,localMap,
      LinearMap.pi_apply,LinearMap.proj_apply]
  | gate t =>
    let source : R → Fin V → Bit := fun r i => gateInputMap p t (fun port => values port i) r
    have he : ∀ r∈(p.get t).ports,
        gateBank p t (fun port => pack B hB (List.ofFn (values port))) r =
          pack B hB (List.ofFn (source r)) := by
      intro r hr
      simp only [gateBank,dif_pos hr,source,gateInputMap,LinearMap.pi_apply,
        LinearMap.proj_apply]
    rw [nodeOutput,runOutput_congr B V (p.get t) out.val.2
      (outgoing_gate_port p t out.val out.property) _ _ he,
      runOutput_correct B V hB (p.get t) out.val.2 source]
    rfl
  | pass t r =>
    have hr := (outgoing_pass_index p t r out.val out.property).2
    simp only [nodeOutput,nodeScans,dif_neg hr,Nat.zero_mul,localMap,
      LinearMap.pi_apply,LinearMap.proj_apply]
  | sink r => exact (no_outgoing_sink p r out.val out.property).elim

end
end CSL.NodeStreamMachine
end NodeStreamMachine


