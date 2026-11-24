-- Prove2me | Definitions.Def_CSL_Shared_Programs_FullShapeContinuation
-- name    : CSL_Shared_Programs_FullShapeContinuation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T16:14:22.51915+00:00
-- url     : https://prove2.me/theorems/e36edd0e-2771-4a3e-a513-50b019aa4773
-- title:
--   Coded sorting library: Shared / Programs / FullShapeContinuation
-- statement:
--   Module `CodedSorting.Shared.Programs.FullShapeContinuation` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A physical return continuation whose scan dimensions and file handles
--   are read from the restored word frame. The enclosing recursive file driver
--   must supply this callback; this module does not identify a generic stored
--   shape with a completed finite-register implementation of that driver.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.FullShapeContinuation

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveControl
import Definitions.Def_CSL_Interchange_Framework_Recursion_PhysicalRecursiveExchange
import Definitions.Def_CSL_Shared_Memory_ProgramWorkspace

section FullShapeControl
/-! A physical return continuation whose scan dimensions and file handles
are read from the restored word frame. The enclosing recursive file driver
must supply this callback; this module does not identify a generic stored
shape with a completed finite-register implementation of that driver. -/

namespace CSL.FullShapeControl
open RecursiveControl RecursiveExchange WordControl PhysicalRecursiveExchange
noncomputable section

/-- Width is the scalar width of the long-vector scan being resumed. The
prefix, gap and suffix are its complete spectator cardinalities. File bases
are external-file handles; capacities are allocated block counts. -/
structure Shape where
  depth : ℕ
  width : ℕ
  volume : ℕ
  rows : ℕ
  prefixCount : ℕ
  gap : ℕ
  suffix : ℕ
  sourceBase : ℕ
  sourceBlocks : ℕ
  targetBase : ℕ
  targetBlocks : ℕ
  workBase : ℕ
  workBlocks : ℕ
  deriving DecidableEq

def Shape.values (s : Shape) (i : Fin 13) : ℕ :=
  match i.val with
  | 0 => s.depth
  | 1 => s.width
  | 2 => s.volume
  | 3 => s.rows
  | 4 => s.prefixCount
  | 5 => s.gap
  | 6 => s.suffix
  | 7 => s.sourceBase
  | 8 => s.sourceBlocks
  | 9 => s.targetBase
  | 10 => s.targetBlocks
  | 11 => s.workBase
  | _ => s.workBlocks

variable {N exponent B w : ℕ}

abbrev Frame := Descriptor 13 N exponent Parameters.S

def shapeOf (d : Frame (N := N) (exponent := exponent)) : Shape :=
  ⟨(d.counters 0).val,(d.counters 1).val,(d.counters 2).val,(d.counters 3).val,
    (d.counters 4).val,(d.counters 5).val,(d.counters 6).val,(d.counters 7).val,
    (d.counters 8).val,(d.counters 9).val,(d.counters 10).val,(d.counters 11).val,
    (d.counters 12).val⟩

def makeFrame (s : Shape) (bound : ∀ i, s.values i ≤ N^exponent) (child : Child) :
    Frame (N := N) (exponent := exponent) :=
  boundedDescriptor (fun i => ⟨s.values i,Nat.lt_succ_of_le (bound i)⟩) child

@[simp] theorem shapeOf_makeFrame (s : Shape) (bound : ∀ i, s.values i ≤ N^exponent) (child : Child) :
    shapeOf (makeFrame s bound child) = s := by
  cases s
  rfl

@[simp] theorem childOf_makeFrame (s : Shape) (bound : ∀ i, s.values i ≤ N^exponent) (child : Child) :
    childOf (makeFrame s bound child) = child := childOf_boundedDescriptor _ _

theorem frame_numeric_bound (d : Frame (N := N) (exponent := exponent)) (i : Fin 13) :
    (shapeOf d).values i ≤ N^exponent := by
  fin_cases i <;> simpa only [shapeOf,Shape.values] using Nat.le_of_lt_succ (d.counters _).isLt

/-- The file table is external storage. The returned descriptor, rather
than a pre-call closure, selects the source and target file handles. -/
abbrev FileStore := ℕ → File

structure State (B w : ℕ) where
  control : Runtime B w
  files : FileStore
  dataTransfers : ℕ

def resume (B : ℕ) (hB : 0 < B) (d : Frame (N := N) (exponent := exponent))
    (files : FileStore) : Option (FileStore × ℕ) :=
  let s := shapeOf d
  if hS : 0 < s.suffix then
    (executeProgram B hB
      (RecursiveExchangeCost.scalarAfter s.width s.prefixCount s.gap s.suffix (childOf d) hS)
      (files s.sourceBase)).map (fun out => (Function.update files s.targetBase out.1,out.2))
  else none

/-- This data continuation explicitly decodes the physical pop result and
then executes the real disk scan using its dimensions and file handles.
The callback returns the updated external files produced by the child. -/
def invoke (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (d : Frame (N := N) (exponent := exponent))
    (child : State B w → Option (State B w)) (state : State B w) : Option (State B w) := do
  let entered := { state with control := enterRuntime hN hw d state.control }
  let returned ← child entered
  let restored := leaveRuntime (fields := 13) (N := N) (exponent := exponent) child_states_pos hB returned.control
  let scanned ← resume B hB restored.1 returned.files
  return ⟨restored.2,scanned.1,returned.dataTransfers+scanned.2⟩

theorem resume_exact (s : Shape) (bound : ∀ i, s.values i ≤ N^exponent) (child : Child)
    (B : ℕ) (hB : 0 < B) (hS : 0 < s.suffix) (files : FileStore) :
    resume B hB (makeFrame s bound child) files =
      (executeProgram B hB (RecursiveExchangeCost.scalarAfter s.width s.prefixCount s.gap s.suffix child hS)
        (files s.sourceBase)).map (fun out => (Function.update files s.targetBase out.1,out.2)) := by
  simp only [resume,shapeOf_makeFrame,childOf_makeFrame,dif_pos hS]
  rfl

/-- A successful restored continuation runs the concrete primitive chain on
the child's actual source file and writes the resulting target file. Its
charge is the primitive execution's charge, not an assigned scan constant. -/
theorem resume_canonical (s : Shape) (bound : ∀ i, s.values i ≤ N^exponent) (child : Child)
    (B : ℕ) (hB : 0 < B) (hS : 0 < s.suffix) (files : FileStore)
    (F : Fin (RecursiveExchangeCost.longVolume s.width s.prefixCount s.gap s.suffix) → Circuit.Bit)
    (hsource : files s.sourceBase = canonical B hB F) :
    ∃ cost, resume B hB (makeFrame s bound child) files =
      some (Function.update files s.targetBase
        (canonical B hB (ScanProgram.eval
          (RecursiveExchangeCost.scalarAfter s.width s.prefixCount s.gap s.suffix child hS) F)),cost) ∧
      cost ≤ 20*(RecursiveExchangeCost.longVolume s.width s.prefixCount s.gap s.suffix/B+1) := by
  obtain ⟨cost,hactual,_,hcost⟩ := executeProgram_exists B hB
    (RecursiveExchangeCost.scalarAfter s.width s.prefixCount s.gap s.suffix child hS) F
  refine ⟨cost,?_,?_⟩
  · rw [resume_exact s bound child B hB hS,hsource,hactual]
    rfl
  · simpa only [RecursiveExchangeCost.scalarAfter_constant] using hcost

/-- The saved shape is not merely recorded: the continuation invokes
`resume` with the decoded descriptor. Validity proves that this actual
numeric execution is the expected continuation after the child returns. -/
theorem invoke_after_child (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (d : Frame (N := N) (exponent := exponent))
    (child : State B w → Option (State B w)) (state returned : State B w)
    (frames : List (Frame (N := N) (exponent := exponent)))
    (hchild : child { state with control := enterRuntime hN hw d state.control } = some returned)
    (hvalid : runtimeValid hN hw (d::frames) returned.control) :
    invoke hN hw hB d child state =
      (resume B hB d returned.files).map (fun scanned =>
        ⟨(leaveRuntime (fields := 13) (N := N) (exponent := exponent) child_states_pos hB returned.control).2,
          scanned.1,returned.dataTransfers+scanned.2⟩) := by
  have hrestore := (leaveRuntime_valid hN hw child_states_pos hB d frames returned.control hvalid).1
  simp only [invoke,hchild,bind,Option.bind,hrestore,pure]
  cases hr : resume B hB d returned.files <;> rfl

theorem invoke_control_valid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (d : Frame (N := N) (exponent := exponent))
    (child : State B w → Option (State B w)) (state returned output : State B w)
    (frames : List (Frame (N := N) (exponent := exponent)))
    (hchild : child { state with control := enterRuntime hN hw d state.control } = some returned)
    (hvalid : runtimeValid hN hw (d::frames) returned.control)
    (houtput : invoke hN hw hB d child state = some output) :
    runtimeValid hN hw frames output.control ∧
      output.control.trace.length=returned.control.trace.length+
        blocksPerFrame (frameWords 13 exponent Parameters.S) B := by
  rw [invoke_after_child hN hw hB d child state returned frames hchild hvalid] at houtput
  cases hresume : resume B hB d returned.files with
  | none => simp only [hresume,Option.map_none] at houtput; contradiction
  | some result =>
    simp only [hresume,Option.map_some,Option.some.injEq] at houtput
    cases houtput
    exact ⟨(leaveRuntime_valid hN hw child_states_pos hB d frames returned.control hvalid).2,
      leaveRuntime_transfers hN hw child_states_pos hB d frames returned.control hvalid⟩

/-- Fusion interface for the file interpreter: its child call and postscan
are exactly this one callback. The postscan's result and actual cost appear
once, so callers do not execute a second postscan after `invoke`. -/
theorem invoke_exact (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (s : Shape) (bound : ∀ i, s.values i ≤ N^exponent) (c : Child) (hS : 0 < s.suffix)
    (child : State B w → Option (State B w)) (state returned : State B w)
    (frames : List (Frame (N := N) (exponent := exponent)))
    (hchild : child { state with control := enterRuntime hN hw (makeFrame s bound c) state.control } =
      some returned)
    (hvalid : runtimeValid hN hw (makeFrame s bound c::frames) returned.control)
    (target : File) (cost : ℕ)
    (hscan : executeProgram B hB
      (RecursiveExchangeCost.scalarAfter s.width s.prefixCount s.gap s.suffix c hS)
      (returned.files s.sourceBase) = some (target,cost)) :
    invoke hN hw hB (makeFrame s bound c) child state = some
      ⟨(leaveRuntime (fields := 13) (N := N) (exponent := exponent) child_states_pos hB returned.control).2,
        Function.update returned.files s.targetBase target,returned.dataTransfers+cost⟩ := by
  rw [invoke_after_child hN hw hB (makeFrame s bound c) child state returned frames hchild hvalid,
    resume_exact s bound c B hB hS,hscan]
  rfl

end
end CSL.FullShapeControl
end FullShapeControl

section FullShapeAllocation
/-! The continuation stores actual used block counts, together with bases
from the polynomial external allocator. Reservation slack is not scanned. -/

namespace CSL.FullShapeAllocation
open FullShapeControl RecursiveControl WorkspaceAllocation WordControl
noncomputable section

/-- Numeric shape of the lane whose scalar postscan follows a depth k+1
recursive pivot. These are the same rows and width used by the actual
stateful evaluator's full-level invocation. -/
def laneShape (base k rows G S : ℕ) : Shape :=
  let f := base*Parameters.m^k
  let P := rows*Parameters.W^k
  ⟨k+1,f,RecursiveExchangeCost.longVolume f P G S,rows,P,G,S,0,0,0,0,0,0⟩

/-- All seven dynamic shape fields are bounded by this actual lane's
complete data volume. Only the file volume's global polynomial bound is
supplied; the depth and dimension bounds are derived here. -/
theorem laneShape_bound {N exponent : ℕ} (base k rows G S : ℕ)
    (hb : 0 < base) (hr : 0 < rows) (hG : 0 < G) (hS : 0 < S)
    (hV : (laneShape base k rows G S).volume ≤ N^exponent) :
    ∀ i : Fin 7, (laneShape base k rows G S).values (i.castAdd 6) ≤ N^exponent := by
  let f := base*Parameters.m^k
  let P := rows*Parameters.W^k
  let Q := (RecursiveExchange.radix^f)^Parameters.m
  have hW : 0 < Parameters.W := by norm_num [Parameters.W_value]
  have hm : 2 ≤ Parameters.m := by norm_num [Parameters.m_value]
  have hP : 0 < P := Nat.mul_pos hr (pow_pos hW _)
  have hq : 0 < RecursiveExchange.radix^f := pow_pos RecursiveExchange.radix_prime.pos _
  have hQ : 0 < Q := pow_pos hq _
  obtain ⟨hpv,hqv,hgv,hsv⟩ := address_dimensions_le_volume P Q G S hP hQ hG hS
  have hqQ : RecursiveExchange.radix^f ≤ Q := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ Parameters.m by omega)
  have hfv : f ≤ P*(Q*(G*(Q*S))) :=
    (Nat.lt_pow_self RecursiveExchange.radix_prime.one_lt).le.trans (hqQ.trans hqv)
  have hdepth : k+1 ≤ f :=
    (Nat.succ_le_of_lt (Nat.lt_pow_self (show 1 < Parameters.m by omega))).trans
      (Nat.le_mul_of_pos_left _ hb)
  have hrows : rows ≤ P := Nat.le_mul_of_pos_right _ (pow_pos hW _)
  have hvolume : P*(Q*(G*(Q*S))) ≤ N^exponent := hV
  intro i
  fin_cases i
  · exact (hdepth.trans hfv).trans hvolume
  · exact hfv.trans hvolume
  · exact hvolume
  · exact (hrows.trans hpv).trans hvolume
  · exact hpv.trans hvolume
  · exact hgv.trans hvolume
  · exact hsv.trans hvolume

def installFiles (s : Shape) (source target work : Span)
    (sourceCount targetCount workCount : ℕ) : Shape :=
  { s with
    sourceBase := source.start
    sourceBlocks := sourceCount
    targetBase := target.start
    targetBlocks := targetCount
    workBase := work.start
    workBlocks := workCount }

theorem installed_bound {N exponent : ℕ} (s : Shape) (source target work : Span)
    (sourceCount targetCount workCount : ℕ)
    (hdim : ∀ i : Fin 7, s.values (i.castAdd 6) ≤ N^exponent)
    (hs : source.stop ≤ N^exponent) (ht : target.stop ≤ N^exponent) (hw : work.stop ≤ N^exponent)
    (hsc : sourceCount ≤ source.blocks) (htc : targetCount ≤ target.blocks)
    (hwc : workCount ≤ work.blocks) :
    ∀ i, (installFiles s source target work sourceCount targetCount workCount).values i ≤ N^exponent := by
  have hsb : source.start ≤ N^exponent := (Nat.le_add_right _ _).trans hs
  have htb : target.start ≤ N^exponent := (Nat.le_add_right _ _).trans ht
  have hwb : work.start ≤ N^exponent := (Nat.le_add_right _ _).trans hw
  have hsn : sourceCount ≤ N^exponent := hsc.trans ((Nat.le_add_left _ _).trans hs)
  have htn : targetCount ≤ N^exponent := htc.trans ((Nat.le_add_left _ _).trans ht)
  have hwn : workCount ≤ N^exponent := hwc.trans ((Nat.le_add_left _ _).trans hw)
  intro i
  fin_cases i
  · exact hdim 0
  · exact hdim 1
  · exact hdim 2
  · exact hdim 3
  · exact hdim 4
  · exact hdim 5
  · exact hdim 6
  · exact hsb
  · exact hsn
  · exact htb
  · exact htn
  · exact hwb
  · exact hwn

/-- Construction of the finite saved shape uses the allocator's endpoint
bounds and each file's actual used block count. No address is reduced modulo
the available word capacity. -/
def allocatedFrame {N exponent : ℕ} (s : Shape) (source target work : Span)
    (sourceCount targetCount workCount : ℕ)
    (hdim : ∀ i : Fin 7, s.values (i.castAdd 6) ≤ N^exponent)
    (hs : source.stop ≤ N^exponent) (ht : target.stop ≤ N^exponent) (hw : work.stop ≤ N^exponent)
    (hsc : sourceCount ≤ source.blocks) (htc : targetCount ≤ target.blocks)
    (hwc : workCount ≤ work.blocks) (c : RecursiveExchange.Child) :
    FullShapeControl.Frame (N := N) (exponent := exponent) :=
  makeFrame (installFiles s source target work sourceCount targetCount workCount)
    (installed_bound s source target work sourceCount targetCount workCount hdim hs ht hw hsc htc hwc) c

@[simp] theorem allocatedFrame_shape {N exponent : ℕ} (s : Shape) (source target work : Span)
    (sourceCount targetCount workCount : ℕ)
    (hdim : ∀ i : Fin 7, s.values (i.castAdd 6) ≤ N^exponent)
    (hs : source.stop ≤ N^exponent) (ht : target.stop ≤ N^exponent) (hw : work.stop ≤ N^exponent)
    (hsc : sourceCount ≤ source.blocks) (htc : targetCount ≤ target.blocks)
    (hwc : workCount ≤ work.blocks) (c : RecursiveExchange.Child) :
    shapeOf (allocatedFrame s source target work sourceCount targetCount workCount hdim hs ht hw hsc htc hwc c) =
      installFiles s source target work sourceCount targetCount workCount := shapeOf_makeFrame _ _ _

/-- File-local block indices translate to the allocated global block address
without changing payload order. The resulting address fits the same global
polynomial word bound, including the case of unused reservation slack. -/
theorem used_block_address {N exponent : ℕ} (span : Span) (used block : ℕ)
    (hused : used ≤ span.blocks) (hblock : block < used) (hend : span.stop ≤ N^exponent) :
    span.Contains (span.start+block) ∧ span.start+block < N^exponent := by
  have hlt : span.start+block < span.stop := by dsimp [Span.stop]; omega
  exact ⟨⟨Nat.le_add_right _ _,hlt⟩,hlt.trans_le hend⟩

def usedBlockWords {N exponent w : ℕ} (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (span : Span) (used block : ℕ) (hused : used ≤ span.blocks) (hblock : block < used)
    (hend : span.stop ≤ N^exponent) : Words (exponent+1) w :=
  encodeCounter N w exponent hN hw
    ⟨span.start+block,Nat.lt_succ_of_lt (used_block_address span used block hused hblock hend).2⟩

@[simp] theorem usedBlockWords_decode {N exponent w : ℕ} (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (span : Span) (used block : ℕ) (hused : used ≤ span.blocks) (hblock : block < used)
    (hend : span.stop ≤ N^exponent) :
    decodeWords (usedBlockWords hN hw span used block hused hblock hend) = span.start+block :=
  decode_encodeCounter _ _ _ _ _ _

end
end CSL.FullShapeAllocation
end FullShapeAllocation

section FullShapeContinuation
/-! The data continuation also returns the physically decoded parent frame.
An enclosing scheduler can therefore consume its restored dimensions and
file handles instead of retaining an earlier parent-shape closure. -/

namespace CSL.FullShapeContinuation
open FullShapeControl RecursiveControl WordControl
noncomputable section
variable {N exponent B w : ℕ}

def invokeWithFrame (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (d : FullShapeControl.Frame (N := N) (exponent := exponent))
    (child : FullShapeControl.State B w → Option (FullShapeControl.State B w)) (state : FullShapeControl.State B w) :
    Option (FullShapeControl.Frame (N := N) (exponent := exponent) × FullShapeControl.State B w) := do
  let entered := { state with control := enterRuntime hN hw d state.control }
  let returned ← child entered
  let restored := leaveRuntime (fields := 13) (N := N) (exponent := exponent) child_states_pos hB returned.control
  let scanned ← resume B hB restored.1 returned.files
  return (restored.1,⟨restored.2,scanned.1,returned.dataTransfers+scanned.2⟩)

/-- Exposing the restored frame does not add a pass: the payload/control
execution is literally the existing fused child-and-postscan procedure. -/
theorem invokeWithFrame_projection (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (d : FullShapeControl.Frame (N := N) (exponent := exponent))
    (child : FullShapeControl.State B w → Option (FullShapeControl.State B w)) (state : FullShapeControl.State B w) :
    (invokeWithFrame hN hw hB d child state).map Prod.snd = invoke hN hw hB d child state := by
  unfold invokeWithFrame invoke
  cases hc : child { state with control := enterRuntime hN hw d state.control } with
  | none =>
    simp only [hc,bind,Option.bind,pure,Option.map_none]
    try rfl
  | some returned =>
    simp only [hc,bind,Option.bind,pure]
    cases hr : resume B hB
      (leaveRuntime (fields := 13) (N := N) (exponent := exponent) child_states_pos hB returned.control).1
      returned.files <;> rfl

/-- Every returned parent number and file handle is read from the pop.
The equality is proved from valid disk contents, not implemented by replacing
the result with the pre-call descriptor. -/
theorem invokeWithFrame_restored (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (d : FullShapeControl.Frame (N := N) (exponent := exponent))
    (child : FullShapeControl.State B w → Option (FullShapeControl.State B w)) (state returned : FullShapeControl.State B w)
    (frames : List (FullShapeControl.Frame (N := N) (exponent := exponent)))
    (hchild : child { state with control := enterRuntime hN hw d state.control } = some returned)
    (hvalid : runtimeValid hN hw (d::frames) returned.control)
    (out : FullShapeControl.Frame (N := N) (exponent := exponent) × FullShapeControl.State B w)
    (hout : invokeWithFrame hN hw hB d child state = some out) :
    out.1=d ∧ runtimeValid hN hw frames out.2.control := by
  have hp := leaveRuntime_valid hN hw child_states_pos hB d frames returned.control hvalid
  simp only [invokeWithFrame,hchild,bind,Option.bind,pure] at hout
  cases hr : resume B hB
    (leaveRuntime (fields := 13) (N := N) (exponent := exponent) child_states_pos hB returned.control).1
    returned.files with
  | none => simp only [hr,Option.bind] at hout; contradiction
  | some scanned =>
    simp only [hr,Option.bind,Option.some.injEq] at hout
    cases hout
    exact hp

/-- The next scheduler obtains its output-file handle and all shape fields
from the returned frame. For a valid completed call these equal the saved
metadata, while the code above has not retained that metadata for return. -/
theorem returned_shape (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (d : FullShapeControl.Frame (N := N) (exponent := exponent))
    (child : FullShapeControl.State B w → Option (FullShapeControl.State B w)) (state returned : FullShapeControl.State B w)
    (frames : List (FullShapeControl.Frame (N := N) (exponent := exponent)))
    (hchild : child { state with control := enterRuntime hN hw d state.control } = some returned)
    (hvalid : runtimeValid hN hw (d::frames) returned.control)
    (out : FullShapeControl.Frame (N := N) (exponent := exponent) × FullShapeControl.State B w)
    (hout : invokeWithFrame hN hw hB d child state = some out) :
    shapeOf out.1=shapeOf d :=
  congrArg shapeOf (invokeWithFrame_restored hN hw hB d child state returned frames hchild hvalid out hout).1

end
end CSL.FullShapeContinuation
end FullShapeContinuation


