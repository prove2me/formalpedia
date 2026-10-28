-- Prove2me | Definitions.Def_BitDFT_SerializerControllerBridge
-- name    : BitDFT_SerializerControllerBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T07:12:27.150525+00:00
-- url     : https://prove2.me/theorems/3fa264d8-513f-43c1-aae8-cb245f3aad08
-- title:
--   Lift and compose the multiplier suffix with the serializer
-- statement:
--   A multiplier-side controller can be lifted to the enlarged serializer host by running on the multiplier's original tape prefix and leaving appended tapes unchanged. If this lifted controller reaches its exit state with a specified serializer start frame, one stationary handoff joins it to the routed counted-block serializer. For any exact run of each component, the combined controller runs the multiplier segment, the handoff, and the serializer segment in sequence.
-- source:
--   The controller embedding gives a step-by-step configuration simulation on the wider tape bank. The composition theorem uses exact run iteration, rules out an early exit before the suffix endpoint, and matches the endpoint frame to the serializer's start frame.

import Definitions.Def_BitDFT_RoutedCountedBlockFreshTapes
import Definitions.Def_BitDFT_ControllerPadding

set_option autoImplicit false
noncomputable section
namespace BitDFT.RoutedCountedBlockFreshTapes
open IntMul BitDFT.MachineSequence

private theorem source_tapes_fit (M : MultitapeTM) :
    (source M).k ≤ (extension M).k := by
  dsimp [extension, host, source, CountedBlockOnMultiplierAlphabet.host,
    TapeExtension.machine]
  have hk := (source M).two_le_k
  omega

private def sourceTape (M : MultitapeTM) (i : Fin (source M).k) :
    Fin (extension M).k := ⟨i.val, by have := source_tapes_fit M; omega⟩

private def suffixTransition (M : MultitapeTM) (C : Controller (source M))
    (q : C.K) (a : Fin (extension M).k → (extension M).Sym) :=
  let z := C.transition q (fun i => a (sourceTape M i))
  (z.1, fun j => if h : j.val < (source M).k then
    z.2 ⟨j.val,h⟩ else (a j,.stay))

/-- Run a multiplier-side controller on the original tape prefix of the
    serializer host. The extra tapes are inert until the serializer starts. -/
def suffixControllerOnSerializerHost (M : MultitapeTM)
    (C : Controller (source M)) : Controller (extension M) where
  K := C.K
  entry := C.entry
  exit := C.exit
  distinct := C.distinct
  transition := suffixTransition M C
  marker := by
    intro q a j hj
    by_cases h : j.val < (source M).k
    · have hm := C.marker q (fun i => a (sourceTape M i)) ⟨j.val,h⟩ hj
      simpa [suffixTransition,h] using hm
    · simp [suffixTransition,h,hj]
  noMarker := by
    intro q a j hj
    by_cases h : j.val < (source M).k
    · have hm := C.noMarker q (fun i => a (sourceTape M i)) ⟨j.val,h⟩ hj
      simpa [suffixTransition,h] using hm
    · simp [suffixTransition,h,hj]
  frozen := by
    intro a
    have hf := C.frozen (fun i => a (sourceTape M i))
    apply Prod.ext
    · simpa [suffixTransition] using congrArg Prod.fst hf
    · funext j
      by_cases h : j.val < (source M).k
      · have idx : sourceTape M (⟨j.val,h⟩ : Fin (source M).k) = j := by
          apply Fin.ext
          rfl
        simpa [suffixTransition,h,idx] using
          congrFun (congrArg Prod.snd hf) (⟨j.val,h⟩ : Fin (source M).k)
      · simp [suffixTransition,h]
  readonly := by
    intro q a
    have hi : sourceTape M (source M).inTape = (extension M).inTape := by
      apply Fin.ext
      rfl
    rw [← hi]
    have hbound : (sourceTape M (source M).inTape).val < (source M).k := by
      simp only [sourceTape, MultitapeTM.inTape, Fin.val_mk]
      have hk := (source M).two_le_k
      omega
    simpa [suffixTransition,sourceTape,hbound] using
      C.readonly q (fun i => a (sourceTape M i))

def suffixEmbed (M : MultitapeTM) (C : Controller (source M))
    (extraCells : Fin (extension M).k → ℕ → (source M).Sym)
    (extraHeads : Fin (extension M).k → ℕ)
    (c : C.machine.Cfg) : (suffixControllerOnSerializerHost M C).machine.Cfg where
  state := c.state
  cells := fun j => if h : j.val < (source M).k then c.cells ⟨j.val,h⟩ else extraCells j
  head := fun j => if h : j.val < (source M).k then c.head ⟨j.val,h⟩ else extraHeads j

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem suffixEmbed_step (M : MultitapeTM) (C : Controller (source M))
    (extraCells : Fin (extension M).k → ℕ → (source M).Sym)
    (extraHeads : Fin (extension M).k → ℕ) (c : C.machine.Cfg) :
    (suffixControllerOnSerializerHost M C).machine.step
        (suffixEmbed M C extraCells extraHeads c) =
      suffixEmbed M C extraCells extraHeads (C.machine.step c) := by
  cases c
  apply cfg_ext (suffixControllerOnSerializerHost M C).machine
  · simp [MultitapeTM.step, suffixControllerOnSerializerHost, suffixTransition,
      suffixEmbed, sourceTape]
  · funext j p
    by_cases h : j.val < (source M).k
    · have idx : sourceTape M (⟨j.val,h⟩ : Fin (source M).k) = j := by
        apply Fin.ext
        rfl
      simp [MultitapeTM.step, suffixControllerOnSerializerHost, suffixTransition,
        suffixEmbed, sourceTape, h]
    · simp [MultitapeTM.step, suffixControllerOnSerializerHost, suffixTransition,
        suffixEmbed, sourceTape, h]
  · funext j
    by_cases h : j.val < (source M).k
    · have idx : sourceTape M (⟨j.val,h⟩ : Fin (source M).k) = j := by
        apply Fin.ext
        rfl
      simp [MultitapeTM.step, suffixControllerOnSerializerHost, suffixTransition,
        suffixEmbed, sourceTape, h]
    · simp [MultitapeTM.step, suffixControllerOnSerializerHost, suffixTransition,
        suffixEmbed, sourceTape, h]

theorem suffixEmbed_run (M : MultitapeTM) (C : Controller (source M))
    (extraCells : Fin (extension M).k → ℕ → (source M).Sym)
    (extraHeads : Fin (extension M).k → ℕ) (c : C.machine.Cfg) (t : ℕ) :
    (suffixControllerOnSerializerHost M C).machine.step^[t]
        (suffixEmbed M C extraCells extraHeads c) =
      suffixEmbed M C extraCells extraHeads (C.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', suffixEmbed_step]

def serializerController (M : MultitapeTM) : Controller (extension M) :=
  let r := (source M).k - 2
  let C := CountedBlockOnMultiplierAlphabet.controller (source M)
  let E := TapeExtension.machine (host M) r
  let hroute : SerializerFreshTapeRouting.routing r E.inTape = E.inTape := by
    change SerializerFreshTapeRouting.routing r ⟨0, by omega⟩ = ⟨0, by omega⟩
    exact SerializerFreshTapeRouting.routing_input r
  permuteController (padController C r) (SerializerFreshTapeRouting.routing r) hroute

theorem serializerController_machine (M : MultitapeTM) :
    (serializerController M).machine = machine M := by
  rfl

def suffixSerializerController (M : MultitapeTM)
    (C : Controller (source M)) : Controller (extension M) :=
  MachineSequence.sequence (suffixControllerOnSerializerHost M C)
    (serializerController M)

private theorem sequence_left_step {B : MultitapeTM} (P Q : Controller B)
    (c : P.machine.Cfg) (hc : c.state ≠ P.exit) :
    (MachineSequence.sequence P Q).machine.step (MachineSequence.leftCfg P Q c) =
      MachineSequence.leftCfg P Q (P.machine.step c) := by
  simp [MultitapeTM.step, MachineSequence.sequence, MachineSequence.leftCfg, hc]

private theorem sequence_left_run {B : MultitapeTM} (P Q : Controller B)
    (c : P.machine.Cfg) (t : ℕ)
    (hno : ∀ s, s < t → (P.machine.step^[s] c).state ≠ P.exit) :
    (MachineSequence.sequence P Q).machine.step^[t]
        (MachineSequence.leftCfg P Q c) =
      MachineSequence.leftCfg P Q (P.machine.step^[t] c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [Function.iterate_succ_apply']
      · exact sequence_left_step P Q _ (hno t (Nat.lt_succ_self t))
      · intro s hs
        exact hno s (Nat.lt_trans hs (Nat.lt_succ_self t))

private theorem sequence_handoff_step {B : MultitapeTM} (P Q : Controller B)
    (c : P.machine.Cfg) (hc : c.state = P.exit) :
    (MachineSequence.sequence P Q).machine.step (MachineSequence.leftCfg P Q c) =
      MachineSequence.rightCfg P Q (MachineSequence.handoff P Q c) := by
  simp [MultitapeTM.step, MachineSequence.sequence, MachineSequence.leftCfg,
    MachineSequence.rightCfg, MachineSequence.handoff, hc]

private theorem sequence_right_step {B : MultitapeTM} (P Q : Controller B)
    (c : Q.machine.Cfg) :
    (MachineSequence.sequence P Q).machine.step (MachineSequence.rightCfg P Q c) =
      MachineSequence.rightCfg P Q (Q.machine.step c) := by
  simp [MultitapeTM.step, MachineSequence.sequence, MachineSequence.rightCfg]

private theorem sequence_right_run {B : MultitapeTM} (P Q : Controller B)
    (c : Q.machine.Cfg) (t : ℕ) :
    (MachineSequence.sequence P Q).machine.step^[t]
        (MachineSequence.rightCfg P Q c) =
      MachineSequence.rightCfg P Q (Q.machine.step^[t] c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', sequence_right_step]

/-- Compose the lifted multiplier suffix, its one stationary handoff, and the
    routed serializer. The frame equality is isolated as the caller-layout
    obligation, while both execution segments are reused as exact run proofs. -/
theorem suffix_then_serializer (M : MultitapeTM)
    (C : Controller (source M))
    (extraCells : Fin (extension M).k → ℕ → (source M).Sym)
    (extraHeads : Fin (extension M).k → ℕ)
    (c cEnd : C.machine.Cfg) (ts tr : ℕ)
    (hRun : C.machine.step^[ts] c = cEnd)
    (hNoEarlyExit : ∀ s, s < ts →
      ((suffixControllerOnSerializerHost M C).machine.step^[s]
        (suffixEmbed M C extraCells extraHeads c)).state ≠ C.exit)
    (hExit : cEnd.state = C.exit)
    (serStart serEnd : (serializerController M).machine.Cfg)
    (hFrame : MachineSequence.handoff (suffixControllerOnSerializerHost M C)
      (serializerController M) (suffixEmbed M C extraCells extraHeads cEnd) = serStart)
    (hSer : (serializerController M).machine.step^[tr] serStart = serEnd) :
    (suffixSerializerController M C).machine.step^[ts+1+tr]
      (MachineSequence.leftCfg (suffixControllerOnSerializerHost M C)
        (serializerController M) (suffixEmbed M C extraCells extraHeads c)) =
      MachineSequence.rightCfg (suffixControllerOnSerializerHost M C)
        (serializerController M) serEnd := by
  let P := suffixControllerOnSerializerHost M C
  let Q := serializerController M
  have hpadded : P.machine.step^[ts] (suffixEmbed M C extraCells extraHeads c) =
      suffixEmbed M C extraCells extraHeads cEnd := by
    rw [suffixEmbed_run, hRun]
  have hleft : (MachineSequence.sequence P Q).machine.step^[ts]
        (MachineSequence.leftCfg P Q (suffixEmbed M C extraCells extraHeads c)) =
      MachineSequence.leftCfg P Q (suffixEmbed M C extraCells extraHeads cEnd) := by
    rw [sequence_left_run]
    · exact congrArg (MachineSequence.leftCfg P Q) hpadded
    · exact hNoEarlyExit
  have hprefix : (MachineSequence.sequence P Q).machine.step^[ts+1]
      (MachineSequence.leftCfg P Q (suffixEmbed M C extraCells extraHeads c)) =
      MachineSequence.rightCfg P Q serStart := by
    rw [Function.iterate_succ_apply', hleft]
    have hend : (suffixEmbed M C extraCells extraHeads cEnd).state = P.exit := by
      simpa [suffixEmbed, P, suffixControllerOnSerializerHost] using hExit
    rw [sequence_handoff_step P Q _ hend, hFrame]
  change (MachineSequence.sequence P Q).machine.step^[ts+1+tr]
      (MachineSequence.leftCfg P Q (suffixEmbed M C extraCells extraHeads c)) =
    MachineSequence.rightCfg P Q serEnd
  rw [show ts+1+tr = tr+(ts+1) by omega, Function.iterate_add_apply, hprefix]
  rw [sequence_right_run, hSer]

end BitDFT.RoutedCountedBlockFreshTapes
end


