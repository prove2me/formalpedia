-- Prove2me | Definitions.Def_BitDFT_CountedBlockOnWorkTapes
-- name    : BitDFT_CountedBlockOnWorkTapes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T04:40:45.547162+00:00
-- url     : https://prove2.me/theorems/dd118289-89d7-4642-a79c-4e303110f322
-- title:
--   Run the counted serializer on dedicated work tapes
-- statement:
--   A fixed five-tape controller runs the counted-block serializer on work tapes 1 through 4, leaving tape 0 as the machine's read-only input and preserving its contents and head. It also preserves the supplied configuration on all four work tapes while the serializer advances from its initial to final frame.
-- source:
--   Tape-relocated controller for the existing CountedStream serializer. The relocation keeps the machine's distinguished input tape untouched, so a serializer can consume a product staged on a work tape and write its result to a separate work tape.

import Definitions.Def_BitDFT_CountedBlock
import Definitions.Def_BitDFT_MachineSequence

set_option autoImplicit false
noncomputable section

namespace BitDFT.CountedBlockOnWorkTapes
open IntMul BitDFT.MachineSequence

private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

abbrev sourceMachine := CountedStream.machine

abbrev host : MultitapeTM where
  Sym := sourceMachine.Sym
  blank := sourceMachine.blank
  startSym := sourceMachine.startSym
  zero := sourceMachine.zero
  one := sourceMachine.one
  sep := sourceMachine.sep
  syms_distinct := sourceMachine.syms_distinct
  K := Bool
  qStart := false
  qHalt := true
  start_ne_halt := by decide
  k := 5
  two_le_k := by decide
  δ := fun _ a => (true, fun i => (a i, .stay))
  start_preserved := by
    intro q a i hi
    exact ⟨hi, by change Move.stay ≠ Move.left; decide⟩
  start_only_at_start := by intro q a i hi; exact hi
  halt_fixed := by intro a; rfl
  input_readonly := by intro q a; rfl

def workTape (i : Fin 4) : Fin 5 := ⟨i.val + 1, by omega⟩

def hostToWork (j : Fin 5) : Fin 4 := ⟨j.val - 1, by have := j.isLt; omega⟩

theorem workTape_hostToWork (j : Fin 5) (hj : 0 < j.val) :
    workTape (hostToWork j) = j := by
  apply Fin.ext
  simp [workTape, hostToWork]
  omega

def transition (q : sourceMachine.K)
    (a : Fin 5 → sourceMachine.Sym) :
    sourceMachine.K × (Fin 5 → sourceMachine.Sym × Move) := by
  classical
  let inner : Fin 4 → sourceMachine.Sym := fun i => a (workTape i)
  let r := sourceMachine.δ q inner
  exact (r.1, fun j => if hj : j.val = 0 then (a j, .stay)
    else r.2 (hostToWork j))

def controller : Controller host where
  K := sourceMachine.K
  entry := sourceMachine.qStart
  exit := sourceMachine.qHalt
  distinct := sourceMachine.start_ne_halt
  transition := fun q a => transition q a
  marker := by
    intro q a j hj
    by_cases h0 : j = 0
    · subst j
      simp [transition, hj]
    · have hval : j.val ≠ 0 := by
        intro hv
        exact h0 (Fin.ext hv)
      have hp : 0 < j.val := Nat.pos_of_ne_zero hval
      have hinner : (fun i : Fin 4 => a (workTape i)) (hostToWork j) = host.startSym := by
        change a (workTape (hostToWork j)) = host.startSym
        rw [workTape_hostToWork j hp]
        exact hj
      have hm := sourceMachine.start_preserved q (fun i : Fin 4 => a (workTape i))
        (hostToWork j) hinner
      simpa [transition, h0] using hm
  noMarker := by
    intro q a j hj
    by_cases h0 : j = 0
    · subst j
      simp [transition, hj]
    · have hval : j.val ≠ 0 := by
        intro hv
        exact h0 (Fin.ext hv)
      have hp : 0 < j.val := Nat.pos_of_ne_zero hval
      have hinner : (fun i : Fin 4 => a (workTape i)) (hostToWork j) ≠
          sourceMachine.startSym := by
        change a (workTape (hostToWork j)) ≠ sourceMachine.startSym
        rw [workTape_hostToWork j hp]
        exact hj
      have hm := sourceMachine.start_only_at_start q
        (fun i : Fin 4 => a (workTape i)) (hostToWork j) hinner
      simpa [transition, h0] using hm
  frozen := by
    intro a
    have h := sourceMachine.halt_fixed (fun i : Fin 4 => a (workTape i))
    apply Prod.ext
    · simpa [transition] using congrArg Prod.fst h
    · funext j
      by_cases h0 : j = 0
      · subst j
        simp [transition]
      · have hval : j.val ≠ 0 := by
          intro hv
          exact h0 (Fin.ext hv)
        have hp : 0 < j.val := Nat.pos_of_ne_zero hval
        simpa [transition, h0, workTape_hostToWork j hp] using
          congrFun (congrArg Prod.snd h) (hostToWork j)
  readonly := by
    intro q a
    simp [transition, MultitapeTM.inTape]

abbrev machine := controller.machine

def embed (base : machine.Cfg) (c : sourceMachine.Cfg) : machine.Cfg where
  state := c.state
  cells := fun j => if hj : j.val = 0 then base.cells j
    else c.cells (hostToWork j)
  head := fun j => if hj : j.val = 0 then base.head j
    else c.head (hostToWork j)

theorem step (base : machine.Cfg) (c : sourceMachine.Cfg) :
    machine.step (embed base c) = embed base (sourceMachine.step c) := by
  cases c
  apply cfg_ext machine
  · rfl
  · funext j p
    fin_cases j <;>
      simp [MultitapeTM.step, machine, controller, transition, embed, workTape,
        hostToWork, workTape_hostToWork]
  · funext j
    fin_cases j <;>
      simp [MultitapeTM.step, machine, controller, transition, embed, workTape,
        hostToWork, workTape_hostToWork]

theorem run (base : machine.Cfg) (c : sourceMachine.Cfg) (t : ℕ) :
    machine.step^[t] (embed base c) = embed base (sourceMachine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', step]

end BitDFT.CountedBlockOnWorkTapes
end


