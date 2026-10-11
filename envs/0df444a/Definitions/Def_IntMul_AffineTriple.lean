-- Prove2me | Definitions.Def_IntMul_AffineTriple
-- name    : IntMul_AffineTriple
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T15:38:34.016976+00:00
-- url     : https://prove2.me/theorems/3123e18f-4acf-4543-9140-413437f91725
-- title:
--   Physical finite-carry descriptor transformation from a to 3a+2
-- statement:
--   A fixed three-tape machine reads an actual marked big-endian bit word from an explicit framed source, with empty output and scratch. It physically seeks the source blank, reads bits backwards, and emits the little-endian word for three times the source value plus two. Its finite carry has only the values zero, one and two; the actual source marker triggers carry emission and halting. Original source cells are retained, the source head returns to its real marker, and output ends at its actual blank. Correctness, full terminal frame and linear transition bound are separate theorem obligations. For a block-size-minus-one word this produces the coefficient-precision-minus-one value 3B-1.
-- source:
--   Original physical affine parameter descriptor construction for sufficient convolution precision. Written by Codex.

import Definitions.Def_IntMul_TapeAdder
namespace IntMul.AffineTriple
open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive State | open | seek | calc (c : Fin 3) | emit | halt deriving DecidableEq
instance : Fintype State where
  elems := {.open,.seek,.calc 0,.calc 1,.calc 2,.emit,.halt}
  complete := by intro q;cases q <;> simp;rename_i c;fin_cases c <;> simp

def digit (c : Fin 3) (b : Bool) : Bool := decide ((3*b.toNat+c.val)%2=1)
def nextCarry (c : Fin 3) (b : Bool) : Fin 3 :=
  ⟨(3*b.toNat+c.val)/2,by fin_cases c <;> cases b <;> decide⟩
def triple (c : Fin 3) : List Bool → List Bool
  | [] => if c=0 then [] else if c=1 then [true] else [false,true]
  | b::bs => digit c b::triple (nextCarry c b) bs

def bitAction (a : Fin 3 → Sym) (c : Fin 3) (b : Bool) : Fin 3 → Sym × Move :=
  fun i => (if i=1 then if digit c b then .one else .zero else a i,
    if i=0 then .left else if i=1 then .right else .stay)
def rawTransition (q : State) (a : Fin 3 → Sym) : State × (Fin 3 → Sym × Move) :=
  match q with
  | .open => (.seek,fun i => (a i,if i=0 ∨ i=1 then .right else .stay))
  | .seek => if a 0=.zero ∨ a 0=.one then
      (.seek,fun i => (a i,if i=0 then .right else .stay))
    else (.calc 2,fun i => (a i,if i=0 then .left else .stay))
  | .calc c =>
      if a 0=.start then
        if c=0 then (.halt,fun i => (a i,.stay))
        else if c=1 then (.halt,fun i => (if i=1 then .one else a i,if i=1 then .right else .stay))
        else (.emit,fun i => (if i=1 then .zero else a i,if i=1 then .right else .stay))
      else if a 0=.zero then (.calc (nextCarry c false),bitAction a c false)
      else if a 0=.one then (.calc (nextCarry c true),bitAction a c true)
      else (.halt,fun i => (a i,.stay))
  | .emit => (.halt,fun i => (if i=1 then .one else a i,if i=1 then .right else .stay))
  | .halt => (.halt,fun i => (a i,.stay))
def transition (q : State) (a : Fin 3 → Sym) : State × (Fin 3 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

abbrev machine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := .open
  qHalt := .halt
  start_ne_halt := by decide
  k := 3
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    change (safeStep (a i) _ _).1=.start ∧ (safeStep (a i) _ _).2≠Move.left
    simp only [safeStep,hi,if_true];split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    change (safeStep (a i) _ _).1≠.start
    simp only [safeStep,if_neg hi];split <;> simp_all
  halt_fixed := by intro a;simp [transition,rawTransition,TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    have h : ((rawTransition q a).2 0).1=a 0 := by
      cases q <;> simp only [rawTransition]
      all_goals try split_ifs
      all_goals simp_all [bitAction]
    change (safeStep (a 0) ((rawTransition q a).2 0).1 _).1=a 0
    rw [h]
    by_cases hs : a 0=Sym.start <;> simp [safeStep,hs]

def initialFrame (w : List Bool) : machine.Cfg where
  state := .open
  cells := fun i => if i=0 then machine.tapeOf (w.map machine.bitSym) else machine.tapeOf []
  head := fun _ => 0
def finalFrame (w : List Bool) : machine.Cfg where
  state := .halt
  cells := fun i => if i=0 then machine.tapeOf (w.map machine.bitSym)
    else if i=1 then machine.tapeOf ((triple 2 w.reverse).map machine.bitSym) else machine.tapeOf []
  head := fun i => if i=1 then (triple 2 w.reverse).length+1 else 0
end IntMul.AffineTriple


