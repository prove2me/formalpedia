-- Prove2me | Definitions.Def_BitDFT_unpackerMachine
-- name    : BitDFT_unpackerMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T02:39:40.191363+00:00
-- url     : https://prove2.me/theorems/8d96031a-e6c6-4047-b703-12956d8645d2
-- title:
--   The unpacking machine: balanced base-$2^\beta$ digit extraction on six tapes
-- statement:
--   A six-tape deterministic Turing machine that turns a packed integer into its balanced base-$2^\beta$ digits.
--
--   **Input.** The machine reads the binary encoding of $r$, of $\beta$ and of a signed integer $W$ with $|W| < 2^{\beta r}$, in the platform's self-delimiting format.
--
--   **Behaviour.** It counts the unary prefix of each header to skip or to copy the header's binary digits, expands $\beta$'s binary digits into $\beta$ unary marks by shift and add, reads the sign bit into a two's-complement carry, walks to the last magnitude bit, and then repeats $r$ times: consume $\beta$ marks while walking the input leftwards, so that the two's-complement carry and the digit's add-carry are folded one bit at a time into a buffer; the top bit of the field gives the digit's sign, which is written first, and the buffer then yields the digit's magnitude most significant bit first. After each field the $\beta$ counter is restored from its unary template and one field is counted off the $r$ counter; the machine halts when that counter runs out.
--
--   The tapes are: input (read only), output, the working $\beta$ counter, the $\beta$ template together with the scratch space of the binary expansion, the field buffer, and the working $r$ counter. The state carries a phase together with the three bits the computation needs (two's-complement carry, digit carry, digit sign). Every phase is a one-symbol-per-step transducer, so the machine takes a number of steps proportional to $r\beta$ plus a term linear in the two header lengths.
--
--   Only the transition system and the four structural obligations of the machine model are defined here. The claim that this machine computes `IntMul.HvdH.kunpack` in linear time is the separate open problem `BitDFT.unpacking_machine`.
-- source:
--   Internal: the machine component of the Prove2me theorem BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), following the design in the Harvey--van der Hoeven digit-extraction step (arXiv:2503.22848, Section 2, fixed-point rounding and Kronecker substitution).

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_BitDFT_machineKit

set_option autoImplicit false
noncomputable section
namespace BitDFT.Unpacker

open IntMul TMKit

/-!
# The unpacking machine

Tapes `0` input, `1` output, `2` the working `β` counter (unary), `3` the `β` template (unary, and
scratch for the binary expansion before that), `4` the field buffer, `5` the working `r` counter.

The machine parses `encNat r` and `encNat β`, turns `β`'s binary digits into `β` unary marks (shift
and add), reads the sign bit into the two's-complement carry, walks to the last magnitude bit, and
then loops: consume `β` marks while walking the input leftwards computing the digit's bits into the
buffer; emit the digit's sign and magnitude; restore the `β` counter from the template; count one
field off the `r` counter; halt when it runs out.

Every phase is a one-symbol-per-step transducer; the heads are parked at cell `1` (just after `▷`)
before a write pass and at the first free cell after it.
-/

inductive Ph
  | seekLeft | rUnary | rSkipFalse | rBinary
  | betaUnary | bSkipFalse | betaCopy
  | tplRew1 | expBit | dblCnt | dblBuf | dblCopy | dblRew | dblApp | dblBit
  | expRew1 | expRew2 | cntTpl | cntRewSign
  | sign | toEnd
  | fieldBits | emitSign | bufRewind | emitMag | cntRewLoad
  | tplRew2 | loadCnt | tplBack | nextField | halt
  deriving DecidableEq

instance : Fintype Ph where
  elems := {.seekLeft, .rUnary, .rSkipFalse, .rBinary, .betaUnary, .bSkipFalse, .betaCopy,
    .tplRew1, .expBit, .dblCnt, .dblBuf, .dblCopy, .dblRew, .dblApp, .dblBit,
    .expRew1, .expRew2, .cntTpl, .cntRewSign,
    .sign, .toEnd, .fieldBits, .emitSign, .bufRewind, .emitMag, .cntRewLoad,
    .tplRew2, .loadCnt, .tplBack, .nextField, .halt}
  complete := by intro x; cases x <;> simp

/-- Machine state. -/
structure Q where
  ph : Ph
  g : Bool
  κ : Bool
  s : Bool
  deriving DecidableEq

instance : Fintype Q where
  elems := Finset.univ.biUnion (fun p => ({⟨p, true, true, true⟩, ⟨p, true, true, false⟩,
    ⟨p, true, false, true⟩, ⟨p, true, false, false⟩, ⟨p, false, true, true⟩,
    ⟨p, false, true, false⟩, ⟨p, false, false, true⟩, ⟨p, false, false, false⟩} : Finset Q))
  complete := by
    intro ⟨p, g, κ, s⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    refine ⟨p, ?_⟩
    cases g <;> cases κ <;> cases s <;> simp

abbrev inT : Fin 6 := 0
abbrev outT : Fin 6 := 1
abbrev cnt : Fin 6 := 2
abbrev tpl : Fin 6 := 3
abbrev buf : Fin 6 := 4
abbrev cntR : Fin 6 := 5

/-- The symbol a cell keeps: `▷` is never rewritten, the guard of `mkMachine` restores it. -/
def keepSym (a : Sym) : Sym := if a = Sym.start then Sym.blank else a

theorem keepSym_ne (x : Sym) : keepSym x ≠ Sym.start := by
  unfold keepSym; split <;> simp_all

def stay (a : Fin 6 → Sym) : Fin 6 → Sym × Move := fun i => (keepSym (a i), Move.stay)

/-- Change phase, keeping the carries and all tapes. -/
def go (q : Q) (p : Ph) (a : Fin 6 → Sym) : Q × (Fin 6 → Sym × Move) :=
  (⟨p, q.g, q.κ, q.s⟩, stay a)

/-- Move a designated head one cell in a direction, keeping everything else. -/
def mv (a : Fin 6 → Sym) (t : Fin 6) (d : Move) : Fin 6 → Sym × Move :=
  fun i => if i = t then (keepSym (a i), d) else (keepSym (a i), Move.stay)

def isBit (s : Sym) : Bool := s = Sym.zero || s = Sym.one

/-- The raw transition function of the unpacking machine. -/
def spec (q : Q) (a : Fin 6 → Sym) : Q × (Fin 6 → Sym × Move) :=
  match q.ph with
  -- ── preamble: skip `▷`, parse `encNat r` ──────────────────────────────────
  | .seekLeft =>
      if a inT = Sym.start then (q, mv a inT Move.right) else go q .rUnary a
  | .rUnary =>
      if a inT = Sym.one then (q, fun i => if i = inT then (a i, Move.right)
        else if i = cntR then (Sym.one, Move.right) else (a i, Move.stay))
      else go q .rSkipFalse a
  | .rSkipFalse => (q, mv a inT Move.right)
  | .rBinary =>
      if a cntR = Sym.one then (q, fun i => if i = cntR then (Sym.blank, Move.left)
        else if i = inT then (a i, Move.right) else (a i, Move.stay))
      else go q .betaUnary a
  -- ── parse `encNat β`: count its marks, copy its bits to tape 3 ────────────
  | .betaUnary =>
      if a inT = Sym.one then (q, fun i => if i = inT then (a i, Move.right)
        else if i = cnt then (Sym.one, Move.right) else (a i, Move.stay))
      else go q .bSkipFalse a
  | .bSkipFalse => (q, mv a inT Move.right)
  | .betaCopy =>
      if a cnt = Sym.one then (q, fun i => if i = cnt then (Sym.blank, Move.left)
        else if i = tpl then (a inT, Move.right)
        else if i = inT then (a i, Move.right) else (a i, Move.stay))
      else go q .tplRew1 a
  -- ── expand β's binary digits into β unary marks on tape 2 (shift and add) ─
  | .tplRew1 =>
      if a tpl = Sym.start then (q, mv a tpl Move.right) else (q, mv a tpl Move.left)
  | .expBit =>
      if isBit (a tpl) then go q .dblCnt a else go q .expRew1 a
  | .dblCnt =>
      if a cnt = Sym.start then (q, mv a cnt Move.right) else (q, mv a cnt Move.left)
  | .dblBuf =>
      if a buf = Sym.start then (q, mv a buf Move.right) else (q, mv a buf Move.left)
  | .dblCopy =>
      if a cnt = Sym.one then (q, fun i => if i = buf then (Sym.one, Move.right)
        else if i = cnt then (a i, Move.right) else (a i, Move.stay))
      else go q .dblRew a
  | .dblRew =>
      if a buf = Sym.start then (q, mv a buf Move.right) else (q, mv a buf Move.left)
  | .dblApp =>
      if a buf = Sym.one then (q, fun i => if i = cnt then (Sym.one, Move.right)
        else if i = buf then (a i, Move.right) else (a i, Move.stay))
      else go q .dblBit a
  | .dblBit =>
      (⟨.expBit, q.g, q.κ, q.s⟩, fun i =>
        if i = tpl then (a i, Move.right)
        else if i = cnt then (if a tpl = Sym.one then Sym.one else keepSym (a i),
          if a tpl = Sym.one then Move.right else Move.stay)
        else (a i, Move.stay))
  -- ── make the unary marks the template ────────────────────────────────────
  | .expRew1 =>
      if a tpl = Sym.start then (q, mv a tpl Move.right) else (q, mv a tpl Move.left)
  | .expRew2 =>
      if a cnt = Sym.start then (q, mv a cnt Move.right) else (q, mv a cnt Move.left)
  | .cntTpl =>
      if a cnt = Sym.one then (q, fun i => if i = tpl then (Sym.one, Move.right)
        else if i = cnt then (a i, Move.right) else (a i, Move.stay))
      else go q .cntRewSign a
  | .cntRewSign =>
      if a cnt = Sym.start then go q .sign a
      else (q, mv a cnt Move.left)
  -- ── sign bit, then walk to the last magnitude bit ────────────────────────
  | .sign =>
      (⟨.toEnd, decide (a inT = Sym.one), q.κ, q.s⟩, mv a inT Move.right)
  | .toEnd =>
      if a inT = Sym.sep then
        (⟨.fieldBits, q.g, q.κ, q.s⟩, mv a inT Move.left)
      else (q, mv a inT Move.right)
  -- ── one field: consume the marks, fold the carries, fill the buffer ──────
  | .fieldBits =>
      if a cnt = Sym.one then
        (⟨.fieldBits, q.g && !(decide (a inT = Sym.one)),
            (decide (a inT = Sym.one) != q.g) && q.κ,
            (decide (a inT = Sym.one) != q.g) != q.κ⟩,
          fun i =>
            if i = buf then ((if (decide (a inT = Sym.one) != q.g) != q.κ then Sym.one else Sym.zero),
              Move.right)
            else if i = cnt then (Sym.blank, Move.right)
            else if i = inT then (a i, Move.left) else (a i, Move.stay))
      else go q .emitSign a
  | .emitSign =>
      (⟨.bufRewind, q.g, q.κ, q.s⟩,
        fun i => if i = outT then ((if q.s then Sym.one else Sym.zero), Move.right)
          else (a i, Move.stay))
  | .bufRewind => (⟨.emitMag, q.g, q.κ, q.s⟩, mv a buf Move.left)
  | .emitMag =>
      if isBit (a buf) then (q, fun i => if i = outT then (keepSym (a buf), Move.right)
        else if i = buf then (Sym.blank, Move.left) else (a i, Move.stay))
      else go q .cntRewLoad a
  | .cntRewLoad =>
      if a cnt = Sym.start then go q .tplRew2 a
      else (q, mv a cnt Move.left)
  -- ── restore the β counter, count the field, halt when r is exhausted ─────
  | .tplRew2 =>
      if a tpl = Sym.start then (q, mv a tpl Move.right) else (q, mv a tpl Move.left)
  | .loadCnt =>
      if a tpl = Sym.one then (q, fun i => if i = cnt then (Sym.one, Move.right)
        else if i = tpl then (a i, Move.right) else (a i, Move.stay))
      else go q .tplBack a
  | .tplBack =>
      if a tpl = Sym.start then go q .nextField a else (q, mv a tpl Move.left)
  | .nextField =>
      if a cntR = Sym.one then (q, fun i => if i = cntR then (Sym.blank, Move.left)
        else (a i, Move.stay))
      else go q .halt a
  | .halt => (q, stay a)

/-- The machine's guard.  A cell holding `▷` keeps it and stays; tape `0` keeps its symbol and only
takes the movement; any other cell takes the specification's symbol unless that would write `▷`, in
which case it is blanked.  With these three clauses the four structural axioms hold by construction,
so the specification is never reasoned about again. -/
def guard (q : Q) (a : Fin 6 → Sym) : Fin 6 → Sym × Move :=
  let r := spec q a
  fun i =>
    if a i = Sym.start then (a i, Move.stay)
    else if i = inT then (a i, (r.2 i).2)
    else if (r.2 i).1 = Sym.start then (Sym.blank, (r.2 i).2)
    else (r.2 i)

/-- The unpacking machine: six tapes, alphabet `TMKit.Sym`, states `Option Q`. -/
def machine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := Option Q
  qStart := some ⟨.seekLeft, false, false, false⟩
  qHalt := none
  start_ne_halt := by simp
  k := 6
  two_le_k := by norm_num
  δ q a := match q with
    | none => (none, fun i => (a i, Move.stay))
    | some q => ((spec q a).1, guard q a)
  start_preserved := by
    intro q a i hi
    rcases q with _ | q
    · exact ⟨hi, by simp⟩
    · simp [guard, hi]
  start_only_at_start := by
    intro q a i hi
    rcases q with _ | q
    · simpa using hi
    · simp only [guard, if_neg hi]
      by_cases h0 : i = inT
      · subst h0; exact hi
      · simp only [h0, if_false]
        by_cases hw : ((spec q a).2 i).1 = Sym.start
        · simp [hw]
        · simp [hw]
  halt_fixed := by
    intro a
    rfl
  input_readonly := by
    intro q a
    rcases q with _ | q
    · rfl
    · simp only [guard]
      by_cases h : a inT = Sym.start
      · simp [h]
      · simp [h]

end BitDFT.Unpacker


