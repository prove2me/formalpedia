-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CR23Dec
-- name    : LinearSetReconciliation327_Main_CR23Dec
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T12:00:06.703575+00:00
-- url     : https://prove2.me/theorems/07a98b55-285d-437e-aa56-075f217f0155
-- title:
--   Proposition 2.3's decoder, exported as a compiled `Stmt` (`decStmt`) and its program
-- statement:
--   The decoder of Proposition 2.3 as a source-level program: the `Stmt` `decStmt`, built from a 63-instruction prologue (computation half plus store half), the round loop `decRoundStmt` and the emit pass, and the program `progDec = decStmt.compile 0 ++ [halt]` obtained from it.  One round is the five-stage chain seed scan, candidate scan, `r1 := 0`, XOR of the candidate columns, parity pass, followed by the bookkeeping `w := w/4`, `tag := tag+1`, `mstLen := mstLen+len`.  The point of exporting the `Stmt` rather than only the compiled `Program` is that `Stmt.compile` is what relocates absolute jump targets, so a `Stmt` can be sequenced with a further stage while a bare `Program` cannot.  Every declaration is copied byte-identically from the accepted development's section 3 vocabulary.
-- source:
--   A. (2026), arXiv:2611.11409, \u00a72.3 (Proposition 2.3, the CR23 decoder); M. Cheraghchi and I. Ribeiro, Simple Codes for Sparse Recovery, arXiv:1901.02852, https://arxiv.org/abs/1901.02852

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23

/-!
# Proposition 2.3: the decoder as a `Stmt`

`progDec` is the decoder program of Proposition 2.3 (`progDec = decStmt.compile 0 ++ [iHalt]`).
The parent theorem `proposition_2_3` only exports the bare `Program`, whose jump targets are
absolute, so it cannot be relocated by `Stmt.compile`; Theorem 6.5's CR stage needs the `Stmt`.

Every declaration below is copied byte-identically from the accepted development
`Solutions/Sol_proposition_2_3.lean` (skeleton subtraction); this module only publishes the
definition vocabulary of that file's section 3, which the accepted file kept local.
-/

set_option autoImplicit false

namespace LinearSetReconciliation327.Main

/-- The computation half of the prologue: `D`, `N`, `graph0`, `decBase`, `M`, `lb`, `L = lb+1`,
`2^L`, `4096`, `t = M/4096`, `R = D·M·L`, and the frame start. -/
def progDecPreC : List Instr :=
  [iImm r2 1, iTbl r3 r0, iTbl r4 r2, iSub r4 r4 r2, iAdd r5 r2 r4, iMul r6 r3 r4,
   iAdd r7 r6 r6, iAdd r5 r5 r7, iAdd r7 r5 r6, iTbl r8 r7, iAdd r7 r7 r2, iTbl r10 r7,
   iAdd r9 r10 r2, iShl r11 r2 r9, iImm r12 295147905179352825856, iDiv r13 r8 r12, iMul r14 r3 r8,
   iMul r14 r14 r9, iAdd r14 r14 r5, iAdd r14 r14 r6, iAdd r14 r14 r2, iAdd r14 r14 r2]

/-- The store half of the prologue: the fifteen slot values, `mem (frame+1+k)`. -/
def progDecPreS : List Instr :=
  [iBor r15 r14 r14, iAdd r15 r15 r2,
   iSt r15 r3, iAdd r15 r15 r2,
   iSt r15 r4, iAdd r15 r15 r2,
   iSt r15 r8, iAdd r15 r15 r2,
   iSt r15 r9, iAdd r15 r15 r2,
   iSt r15 r10, iAdd r15 r15 r2,
   iSt r15 r11, iAdd r15 r15 r2,
   iSt r15 r13, iAdd r15 r15 r2,
   iSt r15 r13, iAdd r15 r15 r2,
   iSt r15 r2,
   iImm r7 32, iAdd r7 r14 r7, iAdd r15 r15 r2,
   iSt r15 r7,
   iAdd r7 r7 r13, iAdd r7 r7 r13, iAdd r7 r7 r2, iAdd r15 r15 r2,
   iSt r15 r7,
   iAdd r7 r7 r11, iAdd r15 r15 r2,
   iSt r15 r7,
   iAdd r7 r7 r13, iAdd r7 r7 r13, iAdd r7 r7 r2, iAdd r15 r15 r2,
   iSt r15 r7,
   iAdd r7 r7 r11, iAdd r15 r15 r2,
   iSt r15 r7,
   iAdd r15 r15 r2,
   iSt r15 r0]

/-- The initialisation of body (a): read `D, M, L, lb` out of the slot block through `r14`, set the
constants, and start the walk at `q = 0`. -/
def decScanInit : List Instr :=
  [iImm r13 1, iAdd r13 r14 r13, iLd r13 r13, iImm r15 3, iAdd r15 r14 r15, iLd r7 r15,
   iMul r1 r13 r7, iImm r15 4, iAdd r15 r14 r15, iLd r8 r15, iImm r15 5, iAdd r15 r14 r15,
   iLd r10 r15, iImm r11 1, iImm r12 1024, iBor r6 r7 r7, iImm r0 0, iImm r2 0, iImm r3 0,
   iImm r4 0, iImm r5 0]

/-- Bit extraction, part 1: `r13 = mem[q/1024]` and `r15 = (q % 1024)·L + lb`. -/
def decScanBA : List Instr :=
  [iDiv r13 r0 r12, iLd r13 r13, iMod r15 r0 r12, iMul r15 r15 r8, iAdd r15 r15 r10]

/-- Bit extraction, part 2: `bit = (mem[q/1024] >>> off) &&& 1` and `cnt += bit`. -/
def decScanBB : List Instr := [iShr r13 r13 r15, iBand r13 r13 r11, iAdd r2 r2 r13]

/-- The close indicator `zc` and the gated comparison `gg = g·zc`. -/
def decScanBC : List Instr :=
  [iLt r15 r11 r6, iSub r13 r11 r15, iLt r15 r3 r2, iMul r15 r15 r13]

/-- The argmax seed: `bestseed := bestseed + gg·(s − bestseed)`. -/
def decScanBD : List Instr := [iSub r13 r5 r4, iMul r13 r13 r15, iAdd r4 r4 r13]

/-- The maximum: `best := best + gg·(cnt − best)`. -/
def decScanBE : List Instr := [iSub r13 r2 r3, iMul r13 r13 r15, iAdd r3 r3 r13]

/-- The seed step and `1 − zc`. -/
def decScanBF : List Instr := [iLt r15 r11 r6, iSub r13 r11 r15, iAdd r5 r5 r13, iSub r15 r11 r13]

/-- The counter reset, the bucket countdown and the check index. -/
def decScanBG : List Instr :=
  [iMul r2 r2 r15, iMul r15 r13 r7, iSub r6 r6 r11, iAdd r6 r6 r15, iAdd r0 r0 r11]

/-- **The body of body (a): 27 straight-line instructions, no branch.**  It reads the count-parity
bit of check `q` (`decBit_read`), adds it to `cnt` and folds the running argmax **only when the seed
closes** (`decScanClose_ind`), then steps `s`, resets `cnt` and counts `b` down. -/
def decScanBody : List Instr :=
  decScanBA ++ decScanBB ++ decScanBC ++ decScanBD ++ decScanBE ++ decScanBF ++ decScanBG

/-- **Body (a)** as a statement: the initialisation, then the `D·M`-step scan, then nothing (the
argmax seed is left in `r4`, and the body writes no memory at all). -/
def decScanStmt : Stmt :=
  Stmt.seq (Stmt.code decScanInit)
    (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decScanBody))

/-- Loading part 1: the slot address of the candidate base. -/
def decXorL1 : List Instr := [iImm r8 32, iAdd r8 r14 r8]

/-- Loading part 2: `r8 := decCandBase N t + i` and `r0 := mem r8`. -/
def decXorL2 : List Instr := [iAdd r8 r8 r1, iLd r0 r8]

/-- The candidate value: `r0 := mem (decCandBase N t + i)`. -/
def decXorLoad : List Instr := decXorL1 ++ decXorL2

/-- The `UpData` prologue: `r3 = D`, `r5 = upBase v`, `r6 = D`, `r7 = upBase v`,
`r10 = upBase v + 1`, `r11 = upBase v + 2D`, `r12 = 2`, `r13 = 1`, `r15 = 1`. -/
def decXorPre : List Instr :=
  [iImm r8 1, iAdd r8 r14 r8, iLd r3 r8, iImm r8 1, iAdd r8 r0 r8,
   iTbl r5 r8, iBor r6 r3 r3, iBor r7 r5 r5, iImm r15 1, iAdd r10 r5 r15,
   iAdd r11 r5 r3, iAdd r11 r11 r3, iImm r12 2, iBor r13 r15 r15]

/-- The candidate index bump `i := i + 1`. -/
def decXorPost : List Instr := [iImm r15 1, iAdd r1 r1 r15]

/-- The seed loop: `progUp`'s countdown loop, verbatim. -/
def decXorInner : Stmt := Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody)

/-- **Body (c)**: `for i < len: v := mem (candBase + i); toggle the column of `v` into the payload`. -/
def decXorStmt : Stmt :=
  Stmt.loop (Cond.lt r8 r1 r2)
    (Stmt.seq (Stmt.code decXorLoad)
      (Stmt.seq (Stmt.code decXorPre) (Stmt.seq decXorInner (Stmt.code decXorPost))))

namespace DecCandPay

/-- Initialisation of body (b): the two counters, `M`, `L`, `lb`, `tag`, `1`, `1024`. -/
def decCandIA : List Instr := [iImm r0 0, iImm r2 0, iImm r6 3, iAdd r6 r14 r6, iLd r7 r6]

def decCandIB : List Instr := [iImm r6 4, iAdd r6 r14 r6, iLd r8 r6, iImm r6 5, iAdd r6 r14 r6]

def decCandIC : List Instr := [iLd r10 r6, iImm r6 9, iAdd r6 r14 r6, iLd r3 r6, iImm r11 1]

def decCandID : List Instr := [iImm r12 1024]

/-- The initialisation block of body (b). -/
def decCandInit : List Instr := decCandIA ++ decCandIB ++ decCandIC ++ decCandID

/-- Chunk A: the check index `q = M·s* + b`, its payload word and `q % 1024`. -/
def decCandBA : List Instr :=
  [iMul r6 r7 r4, iAdd r6 r6 r0, iDiv r5 r6 r12, iMod r6 r6 r12, iLd r5 r5]

/-- Chunk B: the shift `off = (q % 1024)·L`, the field `word >>> off`, `2^lb` and `field / 2^lb`. -/
def decCandBB : List Instr := [iMul r6 r6 r8, iShr r5 r5 r6, iShl r1 r11 r10, iDiv r15 r5 r1]

/-- Chunk C: the parity bit `par = (field / 2^lb) &&& 1`, the label `lbl = field % 2^lb`, and `N`. -/
def decCandBC : List Instr := [iBand r15 r15 r11, iMod r5 r5 r1, iImm r6 2, iAdd r6 r14 r6, iLd r6 r6]

/-- Chunk D: the mask `sN = (lbl < N)`, `ps = par·sN`, and the candidate base. -/
def decCandBD : List Instr := [iLt r6 r5 r6, iMul r15 r15 r6, iImm r1 10, iAdd r1 r14 r1, iLd r1 r1]

/-- Chunk E: the unconditional candidate store `mem (candBase+len) := lbl` and the tag base. -/
def decCandBE : List Instr := [iAdd r1 r1 r2, iSt r1 r5, iImm r1 11, iAdd r1 r14 r1, iLd r1 r1]

/-- Chunk F: the tag address, `old`, and the two comparison masks `g1 = old < tag`, `g2 = tag < old`. -/
def decCandBF : List Instr := [iAdd r1 r1 r5, iLd r6 r1, iLt r5 r6 r3, iLt r13 r3 r6, iAdd r5 r5 r13]

/-- Chunk G: `sel = ps·ne`, `len := len + sel` and the tag store value `old + sel·(tag-old)`. -/
def decCandBG : List Instr :=
  [iMul r15 r15 r5, iAdd r2 r2 r15, iSub r13 r3 r6, iMul r13 r13 r15, iAdd r6 r6 r13]

/-- Chunk H: the tag store and the bucket counter. -/
def decCandBH : List Instr := [iSt r1 r6, iAdd r0 r0 r11]

/-- **The body of body (b)**: 36 straight-line instructions, no branch. -/
def decCandBody : List Instr :=
  decCandBA ++ decCandBB ++ decCandBC ++ decCandBD ++ decCandBE ++ decCandBF ++ decCandBG
    ++ decCandBH

/-- **Body (b)** as a statement: the loop over the `M` buckets of the seed in `r4`. -/
def decCandStmt : Stmt := Stmt.loop (Cond.lt r15 r0 r7) (Stmt.code decCandBody)

/-- **Body (b) as a whole statement**: the sixteen initialisation instructions, then the candidate
scan of `_cr23_bodyb4.lean.txt` (`decCandStmt`, the loop itself). -/
def decCandStmtFull : Stmt := Stmt.seq (Stmt.code decCandInit) decCandStmt

end DecCandPay

/-- Init, chunk A: `r4 := 1`, `r5 := mem (frame+10)` (`= candBase`), `r6 := 13`. -/
def decParIA : List Instr := [iImm r4 1, iImm r5 10, iAdd r5 r14 r5, iLd r5 r5, iImm r6 13]

/-- Init, chunk B: `r6 := mem (frame+13)` (`= parBase`), `r7 := mem (frame+12)` (`= mstBase`). -/
def decParIB : List Instr := [iAdd r6 r14 r6, iLd r6 r6, iImm r7 12, iAdd r7 r14 r7, iLd r7 r7]

/-- Init, chunk C: `r8 := mem (frame+15)` (`= mstLen`), `r7 := mstBase + mstLen`, `r1 := len`. -/
def decParIC : List Instr := [iImm r8 15, iAdd r8 r14 r8, iLd r8 r8, iAdd r7 r7 r8, iBor r1 r2 r2]

/-- Init, chunk D: `r0 := 0`. -/
def decParID : List Instr := [iImm r0 0]

/-- Body (d)'s initialisation (16 instructions). -/
def decParInit : List Instr := decParIA ++ decParIB ++ decParIC ++ decParID

/-- Body (d), chunk A: `r9 := candBase + i`, `v := mem r9`, `r9 := parBase + v`, `old := mem r9`,
`r3 := 1 - old`. -/
def decParBA : List Instr := [iAdd r9 r5 r0, iLd r2 r9, iAdd r9 r6 r2, iLd r3 r9, iSub r3 r4 r3]

/-- Body (d), chunk B: `par[v] := 1 - old`, `mst[mstLen+i] := v`, advance both pointers. -/
def decParBB : List Instr := [iSt r9 r3, iSt r7 r2, iAdd r7 r7 r4, iAdd r0 r0 r4]

/-- Body (d) (9 instructions per element). -/
def decParBody : List Instr := decParBA ++ decParBB

/-- **Body (d)** as a statement. -/
def decParStmt : Stmt :=
  Stmt.seq (Stmt.code decParInit) (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decParBody))

/-- Init, chunk A: `r6 := 1`, `r8 := mem (frame+12)` (`= mstBase`). -/
def decEmitEA : List Instr := [iImm r6 1, iImm r5 12, iAdd r5 r14 r5, iLd r8 r5]

/-- Init, chunk B: `r9 := mem (frame+13)` (`= parBase`). -/
def decEmitEB : List Instr := [iImm r5 13, iAdd r5 r14 r5, iLd r9 r5]

/-- Init, chunk C: `r10 := mem (frame+14)` (`= outBase`). -/
def decEmitEC : List Instr := [iImm r5 14, iAdd r5 r14 r5, iLd r10 r5]

/-- Init, chunk D: `r2 := mem (frame+15)` (`= mstLen`). -/
def decEmitED : List Instr := [iImm r5 15, iAdd r5 r14 r5, iLd r2 r5]

/-- Init, chunk E: `r11 := 0`, `r1 := 0`, `r0 := 0`. -/
def decEmitEE : List Instr := [iImm r11 0, iImm r1 0, iImm r0 0]

/-- Body (e)'s initialisation (16 instructions). -/
def decEmitInit : List Instr := decEmitEA ++ decEmitEB ++ decEmitEC ++ decEmitED ++ decEmitEE

/-- Body (e), chunk A: `x := mst[j]`, `sel := par[x]`, `par[x] := 0`. -/
def decEmitBA : List Instr := [iAdd r5 r8 r0, iLd r3 r5, iAdd r5 r9 r3, iLd r4 r5, iSt r5 r11]

/-- Body (e), chunk B: `out[cnt] := x`, `j += 1`, `cnt += sel`. -/
def decEmitBB : List Instr := [iAdd r5 r10 r1, iSt r5 r3, iAdd r0 r0 r6, iAdd r1 r1 r4]

/-- Body (e) (9 instructions per element). -/
def decEmitBody : List Instr := decEmitBA ++ decEmitBB

/-- The postlude: `r0 := outBase`. -/
def decEmitPost : List Instr := [iBor r0 r10 r10]

/-- **Body (e)** as a statement: the initialisation, the walk over the master list, the postlude. -/
def decEmitStmt : Stmt :=
  Stmt.seq (Stmt.code decEmitInit)
    (Stmt.seq (Stmt.loop (Cond.lt r13 r0 r2) (Stmt.code decEmitBody)) (Stmt.code decEmitPost))

/-- The per-round bookkeeping: `w := w / 4`, `tag := tag + 1`, `mstLen := mstLen + len`. -/
def decAdvance : List Instr :=
  [iImm r15 8, iAdd r15 r14 r15, iLd r9 r15, iImm r12 4, iDiv r9 r9 r12, iSt r15 r9,
   iImm r15 9, iAdd r15 r14 r15, iLd r6 r15, iImm r5 1, iAdd r6 r6 r5, iSt r15 r6,
   iImm r15 15, iAdd r15 r14 r15, iLd r6 r15, iAdd r6 r6 r1, iSt r15 r6]

/-- The loop entry: `r9 := mem (slot 7) = w` (the prologue does not touch `r9`, and body (c) uses
`r9` as a mask temporary, so the counter is reloaded from its slot at the entry and again by
`decAdvance` at the end of every round). -/
def decLoadW : List Instr := [iImm r15 8, iAdd r15 r14 r15, iLd r9 r15]

/-- **One round**: seed scan, candidate scan, `r1 := 0`, XOR pass, parity pass, bookkeeping.

The `r1 := 0` between the candidate scan and the XOR pass is load-bearing: `decXorStmt` is
`Stmt.loop (Cond.lt r8 r1 r2) …` and `DecXorInv` requires `s.regs r1 = i` with `i = 0` at entry,
but body (b) leaves `r1 = decTagBase N t + lbl` (`decCandBE`, `decCandBF`, `decCandBH` are its last
register writes).  Without the reset the test is false and body (c) never runs. -/
def decRoundBody : Stmt :=
  Stmt.seq decScanStmt
    (Stmt.seq (Stmt.seq DecCandPay.decCandStmtFull (Stmt.code [iImm r1 0]))
      (Stmt.seq decXorStmt (Stmt.seq decParStmt (Stmt.code decAdvance))))

/-- **The round loop**: `Nat.clog 4 (t + 1)` rounds, tested on `r9 = w`. -/
def decRoundStmt : Stmt :=
  Stmt.loop (Cond.neqz r9) decRoundBody

/-- **The decoder** (without the final `halt`): prologue, round loop, emit pass. -/
def decStmt : Stmt :=
  Stmt.seq (Stmt.code progDecPreC)
    (Stmt.seq (Stmt.code progDecPreS)
      (Stmt.seq (Stmt.code decLoadW) (Stmt.seq decRoundStmt decEmitStmt)))

/-- **The decoder program**: the statement at address `0`, then `halt`. -/
def progDec : Program := Stmt.compile decStmt 0 ++ [iHalt]

end LinearSetReconciliation327.Main


