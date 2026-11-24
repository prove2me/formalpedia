-- Prove2me | Definitions.Def_RHX_RunSplit
-- name    : RHX_RunSplit
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:47:45.977601+00:00
-- url     : https://prove2.me/theorems/2c0fe05d-08f0-4f6d-ace4-5d5ff51eea61
-- title:
--   Piece, box and cell checkers from a given evaluator state
-- statement:
--   The framework checkers `Arb4.pieceOK`, `Arb4.boxOK` and `Arb4.cellOK` with their long evaluator run replaced by a given state $S$: `RHX.pieceOKs`, `RHX.boxOKs`, `RHX.cellOKs`. The bodies are copied from the framework checkers. The theorems `RHX.pieceOK_of_run`, `RHX.boxOK_of_run` and `RHX.cellOK_of_run` recover the framework checkers when $S$ equals the result of the run.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
import Definitions.Def_RHX_RunChain
/-! The piece, box and cell checkers with the long evaluator run replaced by a given state `S`
    (bodies copied from `Arb4.pieceOK`, `Arb4.boxOK`, `Arb4.cellOK`); `S` is tied to the run by
    checkpointed equalities. -/

namespace RHX
open Arb4 Arb4.Q

noncomputable def pieceOKs (tn tq N : ℕ) (L : Q) (P : PieceD) (S : ArbEcon.Off.StO) : Bool :=
  let c := ArbEcon.OrderK.cfg64 tn tq
  let s1 := S
  let sN := ArbEcon.Off.runO c P.oc 1 s1
  Nat.ble 2 N && Nat.ble 1 P.q && Nat.ble 1 P.rd && Nat.ble 1 P.FD &&
    H1000Oct.checkOct c P.oc 6 N 5 s1.acc sN.acc P.rn P.rd P.FN P.FD P.kk &&
    geomOK tn tq L sN.lhi P && gOK N P && remOK tn tq N P && budgetOK N L P

noncomputable def boxOKs (tn tq N : ℕ) (P : PieceD) (D : ℕ) (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (qlo qhi : Q) (S : ArbEcon.Off.StO) : Bool :=
  let c := ArbEcon.OrderK.cfg64 tn tq
  let s1 := S
  let sN := ArbEcon.Off.runO c P.oc 1 s1
  Nat.ble 2 N && Nat.ble 1 P.q && Nat.ble 1 D && !s1.acc.isEmpty && !sN.acc.isEmpty &&
    ArbEcon.Off.checkG c P.oc 6 N (s1.acc.headD ArbEcon.Off.Acc.zero)
      (sN.acc.headD ArbEcon.Off.Acc.zero) D reLo reHi imLo imHi Qp Rn Rd &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reLo D) (frac imLo D) qlo qhi &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reLo D) (frac imHi D) qlo qhi &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reHi D) (frac imLo D) qlo qhi &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reHi D) (frac imHi D) qlo qhi

noncomputable def cellOKs (S : SlabD) (j : ℕ) (St : ArbEcon.Off.StO) : Bool :=
  let C := S.cell j
  let c := ArbEcon.OrderK.cfg64 C.tn S.tq
  let s1 := St
  let sN := ArbEcon.Off.runO c C.oc 1 s1
  Nat.ble 2 S.N && Nat.ble 1 C.q && Nat.ble 1 C.rd && Nat.ble C.b C.a &&
    ArbEcon.Off.checkCell c C.oc 6 S.N 5 s1.acc sN.acc C.rn C.rd S.FN S.FD &&
    le (frac (C.rn : ℤ) C.rd) S.R && le (ofNat sN.lhi) (mul S.L (ofNat (2 ^ 64))) &&
    le S.lo (tQ C.tn S.tq) &&
    le (add (npow (add C.σQ (ofNat 11)) 2) (npow (tQ C.tn S.tq) 2)) (npow S.U 2) &&
    le (qabs (sub (S.xs j) C.σQ)) C.w && le (qabs (sub (S.xs (j + 1)) C.σQ)) C.w &&
    le (qabs (sub S.lo (tQ C.tn S.tq))) C.hh && le (qabs (sub S.hi (tQ C.tn S.tq))) C.hh &&
    le (add (npow C.w 2) (npow C.hh 2)) (npow (frac (C.rn : ℤ) C.rd) 2)

end RHX

def RHX_RunSplit : Nat := 0


