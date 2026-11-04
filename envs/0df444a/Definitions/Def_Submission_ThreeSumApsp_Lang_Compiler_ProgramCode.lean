-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
-- name    : Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:11:36.726205+00:00
-- url     : https://prove2.me/theorems/a850158d-a9f2-4946-b328-5eae7725de4c
-- title:
--   Program Code
-- statement:
--   Definitions and structural lemmas for Program Code, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
def frameSize (P : Program) : ℕ := max 3 (maxOf Stmt.width P)
def _root_.Light.mainStmt (p0 : ℕ) : Stmt := .call p0 [.var 1, .var 2] 0
def tailCode (dec : Bool) (pos : ℕ) : List Instr :=
  .add cRESULT (cStack mainFrame) cZERO ::
    (if dec then [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept]
      else [.accept])
def mainPos : ℕ := 4
def tailPos (F : ℕ) : ℕ := mainPos + (mainStmt 0).size F
def firstBody (F : ℕ) (dec : Bool) : ℕ := tailPos F + (tailCode dec 0).length
def entries (F : ℕ) : List Stmt → ℕ → List ℕ
  | [], _ => []
  | b :: bs, pos => pos :: entries F bs (pos + b.size F + epilogueSize)
def endPos (F : ℕ) : List Stmt → ℕ → ℕ
  | [], pos => pos
  | b :: bs, pos => endPos F bs (pos + b.size F + epilogueSize)
def dispPos (P : Program) (dec : Bool) : ℕ := endPos (frameSize P) P (firstBody (frameSize P) dec)
def codeLayout (P : Program) (dec : Bool) : CodeLayout :=
  ⟨frameSize P, entries (frameSize P) P (firstBody (frameSize P) dec), dispPos P dec⟩
def bodiesCode (G : CodeLayout) : List Stmt → ℕ → List Instr
  | [], _ => []
  | b :: bs, pos =>
    (compileStmt G b pos ++ epilogue G) ++ bodiesCode G bs (pos + b.size G.F + epilogueSize)
def headStraight : List Instr := [.one cONE, .sub cZERO cONE cONE, .sub cNEG cZERO cONE]
def poolCode (N : ℕ) : List Instr :=
  .sub (cPool 0) cONE cONE :: (List.range N).map fun n => .add (cPool (n + 1)) (cPool n) cONE
def zeroCode (F : ℕ) : List Instr :=
  (List.range F).map fun x => .sub (cStack (mainFrame + x)) cONE cONE
def frameCode (F : ℕ) : List Instr :=
  .sub cFP cZERO (cPool (2 * mainFrame)) ::
    (zeroCode F ++
      [.add (cStack (mainFrame + 1)) cARG1 cZERO, .add (cStack (mainFrame + 2)) cARG2 cZERO])
def startStraight (F N : ℕ) : List Instr := poolCode N ++ frameCode F
def headCode (P : Program) (dec : Bool) : List Instr :=
  headStraight ++ [.bltz cNEG (3 * dispPos P dec)]
def mainCode (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  compileStmt (codeLayout P dec) (mainStmt p0) mainPos ++ tailCode dec (tailPos (frameSize P))
def startCode (P : Program) (dec : Bool) : List Instr :=
  startStraight (frameSize P) (dispPos P dec) ++ [.bltz cNEG mainPos]
def _root_.Light.compileProgram (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  headCode P dec ++ mainCode P p0 dec ++ bodiesCode (codeLayout P dec) P
      (firstBody (frameSize P) dec) ++
    dispatcher (dispPos P dec) ++ startCode P dec
section parts
variable (P : Program) (p0 : ℕ) (dec : Bool)
end parts
end Light.Compiler


