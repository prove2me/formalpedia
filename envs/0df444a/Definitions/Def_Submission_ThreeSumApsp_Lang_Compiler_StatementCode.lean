-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
-- name    : Submission_ThreeSumApsp_Lang_Compiler_StatementCode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:57:22.774209+00:00
-- url     : https://prove2.me/theorems/4af7df70-aa22-46d8-a900-d53a8221ff79
-- title:
--   Statement Code
-- statement:
--   Supporting definitions from the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
set_option autoImplicit false
section
namespace Light.Compiler
open EndStatement (Instr)
def cARG1 : ℤ := -1
def cARG2 : ℤ := -2
def cRESULT : ℤ := -3
def cONE : ℤ := -5
def cZERO : ℤ := -7
def cNEG : ℤ := -9
def cFP : ℤ := -11
def cADDR : ℤ := -13
def cRET : ℤ := -15
def cRR : ℤ := -17
def cNFP : ℤ := -19
def cD : ℤ := -21
def cT (k : ℕ) : ℤ := -(23 + 4 * (k : ℤ))
def cPool (n : ℕ) : ℤ := -(25 + 4 * (n : ℤ))
def cStack (j : ℕ) : ℤ := -(2 * (j : ℤ))
def mainFrame : ℕ := 4
def _root_.Light.Op.instr : Op → ℤ → ℤ → ℤ → Instr
  | .add => .add
  | .sub => .sub
  | .mul => .mul
def digitsCode (c : ℤ) : List ℕ → List Instr
  | [] => [.sub c c c]
  | d :: L => digitsCode c L ++ [.add c c c] ++ (if d = 0 then [] else [.add c c cONE])
def digitsLen : List ℕ → ℕ
  | [] => 1
  | d :: L => digitsLen L + 1 + (if d = 0 then 0 else 1)
def compileExpr : Expr → ℕ → List Instr
  | .const n, k => digitsCode (cT k) (Nat.digits 2 n)
  | .var x, k => [.sub cADDR cFP (cPool (2 * x)), .load (cT k) cADDR]
  | .op o a b, k => compileExpr a k ++ compileExpr b (k + 1) ++ [o.instr (cT k) (cT k) (cT (k + 1))]
  | .load a, k => compileExpr a k ++ [.load (cT k) (cT k)]
def _root_.Light.Expr.size : Expr → ℕ
  | .const n => digitsLen (Nat.digits 2 n)
  | .var _ => 2
  | .op _ a b => a.size + b.size + 1
  | .load a => a.size + 1
def compileCond : Cond → ℕ → List Instr
  | .lt a b, l =>
    compileExpr a 0 ++ compileExpr b 1 ++ [.sub cD (cT 1) (cT 0), .sub cD cD cONE, .bltz cD l]
  | .eq a b, l =>
    compileExpr a 0 ++ compileExpr b 1 ++
      [.sub cD (cT 0) (cT 1), .bltz cD l, .sub cD cZERO cD, .bltz cD l]
def _root_.Light.Cond.size : Cond → ℕ
  | .lt a b => a.size + b.size + 3
  | .eq a b => a.size + b.size + 4
structure CodeLayout : Type where
  /-- The number of local variables of every frame. -/
  F : ℕ
  /-- The positions of the procedures. -/
  entry : List ℕ
  /-- The position of the dispatcher. -/
  disp : ℕ
def argsCode : List Expr → ℕ → List Instr
  | [], _ => []
  | e :: es, k => compileExpr e k ++ argsCode es (k + 1)
def argsSize : List Expr → ℕ
  | [] => 0
  | e :: es => e.size + argsSize es
def frameInit (F n : ℕ) : List Instr :=
  (List.range F).flatMap fun i =>
    [.sub cADDR cNFP (cPool (2 * i)), .store cADDR (if i < n then cT i else cZERO)]
def newFrame (F n ret : ℕ) : List Instr :=
  [.sub cNFP cFP (cPool (2 * (F + 1)))] ++ frameInit F n ++
    [.add cADDR cNFP (cPool 2), .store cADDR (cPool ret), .add cFP cNFP cZERO]
def callCode (G : CodeLayout) (p : ℕ) (args : List Expr) (ret : ℕ) : List Instr :=
  argsCode args 0 ++ newFrame G.F args.length ret ++ [.bltz cNEG (G.entry.getD p 0)]
def callSize (F : ℕ) (args : List Expr) : ℕ := argsSize args + 1 + 2 * F + 4
def _root_.Light.Stmt.size (F : ℕ) : Stmt → ℕ
  | .skip => 0
  | .set _ e => e.size + 2
  | .store a e => a.size + e.size + 1
  | .seq s t => s.size F + t.size F
  | .ite c s t => c.size + s.size F + 1 + t.size F
  | .while c s => c.size + s.size F + 1
  | .call _ args _ => callSize F args + 2
def compileStmt (G : CodeLayout) : Stmt → ℕ → List Instr
  | .skip, _ => []
  | .set x e, _ => compileExpr e 0 ++ [.sub cADDR cFP (cPool (2 * x)), .store cADDR (cT 0)]
  | .store a e, _ => compileExpr a 0 ++ compileExpr e 1 ++ [.store (cT 0) (cT 1)]
  | .seq s t, pos => compileStmt G s pos ++ compileStmt G t (pos + s.size G.F)
  | .ite c s t, pos =>
    compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ++
      compileStmt G t (pos + c.size + s.size G.F + 1)
  | .while c s, pos =>
    compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [.bltz cNEG pos]
  | .call p args x, pos =>
    callCode G p args (pos + callSize G.F args) ++
      [.sub cADDR cFP (cPool (2 * x)), .store cADDR cRET]
def epilogue (G : CodeLayout) : List Instr :=
  [.load cRET cFP, .add cADDR cFP (cPool 2), .load cRR cADDR,
    .add cFP cFP (cPool (2 * (G.F + 1))), .bltz cNEG G.disp]
def epilogueSize : ℕ := 5
def dispatcher (n : ℕ) : List Instr :=
  (List.range n).flatMap fun j => [.sub cRR cRR cONE, .bltz cRR j]
end Compiler
def Expr.vars : Expr → ℕ
  | .const _ => 0
  | .var x => x + 1
  | .op _ a b => max a.vars b.vars
  | .load a => a.vars
def Expr.height : Expr → ℕ
  | .const _ => 1
  | .var _ => 1
  | .op _ a b => max a.height (b.height + 1)
  | .load a => a.height
def Expr.width (e : Expr) : ℕ := max e.vars e.height
def Cond.width : Cond → ℕ
  | .lt a b => max a.width b.width
  | .eq a b => max a.width b.width
def maxOf {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: l => max (f x) (maxOf f l)
def Stmt.width : Stmt → ℕ
  | .skip => 0
  | .set x e => max (x + 1) e.width
  | .store a e => max a.width e.width
  | .seq s t => max s.width t.width
  | .ite c s t => max c.width (max s.width t.width)
  | .while c s => max c.width s.width
  | .call _ args x => max (x + 1) (max args.length (maxOf Expr.width args))
section width
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}
end width
end Light


