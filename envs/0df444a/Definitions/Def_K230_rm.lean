-- Prove2me | Definitions.Def_K230_rm
-- name    : K230_rm
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T21:13:42.6046+00:00
-- url     : https://prove2.me/theorems/91943213-c02c-4e23-a26b-1f140f48ea74
-- title:
--   K230: register machine semantics
-- statement:
--   The register machine implemented by the K230 Turing machine: a program is a shared binary tree of cons cells whose leaves are register operations, break/continue, or halt. The path semantics `rmStep`/`rmRun` walks the tree with an instruction-pointer bit list; `rmHalts p c` means some run reaches the halt leaf. Ports the path-semantics portion of `RM.v`.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/tm/RM.v

namespace K230
inductive Edge where | ENode (n : Nat) | EInc (r : Nat) | EDecnz (r : Nat) | EBreak (k : Nat) | EContinue (k : Nat) | EHalt
structure Prog where
  nodes : Nat → Edge × Edge
  root : Nat
  nnodes : Nat
def Regs := Nat → Nat
def upd (R : Regs) (r v : Nat) : Regs := fun i => if i = r then v else R i
def regs0 : Regs := fun _ => 0
def nthBool : List Bool → Nat → Bool | [], _ => false | b :: _, 0 => b | _ :: l, n + 1 => nthBool l n
def walk (p : Prog) (fuel : Nat) (n : Nat) (P : List Bool) (i : Nat) : Option (Edge × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let (a, b) := p.nodes n
      let e := if nthBool P i = true then b else a
      match e with | .ENode n' => walk p fuel n' P (i + 1) | _ => some (e, i + 1)
def incRev : List Bool → List Bool | [] => [] | false :: l => true :: l | true :: l => false :: incRev l
def incPath (P : List Bool) : List Bool := (incRev P.reverse).reverse
def stripRev (b : Bool) : Nat → List Bool → List Bool
  | 0, l => l
  | k + 1, l => match l with | [] => [] | x :: l => if x = b then stripRev b k l else stripRev b (k + 1) l
def stripPath (b : Bool) (k : Nat) (P : List Bool) : List Bool := (stripRev b k P.reverse).reverse
def brk (k : Nat) (P : List Bool) : List Bool := incPath (stripPath false k P)
def cont (k : Nat) (P : List Bool) : List Bool := stripPath true k P
def Conf := List Bool × Regs
def rmStep (p : Prog) (c : Conf) : Option Conf :=
  let (P, R) := c
  match walk p (p.nnodes + 1) p.root P 0 with
  | none => none
  | some (e, d) =>
      let P := (P ++ List.replicate d false).take d
      match e with
      | .ENode _ => none
      | .EInc r => some (incPath P, upd R r (R r + 1))
      | .EDecnz r => match R r with | 0 => some (brk 1 P, R) | v + 1 => some (incPath P, upd R r v)
      | .EBreak k => some (brk k P, R)
      | .EContinue k => some (cont k P, R)
      | .EHalt => none
def rmRun (p : Prog) (fuel : Nat) (c : Conf) : Option Conf :=
  match fuel with | 0 => some c | fuel + 1 => match rmStep p c with | none => none | some c' => rmRun p fuel c'
def atHalt (p : Prog) (c : Conf) : Prop := ∃ d, walk p (p.nnodes + 1) p.root c.1 0 = some (.EHalt, d)
def rmHalts (p : Prog) (c : Conf) : Prop := ∃ n c', rmRun p n c = some c' ∧ atHalt p c'
end K230


