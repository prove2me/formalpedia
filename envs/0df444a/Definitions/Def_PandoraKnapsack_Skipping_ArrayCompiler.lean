-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_ArrayCompiler
-- name    : PandoraKnapsack_Skipping_ArrayCompiler
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:43:53.978871+00:00
-- url     : https://prove2.me/theorems/a2ed2b48-6e05-4dd4-8f57-3aa59037b8ab
-- title:
--   Array operations lowered to costed real pointer-machine code
-- statement:
--   The compiler lowers typed expressions, dynamically addressed tables and structured loops into primitive operations on the mission machine. Temporary locations are separated from source registers. Scratch tables occupy negative addresses while the decoder reads nonnegative output addresses.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, explicit implementation of Algorithm 1 and the polynomial-time clause of Theorem 5.1 under the machine model in Prove2Me theorem 7898d376-37b2-42fd-8375-13696ef594ef. Derived implementation for the dyadic approximate solver.

import Definitions.Def_PandoraKnapsack_Skipping_ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
open StructuredRAM (Cmd Prim)

/-- Registers for permanent naturals, permanent reals, and nested temporary slots. -/
def nr (r : ℕ) := 4*r
def rr (r : ℕ) := 4*r+1
def tr (r : ℕ) := 4*r+2

def ins := Cmd.prim
def block (xs : List Cmd) := xs.foldr Cmd.seq Cmd.skip
def copyReg (d s : ℕ) := ins (.sub d s 3)

def negGap (q addr tmp : ℕ) : Cmd :=
  .seq (ins (.ptrReal tmp q)) (ins (.add tmp addr tmp))
def negSeek (q addr tmp : ℕ) : Cmd :=
  .seq (ins (.pset q 0)) (.seq (negGap q addr tmp) (.whilePos tmp (.seq (ins (.pdec q)) (negGap q addr tmp))))
def readTable (dst addr tmp : ℕ) := Cmd.seq (negSeek 2 addr tmp) (ins (.load dst 2))
def writeTable (addr src tmp : ℕ) := Cmd.seq (negSeek 2 addr tmp) (ins (.store 2 src))

noncomputable def N.lower (d : ℕ) : N → Cmd
  | .lit c => ins (.const (tr d) c)
  | .var i => copyReg (tr d) (nr i)
  | .add a b => block [a.lower d,b.lower (d+1),ins (.add (tr d) (tr d) (tr (d+1)))]
  | .mul a b => block [a.lower d,b.lower (d+1),ins (.mul (tr d) (tr d) (tr (d+1)))]

noncomputable def tableAddress (d : ℕ) (t : Fin 16) (a : N) := block [
  a.lower d,ins (.const (tr (d+1)) 16),ins (.mul (tr d) (tr d) (tr (d+1))),
  ins (.const (tr (d+1)) (t.val+1 : ℕ)),ins (.add (tr d) (tr d) (tr (d+1)))]

noncomputable def R.lower (d : ℕ) : R → Cmd
  | .lit c => ins (.const (tr d) c)
  | .var i => copyReg (tr d) (rr i)
  | .nat a => a.lower d
  | .get t i => .seq (tableAddress d t i) (readTable (tr d) (tr d) (tr (d+1)))
  | .add a b => block [a.lower d,b.lower (d+1),ins (.add (tr d) (tr d) (tr (d+1)))]
  | .sub a b => block [a.lower d,b.lower (d+1),ins (.sub (tr d) (tr d) (tr (d+1)))]
  | .mul a b => block [a.lower d,b.lower (d+1),ins (.mul (tr d) (tr d) (tr (d+1)))]
  | .div a b => block [a.lower d,b.lower (d+1),ins (.div (tr d) (tr d) (tr (d+1)))]

noncomputable def setIndex (d q : ℕ) (i : N) : Cmd := .seq (i.lower d) (StructuredRAM.seek q (tr d) (tr (d+1)))

noncomputable def C.lower (d : ℕ) : C → Cmd
  | .skip => .skip
  | .seq a b => .seq (a.lower d) (b.lower d)
  | .letN r a => .seq (a.lower d) (copyReg (nr r) (tr d))
  | .letR r a => .seq (a.lower d) (copyReg (rr r) (tr d))
  | .put t i e => block [tableAddress d t i, e.lower (d+1), writeTable (tr d) (tr (d+1)) (tr (d+2))]
  | .out i e => block [i.lower d,e.lower (d+1),StructuredRAM.writeAt (tr d) (tr (d+1)) 2 (tr (d+2))]
  | .itePos e a b => .seq (e.lower d) (.itePos (tr d) (a.lower d) (b.lower d))
  | .whilePos e a => .seq (e.lower d) (.whilePos (tr d) (.seq (a.lower d) (e.lower d)))
  | .forN idx bound body => block [
      bound.lower d,ins (.const (tr (d+1)) 0),ins (.sub (tr (d+2)) (tr d) (tr (d+1))),
      .whilePos (tr (d+2)) (block [copyReg (nr idx) (tr (d+1)),body.lower (d+3),
        ins (.add (tr (d+1)) (tr (d+1)) 7),ins (.sub (tr (d+2)) (tr d) (tr (d+1)))]),
      copyReg (nr idx) (tr (d+1))]
  | .value dst i => .seq (setIndex d 0 i) (ins (.value (rr dst) 0))
  | .cost dst i j => block [setIndex d 0 i,setIndex d 1 j,ins (.cost (rr dst) 0 1)]
  | .cdf dst i j e => block [setIndex d 0 i,setIndex d 1 j,e.lower d,ins (.cdf (rr dst) 0 1 (tr d))]
  | .truncMean dst i j e => block [setIndex d 0 i,setIndex d 1 j,e.lower d,ins (.truncMean (rr dst) 0 1 (tr d))]
  | .uniform dst => ins (.uniform (rr dst))

/-- Initialize the lone real constant one, read n,m,T and leave input memory intact. -/
def prologue : Cmd := block [ins (.const 7 1),ins (.pset 0 0),ins (.load (nr 0) 0),
    ins (.pinc 0),ins (.load (nr 1) 0),ins (.pinc 0),ins (.load (rr 0) 0)]

noncomputable def compile (c : C) := StructuredRAM.program (.seq prologue (c.lower 0))

end PandoraKnapsack.Skipping.ArrayRAM


