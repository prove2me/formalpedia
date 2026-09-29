-- Prove2me | Definitions.Def_r03_defs_c874916438_v7_CoreBranch
-- name    : r03_defs_c874916438_v7_CoreBranch
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:09.39201+00:00
-- url     : https://prove2.me/theorems/34554a7f-ca79-4d15-8c4e-a54f2d035166
-- title:
--   R03 candidate definition: r03 defs c874916438 v7 CoreBranch
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_c874916438_v7_CoreBranch.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Mathlib.Data.Fin.VecNotation

/- Candidate-only fixed 9-vertex relative-boundary core. Not the root graph.
   The 11 coordinates follow v7_core_branches.observation.json edge order.
   Codes on external ports 4,5,6,7,8 are 0,0,1,2,0 (incoming convention).
   Independent graph interpretation and admission remain separate. -/
namespace R03CoreBranchV7
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 100000

def state (a b c : Fin 3) : Fin 11 → Fin 3 :=
  ![a+b+c, 2+2*b+2*c, 2+2*a, 2+2*b+2*c, 2+b, c, a, 1+2*b, 2+2*c, b, c]

def Core (x : Fin 11 → Fin 3) : Prop :=
  x 0+x 1+x 2=1 ∧ x 3+x 4+x 5=1 ∧ x 0+x 3+2*x 6=2 ∧
  x 1+2*x 7+2*x 8=2 ∧ x 2+x 6=2 ∧ x 4+2*x 9=2 ∧
  x 7+x 9=1 ∧ x 5+2*x 10=0 ∧ x 8+x 10=2

private theorem add2 : ∀ a b : Fin 3, a+b=2 → a=2+2*b := by decide +kernel
private theorem add1 : ∀ a b : Fin 3, a+b=1 → a=1+2*b := by decide +kernel
private theorem signed2 : ∀ a b : Fin 3, a+2*b=2 → a=2+b := by decide +kernel
private theorem signed0 : ∀ a b : Fin 3, a+2*b=0 → a=b := by decide +kernel
private theorem twosigned : ∀ a b c : Fin 3, a+2*b+2*c=2 → a=2+b+c := by decide +kernel
private theorem three1 : ∀ a b c : Fin 3, a+b+c=1 → a=1+2*b+2*c := by decide +kernel
private theorem norm : ∀ a b c : Fin 3,
    (2+(1+2*b)+(2+2*c)=2+2*b+2*c) ∧
    (1+2*(2+b)+2*c=2+2*b+2*c) ∧
    (1+2*(2+2*b+2*c)+2*(2+2*a)=a+b+c) := by decide +kernel
private theorem cases11 : ∀ i : Fin 11,
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 := by decide +kernel

def codes (x : Fin 11 → Fin 3) : Fin 9 → Fin 3 → Fin 3 :=
  ![![2*x 0,2*x 1,2*x 2], ![2*x 3,2*x 4,2*x 5], ![x 0,x 3,2*x 6],
    ![x 1,2*x 7,2*x 8], ![x 2,x 6,0], ![x 4,2*x 9,0],
    ![x 7,x 9,1], ![x 5,2*x 10,2], ![x 8,x 10,0]]
def ins (r : Fin 3 → Fin 3) : Nat :=
  (if r 0=1 then 1 else 0)+(if r 1=1 then 1 else 0)+(if r 2=1 then 1 else 0)
def outs (r : Fin 3 → Fin 3) : Nat :=
  (if r 0=2 then 1 else 0)+(if r 1=2 then 1 else 0)+(if r 2=2 then 1 else 0)
def Good (x : Fin 11 → Fin 3) : Prop :=
  ∀ v : Fin 9, (ins (codes x v)=2 ∧ outs (codes x v)=0) ∨
    (ins (codes x v)=0 ∧ outs (codes x v)=1)
def BadAt (x : Fin 11 → Fin 3) (v : Fin 9) : Prop :=
  ins (codes x v)=1 ∧ outs (codes x v)=2

end R03CoreBranchV7


