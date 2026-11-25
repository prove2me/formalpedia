-- Prove2me | Definitions.Def_DetDLP_S8M_StepBaseDefs
-- name    : DetDLP_S8M_StepBaseDefs
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:39:28.05586+00:00
-- url     : https://prove2.me/theorems/3306bb7b-c113-4912-a364-adafbf23824b
-- title:
--   Natural-address step and base definitions
-- statement:
--   Natural-number register encodings for the EC addition step, accumulator fold, and base packet network.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_AtomMapNat
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.StepBaseNat
open S8H0 RegisterMap S8H.MakeCombinators EffCombinators AtomMapNat Groundwork S8N.ECAddRoutes

theorem add_size (d e : ℕ) : (addShape d e).size = 253*d+30*e+97 := by
  simp only [addShape,ECMapRows.slot,run,mul,triple,GateRoutes.auxShape,Shape.size]; omega

def hashN (d e pin z aux : ℕ) (a x b : ℕ → ℕ) : NC :=
  let w := fun o n => wd o n pin; let r := z+3*d+1; let q := r+3*d+1
  let p := q+d; let t := p+2*d+e
  genHashN d e (p+2*d) (t+2*d) pin a x b (w z d) (w r d) (w q d) (w p (2*d)) (w t (2*d))
    (w (aux+2*d) (d+1)) (fun _ => t+2*d+e) (aux+·) (aux+3*d+1+·) (aux+4*d+2+·)

def mapOff (m d e i : ℕ) := 2*m*(ECAtomSlot.slotShape d e).size+i*(ECMapRows.mapShape d e).size
def addOff (m d e i : ℕ) := mapOff m d e (2*m)+i*(addShape d e).size
def tags (g : ℕ) : ℕ × ℕ × ℕ :=
  args 0 0 0 0 0 1 2 3 4 5 (fun i => 6+i.val) (fun i => 10+i.val) (Fin.ofNat 15 g)
def operand (d e pin u v o : ℕ) (k j : ℕ) :=
  let tr := 3*d+1; let a := fun h => o+1+h*tr; let l := a 4+2
  if k=0 then pin else wd (if k=1 then u+1 else if k=2 then u+1+tr else if k=3 then v+1 else if k=4 then v+1+tr else if k=5 then l else if k<10 then a (k-6) else l+d+(k-10)*(16*d+2*e+6)) d pin j
def tile (d e pin u v o : ℕ) : NC :=
  let tr := 3*d+1; let a := fun k => o+1+k*tr; let f := a 4; let l := f+2
  let z := fun k => l+d+k*(16*d+2*e+6)
  let op := operand d e pin u v o
  let h := fun g => hashN d e pin (z g) (z g+11*d+2*e+3) (op (tags g).1) (op (tags g).2.1) (op (tags g).2.2)
  let rng := rangeN d pin; let inv := fun k => rowN d 4 fun j t => if t=0 then f+k else if t=1 then z (2*k)+j else if t=2 then a (2+k)+j else z (2*k+1)+j
  let head := fun t => if t=0 then u else if t=1 then v else if t=2 then f else f+1
  let sel := fun k g => rowN d 8 fun j t => if t<4 then head t else if t=4 then u+1+k*tr+j else if t=5 then v+1+k*tr+j else if t=6 then z g+j else a k+j
  catN (manyN 3 fun k => rng (a k)) <| catN (manyN 14 fun k => catN (rng (z k)) (rng (z k+tr))) <| catN (manyN 14 h) <|
    catN (inv 0) <| catN (inv 1) <| catN (rowN d 7 fun j t => if t<4 then head t else if t=4 then z 5+j else if t=5 then z 8+j else l+j) <|
    catN (rowN 1 5 fun _ t => if t<4 then head t else o) (catN (sel 0 11) (sel 1 14))

def stepN (m d e i : ℕ) : NC := tile d e (Routes.bank m d e).size
  (if i=0 then mapOff m d e 0 else addOff m d e (i-1)) (mapOff m d e (i+1)) (addOff m d e i)
def foldN (m d e : ℕ) : NC :=
  let n := 2*m-1; let o := if n=0 then mapOff m d e 0 else addOff m d e (n-1); let p := (Routes.bank m d e).size
  let eqr := fun len off => rowN len 2 fun j k => if k=0 then off+j else p
  catN (eqr 1 o) (catN (eqr d (o+1)) (catN (eqr d (o+1+(3*d+1))) (repeated n (stepN m d e))))
def digit (m d e b j : ℕ) :=
  let p := (Routes.bank m d e).size; let n := 2*b+1; let h := j/n; let t := j%n
  let o := (h/2 + (h%2)*m)*(ECAtomSlot.slotShape d e).size
  if h<2*m then if t=0 then o else if t<b+1 then wd (o+1) d p (b-t) else wd (o+1+(3*d+1)) d p (2*b-t) else p
def baseN (m d e b l : ℕ) : NC :=
  let p := (Routes.bank m d e).size
  catN (anchorN (p+1) id) <| catN (anchorN 1 fun _ => p) <| catN (repeated (2*m) (atomN m d e)) <|
    catN (repeated (2*m) (mapN m d e)) (catN (foldN m d e) (rowN l 1 fun j _ => digit m d e b j))
end DetDLP.S8M.StepBaseNat


