-- Prove2me | Definitions.Def_StableMSR_SingleCircuitRAM
-- name    : StableMSR_SingleCircuitRAM
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T00:05:27.729048+00:00
-- url     : https://prove2.me/theorems/026687cf-e1f5-448d-9f41-4a588ebfda95
-- title:
--   Dense circuit input and physical RAM record emission
-- statement:
--   A dense integer instruction table with one mask per source gate is rewritten into the mission’s separator record bands and membership storage. The physical board has three records per gate.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleSeparatorCircuit
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.WindowPorts StableMSR.Recovery.SingleCircuit
namespace StableMSR.Recovery.SingleRAM
def opCode : Gate→ℤ | .stop=> -1 | .atom _=>0 | .both _ _=>1 | .either _ _=>2
def leftID : Gate→ℕ | .both l _ | .either l _=>l | _=>0
def rightID : Gate→ℕ | .both _ r | .either _ r=>r | _=>0
def inputTag (x : World) (p : ℕ) :=center x (1+p) 0
def inputLeft (x : World) (p : ℕ) :=witness x (1+p) 0
def inputRight (x : World) (p : ℕ) :=center x (1+rawSize x+p) 0
def inputRoot (x : World) (q : ℕ) :=center x (1+2*rawSize x+q) 0
def inputBit (x : World) (p i : ℕ) :=x.mem (addr x.k (1+5*rawSize x) 0+p*x.n+i)
def Input (x : World) (g : Gates) (roots : ℕ→ℕ) :=rawSize x=g.size ∧
  (∀p< g.size,inputTag x p=opCode (gateAt g p) ∧ inputLeft x p=(leftID (gateAt g p):ℤ) ∧ inputRight x p=(rightID (gateAt g p):ℤ)) ∧
  (∀q<3*g.size,inputRoot x q=(roots q:ℤ)) ∧ ∀p< g.size,∀i : Point x.n,0< inputBit x p i.val ↔ i.val∈tinyMask (gateAt g p)
noncomputable def quotient (x : World) (a : ℕ) :=∑v ∈ Finset.range x.rows,if 3*v≤ a ∧ a<3*(v+1) then v else 0
noncomputable def slot (x : World) (a : ℕ) :=subR x a (3*quotient x a)
def tagFor (t : ℤ) (j : ℕ) : ℤ := if t=0 then (if j=0 then 0 else -1)
  else if t=1 then (if j=0 then 1 else if j=1 then 2 else -1)
  else if t=2 then (if j=0 ∨ j=1 then 1 else if j=2 then 2 else -1) else -1
def childFor (t l r : ℤ) (j : ℕ) := if t=1 ∨ t=2 then (if j=0 then l else if j=1 then r else 0) else 0
noncomputable def packCell (x : World) (r j : ℕ) (s : Bool) : ℤ :=
  let m:=3*rawSize x
  if r=0 then (if s then x.mem 1 else (m:ℤ))
  else if r<1+m then
    let q:=subR x r 1;let p:=quotient x q
    if s then (p:ℤ) else tagFor (inputTag x p) (slot x q)
  else if r<1+2*m then
    let q:=subR x r (1+m);let p:=quotient x q
    childFor (inputTag x p) (inputLeft x p) (inputRight x p) (slot x q)
  else if r<1+3*m then 0
  else if r<1+4*m then inputRoot x (subR x r (1+3*m))
  else
    let off:=2*(subR x r (1+4*m)*x.k+j)+(if s then 1 else 0)
    inputBit x (quotient x (divN x off)) (remN x off)
def denotes (x : World) (g : Gates) (roots : ℕ→ℕ) :=
  room x ∧ rawSize x=3*g.size ∧ ∀q<3*g.size,
    (board x).tag q=(boardOf g roots).tag q ∧ (board x).dest q=(boardOf g roots).dest q ∧
    (board x).child q=(boardOf g roots).child q ∧ (board x).root q=roots q ∧ WindowMasks.block x q=maskAt x.n g q
end StableMSR.Recovery.SingleRAM


