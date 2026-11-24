-- Prove2me | Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
-- name    : StableMSR_UnfilteredSeparatorCandidates
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T23:33:52.7658+00:00
-- url     : https://prove2.me/theorems/1c2a0554-26b4-4f3c-b0af-1243bf9691fb
-- title:
--   Unfiltered separator candidates, tight keys, and provisional output
-- statement:
--   For every tight separator state, list all pivots and menu labels in the prescribed order. Each candidate supplies its literal masks, keys of its child components, and its local consistency test. Row delimiters record the tight key. The finite instruction list is independent of the results of previous candidates. Its evaluation retains a candidate precisely when the test succeeds and every child key has been installed. An installed failing handle is distinct from a missing key.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Ordered finite implementation of its separator search.

import Definitions.Def_StableMSR_RegionalProductionTable
namespace StableMSR.Recovery.NativeWriter.Production.Candidates
open SingleCircuit TightLanguage Compiler OracleQueries WindowCSP
set_option autoImplicit false

/-- A candidate tape lists literal masks and requests for tight child keys,
then the local consistency bit. Sealing a row installs its latest alternative. -/
inductive Instr where
  | lit (points : List ℕ)
  | need (key : ℕ)
  | close (localTest : Bool)
  | seal (key : ℕ)
  | finish
  deriving DecidableEq, Repr

def children (d:Instance) (c:List ℕ) (v:ℕ) (row:Assignment) : List Key :=
  (parts d (c.erase v)).map fun t=>(t,restricted (rimOf d t) row)

def trial (enc:Key→ℕ) (d:Instance) (c:List ℕ) (a:Assignment) (v x:ℕ) : List Instr :=
  let row:=(v,x)::a
  (d.owned v x).map Instr.lit ++ (children d c v row).map (fun k=>.need (enc k)) ++ [.close (localOK d row)]

def entry (enc:Key→ℕ) (d:Instance) (c:List ℕ) (a:Assignment) : List Instr :=
  c.flatMap (fun v=>(d.menu v).flatMap (trial enc d c a v)) ++ [.seal (enc (c,a))]

def visitTape (enc:Key→ℕ) (d:Instance) (k:ℕ) (s c:List ℕ) : List Instr :=
  if c.length==k+1 && rimOf d c==s then (assignments d s).flatMap (entry enc d c) else []

def rowTape (enc:Key→ℕ) (d:Instance) (w:ℕ) : List Instr :=
  let vs:=vertices d
  (List.range d.n).flatMap fun k=>(cuts vs (min w d.n)).flatMap fun s=>
    (keysFor d vs s).flatMap (visitTape enc d k s)

def tape (enc:Key→ℕ) (d:Instance) (w:ℕ) : List Instr :=
  rowTape enc d w ++ (parts d (vertices d)).map (fun c=>.need (enc (c,[]))) ++ [.finish]

structure Work where
  done : List Event
  stage : List Event
  ok : Bool
  acc : ℕ
  exit : ℕ
  dict : ℕ→Option ℕ

def start : Work := ⟨[],[],true,0,0,fun _=>none⟩
def buffer (s:Work) := s.done++s.stage
def step (s:Work) : Instr→Work
  | .lit m=>{s with stage:=s.stage++[.mask m]}
  | .need k=>
    let f:=s.dict k
    {s with stage:=s.stage++[.child (f.getD 0)],ok:=s.ok && f.isSome}
  | .close good=>
    if s.ok && good then
      let out:=buffer s++[.join s.acc]
      {s with done:=out,stage:=[],ok:=true,acc:=out.length}
    else {s with stage:=[],ok:=true}
  | .seal k=>{s with dict:=Function.update s.dict k (some s.acc),acc:=0}
  | .finish=>
    if s.ok then
      let out:=buffer s++[.save]
      {s with done:=out,stage:=[],ok:=true,exit:=out.length}
    else {s with stage:=[],ok:=true,exit:=0}

def eval (xs:List Instr) : Script :=
  let t:=xs.foldl step start
  ⟨t.done,(t.exit:ℤ)⟩

def inputCell (a i:ℕ) := cell 5 (8*i+a)
def Instr.tag : Instr→ℤ | .lit _=>0 | .need _=>1 | .close _=>2 | .seal _=>3 | .finish=>4
def Instr.arg : Instr→ℤ | .need k | .seal k=>(k:ℤ) | .close b=>if b then 1 else 0 | _=>0

def Input (n:ℕ) (m:ℤ→ℤ) (xs:List Instr) :=
  m (inputCell 0 0)=(xs.length:ℤ) ∧ ∀j (hj:j<xs.length),let e:=xs[j]
    m (inputCell 1 j)=e.tag ∧ m (inputCell 2 j)=e.arg ∧
    ∀mask,e=.lit mask → ∀i<n,m (inputCell 3 (j*n+i))=(if mask.contains i then 1 else 0)

end StableMSR.Recovery.NativeWriter.Production.Candidates


