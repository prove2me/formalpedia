-- Prove2me | Definitions.Def_StableMSR_TightComponentTrace
-- name    : StableMSR_TightComponentTrace
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T20:18:20.996215+00:00
-- url     : https://prove2.me/theorems/9c41075b-3bef-4e74-93d9-6db381bd05cc
-- title:
--   Ordered pivot and label words of the tight regional table
-- statement:
--   Let a finite array instance specify which vertices are active, the graph edges, the ordered label menu at each vertex, and the local compatibility tests. The tight table stores a language of words over pairs $(v,c)$ for each ordered component and boundary assignment. For each legal pivot and code, it concatenates the words of all child components in their enumerated order and prefixes the pair $(v,c)$. Each row takes the union over its legal alternatives. An unavailable child discards that alternative. At the root the table concatenates component words, with the empty concatenation giving the empty word. The state interpreter also permits the very same traversal to build a circuit.
-- source:
--   https://prove2.me/theorems/99dbdc83-616a-4376-a6ef-50377501acbd . The executable recurrence is SingleCircuit.compileRegion in Definitions.Def_StableMSR_SingleSeparatorCircuit, lines 64–87. The ordered-word interpretation records the pivot and code in each successful alternative before the child words.

import Definitions.Def_StableMSR_SingleSeparatorCircuit
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
def value (a : Assignment) (v : ℕ) := ((a.find? fun z=>z.1==v).map Prod.snd).getD 0
def restricted (s : List ℕ) (a : Assignment) : Assignment := s.map fun v=>(v,value a v)
def assignments (d : Instance) : List ℕ→List Assignment
  | []=>[[]]
  | v::vs=>(d.menu v).flatMap fun x=>(assignments d vs).map ((v,x)::·)
def cuts : List ℕ→ℕ→List (List ℕ)
  | [],_=>[[]]
  | _::_,0=>[[]]
  | v::vs,w+1=>cuts vs (w+1) ++ (cuts vs w).map (v::·)
def vertices (d : Instance) := (List.range d.n).filter d.active
def pieceAt (d : Instance) (allowed : List ℕ) (v : ℕ) :=
  (List.range d.n).foldl (fun seen _=>allowed.filter fun u=>seen.contains u || seen.any (fun z=>d.edge z u)) [v]
def parts (d : Instance) (allowed : List ℕ) := allowed.filterMap fun v=>
  let c:=pieceAt d allowed v
  if c.head?==some v then some c else none
def rimOf (d : Instance) (c : List ℕ) := (vertices d).filter fun v=>
  !c.contains v && c.any (fun u=>d.edge u v)
def localOK (d : Instance) (a : Assignment) := a.all fun z=>a.all fun t=>
  !(d.edge z.1 t.1) || d.test z.1 t.1 z.2 t.2

/-- The numeric dynamic program stores one value per ordered tight key. -/
abbrev Table (V:Type) := List (Key×V)

def lookup {V:Type} (tab:Table V) (c:List ℕ) (a:Assignment) : Option V :=
  (tab.find? (fun z=>z.1==(c,a))).map Prod.snd

structure Algebra (S V:Type) where
  initial : S
  fail : V
  alternative : S→V→ℕ→ℕ→List V→S×V
  finish : S→List V→S×V

def keysFor (d:Instance) (vs:List ℕ) (s:List ℕ) :=
  parts d (vs.filter (fun v=> !s.contains v))

def refs {V:Type} (d:Instance) (tab:Table V) (c:List ℕ) (v:ℕ) (a:Assignment) :=
  (parts d (c.erase v)).mapM (m:=Option) (fun t=>lookup tab t (restricted (rimOf d t) a))

def offer {S V:Type} (E:Algebra S V) (d:Instance) (tab:Table V) (c:List ℕ) (a:Assignment)
    (v x:ℕ) (b:S×V) : S×V :=
  let row:=(v,x)::a
  if localOK d row then
    match refs d tab c v row with
    | some ids=>E.alternative b.1 b.2 v x ids
    | none=>b
  else b

def collect {S V:Type} (E:Algebra S V) (d:Instance) (tab:Table V) (c:List ℕ) (a:Assignment) (g:S) :=
  c.foldl (fun b v=>(d.menu v).foldl (fun st x=>offer E d tab c a v x st) b) (g,E.fail)

def install {S V:Type} (E:Algebra S V) (d:Instance) (c:List ℕ) (a:Assignment) (st:S×Table V) :=
  let b:=collect E d st.2 c a st.1
  (b.1,((c,a),b.2)::st.2)

def visit {S V:Type} (E:Algebra S V) (d:Instance) (k:ℕ) (s c:List ℕ) (st:S×Table V) :=
  if c.length==k+1 && rimOf d c==s then
    (assignments d s).foldl (fun p a=>install E d c a p) st
  else st

def build {S V:Type} (E:Algebra S V) (d:Instance) (w:ℕ) : S×Table V :=
  let vs:=vertices d
  let ss:=cuts vs (min w d.n)
  (List.range d.n).foldl (fun p k=>ss.foldl (fun z s=>(keysFor d vs s).foldl
    (fun t c=>visit E d k s c t) z) p) (E.initial,[])

def scan {S V:Type} (E:Algebra S V) (d:Instance) (w:ℕ) : S×V :=
  let st:=build E d w
  match (parts d (vertices d)).mapM (m:=Option) (fun c=>lookup st.2 c []) with
  | some ids=>E.finish st.1 ids
  | none=>(st.1,E.fail)

abbrev Letter := ℕ×ℕ
abbrev Lang (A:Type) := List A→Prop
def emptyWord {A:Type} : Lang A := (·=[])
def product {A:Type} (p q:Lang A) : Lang A := fun s=>∃a b,p a ∧ q b ∧ s=a++b
def concatenate {A:Type} (ps:List (Lang A)) : Lang A := ps.foldl product emptyWord

def wordAlgebra : Algebra Unit (Lang Letter) where
  initial:=()
  fail:=fun _=>False
  alternative:=fun _ prior v x children=>((),fun s=>prior s ∨ ∃tail,concatenate children tail ∧ s=(v,x)::tail)
  finish:=fun _ children=>((),concatenate children)

/-- Ordered pivot/label words accepted by the tight component table. A missing
child invalidates an alternative. A missing root invalidates the whole word. -/
def traces (d:Instance) (w:ℕ) : Lang Letter := (scan wordAlgebra d w).2
end StableMSR.Recovery.TightLanguage


