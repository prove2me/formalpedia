-- Prove2me | Definitions.Def_StableMSR_SingleSeparatorCircuit
-- name    : StableMSR_SingleSeparatorCircuit
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T00:01:14.264442+00:00
-- url     : https://prove2.me/theorems/7a4ffc13-2d0e-49eb-9fb2-d863c79c5586
-- title:
--   Executable singleton separator circuit and three-record board layout
-- statement:
--   Executable bottom-up construction for finite vertex IDs, local menus, edge compatibility and owned-block bitmaps. It enumerates bounded separators, deletes one new vertex, looks up strictly smaller child components and emits literal, product and union gates. Each gate lowers to three physical records in the membership-only board.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_WindowBlockMasks
open scoped Classical
set_option autoImplicit false
namespace StableMSR.Recovery.SingleCircuit
open WindowPorts WindowMasks
/-- A sequential circuit appends either a literal, a product, a choice, or an empty-language gate. Gate zero supplies the empty output word. -/
inductive Gate where
  | stop
  | atom (points : List ℕ)
  | both (left right : ℕ)
  | either (left right : ℕ)
  deriving Inhabited, DecidableEq
abbrev Gates := Array Gate
structure Instance where
  n : ℕ
  active : ℕ→Bool
  edge : ℕ→ℕ→Bool
  menu : ℕ→List ℕ
  test : ℕ→ℕ→ℕ→ℕ→Bool
  owned : ℕ→ℕ→List (List ℕ)
abbrev Assignment := List (ℕ×ℕ)
abbrev Key := List ℕ × Assignment
private def value (a : Assignment) (v : ℕ) := ((a.find? fun z=>z.1==v).map Prod.snd).getD 0
private def restricted (s : List ℕ) (a : Assignment) : Assignment := s.map fun v=>(v,value a v)
private def assignments (d : Instance) : List ℕ→List Assignment
  | []=>[[]]
  | v::vs=>(d.menu v).flatMap fun x=>(assignments d vs).map ((v,x)::·)
private def cuts : List ℕ→ℕ→List (List ℕ)
  | [],_=>[[]]
  | _::_,0=>[[]]
  | v::vs,w+1=>cuts vs (w+1) ++ (cuts vs w).map (v::·)
private def vertices (d : Instance) := (List.range d.n).filter d.active
private def pieceAt (d : Instance) (allowed : List ℕ) (v : ℕ) :=
  (List.range d.n).foldl (fun seen _=>allowed.filter fun u=>seen.contains u || seen.any (fun z=>d.edge z u)) [v]
private def parts (d : Instance) (allowed : List ℕ) := allowed.filterMap fun v=>
  let c:=pieceAt d allowed v
  if c.head?==some v then some c else none
private def rimOf (d : Instance) (c : List ℕ) := (vertices d).filter fun v=>
  !c.contains v && c.any (fun u=>d.edge u v)
private def localOK (d : Instance) (a : Assignment) := a.all fun z=>a.all fun t=>
  !(d.edge z.1 t.1) || d.test z.1 t.1 z.2 t.2
private def findState (tab : List (Key×ℕ)) (c : List ℕ) (a : Assignment) :=
  (tab.find? fun z=>z.1==(c,a)).map Prod.snd
private def appendBody (g : Gates) (masks : List (List ℕ)) (sons : List ℕ) : Gates×ℕ := Id.run do
  let mut a:=g
  let mut tail:=0
  for m in masks do
    let l:=a.size
    a:=a.push (.atom m)
    let p:=a.size
    a:=a.push (.both tail l)
    tail:=p
  for s in sons do
    let p:=a.size
    a:=a.push (.both tail s)
    tail:=p
  return (a,tail)
/-- Construct the whole regional grammar bottom-up, selecting exactly one new vertex and one label per alternative. The least point of a component is its canonical seed. The table contains only tight states. -/
def compileRegion (d : Instance) (w : ℕ) : Gates×ℕ := Id.run do
  let all:=vertices d
  let small:=cuts all (min w d.n)
  let mut g : Gates:=#[.atom [],.stop]
  let mut tab : List (Key×ℕ):=[]
  for k in List.range d.n do
    for s in small do
      for c in parts d (all.filter fun v=> !s.contains v) do
        if c.length==k+1 && rimOf d c==s then
          for a in assignments d s do
            let mut acc:=1
            for v in c do
              let children:=parts d (c.erase v)
              for x in d.menu v do
                let b:=(v,x)::a
                if localOK d b then
                  let sons:=children.mapM (m:=Option) fun t=>findState tab t (restricted (rimOf d t) b)
                  if let some ids:=sons then
                    let pair:=appendBody g (d.owned v x) ids
                    let p:=pair.1.size
                    g:=pair.1.push (.either acc pair.2)
                    acc:=p
            tab:=((c,a),acc)::tab
  let roots:=(parts d all).mapM (m:=Option) fun c=>findState tab c []
  if let some ids:=roots then return appendBody g [] ids
  return (g,1)
def gateAt (g : Gates) (p : ℕ) := g[p]?.getD .stop
def tinyTag (op : Gate) (j : ℕ) : ℤ :=
  match op with
  | .stop=> -1
  | .atom _=>if j=0 then 0 else -1
  | .both _ _=>if j=0 then 1 else if j=1 then 2 else -1
  | .either _ _=>if j=0 ∨ j=1 then 1 else if j=2 then 2 else -1
def tinyChild (op : Gate) (j : ℕ) : ℕ :=
  match op with
  | .both l r | .either l r=>if j=0 then l else if j=1 then r else 0
  | _=>0
def tinyMask (op : Gate) := match op with | .atom pts=>pts | _=>[]
def boardOf (g : Gates) (roots : ℕ→ℕ) : Board where
  size:=3*g.size
  tag:=fun q=>tinyTag (gateAt g (q/3)) (q%3)
  dest:=fun q=>q/3
  child:=fun q=>tinyChild (gateAt g (q/3)) (q%3)
  arity:=fun _=>0
  value:=fun _ _ _=>0
  root:=roots
def maskAt (n : ℕ) (g : Gates) (q : ℕ) : Cluster n :=
  Finset.univ.filter fun i=>(tinyMask (gateAt g (q/3))).contains i.val
inductive Language (n : ℕ) (g : Gates) : ℕ→List (Cluster n)→Prop where
  | lit {p pts} : p< g.size → gateAt g p=.atom pts →
      Language n g p (emit (Finset.univ.filter (fun i : Point n=>pts.contains i.val)))
  | both {p i j L R} : p< g.size → gateAt g p=.both i j → i< p → j< p →
      Language n g i L → Language n g j R → Language n g p (L++R)
  | left {p i j L} : p< g.size → gateAt g p=.either i j → i< p → Language n g i L → Language n g p L
  | right {p i j L} : p< g.size → gateAt g p=.either i j → j< p → Language n g j L → Language n g p L
end StableMSR.Recovery.SingleCircuit


