-- Prove2me | Definitions.Def_StableMSR_IntegerWindowCandidates
-- name    : StableMSR_IntegerWindowCandidates
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T00:25:20.042031+00:00
-- url     : https://prove2.me/theorems/87411c46-f12f-4d53-9cc4-2b32a1dc9973
-- title:
--   Executable integer window geometry, menus, compatibility, and owned point masks
-- statement:
--   The finite integer implementation constructs a region from scene labels, selects its greedy net, assigns each point to its least eligible center, decodes ordered ball words, tests candidate partitions, and computes the local compatibility and owned-block incidence. Each decoded row is a filtered finite point set. Duplicate rows are removed and their members are listed in increasing order.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_IntegerRegionalGeometry
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
open Compiler OracleQueries WindowCSP SingleCircuit CartesianBallRows
set_option autoImplicit false

def lookup {n:ℕ} {α:Type} (f:Fin n→α) (i:ℕ) (fallback:α) :=
  if h:i<n then f ⟨i,h⟩ else fallback
def atPair (n:ℕ) (m:ℤ→ℤ) (i j:ℤ) : ℤ :=
  match MinSumFPT.toPoint n i,MinSumFPT.toPoint n j with
  | some a,some b=>m (address a b)
  | _,_=>0
def piece (n:ℕ) (mem:ℕ→ℤ) (u i:ℕ) : Cluster n :=
  let label:=fun p:Fin n=>mem (3+u*(n+2)+2+p.val)
  Finset.univ.filter fun p:Fin n=>
    let fibre:=Finset.univ.filter (fun q:Fin n=>label q=label p)
    (fibre.min' ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩).val=i
def net {n:ℕ} (m:ℤ→ℤ) (W:Cluster n) : Cluster n :=
  (W.sort (·≤·)).foldl (fun A p=>if ∀z∈A,2*(unit n:ℤ) < m (address p z) then insert p A else A) ∅
def owner {n:ℕ} (m:ℤ→ℤ) (N:Cluster n) (p:Fin n) : Fin n :=
  let C:=N.filter (fun a=>m (address a p) ≤ 2*(unit n:ℤ))
  if h:C.Nonempty then C.min' h else p
def win {n:ℕ} (m:ℤ→ℤ) (W:Cluster n) (a:Fin n) : Cluster n :=
  W.filter fun p=>m (address a p) ≤ 4*(unit n:ℤ)
def joins (n:ℕ) (m:ℤ→ℤ) (h c:ℕ) (i j:Fin n) : Bool :=
  let g:=c%(h+1)
  let u:=c/(h+1)
  let center:=fun v:ℕ=>(digit n u (2*v):ℤ)
  let witness:=fun v:ℕ=>(digit n u (2*v+1):ℤ)
  let hit:=fun v:ℕ=>fun p:Fin n=>decide (atPair n m (center v) (p.val:ℤ) ≤ atPair n m (center v) (witness v))
  let vs:=(List.range (h+1)).filter (fun v=>0<v && v≤g)
  vs.any (fun v=>hit v i && hit v j) ||
    ((!vs.any (fun v=>hit v i)) && (!vs.any (fun v=>hit v j)) &&
      decide (atPair n m (i.val:ℤ) (j.val:ℤ) ≤ atPair n m (center 0) (witness 0)))
def block {n:ℕ} (m:ℤ→ℤ) (U:Cluster n) (h c:ℕ) (p:Fin n) :=
  U.filter (fun q=>joins n m h c p q=true)
def blocks {n:ℕ} (m:ℤ→ℤ) (U:Cluster n) (h c:ℕ) : List (Cluster n) :=
  ((U.sort (·≤·)).map (block m U h c)).eraseDups
def feasible {n:ℕ} (U:Cluster n) (P:List (Cluster n)) : Bool :=
  P.all (fun C=>decide C.Nonempty) && P.all (fun C=>P.all (fun D=>decide (C=D) || decide (Disjoint C D))) &&
    decide (P.toFinset.biUnion id=U)
def touchesB {n:ℕ} (own:Fin n→Fin n) (a:Fin n) (C:Cluster n) : Bool :=
  (C.sort (·≤·)).any (fun p=>own p==a)
def holdsB {n:ℕ} (own:Fin n→Fin n) (a:Fin n) (C:Cluster n) : Bool :=
  if h:C.Nonempty then own (C.min' h)==a else false
def compat {n:ℕ} (own:Fin n→Fin n) (a b:Fin n) (P Q:List (Cluster n)) : Bool :=
  P.all (fun C=>Q.all fun D=> !touchesB own a C || !touchesB own b D || decide (Disjoint C D) || decide (C=D))
def listed {n:ℕ} (C:Cluster n) := (C.sort (·≤·)).map Fin.val
def menus {n:ℕ} (m:ℤ→ℤ) (U:Cluster n) (h:ℕ) := (SingleCodes.words n h).filter fun c=>feasible U (blocks m U h c)
def normalized {n:ℕ} (m:ℤ→ℤ) (W:Cluster n) (h:ℕ) : Instance :=
  let N:=net m W
  let own:=owner m N
  let U:=win m W
  let family:=fun a c=>blocks m (U a) h c
  {n:=n
   active:=fun a=>lookup (fun v=>decide (v∈N)) a false
   edge:=fun a b=>lookup (fun v:Fin n=>lookup (fun u:Fin n=>decide (v≠u ∧ m (address v u) ≤ 8*(unit n:ℤ) ∧ m (address u v) ≤ 8*(unit n:ℤ))) b false) a false
   menu:=fun a=>lookup (fun v=>menus m (U v) h) a []
   test:=fun a b c k=>lookup (fun v=>lookup (fun u=>compat own v u (family v c) (family u k)) b false) a false
   owned:=fun a c=>lookup (fun v=>((family v c).filter (holdsB own v)).map listed) a []}
/-- Compare literal blocks through their point sets, retaining their multiplicities. -/
def MasksAgree (a b:List (List ℕ)) := (a.map List.toFinset).Perm (b.map List.toFinset)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits


