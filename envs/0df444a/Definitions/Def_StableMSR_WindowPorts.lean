-- Prove2me | Definitions.Def_StableMSR_WindowPorts
-- name    : StableMSR_WindowPorts
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T23:16:52.386848+00:00
-- url     : https://prove2.me/theorems/4e8f0fe1-9b66-4c5f-896e-3c056c8e1a8c
-- title:
--   Independent separator ports for binary window assignments
-- statement:
--   A finite board carries literal bag contributions and individual left or right separator choices. Counts appear only on literals. A fork chooses one predecessor on each port and adds the two derivation counts. The explicit lowering allocates one empty state plus a left selector and a completed state for each label and count. Regional roots are independent of the requested count.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowJoins
import Definitions.Def_StableMSR_WindowProfilePacking
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.Supplement (interactionGraph)
open StableMSR.Recovery.WindowProfiles (piece index keys Owned divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize)
namespace StableMSR.Recovery.WindowPorts
structure Board where
  size : ℕ
  tag : ℕ→ℤ
  dest : ℕ→ℕ
  child : ℕ→ℕ
  arity : ℕ→ℕ
  value : ℕ→Word
  root : ℕ→ℕ
def initial (B : Board) (q p : ℕ) := q< B.size ∧ B.tag q=0 ∧ B.dest q=p ∧ p< B.size
def port (B : Board) (t : ℤ) (q p : ℕ) := q< B.size ∧ B.tag q=t ∧ B.dest q=p ∧ p< B.size ∧ B.child q< p
def trimWord (c : ℕ) (u : Word) : Word := fun j b=>if j< c then u j b else 0
inductive Reach (k : ℕ) (B : Board) : ℕ→ℕ→Word→Prop where
  | literal {q p} : initial B q p → B.arity q≤ k → Reach k B p (B.arity q) (trimWord (B.arity q) (B.value q))
  | fork {l r p i j u v} : port B 1 l p → port B 2 r p →
      Reach k B (B.child l) i u → Reach k B (B.child r) j v → i+j≤ k →
      Reach k B p (i+j) (appendWords k i (i+j) u v)
def stage (n p c : ℕ) := 1+(2*p)*n+c
def finish (n p c : ℕ) := 1+(2*p+1)*n+c
def ticket (n q a b : ℕ) := 1+(q*n+a)*n+b
def volume (m n : ℕ) := 1+m*n*n
def expandLen (n v : ℕ) := (v-1)%n
def sourceRow (n q : ℕ) := ((q-1)/n)/n
def firstCount (n q : ℕ) := ((q-1)/n)%n
def lastCount (n q : ℕ) := (q-1)%n
noncomputable def activeTicket (B : Board) (n k q a b : ℕ) : ℤ :=
  let p:=B.dest q
  if initial B q p ∧ a=B.arity q ∧ a≤ k ∧ b=0 then (finish n p a:ℤ)
  else if port B 1 q p ∧ a≤ k ∧ b=0 then (stage n p a:ℤ)
  else if port B 2 q p ∧ a+b≤ k then (finish n p (a+b):ℤ)
  else -1
noncomputable def lower (B : Board) (n k : ℕ) : Rules where
  size:=volume B.size n
  len:=fun v=>if v< volume B.size n then min k (expandLen n v) else 0
  goal:=fun r=>finish n (B.root (r/n)) (r%n)
  dst:=fun z=>if z=0 then 0 else activeTicket B n k (sourceRow n z) (firstCount n z) (lastCount n z)
  fork:=fun z=>z≠0 ∧ B.tag (sourceRow n z)≠0
  lhs:=fun z=>let q:=sourceRow n z;let a:=firstCount n z
               if B.tag q=1 then finish n (B.child q) a else stage n (B.dest q) a
  rhs:=fun z=>let q:=sourceRow n z
               if B.tag q=1 then 0 else finish n (B.child q) (lastCount n z)
  payload:=fun z=>if z=0 then (fun _ _=>0) else B.value (sourceRow n z)
inductive TicketCase (B : Board) (n k : ℕ) : ℕ→ℕ→Prop where
  | zero : TicketCase B n k 0 0
  | atom (q : ℕ) : initial B q (B.dest q) → B.arity q≤ k →
      TicketCase B n k (finish n (B.dest q) (B.arity q)) (ticket n q (B.arity q) 0)
  | left (q i : ℕ) : port B 1 q (B.dest q) → i≤ k →
      TicketCase B n k (stage n (B.dest q) i) (ticket n q i 0)
  | right (q a b : ℕ) : port B 2 q (B.dest q) → a+b≤ k →
      TicketCase B n k (finish n (B.dest q) (a+b)) (ticket n q a b)
def rawSize (x : World) := (x.mem 0).toNat
def readBand (x : World) (b q j : ℕ) (s : Bool) := field x (1+b*rawSize x+q) j s
def board (x : World) : Board where
  size:=rawSize x
  tag:=fun q=>readBand x 0 q 0 false
  dest:=fun q=>(readBand x 0 q 0 true).toNat
  child:=fun q=>(readBand x 1 q 0 false).toNat
  arity:=fun q=>(readBand x 1 q 0 true).toNat
  value:=fun q j s=>legalize x.n (readBand x 2 q j s)
  root:=fun r=>(readBand x 3 r 0 false).toNat
def capacity (x : World) := volume (rawSize x) x.n
def room (x : World) := 1+5*capacity x< x.rows
structure Presents (x : World) (e : ℚ) (y : World) : Prop where
  space : room y
  scenes : y.mem 1=(x.rows:ℤ)
  targets : ∀u< x.rows,∀i< x.n,let B:=board y;let p:=B.root (u*x.n+i)
    u*x.n+i< B.size ∧ p< B.size ∧ ∀c≤ x.k,
    (∀w,Reach y.k B p c w → Owned x (piece x u i) c w) ∧
    (i∉keys x u → c=0 → ∃w,Reach y.k B p c w) ∧
    (i∈keys x u → 0< scale x u →
      RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist (scale x u) (piece x u i)) (widthBound (e:ℝ)) →
      ∀P : Pick x.n,valid x (piece x u i) (scale x u) (budget (e:ℝ)) P →
        number x (piece x u i) (scale x u) P=c →
        ∃w,Reach y.k B p c w ∧ weight y c w≤ WindowCSP.price x (piece x u i) (scale x u) P)
def portSpec (e : ℚ) (c D b : ℕ) (cmd : Cmd) :=
  ∀(x : World) (s : Store),1≤ x.k → x.k< x.n → IsMetricArray x.dist → Ready x s →
   ∃t z H,Executes x.dist cmd s t z ∧ z≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    H≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧ Ready (worldOf x.k H x.dist t) t ∧ Presents x e (worldOf x.k H x.dist t)
end StableMSR.Recovery.WindowPorts


