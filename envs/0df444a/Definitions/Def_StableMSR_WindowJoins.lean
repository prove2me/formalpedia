-- Prove2me | Definitions.Def_StableMSR_WindowJoins
-- name    : StableMSR_WindowJoins
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T22:34:44.232462+00:00
-- url     : https://prove2.me/theorems/c355d31b-7aab-4845-8efc-d1b2bc83d513
-- title:
--   Binary local-window join tables with exact counts and ball witnesses
-- statement:
--   A topologically ordered table generates ball words using literal local contributions and binary concatenation. Exact counts are explicit in the states. Every regional output has a designated state with sound derivations and a cost-bounded derivation for every compatible window assignment. The table carries the unoptimized alternatives and needs no selected minimum or backpointers.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.6 (tree-decomposition dynamic programming over regional windows), in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowProfiles
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowProfiles StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight)
namespace StableMSR.Recovery.WindowJoins
structure Rules where
  size : ℕ
  len : ℕ→ℕ
  goal : ℕ→ℕ
  dst : ℕ→ℤ
  fork : ℕ→Prop
  lhs : ℕ→ℕ
  rhs : ℕ→ℕ
  payload : ℕ→Word
noncomputable def shift (k j a : ℕ) : ℕ := ∑t∈Finset.range k,if a+t=j then t else 0
def atomWord (g : Rules) (v q : ℕ) : Word := fun j w=>if j< g.len v then g.payload q j w else 0
noncomputable def appendWords (k a c : ℕ) (L R : Word) : Word := fun j w=>
  if j< a then L j w else if j< c then R (shift k j a) w else 0
def arc (g : Rules) (v q : ℕ) := q< g.size ∧ g.dst q=(v:ℤ)
def joint (g : Rules) (v q : ℕ) := g.lhs q< v ∧ g.rhs q< v ∧ g.len (g.lhs q)+g.len (g.rhs q)=g.len v
inductive Derives (k : ℕ) (g : Rules) : ℕ→Word→Prop where
  | leaf {v q} : arc g v q → ¬g.fork q → Derives k g v (atomWord g v q)
  | join {v q u w} : arc g v q → g.fork q → joint g v q → Derives k g (g.lhs q) u →
      Derives k g (g.rhs q) w → Derives k g v (appendWords k (g.len (g.lhs q)) (g.len v) u w)
noncomputable def eligible (g : Rules) (on : ℕ→Prop) (v q : ℕ) := arc g v q ∧
  (g.fork q → joint g v q ∧ on (g.lhs q) ∧ on (g.rhs q))
noncomputable def candidate (k : ℕ) (g : Rules) (T : ℕ→Word) (v q : ℕ) : Word :=
  if g.fork q then appendWords k (g.len (g.lhs q)) (g.len v) (T (g.lhs q)) (T (g.rhs q)) else atomWord g v q
noncomputable def winner (x : World) (g : Rules) (on : ℕ→Prop) (T : ℕ→Word) (v q : ℕ) :=
  let val (r : ℕ):=weight x (g.len v) (candidate x.k g T v r)
  eligible g on v q ∧ ∀r< x.rows,eligible g on v r → val q< val r ∨ val q=val r ∧ q≤ r
noncomputable def bestWord (x : World) (g : Rules) (on : ℕ→Prop) (T : ℕ→Word) (v : ℕ) : Word := fun j w=>
  if ∃q< x.rows,eligible g on v q then ∑q∈Finset.range x.rows,if winner x g on T v q then candidate x.k g T v q j w else 0 else -1
def RowOK (x : World) (g : Rules) (v : ℕ) (on : Prop) (u : Word) :=
  (on → Derives x.k g v u) ∧ ∀a,Derives x.k g v a → on ∧ weight x (g.len v) u≤ weight x (g.len v) a
def Sane (x : World) (g : Rules) := (∀v,g.len v≤ x.k) ∧ ∀q j w,0≤ g.payload q j w ∧ g.payload q j w<(x.n:ℤ)
def slots (x : World) := (center x 0 0).toNat
def band (x : World) (b q j : ℕ) (w : Bool) :=
  if q< slots x ∧ j< x.k then field x (1+b*slots x+q) j w else 0
noncomputable def decode (x : World) : Rules where
  size:=slots x
  len:=fun v=>min x.k (band x 2 v 0 false).toNat
  goal:=fun r=>(band x 2 r 0 true).toNat
  dst:=fun q=>band x 3 q 0 false
  fork:=fun q=>0< band x 3 q 0 true
  lhs:=fun q=>(band x 4 q 0 false).toNat
  rhs:=fun q=>(band x 4 q 0 true).toNat
  payload:=fun q j w=>legalize x.n (band x 1 q j w)
def shaped (x : World) := 1+5*slots x< x.rows
def rowWord (x : World) (v : ℕ) := word x (1+v)
def liveRow (x : World) (v : ℕ) := 0≤ center x (1+v) 0
def storedScenes (x : World) := center x (x.rows-1) 0
def seed (x : World) (r j : ℕ) (w : Bool) : ℤ :=
  if r=0 ∧ j=0 ∧ w=true then 0 else field x r j w
noncomputable def advance (x : World) (r j : ℕ) (w : Bool) : ℤ :=
  let v:=(witness x 0 0).toNat
  if r=0 ∧ j=0 ∧ w=true then witness x 0 0+1 else
  if v< slots x ∧ r=1+v then bestWord x (decode x) (liveRow x) (rowWord x) v j w else field x r j w
noncomputable def project (x : World) (r j : ℕ) (w : Bool) : ℤ :=
  if r< slots x then field x (1+(decode x).goal r) j w else field x r j w
structure Encodes (x : World) (e : ℚ) (y : World) : Prop where
  shape : shaped y
  scenes : storedScenes y=(x.rows:ℤ)
  targets : ∀u< x.rows,∀i< x.n,∀c≤ x.k,
    let g:=decode y;let r:=index x.n u i c;let v:=g.goal r
    r< g.size ∧ v< g.size ∧ g.len v=c ∧
    (∀w,Derives y.k g v w → Owned x (piece x u i) c w) ∧
    (i∉keys x u → c=0 → ∃w,Derives y.k g v w) ∧
    (i∈keys x u → 0< scale x u →
      RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist (scale x u) (piece x u i)) (widthBound (e:ℝ)) →
      ∀P : Pick x.n,valid x (piece x u i) (scale x u) (budget (e:ℝ)) P →
        number x (piece x u i) (scale x u) P=c →
        ∃w,Derives y.k g v w ∧ weight y c w≤ WindowCSP.price x (piece x u i) (scale x u) P)
def buildSpec (e : ℚ) (c D b : ℕ) (cmd : Cmd) :=
  ∀(x : World) (s : Store),1≤ x.k → x.k< x.n → IsMetricArray x.dist → Ready x s →
   ∃t z H,Executes x.dist cmd s t z ∧ z≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    H≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧ Ready (worldOf x.k H x.dist t) t ∧ Encodes x e (worldOf x.k H x.dist t)
end StableMSR.Recovery.WindowJoins


