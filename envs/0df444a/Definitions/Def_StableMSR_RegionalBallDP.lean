-- Prove2me | Definitions.Def_StableMSR_RegionalBallDP
-- name    : StableMSR_RegionalBallDP
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-21T13:12:04.789017+00:00
-- url     : https://prove2.me/theorems/e23ae4c6-018e-4c97-a655-c342e7dfcc1f
-- title:
--   Witness-carrying regional ball paths in real-distance RAM tables
-- statement:
--   The mutable rows of a distance-oracle table store partial ball covers. An acyclic edge appends a local menu choice to a specified prefix of a row of centers and radius witnesses. A path represents the concatenation of these choices and its weight is its true oracle sum of radii. Synchronous applications of the table update choose a cheapest reachable witness for each exact count.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, equation (2), and Appendix A.4–A.6. Real-distance oracle implementation and witness reconstruction for the Prove2Me recovery mission.

import Definitions.Def_StableMSR_FewBallRows
set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
namespace StableMSR.Recovery.RegionalBallDP

abbrev Word := ℕ → Bool → ℤ
def blank : Word := fun _ _=>0
def field (x : World) (r j : ℕ) (w : Bool) : ℤ := if w then witness x r j else center x r j
def word (x : World) (v : ℕ) : Word := fun j w=>if j<x.k then field x v j w else 0
def slots (x : World) : ℕ := (center x 0 0).toNat
def shape (x : World) : Prop := 0 < slots x ∧ 4*slots x < x.rows
def vertex (x : World) (v : ℕ) : Prop := 0<v ∧ v≤ slots x
def width (x : World) (v : ℕ) : ℕ :=
  if v=1 then 0 else min x.k (center x (slots x+slots x+v) 0).toNat
def parent (x : World) (q : ℕ) := (center x (slots x+slots x+slots x+q) 0).toNat
def destination (x : World) (q : ℕ) := witness x (slots x+slots x+slots x+q) 0
def legalize (n : ℕ) (z : ℤ) : ℤ := if 0≤z ∧ z<(n:ℤ) then z else 0
def payload (x : World) (q j : ℕ) (w : Bool) := legalize x.n (field x (slots x+q) j w)
def link (x : World) (v q : ℕ) : Prop :=
  vertex x q ∧ vertex x (parent x q) ∧ parent x q<v ∧
    destination x q=(v:ℤ) ∧ width x (parent x q)≤width x v
def splice (x : World) (v q : ℕ) (u : Word) : Word := fun j w=>
  if j<width x (parent x q) then u j w else if j<width x v then payload x q j w else 0
noncomputable def weight (x : World) (c : ℕ) (u : Word) : ℝ :=
  ∑j ∈ Finset.range x.k, if j<c then MinSumFPT.oracleAnswer x.dist (u j false) (u j true) else 0
noncomputable def covers (x : World) (u : Word) : Prop :=
  (∀j<x.k,∀l<x.k,u j false=u l false → j=l) ∧
  ∀i<x.n,∃j<x.k,MinSumFPT.oracleAnswer x.dist (u j false) (i:ℤ) ≤
    MinSumFPT.oracleAnswer x.dist (u j false) (u j true)
inductive Route (x : World) : ℕ→Word→Prop
  | root : Route x 1 blank
  | append {v q : ℕ} {u : Word} : vertex x v → link x v q → Route x (parent x q) u →
      Route x v (splice x v q u)
def wave (x : World) : ℕ → ℕ → Word → Prop
  | 0,v,u => v=1 ∧ u=blank
  | t+1,v,u => (v=1 ∧ u=blank) ∨
      ∃q a,vertex x v ∧ link x v q ∧ wave x t (parent x q) a ∧ u=splice x v q a
def live (x : World) (v : ℕ) : Prop := 0≤center x v 0
def eligible (x : World) (v q : ℕ) : Prop := link x v q ∧ live x (parent x q)
def candidate (x : World) (v q : ℕ) : Word := splice x v q (word x (parent x q))
noncomputable def price (x : World) (v q : ℕ) := weight x (width x v) (candidate x v q)
noncomputable def winner (x : World) (v q : ℕ) : Prop :=
  eligible x v q ∧ ∀z<x.rows,eligible x v z →
    price x v q < price x v z ∨ price x v q=price x v z ∧ q≤z
noncomputable def tick (x : World) (v j : ℕ) (w : Bool) : ℤ :=
  if v=0 then (if j=0 ∧ w=true then witness x 0 0+1 else field x v j w)
  else if v≤ slots x then
    (if v=1 then 0 else if ∃q<x.rows,eligible x v q then
       ∑q ∈ Finset.range x.rows, if winner x v q then candidate x v q j w else 0
     else -1)
  else field x v j w
def seedTable (x : World) (v j : ℕ) (w : Bool) : ℤ :=
  if v=0 then (if j=0 ∧ w=true then 0 else field x v j w)
  else if v≤ slots x then (if v=1 then 0 else -1) else field x v j w
def clean (x : World) (v j : ℕ) (w : Bool) := legalize x.n (field x v j w)
def Writes (x y : World) (f : World→ℕ→ℕ→Bool→ℤ) : Prop :=
  ∀v<x.rows,∀j<x.k,∀b,field y v j b=f x v j b
def InTable (x : World) (v : ℕ) : Prop := v<x.rows ∧ width x v=x.k ∧
  ∀u,Route x v u → covers x u
def regionalSpec (e : ℚ) (a b : ℕ) (cmd : Cmd) (n k : ℕ) (d : Point n→Point n→ℝ) : Prop :=
  ∃s z H,Executes d cmd (initialStore n k) s z ∧
    z≤a*n^(b*parameterEnvelope (e:ℝ)) ∧ H≤a*n^(b*parameterEnvelope (e:ℝ)) ∧
    let x:=worldOf k H d s
    Ready x s ∧ shape x ∧ ∀O,Stable d k (1+(e:ℝ)) O →
      fewBound (e:ℝ)<(largeClusters d O (e:ℝ)).card →
      ∃v,vertex x v ∧ InTable x v ∧ ∃u,Route x v u ∧ weight x x.k u≤cost d O
end StableMSR.Recovery.RegionalBallDP


