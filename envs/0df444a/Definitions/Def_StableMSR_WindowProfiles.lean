-- Prove2me | Definitions.Def_StableMSR_WindowProfiles
-- name    : StableMSR_WindowProfiles
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T21:53:57.940796+00:00
-- url     : https://prove2.me/theorems/ae8432f8-558f-408e-87e5-da2c7cecd370
-- title:
--   Exact-count endpoint menus for individual scenario regions
-- statement:
--   A representative-indexed local table supplies one feasible ball cover per available count. Covers are certified within their own region. A separate layered-count path specification describes the cross-region convolution.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Sections 4.1–4.4 and Appendices A.4–A.6. Exact-count combination over disjoint regions in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowCSP
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.OracleQueries StableMSR.Recovery.Compiler
open StableMSR.Recovery.Supplement StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowCSP
namespace StableMSR.Recovery.WindowProfiles
abbrev Mem := ℕ → ℤ
def replace (x : World) (m : Mem) : World := {x with mem:=m}
def index (n u i c : ℕ) := (u*n+i)*n+c
def node (n u i b : ℕ) := 2+index n u i b
def arc (n u i a b : ℕ) := 2+index n u i a*n+b
def prior (n u i a : ℕ) := if i=0 then 1 else node n u (i-1) a
def capacity (S n : ℕ) := 1+S*n*n*n
def height (x : World) := 4*capacity x.rows x.n+1
def arena (x : World) (m : Mem) : World := {x with rows:=height x,mem:=m}
def active (x : World) (u i c : ℕ) := 0≤ center x (index x.n u i c) 0
def token (x : World) (u i c : ℕ) : RegionalBallDP.Word := fun j s =>
  RegionalBallDP.legalize x.n (RegionalBallDP.field x (index x.n u i c) j s)
def allowed (x : World) (u i a b : ℕ) := a≤ b ∧ (i=0 → a=0) ∧ active x u i (b-a)
def fibre (x : World) (u : ℕ) (p : Point x.n) : Cluster x.n :=
  Finset.univ.filter (fun q=>label x u q=label x u p)
noncomputable def rep (x : World) (u : ℕ) (p : Point x.n) : Point x.n :=
  (fibre x u p).min' ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
noncomputable def keys (x : World) (u : ℕ) : Finset ℕ :=
  Finset.univ.image (fun p=>(rep x u p).val)
noncomputable def piece (x : World) (u i : ℕ) : Cluster x.n :=
  Finset.univ.filter (fun p=>(rep x u p).val=i)
def contains (x : World) (u : RegionalBallDP.Word) (j : ℕ) (p : Point x.n) :=
  RegionalBallDP.containsPoint x u j p.val
def Owned (x : World) (W : Cluster x.n) (c : ℕ) (v : RegionalBallDP.Word) : Prop :=
  (∀j< c,∃p∈W,v j false=(p.val:ℤ)) ∧
  (∀j< c,∀l< c,v j false=v l false → j=l) ∧
  ∀p∈W,∃j< c,contains x v j p
noncomputable def Profiles (x : World) (e : ℚ) (m : Mem) : Prop :=
  let y:=replace x m
  ∀u< x.rows,∀i< x.n,
    (∀c≤ x.k,active y u i c → Owned x (piece x u i) c (token y u i c)) ∧
    (i∉keys x u → active y u i 0) ∧
    (i∈keys x u → 0< scale x u →
      RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist (scale x u) (piece x u i)) (widthBound (e:ℝ)) →
      ∀P : Pick x.n,valid x (piece x u i) (scale x u) (budget (e:ℝ)) P →
        let c:=number x (piece x u i) (scale x u) P
        c≤ x.k → active y u i c ∧ RegionalBallDP.weight x c (token y u i c)≤ WindowCSP.price x (piece x u i) (scale x u) P)
def profileSpec (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀(x : World) (s : Store),1≤ x.k → x.k< x.n → IsMetricArray x.dist → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
       Ready (worldOf x.k x.rows x.dist t) t ∧ Profiles x e (worldOf x.k x.rows x.dist t).mem
structure Grid (x : World) (m : Mem) : Prop where
  sized : RegionalBallDP.shape (arena x m)
  states : ∀u< x.rows,∀i< x.n,∀b≤ x.k,
    RegionalBallDP.vertex (arena x m) (node x.n u i b) ∧
    RegionalBallDP.width (arena x m) (node x.n u i b)=b
  pred : ∀u< x.rows,∀i< x.n,∀b≤ x.k,∀q,RegionalBallDP.link (arena x m) (node x.n u i b) q →
    ∃a,allowed x u i a b ∧ q=arc x.n u i a b
  step : ∀u< x.rows,∀i< x.n,∀b≤ x.k,∀a,allowed x u i a b →
    RegionalBallDP.link (arena x m) (node x.n u i b) (arc x.n u i a b) ∧
    RegionalBallDP.parent (arena x m) (arc x.n u i a b)=prior x.n u i a ∧
    ∀j,a≤ j → j< b → ∀w,RegionalBallDP.payload (arena x m) (arc x.n u i a b) j w=token x u i (b-a) (j-a) w
end StableMSR.Recovery.WindowProfiles


