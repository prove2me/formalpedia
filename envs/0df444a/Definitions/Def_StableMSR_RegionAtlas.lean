-- Prove2me | Definitions.Def_StableMSR_RegionAtlas
-- name    : StableMSR_RegionAtlas
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T23:27:19.805405+00:00
-- url     : https://prove2.me/theorems/bc0cbce6-4343-4c31-97a1-92a4baec5a40
-- title:
--   Exact regional greedy-net, anchor, window and interaction-graph arrays
-- statement:
--   The input gives one region bitmap and two point identifiers determining its scale. The scan uses the fixed input order and a strict two-radius separation test. Its output lists the canonical net, least covering anchors, four-radius window memberships and eight-radius graph entries.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowPorts
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.Supplement
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.RegionalBallDP (field)
namespace StableMSR.Recovery.WindowGeometry
def inside (x : World) (i : ℕ) := 0< center x (2+i) 0
noncomputable def region (x : World) : Cluster x.n := Finset.univ.filter (fun p=>inside x p.val)
noncomputable def unitR (x : World) := MinSumFPT.oracleAnswer x.dist (center x 0 0) (center x 1 0)
def selected (x : World) (i : ℕ) := 0< witness x (2+i) 0
noncomputable def admitPoint (x : World) (i : ℕ) := inside x i ∧
  ∀j< x.n,selected x j → 2*unitR x< FewBallRows.distAt x i j
noncomputable def nearestKey (x : World) (i : ℕ) : ℤ :=
  let hit (a : ℕ):=selected x a ∧ FewBallRows.distAt x a i≤2*unitR x
  if ∃a< x.n,hit a then first x.n hit else (i:ℤ)
noncomputable def rect (x : World) (a i : ℕ) (s : Bool) : Prop :=
  if s then a≠i ∧ selected x a ∧ selected x i ∧
    FewBallRows.distAt x a i≤8*unitR x ∧ FewBallRows.distAt x i a≤8*unitR x
  else inside x i ∧ FewBallRows.distAt x a i≤4*unitR x
noncomputable def reset (x : World) (r j : ℕ) (s : Bool) : ℤ :=
  if s=true ∧ j=0 ∧ (r=0 ∨ 2≤ r ∧ r<2+x.n) then 0 else field x r j s
noncomputable def sweep (x : World) (r j : ℕ) (s : Bool) : ℤ :=
  let i:=(witness x 0 0).toNat
  if s=true ∧ r=0 ∧ j=0 then witness x 0 0+1
  else if s=true ∧ j=0 ∧ r=2+i ∧ i< x.n then (if admitPoint x i then 1 else 0) else field x r j s
noncomputable def expose (x : World) (r j : ℕ) (s : Bool) : ℤ :=
  if j=0 ∧ 2≤ r ∧ r<2+x.n then (if s then field x r j s else nearestKey x (subR x r 2))
  else if j=0 ∧ 2+x.n≤ r then
    let v:=subR x r (2+x.n);if rect x (divN x v) (remN x v) s then 1 else 0
  else field x r j s
def pairRow (n a i : ℕ) := 2+n+(a*n+i)
noncomputable def Atlas (x : World) (m : ℕ→ℤ) :=
  let y:={x with mem:=m};let W:=region x;let R:=unitR x;let N:=greedyNet x.dist R W
  (∀i : Point x.n,(0< witness y (2+i.val) 0 ↔ i∈N) ∧
      center y (2+i.val) 0=((anchor x.dist W R i).val:ℤ)) ∧
  (∀a i : Point x.n,0< center y (pairRow x.n a.val i.val) 0 ↔ i∈window x.dist W R a) ∧
  ∀a i : ↥N,0< witness y (pairRow x.n a.val.val i.val.val) 0 ↔ (interactionGraph x.dist R W).Adj a i
end StableMSR.Recovery.WindowGeometry


