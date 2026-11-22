-- Prove2me | Definitions.Def_StableMSR_WindowCSP
-- name    : StableMSR_WindowCSP
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-21T16:02:49.217173+00:00
-- url     : https://prove2.me/theorems/5b68b774-f018-4a9d-a708-a4892a27b951
-- title:
--   Overlapping net windows and pairwise consistency for exact regional recovery
-- statement:
--   A net point chooses a candidate partition of its radius-4R window. Only clusters that touch its owned points participate in compatibility checks, and each nonempty cluster is charged to the owner of its least point. A scenario encodes a radius pair and one region label per point. The two program contracts separate geometric scenario generation from the uniform exact-count optimization of these pairwise choices.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Lemmas 3.3, 3.8, 3.9(iii), 4.4, Proposition 4.2, Algorithm 1, and Appendix A.4–A.6. Alternative pairwise formulation using bounded-overlap window traces in the mission’s real-distance model.

import Definitions.Def_StableMSR_LocalBallTrials
import Definitions.Def_StableMSR_RegionalSeeds
import Definitions.Def_StableMSR_Recovery_Supplement_Partitions
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.Supplement
namespace StableMSR.Recovery.WindowCSP
noncomputable def budget (e : ℝ) : ℕ := 2*(ownerBound e+1)
noncomputable def window {n : ℕ} (d : Point n→Point n→ℝ) (W : Cluster n) (R : ℝ) (a : Point n) :=
  W∩ball d a (4*R)
noncomputable def anchor {n : ℕ} (d : Point n→Point n→ℝ) (W : Cluster n) (R : ℝ) (i : Point n) : Point n :=
  Supplement.representative ((greedyNet d R W).filter (fun a=>d a i≤2*R)) i
def touches {n : ℕ} (owner : Point n→Point n) (a : Point n) (C : Cluster n) : Prop :=
  ∃i∈C,owner i=a
def holds {n : ℕ} (owner : Point n→Point n) (a : Point n) (C : Cluster n) : Prop :=
  ∃i∈C,owner i=a ∧ ∀j∈C,i≤ j
noncomputable def accepted {n : ℕ} (owner : Point n→Point n) (a : Point n) (P : Partition n) :=
  P.filter (touches owner a)
noncomputable def owned {n : ℕ} (owner : Point n→Point n) (a : Point n) (P : Partition n) :=
  P.filter (holds owner a)
abbrev Pick (n : ℕ) := Point n→Partition n
noncomputable def compatible {n : ℕ} (owner : Point n→Point n) (a b : Point n) (P Q : Partition n) : Prop :=
  ∀C∈accepted owner a P,∀D∈accepted owner b Q,(C∩D).Nonempty → C=D
noncomputable def valid (x : World) (W : Cluster x.n) (R : ℝ) (h : ℕ) (P : Pick x.n) : Prop :=
  (∀a∈greedyNet x.dist R W,P a∈traceMenu x h (window x.dist W R a)) ∧
  ∀a b : ↥(greedyNet x.dist R W),(interactionGraph x.dist R W).Adj a b →
    compatible (anchor x.dist W R) a b (P a) (P b)
noncomputable def output (x : World) (W : Cluster x.n) (R : ℝ) (P : Pick x.n) : Partition x.n :=
  (greedyNet x.dist R W).biUnion (fun a=>owned (anchor x.dist W R) a (P a))
noncomputable def number (x : World) (W : Cluster x.n) (R : ℝ) (P : Pick x.n) : ℕ :=
  ∑a ∈ greedyNet x.dist R W,(owned (anchor x.dist W R) a (P a)).card
noncomputable def price (x : World) (W : Cluster x.n) (R : ℝ) (P : Pick x.n) : ℝ :=
  ∑a ∈ greedyNet x.dist R W,cost x.dist (owned (anchor x.dist W R) a (P a))
def sceneBase (x : World) (s : ℕ) := 3+s*(x.n+2)
noncomputable def scale (x : World) (s : ℕ) :=
  MinSumFPT.oracleAnswer x.dist (x.mem (sceneBase x s)) (x.mem (sceneBase x s+1))
def label (x : World) (s : ℕ) (i : Point x.n) := x.mem (sceneBase x s+2+i.val)
noncomputable def regions (x : World) (s : ℕ) : Partition x.n :=
  Finset.univ.image (fun i=>Finset.univ.filter (fun j=>label x s j=label x s i))
def sceneSpec (e : ℚ) (a b : ℕ) (cmd : Cmd) (n k : ℕ) (d : Point n→Point n→ℝ) : Prop :=
  ∃s z H, Executes d cmd (initialStore n k) s z ∧ z≤ a*n^(b*parameterEnvelope (e:ℝ)) ∧
    H≤ a*n^(b*parameterEnvelope (e:ℝ)) ∧
    let x:=worldOf k H d s
    Ready x s ∧ ∀O,Stable d k (1+(e:ℝ)) O → fewBound (e:ℝ)<(largeClusters d O (e:ℝ)).card →
      ∃u< H,0< scale x u ∧ scale x u=largestRadius d O ∧
        ∀W∈regions x u,Aligned O W ∧ diameter d W≤ densityScale d O (e:ℝ)
def searchSpec (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀(x : World) (s : Store),1≤ x.k → x.k< x.n → IsMetricArray x.dist → Ready x s →
    ∃t z H, Executes x.dist cmd s t z ∧ z≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      H≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      let y:=worldOf x.k H x.dist t
      Ready y t ∧ endpoints y ∧ ∀u< x.rows,0< scale x u →
        (∀W∈regions x u,RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist (scale x u) W)
          (widthBound (e:ℝ))) →
        ∀P : Cluster x.n→Pick x.n,(∀W∈regions x u,valid x W (scale x u) (budget (e:ℝ)) (P W)) →
        (∑W ∈ regions x u,number x W (scale x u) (P W))=x.k →
        ∃r< H,good y r ∧ score y r≤∑W ∈ regions x u,price x W (scale x u) (P W)
def originalRows (x : World) := (x.mem 0).toNat
def tableSlots (x : World) := originalRows x+1
noncomputable def unaryField (x : World) (r j : ℕ) (b : Bool) : ℤ :=
  let m:=tableSlots x
  if r=0 then (m:ℤ)
  else if r≤ m+m then ∑i ∈ Finset.range x.rows,
    if i< originalRows x ∧ m+(i+2)=r then RegionalBallDP.field x i j b else 0
  else if r≤ m+m+m then (x.k:ℤ)
  else if b then ∑q ∈ Finset.range x.rows, if m+m+m+q=r then (q:ℤ) else 0
  else 1
end StableMSR.Recovery.WindowCSP


