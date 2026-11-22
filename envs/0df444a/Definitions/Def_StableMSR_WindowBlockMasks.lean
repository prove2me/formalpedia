-- Prove2me | Definitions.Def_StableMSR_WindowBlockMasks
-- name    : StableMSR_WindowBlockMasks
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T23:23:27.687478+00:00
-- url     : https://prove2.me/theorems/f5273de0-8914-4dd3-a99d-91fd23293d8c
-- title:
--   Regional separator programs with unpriced cluster membership leaves
-- statement:
--   A literal contains only a membership bit for each point. A nonempty block emits itself and an empty block emits no cluster. Binary matches concatenate the lists of blocks. Correct regional descriptions require disjoint covering traces and a trace for every valid window partition. There are no distance weights, chosen centers, counts or minimizers in this input contract.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowPorts
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowProfiles (piece keys subR)
open StableMSR.Recovery.RegionalBallDP (Word field)
open StableMSR.Recovery.Supplement (interactionGraph)
namespace StableMSR.Recovery.WindowMasks
def marked (x : World) (q i : ℕ) := 0< x.mem (addr x.k (1+4*rawSize x) 0+q*x.n+i)
noncomputable def block (x : World) (q : ℕ) : Cluster x.n := Finset.univ.filter (fun i=>marked x q i.val)
noncomputable def chargeCount (x : World) (q : ℕ) : ℕ := if ∃i< x.n,marked x q i then 1 else 0
noncomputable def ballPair (x : World) (q a b : ℕ) := marked x q a ∧ marked x q b ∧
  ∀i< x.n,marked x q i → FewBallRows.distAt x a i≤ FewBallRows.distAt x a b
noncomputable def cheapest (x : World) (q a b : ℕ) := ballPair x q a b ∧
  ∀i< x.n,∀j< x.n,ballPair x q i j → FewBallRows.distAt x a b≤ FewBallRows.distAt x i j
noncomputable def chosen (x : World) (q : ℕ) := first x.n (fun a=>∃b< x.n,cheapest x q a b)
noncomputable def farthest (x : World) (q : ℕ) := first x.n (fun b=>cheapest x q (chosen x q).toNat b)
noncomputable def oneWord (x : World) (q : ℕ) : Word := fun j s=>
  if j=0 then (if s then farthest x q else chosen x q) else 0
noncomputable def withBlocks (x : World) : Board :=
  {board x with arity:=chargeCount x,value:=oneWord x}
noncomputable def emit {n : ℕ} (C : Cluster n) : List (Cluster n) := if C.Nonempty then [C] else []
inductive Trace {n : ℕ} (B : Board) (F : ℕ→Cluster n) : ℕ→List (Cluster n)→Prop where
  | literal {q p} : initial B q p → Trace B F p (emit (F q))
  | fork {q r p L R} : port B 1 q p → port B 2 r p → Trace B F (B.child q) L →
      Trace B F (B.child r) R → Trace B F p (L++R)
def support {n : ℕ} (L : List (Cluster n)) := L.toFinset.biUnion id
noncomputable def payment {n : ℕ} (d : Point n→Point n→ℝ) (L : List (Cluster n)) :=
  (L.map (radius d)).sum
noncomputable def normalized (x : World) (r j : ℕ) (s : Bool) : ℤ :=
  let m:=rawSize x
  if r=0 then (if s then x.mem 1 else (m:ℤ))
  else if 1+m≤ r ∧ r<1+2*m then (if s then (chargeCount x (subR x r (1+m)):ℤ) else field x r j s)
  else if 1+2*m≤ r ∧ r<1+3*m then oneWord x (subR x r (1+2*m)) j s
  else field x r j s
structure Describes (x : World) (e : ℚ) (y : World) : Prop where
  space : room y
  scenes : y.mem 1=(x.rows:ℤ)
  targets : ∀u< x.rows,∀i< x.n,let B:=board y;let p:=B.root (u*x.n+i)
    u*x.n+i< B.size ∧ p< B.size ∧
    (∀L,Trace B (block {x with k:=y.k,rows:=y.rows,mem:=y.mem}) p L → L.Pairwise Disjoint ∧ support L=piece x u i) ∧
    (i∉keys x u → Trace B (block {x with k:=y.k,rows:=y.rows,mem:=y.mem}) p []) ∧
    (i∈keys x u → 0< scale x u →
      RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist (scale x u) (piece x u i)) (widthBound (e:ℝ)) →
      ∀P : Pick x.n,valid x (piece x u i) (scale x u) (budget (e:ℝ)) P →
        number x (piece x u i) (scale x u) P≤ x.k →
        ∃L,Trace B (block {x with k:=y.k,rows:=y.rows,mem:=y.mem}) p L ∧ L.toFinset=WindowCSP.output x (piece x u i) (scale x u) P)
def maskSpec (e : ℚ) (c D b : ℕ) (cmd : Cmd) :=
  ∀(x : World) (s : Store),1≤ x.k → x.k< x.n → IsMetricArray x.dist → Ready x s →
   ∃t z H,Executes x.dist cmd s t z ∧ z≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    H≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧ Ready (worldOf x.k H x.dist t) t ∧ Describes x e (worldOf x.k H x.dist t)
end StableMSR.Recovery.WindowMasks


