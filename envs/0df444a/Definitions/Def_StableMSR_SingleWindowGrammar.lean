-- Prove2me | Definitions.Def_StableMSR_SingleWindowGrammar
-- name    : StableMSR_SingleWindowGrammar
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T23:59:36.436083+00:00
-- url     : https://prove2.me/theorems/0e7026d9-f68d-4e19-aeab-f7d876911ab2
-- title:
--   The exact projection of the single-vertex grammar onto owned window blocks
-- statement:
--   The exact projection of the single-vertex grammar onto owned window blocks, and its native RAM interface.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleVertexSearch
import Definitions.Def_StableMSR_WindowBlockMasks
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowProfiles (piece keys)
namespace StableMSR.Recovery.SingleWindows
abbrev Vertex (x : World) (W : Cluster x.n) (R : ℝ) := ↥(Supplement.greedyNet x.dist R W)
noncomputable def domains (x : World) (W : Cluster x.n) (R : ℝ) (h : ℕ) (a : Vertex x W R) :=
  RegionalSeeds.traceMenu x h (window x.dist W R a)
noncomputable def constraint (x : World) (W : Cluster x.n) (R : ℝ) (a b : Vertex x W R) :=
  compatible (anchor x.dist W R) a b
noncomputable def project (x : World) (W : Cluster x.n) (R : ℝ) (O : Finset (Vertex x W R × Partition x.n)) :=
  O.biUnion fun z=>owned (anchor x.dist W R) z.1 z.2
noncomputable def generates (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ) (P : Partition x.n) :=
  ∃O,SingleSearch.root (Supplement.interactionGraph x.dist R W) (domains x W R h) (constraint x W R) w (fun _=>∅) O ∧ project x W R O=P
/-- Physical recognition of the singleton grammar. The order of a root trace is free. Invalid region slots use an empty literal, and nonpositive scales have no productions at live roots. -/
structure Implements (x : World) (e : ℚ) (y : World) : Prop where
  space : room y
  scenes : y.mem 1=(x.rows:ℤ)
  roots : ∀u< x.rows,∀i< x.n,let B:=board y;let p:=B.root (u*x.n+i)
    let F:=WindowMasks.block {x with k:=y.k,rows:=y.rows,mem:=y.mem}
    u*x.n+i< B.size ∧ p< B.size ∧
    (i∉keys x u → ∀L,WindowMasks.Trace B F p L ↔ L=[]) ∧
    (i∈keys x u → scale x u≤0 → ∀L,¬WindowMasks.Trace B F p L) ∧
    (i∈keys x u → 0< scale x u →
      let gen:=generates x (piece x u i) (scale x u) (budget (e:ℝ)) (widthBound (e:ℝ))
      (∀L,WindowMasks.Trace B F p L → L.Nodup ∧ gen L.toFinset) ∧
      ∀Q,gen Q → ∃L,WindowMasks.Trace B F p L ∧ L.toFinset=Q)
def nativeSpec (e : ℚ) (c D b : ℕ) (cmd : Cmd) :=
  ∀(x : World) (s : Store),1≤ x.k → x.k< x.n → IsMetricArray x.dist → Ready x s →
    ∃t z H,Executes x.dist cmd s t z ∧ z≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      H≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧ Ready (worldOf x.k H x.dist t) t ∧ Implements x e (worldOf x.k H x.dist t)
end StableMSR.Recovery.SingleWindows


