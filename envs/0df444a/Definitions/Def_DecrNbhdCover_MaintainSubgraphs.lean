-- Prove2me | Definitions.Def_DecrNbhdCover_MaintainSubgraphs
-- name    : DecrNbhdCover_MaintainSubgraphs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:12.424395+00:00
-- url     : https://prove2.me/theorems/94948697-c036-410b-a6f3-80d6ef435803
-- title:
--   The MaintainSubgraphs problem (Definition 3.12)
-- statement:
--   The input has a decremental graph $G$, a partial $(\epsilon,d,D)$-emulator $H$ for $G$, and $\mu>0$ such that the maximum degree of $G$ is at most $\mu$ and the dynamic degree bound of $H$ is $\mu$, together with a dynamic collection $\mathcal C$ of clusters of $G$. New clusters may be inserted at any time with the list of their vertices, and a cluster then only undergoes vertex deletions, given as pairs $(v,C)$.
--
--   The algorithm must maintain, for every $C\in\mathcal C$, the graphs $G[C]$ and $H_C$.
--
--   This is the bookkeeping that lets all subroutines run on $G[C]$ and $H_C$.
--
--   **Formalization Note** "Maintain" is a reported change log of the two edge sets, one edge per report. $H_C$ is determined by its edges and $C$.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Definition 3.12, p.20 (PDF 24)

import Mathlib
import Definitions.Def_DecrNbhdCover_Emulator
import Definitions.Def_DecrNbhdCover_Streams
import Definitions.Def_DecrNbhdCover_Session

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC

/-! # The MaintainSubgraphs problem (Definition 3.12)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Definition 3.12, p.20.

**Formalization Note.** An update step carries at most one update of `G`, updates of `H`, and changes to the collection: a new cluster with the list of its vertices (it gets the next cluster number), and a vertex deletion `(v, C)`.
"Maintain" reads as reporting the change log of the two edge sets, one edge per report: `0, C, e` adds `e` to the copy of `G[C]`, `1, C, e` removes it, `2, C, f` adds `f` to the copy of `H_C`, `3, C, f` removes it. `H_C` is determined by its edges and `C`, since
its supernodes are the endpoints of its edges. After every step, the copies equal `E(G[C])` and `E(H_C)` for every cluster. The time bound of Claim 3.13 pays for these reports. -/

/-- A report on the maintained copies. -/
inductive SubgraphReport where
  | addG (c e : ℕ)
  | delG (c e : ℕ)
  | addH (c f : ℕ)
  | delH (c f : ℕ)

/-- The words of a report. -/
def SubgraphReport.words : SubgraphReport → List ℕ
  | .addG c e => [0, c, e]
  | .delG c e => [1, c, e]
  | .addH c f => [2, c, f]
  | .delH c f => [3, c, f]

/-- The copies of `E(G[C])` and `E(H_C)` for each cluster number `C`. -/
structure SubgraphState where
  gc : ℕ → Finset ℕ
  hc : ℕ → Finset ℕ

/-- The effect of a report. -/
def subgraphStep (s : SubgraphState) : SubgraphReport → Option SubgraphState
  | .addG c e => some { s with gc := Function.update s.gc c (insert e (s.gc c)) }
  | .delG c e => some { s with gc := Function.update s.gc c ((s.gc c).erase e) }
  | .addH c f => some { s with hc := Function.update s.hc c (insert f (s.hc c)) }
  | .delH c f => some { s with hc := Function.update s.hc c ((s.hc c).erase f) }

/-- A change to the collection of clusters. -/
inductive ClusterUpdate where
  | new (vs : List ℕ)
  | del (v c : ℕ)

/-- The words of a change. -/
def ClusterUpdate.words : ClusterUpdate → List ℕ
  | .new vs => 0 :: vs.length :: vs
  | .del v c => [1, v, c]

/-- The collection of clusters, numbered in order of insertion. -/
def applyClusterUpdate (l : List (Set ℕ)) : ClusterUpdate → List (Set ℕ)
  | .new vs => l ++ [{v | v ∈ vs}]
  | .del v c => l.set c ((l.getD c ∅) \ {v})

/-- A nonempty step of updates. There are no queries in this problem. -/
structure SubgraphOp where
  gs : List GUpdate
  hs : List HUpdate
  cs : List ClusterUpdate

/-- The words of a step. -/
def SubgraphOp.words (o : SubgraphOp) : List ℕ :=
  batchWords o.gs o.hs ++ o.cs.length :: o.cs.flatMap ClusterUpdate.words

/-- The protocol of MaintainSubgraphs. -/
def subgraphProtocol : Protocol SubgraphOp SubgraphReport SubgraphState where
  opWords := SubgraphOp.words
  isQuery := fun _ => false
  enc := SubgraphReport.words
  step := subgraphStep
  st₀ := ⟨fun _ => ∅, fun _ => ∅⟩

/-- The input of the MaintainSubgraphs problem. `C₀` lists the initial clusters. The parameters `ϵ`, `d`, `D` of the emulator are not given to the program. -/
structure SubgraphInput where
  n : ℕ
  mu : ℕ
  edges : List (ℕ × ℕ × ℕ)
  h₀ : List (List (ℕ × ℕ))
  C₀ : List (List ℕ)

namespace SubgraphInput

variable (I : SubgraphInput)

/-- The initialization words. -/
def words : List ℕ :=
  [I.n, I.mu] ++ edgeWords I.edges ++ hInitWords I.h₀ ++
    I.C₀.length :: I.C₀.flatMap (fun vs => vs.length :: vs)

/-- `G` after the first `t` steps. -/
def Gt (σ : List SubgraphOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map SubgraphOp.gs) t

/-- `H` after the first `t` steps. -/
noncomputable def Ht (σ : List SubgraphOp) (t : ℕ) : HState :=
  hAt (hInit I.n I.h₀) (σ.map SubgraphOp.hs) t

/-- The clusters after the first `t` steps. -/
def Ct (σ : List SubgraphOp) (t : ℕ) : List (Set ℕ) :=
  ((σ.take t).flatMap SubgraphOp.cs).foldl applyClusterUpdate (I.C₀.map (fun vs => {v | v ∈ vs}))

/-- A change to the collection is valid: a new cluster is nonempty with no repeated vertex, a deleted vertex lies in its cluster. -/
def clusterUpdateOk (l : List (Set ℕ)) : ClusterUpdate → Prop
  | .new vs => vs ≠ [] ∧ vs.Nodup
  | .del v c => c < l.length ∧ v ∈ l.getD c ∅

/-- Each change of a list is valid when it arrives. -/
def clusterUpdatesOk : List (Set ℕ) → List ClusterUpdate → Prop
  | _, [] => True
  | l, u :: us => clusterUpdateOk l u ∧ clusterUpdatesOk (applyClusterUpdate l u) us

/-- The conditions of Definition 3.12 that do not concern the update stream. -/
structure Ok : Prop where
  n_pos : 1 ≤ I.n
  mu_pos : 0 < I.mu
  edges_ok : EdgesOk I.n I.edges
  deg : (ofEdges I.n I.edges).DegLe I.mu
  h_ok : hInitOk I.n I.h₀
  C_ok : ∀ vs ∈ I.C₀, vs ≠ [] ∧ vs.Nodup

/-- The promise on the input stream, for the emulator parameters `ϵ, d, D`: each step is nonempty and has at most one update of `G`, all updates are valid, clusters stay inside `V(G)`, `H` is a partial `(ϵ, d, D)`-emulator for `G` with dynamic degree bound `μ`, and at most `N` clusters ever contain a single
vertex. -/
structure Promise (eps : ℝ) (d : ℕ) (D : ℝ) (N : ℕ) (σ : List SubgraphOp) : Prop where
  steps : ∀ (t : ℕ) (o : SubgraphOp), σ[t]? = some o →
    o.gs.length ≤ 1 ∧ (o.gs ≠ [] ∨ o.hs ≠ [] ∨ o.cs ≠ []) ∧ gsOk (I.Gt σ t) o.gs ∧
      hsOk (I.Ht σ t) o.hs ∧ clusterUpdatesOk (I.Ct σ t) o.cs
  C_sub : ∀ t ≤ σ.length, ∀ C ∈ I.Ct σ t, C ⊆ (I.Gt σ t).V
  partial' : ∀ t ≤ σ.length, IsPartial (I.Gt σ t) (I.Ht σ t).g eps d D
  deg : (I.Ht σ σ.length).EverDegLe I.mu
  N_bound : ∀ v, (I.C₀.countP (fun vs => decide (v ∈ vs)) +
    (σ.flatMap SubgraphOp.cs).countP (fun u => match u with
      | .new vs => decide (v ∈ vs)
      | .del _ _ => false)) ≤ N

end SubgraphInput

/-- The clauses of MaintainSubgraphs with the time bound `Õ(n·N·μ)` of Claim 3.13. -/
structure SubgraphHolds (C W : ℕ) (P : Program) (I : SubgraphInput) (N : ℕ) (σ : List SubgraphOp) : Prop where
  runs : RunsThrough W P (subgraphProtocol.blocks I.words σ)
  /-- After initialization and after every step, for every cluster `C`, the copies are the edges of `G[C]` and of `H_C`. -/
  log : ∀ t ≤ σ.length, ∃ s, subgraphProtocol.state W P I.words σ t = some s ∧
    ∀ (c : ℕ) (C' : Set ℕ), (I.Ct σ t)[c]? = some C' →
      ((s.gc c : Finset ℕ) : Set ℕ) = ((I.Gt σ t).induced C').E ∧
      ((s.hc c : Finset ℕ) : Set ℕ) = ((I.Ht σ t).g.assocSub C').E
  /-- The total update time. -/
  time : (subgraphProtocol.updateTime W P I.words σ : ℝ) ≤
    polylog C I.n I.edges.length * ((I.n : ℝ) * (N : ℝ) * (I.mu : ℝ))

end DecrNbhdCover


