-- Prove2me | Definitions.Def_DynEdgeColorLLL_Main_EdgeReadout
-- name    : DynEdgeColorLLL_Main_EdgeReadout
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:43.563124+00:00
-- url     : https://prove2.me/theorems/ed85782d-eb9c-4156-aa3a-5ffd0b2c3bef
-- title:
--   The explicit edge colouring and edge partition a program writes, proper edge colourings, and partition recourse
-- statement:
--   The programs of this mission run on the published randomized word RAM (`DynBrooks_Machine`) under the published dynamic-graph protocol (`DynColorWC_Main_Model`). The graph on the vertex set $\{0,\dots,n-1\}$ starts empty, and each legal update inserts a non-edge or deletes an edge. What a program maintains is read off the words it writes, never off the graph.
--
--   The output is read three words at a time, $u, v, q$, meaning "the edge $\{u,v\}$ now carries the label $q$". A triple with $u\ge n$ or $v\ge n$ is ignored, as is an incomplete trailing group. Starting from the all-$0$ labelling and applying every triple written up to the completed state after the first $t$ updates gives the labelling $\chi_t$. Label $0$ is outside every palette and every part range, so every present edge must have been written explicitly.
--
--   A labelling $\chi$ is a **proper edge colouring of $G$ with colours in $\{1,\dots,K\}$** when every edge $e$ of $G$ has $1\le\chi(e)\le K$ and any two distinct edges of $G$ sharing a vertex get different colours. Non-edges are unconstrained.
--
--   Read as a partition, $\chi$ splits $G$ into the subgraphs $G_j=\{e\in E(G):\chi(e)=j\}$. It is an **$F$-partition of maximum degree at most $b$** when every edge has a label in $\{1,\dots,F\}$ and every vertex has at most $b$ incident edges in each $G_j$. The **recourse** of update $t$ is the number of edge membership changes across the subgraphs,
--   $$\sum_{j=1}^{F}\bigl|E(G_j^{(t)})\,\triangle\,E(G_j^{(t+1)})\bigr|,$$
--   comparing the written partitions before and after the update.
--
--   These readouts state Theorems 1, 3, 4 and Lemmas 8 and 9 on the program's actual output.
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Theorem 1, printed p. 1 (PDF p. 3); Lemma 8, printed p. 20 (PDF p. 22); readout modelled on DynColorWC.Main.applyColorLog (published DynColorWC_Main_Model)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynColorWC_Main_Model

namespace DynEdgeColorLLL.Main

/-! # The explicit edge colouring and the explicit edge partition a program writes

Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Theorem 1, printed p. 1
(PDF p. 3); Lemma 8, printed p. 20 (PDF p. 22).

The machine, the update protocol, the legal update sequences from the empty graph, the completed
states `stateAt` and the per-update step counts `updateTime` are the published
`DynBrooks_Machine`, `DynBrooks_Protocol` and `DynColorWC_Main_Model`. What the program maintains
is read off the words it writes: the output is read three words at a time, `u, v, q`, meaning
"the edge `{u, v}` gets the label `q`" (a colour for Theorem 1, a part index for Lemma 8). A triple
whose `u` or `v` is not a vertex is ignored, as is an incomplete trailing group. Labels start at
`0`, which is outside every palette and every part range, so every present edge must have been
written explicitly. -/

/-- Apply a change log of triples `u, v, q` ("label of `{u, v}` := `q`") in order. A triple whose
`u` or `v` is not a vertex is ignored, as is an incomplete trailing group. -/
def applyEdgeColorLog {n : ℕ} : (Sym2 (Fin n) → ℕ) → List ℕ → (Sym2 (Fin n) → ℕ)
  | χ, u :: v :: q :: rest =>
      applyEdgeColorLog
        (if h : u < n ∧ v < n then Function.update χ s(⟨u, h.1⟩, ⟨v, h.2⟩) q else χ) rest
  | χ, _ => χ

/-- The explicit edge labelling after the first `t` updates: the all-`0` labelling with every
triple the machine has written up to that completed state applied in order. -/
noncomputable def edgeColorAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : Sym2 (Fin n) → ℕ :=
  applyEdgeColorLog (fun _ => 0) (DynColorWC.Main.outputAt P ω inp σ t)

/-- A proper edge colouring of `G` with colours in `{1, …, K}`: every edge of `G` has a colour in
`{1, …, K}`, and two distinct edges of `G` sharing a vertex have different colours. Non-edges are
unconstrained. -/
def IsProperEdgeColoring {n : ℕ} (K : ℕ) (G : SimpleGraph (Fin n)) (χ : Sym2 (Fin n) → ℕ) :
    Prop :=
  (∀ e ∈ G.edgeSet, 1 ≤ χ e ∧ χ e ≤ K) ∧
    ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f → ∀ v : Fin n, v ∈ e → v ∈ f → χ e ≠ χ f

/-- The edges of `G` labelled `j` by `χ`: the edge set of the `j`-th subgraph. -/
def partEdges {n : ℕ} (G : SimpleGraph (Fin n)) (χ : Sym2 (Fin n) → ℕ) (j : ℕ) :
    Set (Sym2 (Fin n)) :=
  {e | e ∈ G.edgeSet ∧ χ e = j}

/-- The degree of `v` in the `j`-th subgraph. -/
noncomputable def partDegree {n : ℕ} (G : SimpleGraph (Fin n)) (χ : Sym2 (Fin n) → ℕ) (j : ℕ)
    (v : Fin n) : ℕ :=
  Set.ncard {e | e ∈ partEdges G χ j ∧ v ∈ e}

/-- `χ` partitions `G` into the `F` subgraphs `1, …, F`, each of maximum degree at most `b`: every
edge of `G` has a label in `{1, …, F}`, and every vertex has at most `b` incident edges of each
label. -/
def IsDegreeBoundedPartition {n : ℕ} (F : ℕ) (b : ℝ) (G : SimpleGraph (Fin n))
    (χ : Sym2 (Fin n) → ℕ) : Prop :=
  (∀ e ∈ G.edgeSet, 1 ≤ χ e ∧ χ e ≤ F) ∧
    ∀ j ∈ Finset.Icc 1 F, ∀ v : Fin n, (partDegree G χ j v : ℝ) ≤ b

/-- The edge membership changes across the subgraphs `1, …, F` between two moments: for each part
`j`, the number of edges that enter or leave the `j`-th subgraph, summed over `j`. -/
noncomputable def membershipChanges {n : ℕ} (F : ℕ) (G : SimpleGraph (Fin n))
    (χ : Sym2 (Fin n) → ℕ) (G' : SimpleGraph (Fin n)) (χ' : Sym2 (Fin n) → ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 F, Set.ncard (symmDiff (partEdges G χ j) (partEdges G' χ' j))

/-- The recourse of update `t` (0-based) of a partition program: the edge membership changes
between the written partition before update `t` and the written partition after it. -/
noncomputable def partRecourse (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    (F : ℕ) {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : ℕ :=
  membershipChanges F (DynColorWC.Main.graphAt σ t) (edgeColorAt P ω inp σ t)
    (DynColorWC.Main.graphAt σ (t + 1)) (edgeColorAt P ω inp σ (t + 1))

end DynEdgeColorLLL.Main


