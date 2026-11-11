-- Prove2me | Definitions.Def_LabelConnected_Treewidth_Encoding
-- name    : LabelConnected_Treewidth_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:28:03.288137+00:00
-- url     : https://prove2.me/theorems/a00f8bc0-7e92-4d90-a9fc-f79e8c39c705
-- title:
--   Inputs and outputs on the word RAM: edge-index lists, labelings, witnesses and the Gossiping output
-- statement:
--   All algorithms run on the published unit-cost integer RAM (`CongruencyTU`), deterministically, with registers of $O(\log(n+m))$ bits. A multigraph with vertices $0, \dots, n-1$ and edges $e_1, \dots, e_m$ is the input
--   $$[\,n,\ m,\ u_1, v_1,\ \dots,\ u_m, v_m\,],$$
--   $e_i$ joining $u_i$ and $v_i$; edge $e_i$ is referred to by its index $i - 1$. An edge set is written as its size followed by its indices, each once, in any order. A labeling is written $[\lambda(e_1), \dots, \lambda(e_m)]$.
--
--   * Gossiping output: $[1, \lambda(e_1), \dots, \lambda(e_m)]$ with $\lambda$ a temporal labeling making $G$ temporally connected, if $G$ is a yes-instance; $[0]$ otherwise.
--   * Witness inputs: the graph, then tag $0$ and the two trees of a T-witness, or tag $1$ and $E(C), F_1, F_2$ of an M-witness; or the graph followed by three edge sets $C, D_1, D_2$.
--   * M-witness output: $E(C), F_1, F_2$ of an M-witness of $G$.
--
--   **Formalization Note.** `encIdx`, `ListsSet`, `encLabels`, `IsConnectingLabelingOutput`, `IsGossipingOutput`, `encTWitnessInput`, `encMWitnessInput`, `encThreeSetsInput`, `IsMWitnessOutput`; the graph encoding is the published `MinDegST.AddOne.encGraph`.
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), §2, p. 8, Complexity and Computational Model; §1, p. 2, Gossiping

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_LabelConnected_Treewidth_Multigraph
import Definitions.Def_LabelConnected_Treewidth_Temporal
import Definitions.Def_LabelConnected_Treewidth_Witnesses

open Classical

namespace LabelConnected.Treewidth

/-! # Inputs and outputs of the algorithms on the word RAM

Klasing, Mertzios, Molter, Morawietz, Spirakis, *Recognizing Label-Connected Graphs*,
arXiv:2611.05144 (PDF sha256 8dde27a5…), §2, p. 8: "Running times use the word RAM model with
Θ(log(n+m))-bit words."

**Formalization Note.** The machine is the published integer RAM `CongruencyTU.Program`, run
deterministically, with the published `MinDegST.AddOne.Deterministic`, `WordBounded` (every register
at every step within `W · (1 + log₂(2 + (n + m)))` bits) and `HaltsWithin` (halts within the cost
bound with an output meeting the specification). A multigraph `G` with vertices `Fin n` and edges
`e₁, …, e_m` is the list `es` of endpoint pairs and is given as `MinDegST.AddOne.encGraph n es =
[n, m, u₁, v₁, …, u_m, v_m]`; loops are pairs `(u, u)` and parallel edges repeated pairs. Edge `eᵢ`
is referred to by its index `i − 1 ∈ {0, …, m − 1}`. An edge set is given as a list of indices
preceded by its length (`encIdx`), each edge once, in any order. A labeling is output as
`[λ(e₁), …, λ(e_m)]`. -/

variable {n : ℕ}

/-- A list of edge indices preceded by its length: `[|l|, i₁, i₂, …]`. -/
def encIdx {m : ℕ} (l : List (Fin m)) : List ℤ :=
  (l.length : ℤ) :: l.map fun e => (e.val : ℤ)

/-- The list `l` lists the set `S`, each element once, in any order. -/
def ListsSet {α : Type} (l : List α) (S : Finset α) : Prop :=
  l.Nodup ∧ l.toFinset = S

/-- A labeling of the edges `e₁, …, e_m` as the list `[λ(e₁), …, λ(e_m)]`. -/
def encLabels {m : ℕ} (lab : Fin m → ℕ) : List ℤ :=
  (List.finRange m).map fun e => (lab e : ℤ)

/-- The output is `[λ(e₁), …, λ(e_m)]` for a temporal labeling `λ` under which `G` is temporally
connected. -/
def IsConnectingLabelingOutput (es : List (Fin n × Fin n)) (out : List ℤ) : Prop :=
  ∃ lab : Fin es.length → ℕ, IsTemporalLabeling lab ∧ TemporallyConnected (ofList es) lab ∧
    out = encLabels lab

/-- The output of Gossiping: `[1, λ(e₁), …, λ(e_m)]` with `λ` a temporal labeling under which `G` is
temporally connected, if `G` is a yes-instance; `[0]` if it is not. -/
def IsGossipingOutput (es : List (Fin n × Fin n)) (out : List ℤ) : Prop :=
  (IsLabelConnected (ofList es) ∧
    ∃ lab : Fin es.length → ℕ, IsTemporalLabeling lab ∧ TemporallyConnected (ofList es) lab ∧
      out = 1 :: encLabels lab) ∨
  (¬ IsLabelConnected (ofList es) ∧ out = [0])

/-- Input of a graph with a T-witness: the graph, the tag `0`, then the two trees. -/
def encTWitnessInput (n : ℕ) (es : List (Fin n × Fin n)) (l₁ l₂ : List (Fin es.length)) :
    List ℤ :=
  MinDegST.AddOne.encGraph n es ++ [0] ++ encIdx l₁ ++ encIdx l₂

/-- Input of a graph with an M-witness: the graph, the tag `1`, then the cycle's edge set and the
two forests. -/
def encMWitnessInput (n : ℕ) (es : List (Fin n × Fin n)) (lC l₁ l₂ : List (Fin es.length)) :
    List ℤ :=
  MinDegST.AddOne.encGraph n es ++ [1] ++ encIdx lC ++ encIdx l₁ ++ encIdx l₂

/-- Input of a graph with three edge sets `C, D₁, D₂`. -/
def encThreeSetsInput (n : ℕ) (es : List (Fin n × Fin n)) (lC l₁ l₂ : List (Fin es.length)) :
    List ℤ :=
  MinDegST.AddOne.encGraph n es ++ encIdx lC ++ encIdx l₁ ++ encIdx l₂

/-- The output lists an M-witness `(C, F₁, F₂)` of `G`: `E(C)`, `F₁`, `F₂`, each as `encIdx`. -/
def IsMWitnessOutput (es : List (Fin n × Fin n)) (out : List ℤ) : Prop :=
  ∃ (c : Cycle (ofList es)) (F₁ F₂ : Finset (Fin es.length)) (lC l₁ l₂ : List (Fin es.length)),
    IsMWitness (ofList es) c F₁ F₂ ∧ ListsSet lC c.edgeSet ∧ ListsSet l₁ F₁ ∧ ListsSet l₂ F₂ ∧
    out = encIdx lC ++ encIdx l₁ ++ encIdx l₂

end LabelConnected.Treewidth


