-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:46:25.505364+00:00
-- url     : https://prove2.me/theorems/9788d75f-84c9-44d4-8841-1662ffd4cc4a
-- title:
--   Single-cell diagrams, word diagrams, and boundary summaries of finite-path networks
-- statement:
--   Fix $m\in\mathbb N$ and let $[m]=\{0,\dots,m-1\}$ be a set of state labels. Relations are composed in path order, $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$; $\mathrm{Id}$ is the identity relation and $R^*$ the reflexive–transitive closure. A boundary diagram is a quadruple $a=(F_a,B_a,L_a,R_a)$ of relations on $[m]$ (traversals entering left and leaving right, entering right and leaving left, entering and leaving left, entering and leaving right). Diagrams form a monoid with identity $(\mathrm{Id},\mathrm{Id},\emptyset,\emptyset)$ and product
--   $$ab=\Big(F_a(L_bR_a)^*F_b,\ \ B_b(R_aL_b)^*B_a,\ \ L_a\cup F_a(L_bR_a)^*L_bB_a,\ \ R_b\cup B_bR_a(L_bR_a)^*F_b\Big).$$
--
--   1. **Cell diagram.** For relations $M_1$ (stay), $M_2$ (move right) and $M_0$ (move left) on $[m]$,
--   $$\mathrm{cell}(M_1,M_2,M_0)=\big(M_1^*M_2,\ M_1^*M_0,\ M_1^*M_0,\ M_1^*M_2\big):$$
--   a head that enters the cell from either side performs finitely many stays and then leaves to the right or to the left.
--   2. **Word diagram.** For an assignment $d$ of a diagram to each letter of an alphabet $\Sigma$ and a word $w=a_1\cdots a_n$, $\tau_d(w)=d(a_1)d(a_2)\cdots d(a_n)$, the product in input order; the empty word gives the identity diagram.
--   3. **Networks.** A network with vertex set $V$ consists of an internal edge relation $E\subseteq V\times V$, entrance relations $I_{\mathrm l},I_{\mathrm r}\subseteq[m]\times V$ at the left and right boundary, and exit relations $O_{\mathrm l},O_{\mathrm r}\subseteq V\times[m]$ at the left and right boundary.
--   4. **Summary.** The summary of a network $N$ is the diagram of all finite internal paths between boundary labels,
--   $$\mathrm{sum}(N)=\big(I_{\mathrm l}E^*O_{\mathrm r},\ I_{\mathrm r}E^*O_{\mathrm l},\ I_{\mathrm l}E^*O_{\mathrm l},\ I_{\mathrm r}E^*O_{\mathrm r}\big).$$
--   5. **Join.** For networks $N=(E,I_{\mathrm l},I_{\mathrm r},O_{\mathrm l},O_{\mathrm r})$ on $V$ and $N'=(E',I'_{\mathrm l},I'_{\mathrm r},O'_{\mathrm l},O'_{\mathrm r})$ on $W$, the join $N\bowtie N'$ has vertex set $V\sqcup W$ and edge relation the block relation $\begin{bmatrix}E&O_{\mathrm r}I'_{\mathrm l}\\ O'_{\mathrm l}I_{\mathrm r}&E'\end{bmatrix}$: besides the internal edges of each part, there is an edge from $v\in V$ to $w\in W$ whenever $N$ can exit on the right from $v$ with a label at which $N'$ is entered on the left at $w$, and symmetrically from $W$ to $V$. Its left entrances and exits are those of $N$ (on $V$) and its right entrances and exits are those of $N'$ (on $W$).
--
--   Networks model the tape as a graph of configurations; joining two networks wires the right boundary of the first to the left boundary of the second in both directions, and the summary of a join is the product of the summaries (proved separately). A cell diagram is the summary of a single cell whose internal edges are the stay moves, so the word diagram of $w$ records the boundary behaviour of a two-way automaton on the tape segment carrying $w$.
--
--   **Formalization Note** `cellDiagram m stay right left` and `wordDiagram d w = (w.map d).prod` (product in the diagram monoid, with `wordDiagram_nil` for the empty word). `Network m V` has fields `edge`, `leftIn`, `rightIn`, `leftOut`, `rightOut`; `Network.summary` and `Network.join` are as above, the join using `blockRelation` on `V ⊕ W`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Network.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Network.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Single-cell diagram from stay, rightward, and leftward augmented transitions. -/
def cellDiagram (m : ℕ) (stay right left : SetRel (Fin m) (Fin m)) : Diagram m :=
  ⟨relStar stay ○ right, relStar stay ○ left, relStar stay ○ left, relStar stay ○ right⟩

/-- Multiply the single-letter diagrams in input order, using identity for the empty word. -/
def wordDiagram {Sigma : Type*} {m : ℕ} (d : Sigma → Diagram m) (w : List Sigma) : Diagram m :=
  (w.map d).prod

@[simp]
theorem wordDiagram_nil {Sigma : Type*} {m : ℕ} (d : Sigma → Diagram m) :
    wordDiagram d [] = Diagram.identity m := rfl

/-- A finite-path network with labelled entrances and exits at both boundaries. -/
structure Network (m : ℕ) (V : Type*) where
  /-- Internal transitions. -/
  edge : SetRel V V
  /-- Left boundary entrance. -/
  leftIn : SetRel (Fin m) V
  /-- Right boundary entrance. -/
  rightIn : SetRel (Fin m) V
  /-- Left boundary exit. -/
  leftOut : SetRel V (Fin m)
  /-- Right boundary exit. -/
  rightOut : SetRel V (Fin m)

namespace Network

/-- Summarize all finite internal paths between the four boundary pairs. -/
def summary {m : ℕ} {V : Type*} (N : Network m V) : Diagram m where
  forward := N.leftIn ○ relStar N.edge ○ N.rightOut
  backward := N.rightIn ○ relStar N.edge ○ N.leftOut
  left := N.leftIn ○ relStar N.edge ○ N.leftOut
  right := N.rightIn ○ relStar N.edge ○ N.rightOut

/-- Join two networks, wiring the adjacent exits to entrances in both directions. -/
def join {m : ℕ} {V W : Type*} (N : Network m V) (M : Network m W) : Network m (V ⊕ W) where
  edge := blockRelation N.edge (N.rightOut ○ M.leftIn) (M.leftOut ○ N.rightIn) M.edge
  leftIn := {xy | ∃ v, xy.2 = Sum.inl v ∧ (xy.1, v) ∈ N.leftIn}
  rightIn := {xy | ∃ w, xy.2 = Sum.inr w ∧ (xy.1, w) ∈ M.rightIn}
  leftOut := {xy | ∃ v, xy.1 = Sum.inl v ∧ (v, xy.2) ∈ N.leftOut}
  rightOut := {xy | ∃ w, xy.1 = Sum.inr w ∧ (w, xy.2) ∈ M.rightOut}

end Network

end TwoWayComplementation

end OAI


