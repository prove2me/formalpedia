-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network
-- name    : OAI_Combinatorics_TwoWayAutomata_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:23:07.088846+00:00
-- url     : https://prove2.me/theorems/29366011-dd5c-41c3-9875-9b1c683d23b7
-- title:
--   Single-cell diagrams, word diagrams, and finite-path networks summarized by boundary diagrams
-- statement:
--   Let $m\in\mathbb{N}$ and $[m]=\{0,\dots,m-1\}$. Boundary diagrams $a=(a_{\mathrm f},a_{\mathrm b},a_{\mathrm l},a_{\mathrm r})$ on $[m]$ (forward, backward, left and right traversal relations), their product and the identity diagram $1$ are as in the diagram definitions; relations compose in path order, and $R^*$ is the reflexive–transitive closure.
--
--   1. **Cell diagram.** For relations $S$ (stay), $R$ (move right) and $L$ (move left) on $[m]$,
--   $$\mathrm{cell}(S,R,L)=\big(S^*R,\ S^*L,\ S^*L,\ S^*R\big):$$
--   from whichever side a single cell is entered, the head stays some number of times and then leaves to the right or to the left.
--   2. **Word diagram.** For a map $d$ from an alphabet $\Sigma$ to diagrams and a word $w=a_1\cdots a_n$, $d(w)=d(a_1)\,d(a_2)\cdots d(a_n)$ in input order, with $d(\varepsilon)=1$.
--   3. **Networks.** A network with boundary $[m]$ and vertex set $V$ consists of an internal edge relation $E\subseteq V\times V$, left and right entrances $I_{\mathrm L},I_{\mathrm R}\subseteq[m]\times V$, and left and right exits $O_{\mathrm L},O_{\mathrm R}\subseteq V\times[m]$.
--   4. **Summary.** The summary of a network $N$ records the finite internal paths between boundary labels:
--   $$\langle N\rangle=\big(I_{\mathrm L}E^*O_{\mathrm R},\ I_{\mathrm R}E^*O_{\mathrm L},\ I_{\mathrm L}E^*O_{\mathrm L},\ I_{\mathrm R}E^*O_{\mathrm R}\big).$$
--   5. **Join.** For networks $N$ on $V$ and $M$ on $W$, the join $N\bowtie M$ is the network on $V\sqcup W$ whose edge relation is the block relation
--   $$\begin{bmatrix}E^N & O^N_{\mathrm R}\,I^M_{\mathrm L}\\ O^M_{\mathrm L}\,I^N_{\mathrm R} & E^M\end{bmatrix},$$
--   whose left entrances and exits are those of $N$ (on the copy of $V$), and whose right entrances and exits are those of $M$ (on the copy of $W$). Thus a right exit of $N$ with label $q$ is wired to every left entrance of $M$ with label $q$, and a left exit of $M$ to every right entrance of $N$ with the same label.
--
--   Networks are a combinatorial model of a tape segment, with the vertices standing for (cell, state) pairs. It is shown separately that $\langle N\bowtie M\rangle=\langle N\rangle\langle M\rangle$, so that summarizing a chain of joined cells yields the product of their diagrams; the cell diagram is the summary of a single cell, and the word diagram is the image of a word under the monoid homomorphism determined by the letter diagrams.
--
--   **Formalization Note** The objects are `cellDiagram m stay right left`, `wordDiagram d w` (the list product `(w.map d).prod` in the monoid of diagrams, with the simp lemma `wordDiagram_nil`), the structure `Network m V` with fields `edge`, `leftIn`, `rightIn`, `leftOut` and `rightOut`, and `Network.summary` and `Network.join`, the latter built with `blockRelation`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Network.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Network.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayComplementation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source

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


