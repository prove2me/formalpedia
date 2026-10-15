-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape
-- name    : OAI_Combinatorics_TwoWayAutomata_Tape
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:25:37.277107+00:00
-- url     : https://prove2.me/theorems/0d8903c0-5808-4881-a347-348b1da4f009
-- title:
--   Tape coordinates for chain vertices and the step relation on a bounded tape with a terminal column
-- statement:
--   Let $m,n\in\mathbb{N}$, $[m]=\{0,\dots,m-1\}$, and let $V_{m,n}$ be the set of chain vertices, each with a label $\mathrm{lab}(c)\in[m]$ and a position $\mathrm{pos}(c)\in\{0,\dots,n\}$, as in the chain definitions.
--
--   1. **Exit coordinates.** The bijection
--   $$V_{m,n}\sqcup[m]\ \longrightarrow\ [m]\times\{0,1,\dots,n+1\},\qquad c\mapsto\big(\mathrm{lab}(c),\mathrm{pos}(c)\big),\qquad q\mapsto(q,n+1)$$
--   adds a terminal column at position $n+1$; the extra copy of $[m]$ stands for having left the chain to the right.
--   2. **Chain step relation.** Fix relations $\mu_k(a)$ on $[m]$ for symbols $a$ of an alphabet $\Sigma$ and moves $k\in\{-1,0,+1\}$, a word $w=a_1\cdots a_n$ and a final symbol $a_{\mathrm{last}}$, and let $s_i$ be the symbol of cell $i\le n$, namely $a_{i+1}$ for $i<n$ and $a_{\mathrm{last}}$ for $i=n$. The step relation on $[m]\times\{0,\dots,n+1\}$ relates $(q,i)$ to $(r,j)$ iff
--   $$i\le n\qquad\text{and}\qquad (q,r)\in\mu_k(s_i)\ \text{ and }\ j=i+k\ \text{ for some } k\in\{-1,0,+1\}.$$
--   So the head moves on the cells $0,\dots,n$ according to the local move relations, can step from cell $n$ into the terminal column, and has no step out of the terminal column.
--
--   This is the run of a two-way automaton on a bounded tape, written in plain tape coordinates. It is shown separately that, under the bijection of item 1, the step relation is the edge relation of the chain network extended by its right exits into the terminal column, and that $(r,n+1)$ is reachable from $(q,0)$ iff $(q,r)$ lies in the forward component of the summary of the chain network. This links runs of automata to products of boundary diagrams.
--
--   **Formalization Note** The bijection is `ChainNode.exitEquiv m n : ChainNode m n ⊕ Fin m ≃ Fin m × Fin (n + 2)`, built noncomputably with `Equiv.ofBijective`. The step relation is `chainStep moves w last`, a `SetRel` on `Fin m × Fin (w.length + 2)`; its position condition asks for some chain vertex in position $i$, and the new position is computed in the integers as $i+k$ with $k$ the displacement of the move.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Convert the recursively joined cells and one terminal exit into tape coordinates. -/
noncomputable def ChainNode.exitEquiv (m n : ℕ) :
    (ChainNode m n ⊕ Fin m) ≃ (Fin m × Fin (n + 2)) :=
  Equiv.ofBijective (fun c => match c with
    | .inl v => (v.label, ⟨v.position, by have := v.position_le; omega⟩)
    | .inr q => (q, ⟨n + 1, by omega⟩)) (by
      constructor
      · intro c d h
        have hq := congrArg (fun p : Fin m × Fin (n + 2) => p.1) h
        have hp := congrArg (fun p : Fin m × Fin (n + 2) => p.2.val) h
        cases c with
        | inl c =>
          cases d with
          | inl d => exact congrArg Sum.inl (c.coordinates_injective d hp hq)
          | inr q => have := c.position_le; dsimp at hp; omega
        | inr q =>
          cases d with
          | inl d => have := d.position_le; dsimp at hp; omega
          | inr r => exact congrArg Sum.inr hq
      · rintro ⟨q, p⟩
        by_cases hp : p.val ≤ n
        · obtain ⟨c, hq, hc⟩ := ChainNode.coordinates_surjective q p.val hp
          exact ⟨Sum.inl c, Prod.ext hq (Fin.ext hc)⟩
        · exact ⟨Sum.inr q, Prod.ext rfl (Fin.ext (by change n + 1 = p.val; omega))⟩)

/-- Local moves on the bounded tape, with a final terminal position beyond the last cell. -/
def chainStep {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma) :
    SetRel (Fin m × Fin (w.length + 2)) (Fin m × Fin (w.length + 2)) :=
  {cd | ∃ c : ChainNode m w.length, cd.1.2.val = c.position ∧ ∃ move : Fin 3,
    (cd.1.1, cd.2.1) ∈ moves (chainSymbol w last c) move ∧
      (cd.2.2.val : ℤ) = (cd.1.2.val : ℤ) + (move.val : ℤ) - 1}

end TwoWayComplementation

end OAI


