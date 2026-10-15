-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain
-- name    : OAI_Combinatorics_TwoWayAutomata_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:24:39.05471+00:00
-- url     : https://prove2.me/theorems/1e6c0387-8270-449d-a078-f00998af13c3
-- title:
--   Chains of tape cells: cell coordinates, cell symbols and the joined chain network
-- statement:
--   Let $m,n\in\mathbb{N}$ and $[m]=\{0,\dots,m-1\}$. Networks (internal edges, left and right entrances and exits) and their join $\bowtie$ are as in the network definitions.
--
--   1. **Chain vertices.** The vertex set $V_{m,n}$ is defined recursively by $V_{m,0}=[m]$ and $V_{m,n+1}=[m]\sqcup V_{m,n}$. Every vertex $c$ has a position $\mathrm{pos}(c)$ and a label $\mathrm{lab}(c)\in[m]$: a vertex $q$ of the first summand $[m]$ has position $0$ and label $q$, and a vertex coming from $V_{m,n}$ keeps its label while its position increases by one. Every position is at most $n$, and $c\mapsto(\mathrm{lab}(c),\mathrm{pos}(c))$ is a bijection
--   $$V_{m,n}\ \cong\ [m]\times\{0,1,\dots,n\}:$$
--   position and label determine a vertex, and every pair $(q,i)$ with $i\le n$ occurs.
--   2. **Cell symbols.** For a word $w=a_1\cdots a_n$ over an alphabet $\Sigma$ and a final symbol $a_{\mathrm{last}}\in\Sigma$, the vertices of $V_{m,n}$ in position $i$ carry the symbol $a_{i+1}$ if $i<n$, and $a_{\mathrm{last}}$ if $i=n$.
--   3. **Cell network.** For move relations $\mu_{-1},\mu_0,\mu_{+1}$ on $[m]$, the cell network on the vertex set $[m]$ has internal edges $\mu_0$, both entrances equal to the identity relation, left exit $\mu_{-1}$ and right exit $\mu_{+1}$.
--   4. **Chain network.** Given move relations $\mu_k(a)$ on $[m]$ for every symbol $a\in\Sigma$ and move $k\in\{-1,0,+1\}$, the chain network of $w$ and $a_{\mathrm{last}}$, on the vertex set $V_{m,|w|}$, is defined by
--   $$\mathrm{ch}(\varepsilon,a_{\mathrm{last}})=\mathrm{cell}\big(\mu(a_{\mathrm{last}})\big),\qquad \mathrm{ch}(a\,w',a_{\mathrm{last}})=\mathrm{cell}\big(\mu(a)\big)\bowtie\mathrm{ch}(w',a_{\mathrm{last}}).$$
--
--   The chain network is the transition graph of a two-way automaton on the cells $0,\dots,n$ carrying $a_1,\dots,a_n,a_{\mathrm{last}}$, the vertex with label $q$ in position $i$ standing for state $q$ in cell $i$. It is shown separately that its internal edges are exactly the moves inside and between adjacent cells, that it is entered at cell $0$ and cell $n$, and that it is left by left moves from cell $0$ and right moves from cell $n$. Because joins are summarized by products, its summary is the product of the cell diagrams of its symbols.
--
--   **Formalization Note** The vertex type is `ChainNode m n`, with `ChainNode.position`, `ChainNode.label`, `position_le`, `coordinates_injective` and `coordinates_surjective`. The cell symbols are `chainSymbol w last`, and the networks are `cellNetwork moves` and `chainNetwork moves w last`, where the move relations are indexed by `Fin 3` and the index `k` has displacement `k - 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Chain.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Chain.lean by skeleton subtraction
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

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Internal vertices of a chain with one distinguished final cell. -/
def ChainNode (m : ℕ) : ℕ → Type
  | 0 => Fin m
  | n + 1 => Fin m ⊕ ChainNode m n

namespace ChainNode

/-- Zero-based cell coordinate. -/
def position {m : ℕ} : {n : ℕ} → ChainNode m n → ℕ
  | 0, _ => 0
  | _ + 1, .inl _ => 0
  | _ + 1, .inr c => c.position + 1

/-- State label carried at a cell. -/
def label {m : ℕ} : {n : ℕ} → ChainNode m n → Fin m
  | 0, q => q
  | _ + 1, .inl q => q
  | _ + 1, .inr c => c.label

/-- Every vertex belongs to one of the chain's cells. -/
theorem position_le {m n : ℕ} (c : ChainNode m n) : c.position ≤ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    cases c with
    | inl q => exact Nat.zero_le _
    | inr c => exact Nat.succ_le_succ (ih c)

/-- A cell coordinate and a state label uniquely identify an internal vertex. -/
theorem coordinates_injective {m n : ℕ} (c d : ChainNode m n)
    (hp : c.position = d.position) (hq : c.label = d.label) : c = d := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    cases c with
    | inl q =>
      cases d with
      | inl r => exact congrArg Sum.inl hq
      | inr d => exact (Nat.succ_ne_zero _ hp.symm).elim
    | inr c =>
      cases d with
      | inl r => exact (Nat.succ_ne_zero _ hp).elim
      | inr d => exact congrArg Sum.inr (ih c d (Nat.succ.inj hp) hq)

/-- Every valid cell coordinate and state label occurs. -/
theorem coordinates_surjective {m n : ℕ} (q : Fin m) (p : ℕ) (hp : p ≤ n) :
    ∃ c : ChainNode m n, c.label = q ∧ c.position = p := by
  induction n generalizing p with
  | zero => exact ⟨q, rfl, by dsimp [position]; omega⟩
  | succ n ih =>
    cases p with
    | zero => exact ⟨Sum.inl q, rfl, rfl⟩
    | succ p =>
      obtain ⟨c, hq, hc⟩ := ih p (by omega)
      exact ⟨Sum.inr c, hq, congrArg Nat.succ hc⟩

end ChainNode

/-- The symbol at a vertex in a nonempty cell chain. -/
def chainSymbol {Sigma : Type*} {m : ℕ} (w : List Sigma) (last : Sigma) :
    ChainNode m w.length → Sigma :=
  match w with
  | [] => fun _ => last
  | a :: tail => fun c => match c with
    | .inl _ => a
    | .inr d => chainSymbol tail last d

/-- A single cell retains stays internally and exposes its two moving transitions. -/
def cellNetwork {m : ℕ} (moves : Fin 3 → SetRel (Fin m) (Fin m)) : Network m (Fin m) where
  edge := moves 1
  leftIn := SetRel.id
  rightIn := SetRel.id
  leftOut := moves 0
  rightOut := moves 2

/-- Join a list of cells to a distinguished final cell. -/
def chainNetwork {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma) :
    Network m (ChainNode m w.length) :=
  match w with
  | [] => cellNetwork (moves last)
  | a :: tail => (cellNetwork (moves a)).join (chainNetwork moves tail last)

end TwoWayComplementation

end OAI


