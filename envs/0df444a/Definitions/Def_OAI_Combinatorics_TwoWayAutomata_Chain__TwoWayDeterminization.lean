-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:47:04.606356+00:00
-- url     : https://prove2.me/theorems/8c3cf97d-a5e0-4f8e-8cfc-51901f353fb9
-- title:
--   Chains of tape cells: cell coordinates, cell symbols and the joined chain network
-- statement:
--   Fix $m\in\mathbb N$ and let $[m]=\{0,\dots,m-1\}$ be a set of state labels. A network with vertex set $V$ consists of an edge relation $E\subseteq V\times V$, entrance relations $I_{\mathrm l},I_{\mathrm r}\subseteq[m]\times V$ and exit relations $O_{\mathrm l},O_{\mathrm r}\subseteq V\times[m]$ at the left and right boundary. The join $N\bowtie N'$ of networks on $V$ and $W$ lives on $V\sqcup W$; it keeps the internal edges of both parts, adds an edge $v\to w$ whenever $(v,p)\in O_{\mathrm r}$ and $(p,w)\in I'_{\mathrm l}$ for some label $p$, adds an edge $w\to v$ whenever $(w,p)\in O'_{\mathrm l}$ and $(p,v)\in I_{\mathrm r}$, and takes its left entrances and exits from $N$ and its right ones from $N'$.
--
--   1. **Chain vertices.** For $n\in\mathbb N$ the vertex set $C_{m,n}$ is defined recursively by $C_{m,0}=[m]$ and $C_{m,n+1}=[m]\sqcup C_{m,n}$. Each vertex $c$ has a position $\mathrm{pos}(c)$ (equal to $0$ for $C_{m,0}$ and for the first summand, and to one more than the position inside $C_{m,n}$ for the second summand) and a label $\mathrm{lab}(c)\in[m]$. It is proved that $\mathrm{pos}(c)\le n$, that $c\mapsto(\mathrm{lab}(c),\mathrm{pos}(c))$ is injective, and that every pair $(q,p)\in[m]\times\{0,\dots,n\}$ occurs; thus $C_{m,n}$ is a copy of $[m]\times\{0,\dots,n\}$, cell $p$ carrying state label $q$.
--   2. **Chain symbols.** For a word $w=a_0a_1\cdots a_{n-1}$ (indexed from $0$) and an additional symbol $\ell$, the vertex $c\in C_{m,n}$ is assigned the symbol $a_{\mathrm{pos}(c)}$ if $\mathrm{pos}(c)<n$ and $\ell$ if $\mathrm{pos}(c)=n$.
--   3. **Cell network.** Given move relations $M_0,M_1,M_2$ on $[m]$ (left, stay, right), the single-cell network has vertex set $[m]$, internal edges $M_1$, both entrance relations equal to $\mathrm{Id}$, left exit $M_0$ and right exit $M_2$.
--   4. **Chain network.** Given move relations $M(a)=(M_0(a),M_1(a),M_2(a))$ for every symbol $a$, a word $w$ and the final symbol $\ell$, the chain network on $C_{m,|w|}$ is
--   $$\mathrm{chain}(w,\ell)=\mathrm{cell}(M(a_0))\bowtie\Big(\mathrm{cell}(M(a_1))\bowtie\big(\cdots\bowtie\mathrm{cell}(M(\ell))\big)\Big),$$
--   defined by $\mathrm{chain}(\text{empty word},\ell)=\mathrm{cell}(M(\ell))$ and $\mathrm{chain}(a\,w',\ell)=\mathrm{cell}(M(a))\bowtie\mathrm{chain}(w',\ell)$.
--
--   The chain network models a tape whose cells carry the symbols of $w$ followed by one distinguished final cell. Its vertices are exactly the configurations (label, cell), and its edges are the local moves of the machine, which is the bridge between paths in the network, runs on the tape, and products of cell diagrams.
--
--   **Formalization Note** `ChainNode m n` is the recursive type above, with `ChainNode.position`, `ChainNode.label`, and the facts `position_le`, `coordinates_injective`, `coordinates_surjective`. `chainSymbol w last` gives the symbols, `cellNetwork moves` takes `moves : Fin 3 → SetRel (Fin m) (Fin m)` (codes $0,1,2$ for left, stay, right), and `chainNetwork moves w last : Network m (ChainNode m w.length)` is defined by recursion on `w` using `Network.join`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Chain.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Chain.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization

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


