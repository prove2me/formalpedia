-- Prove2me | Definitions.Def_PadbergRao_UpperBound_graphGxd
-- name    : PadbergRao_UpperBound_graphGxd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T23:19:30.481731+00:00
-- url     : https://prove2.me/theorems/61e3ac35-a48f-4403-a2e0-c698017a99fc
-- title:
--   The labelled weighted graph $G(\bar x, d)$ of Padberg and Rao
-- statement:
--   Let $G=(V,E)$, $b$, $d$ and a point $\bar x\in\mathbb{R}^E$ be as in the $b$-matching system (3.1), with slacks $\bar s_i=b_i-(A\bar x)_i$. Let $E(\bar x)$ denote the edges $e$ of $G$ with $\bar x_e>0$, and fix for every edge $e=[i,j]$ an end $\tau(e)\in e$ (the end that the construction scans first; call the other end $j$).
--
--   The graph $G(\bar x,d)$ has node set
--
--   $$
--   \tilde V=V\cup\{S\}\cup V_*,\qquad V_*=\{i_e : e\in E(\bar x)\},
--   $$
--
--   where $S$ is a special node accounting for the slack variables and $i_e$ is a new node subdividing the edge $e$. Its edge weights $\bar y$ are symmetric:
--
--   1. $\bar y(i,S)=\bar s_i$ for $i\in V$;
--   2. for $e\in E(\bar x)$, $\bar y(\tau(e),i_e)=d_e-\bar x_e$ and $\bar y(j,i_e)=\bar x_e$ for the other end $j$ of $e$;
--   3. every other pair has weight $0$ (no edge).
--
--   Its labels (odd or even) are: $S$ is odd iff $b(V)$ is odd; $i\in V$ is odd iff $b_i+\sum_{e\in E(\bar x),\,\tau(e)=i}d_e$ is odd; $i_e$ is odd iff $d_e$ is odd. A set $U\subseteq\tilde V$ is **odd** when it contains an odd number of odd nodes, and then $(U:\tilde V-U)$ is an **odd cut-set**; its **cut capacity** is
--
--   $$
--   \bar y(U:\tilde V-U)=\sum_{p\in U}\sum_{q\in\tilde V-U}\bar y_{pq}.
--   $$
--
--   This is the graph in which Padberg and Rao reduce the separation of capacitated blossom inequalities to an odd minimum cut-set problem.
--
--   **Formalization Note** The paper builds $G(\bar x,d)$ from $G(\bar x)$ (node set $V\cup\{S\}$, an edge of weight $\bar x_e$ for each $e$ with $\bar x_e>0$, an edge $[i,S]$ of weight $\bar s_i$ when $\bar s_i>0$, $i$ odd iff $b_i$ odd, $S$ odd iff $b(V)$ odd) by scanning the edges of $G(\bar x)$ one at a time: $e=[i,j]$ is replaced by $[i,i_e]$ and $[i_e,j]$, $i_e$ is labelled by the parity of $d_e$, and the label of $i$ is flipped when $i_e$ is odd. The Lean encodes the scan's choice of the first end as an orientation `tail` (every theorem quantifies over it) and gives the labels in closed form: each scan step adds $d_e$ to the parity of $\tau(e)$, and addition mod 2 does not depend on the order of the scan. Nodes are `Option V ⊕ E(x̄)` with `none` the node $S$. Weight $0$ stands for "no edge", which does not change any cut capacity; in particular the edge $[i,S]$ is given weight $\bar s_i$ unconditionally, which agrees with the paper whenever $\bar x$ is feasible ($\bar s_i\ge 0$).
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 75, Section 3 (construction of G(x̄, d)); G(x̄) p. 73, Section 2; odd cut-set p. 68, Section 1

import Mathlib
import Definitions.Def_PadbergRao_UpperBound_bMatchingSystem

namespace PadbergRao.UpperBound

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `G(x̄)` joining two nodes of `V`: the edges `e` of `G` with `x̄_e > 0`.
These are the edges the scan of p. 75 subdivides. -/
def posEdges (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => 0 < x e)

/-- The node set `Ṽ = V ∪ {S} ∪ V_*` of `G(x̄, d)`: `Sum.inl none` is the special slack node
`S`, `Sum.inl (some i)` is the node `i ∈ V`, and `Sum.inr e` is the new node `i_e` created for
the edge `e ∈ E(x̄)` joining two nodes of `V`. -/
abbrev Node (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ) : Type _ :=
  Option V ⊕ {e : Sym2 V // e ∈ posEdges G x}

/-- The special node `S`. -/
def specialNode (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ) : Node G x :=
  Sum.inl none

/-- Weight of the pair `{i, i_e}` in `G(x̄, d)`: the edge `e = [i, j]` is scanned with
`i = tail e`; then `[i, i_e]` has weight `d_e − x̄_e`, `[i_e, j]` has weight `x̄_e`, and `i_e`
is adjacent to no other node (weight `0`). -/
def subdivWeight (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (tail : Sym2 V → V) (i : V) (e : Sym2 V) :
    ℝ :=
  if i = tail e then (d e : ℝ) - x e else if i ∈ e then x e else 0

/-- The (symmetric) edge weights `ȳ` of `G(x̄, d)`: `ȳ(i, S) = s̄_i` for `i ∈ V`,
`ȳ(tail e, i_e) = d_e − x̄_e`, `ȳ(j, i_e) = x̄_e` for the other end `j` of `e`, and weight `0`
(no edge) for every other pair. -/
def yWeight (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (tail : Sym2 V → V) : Node G x → Node G x → ℝ
  | Sum.inl (some i), Sum.inl none => slack G b x i
  | Sum.inl none, Sum.inl (some i) => slack G b x i
  | Sum.inl (some i), Sum.inr e => subdivWeight d x tail i e.1
  | Sum.inr e, Sum.inl (some i) => subdivWeight d x tail i e.1
  | _, _ => 0

/-- The labels of `G(x̄, d)` (`true` = odd), in the closed form produced by the scan of p. 75:
`S` is odd iff `b(V)` is odd; `i ∈ V` is odd iff `b_i + ∑_{e ∈ E(x̄), tail e = i} d_e` is odd;
`i_e` is odd iff `d_e` is odd. -/
def label (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (tail : Sym2 V → V) : Node G x → Bool
  | Sum.inl none => decide (Odd (∑ i, b i))
  | Sum.inl (some i) =>
      decide (Odd (b i + ∑ e ∈ (posEdges G x).filter (fun e => tail e = i), d e))
  | Sum.inr e => decide (Odd (d e.1))

/-- `U ⊆ Ṽ` is odd in `G(x̄, d)`: it contains an odd number of odd-labelled nodes, so that
`(U : Ṽ − U)` is an odd cut-set. -/
def IsOddNodeSet (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (tail : Sym2 V → V) (U : Finset (Node G x)) : Prop :=
  Odd (U.filter (fun p => label G b d x tail p = true)).card

/-- The cut capacity `ȳ(U : Ṽ − U) = ∑_{p ∈ U} ∑_{q ∈ Ṽ − U} ȳ_{pq}` in `G(x̄, d)`. -/
def yCap (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (tail : Sym2 V → V) (U : Finset (Node G x)) : ℝ :=
  ∑ p ∈ U, ∑ q ∈ Uᶜ, yWeight G b d x tail p q

end

end PadbergRao.UpperBound


