-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_ExpanderSplit
-- name    : OnlineMaxWeightMatch_Approx_Supplement_ExpanderSplit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:20:04.071837+00:00
-- url     : https://prove2.me/theorems/1a7691df-9fd6-45e2-8b1c-09247c9516f4
-- title:
--   §2 p. 5 and §3.1 pp. 6–7 — expansion at least 1, the split formula $\phi'$ with consistency clauses (2), and $E_n$
-- statement:
--   **Expansion.** For a finite graph $G=(V,E)$, the expansion is $h(G)=\min\{|E(S,V\setminus S)|/|S| : \emptyset\ne S\subseteq V,\ |S|\le |V|/2\}$, where $E(X,Y)$ is the set of edges with one end in $X$ and the other in $Y$. The graph has **expansion at least 1** when $|E(S,V\setminus S)|\ge|S|$ for every nonempty $S$ with $|S|\le|V|/2$.
--
--   **The split formula (§3.1).** Let $\phi$ be a MAX-SSAT formula and let $a(i)$ be the number of occurrences of $x_i$ in $\phi$. For each deterministic $x_i$, let $G_i$ be a graph on vertices $1,\dots,a(i)$. The formula $\phi'$ is obtained as follows.
--
--   1. The $j$-th occurrence of each deterministic $x_i$ (in reading order) is replaced by a new deterministic variable $x_{i,j}$.
--   2. For each edge $\{j,j'\}$ of $G_i$ the two clauses
--   $$(x_{i,j}\vee\bar x_{i,j'})\wedge(\bar x_{i,j}\vee x_{i,j'})\tag{2}$$
--   are added.
--   3. The variables of $\phi'$ are ordered block by block, in the order of $x_1,\dots,x_n$. A random $x_i$ keeps one position. A deterministic $x_i$ with $a(i)\ge1$ becomes $x_{i,1},y,x_{i,2},y,\dots,x_{i,a(i)}$, where each $y$ is a fresh dummy random variable that occurs in no clause. A deterministic $x_i$ with no occurrence is kept as one unused deterministic variable.
--
--   Every block has odd length, so copies of deterministic (random) variables stay deterministic (random) and the order of $\phi'$ is consistent with that of $\phi$. Finally
--   $$E_n=\sum_{i\ \text{deterministic}}2\,|E(G_i)|$$
--   is the number of clauses of type (2).
--
--   **Formalization Note** The paper leaves the interleaving of the copies with dummy random variables unspecified ("some arbitrary order", "by adding dummy random variables"). The layout above is one admissible choice. The association of vertices with copies is arbitrary in the paper and is carried by the arbitrary graphs $G_i$.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 5, definition of expansion; pp. 6–7, §3.1 'The reduction', eq. (2), and Lemma 3.2 (definition of E_n)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_MaxSSAT

open Classical

namespace OnlineMaxWeightMatch.Approx.Supplement

/-- **Expansion at least 1** (§2, p. 5): `h(G) ≥ 1`, i.e. every nonempty vertex set `S` with
`|S| ≤ |V|/2` has at least `|S|` edges leaving it, `|E(S, V ∖ S)| ≥ |S|`. The minimum in
`h(G)` runs over nonempty `S` (the ratio is undefined at `S = ∅`). -/
def HasExpansionAtLeastOne {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
    S.card ≤ ((S ×ˢ Sᶜ).filter fun e => G.Adj e.1 e.2).card

/-- The number of edges `|E(G)|` of a graph on `{0, …, a-1}`. -/
noncomputable def numEdges {a : ℕ} (G : SimpleGraph (Fin a)) : ℕ :=
  ((Finset.univ : Finset (Fin a × Fin a)).filter fun e => e.1 < e.2 ∧ G.Adj e.1 e.2).card

/-- `a(v)`: the number of occurrences of variable `v` in `φ` (literal positions, in all clauses). -/
def SSATFormula.occ (φ : SSATFormula) (v : ℕ) : ℕ :=
  φ.clauses.flatten.countP fun l => l.1 == v

/-- The length of the block of new variables that replaces `x_{v+1}` in `φ′`: a random variable
is kept (length 1); a deterministic variable with `a(v) ≥ 1` occurrences becomes its copies
`x_{v,1}, …, x_{v,a(v)}` separated by `a(v) - 1` dummy random variables (length `2a(v) - 1`);
a deterministic variable with no occurrence is kept as one unused deterministic variable. -/
def SSATFormula.blockLen (φ : SSATFormula) (v : ℕ) : ℕ :=
  if IsRandomVar v ∨ φ.occ v = 0 then 1 else 2 * φ.occ v - 1

/-- The position in `φ′` at which the block of `x_{v+1}` starts. Every block has odd length, so
this position has the parity of `v`: deterministic and random variables keep their type. -/
def SSATFormula.blockStart (φ : SSATFormula) (v : ℕ) : ℕ :=
  ∑ u ∈ Finset.range v, φ.blockLen u

/-- The variable of `φ′` holding the `j`-th copy (`j = 0, …, a(v)-1`) of the deterministic `v`. -/
def SSATFormula.copyVar (φ : SSATFormula) (v j : ℕ) : ℕ :=
  φ.blockStart v + 2 * j

/-- The original clauses of `φ`, with the `j`-th occurrence (in reading order) of each
deterministic variable `v` replaced by its copy `x_{v,j}`, and random variables renamed to
their new positions. -/
def SSATFormula.splitClauses (φ : SSATFormula) : List (List (ℕ × Bool)) :=
  φ.clauses.mapIdx fun r C => C.mapIdx fun p l =>
    if IsRandomVar l.1 then (φ.blockStart l.1, l.2)
    else (φ.copyVar l.1
      (((φ.clauses.take r).flatten ++ C.take p).countP fun l' => l'.1 == l.1), l.2)

/-- The consistency clauses (2): for every deterministic `v` and every edge `{j, j'}` of the
graph `G v` on the copies of `v`, the two clauses
`(x_{v,j} ∨ ¬x_{v,j'})` and `(¬x_{v,j} ∨ x_{v,j'})`. -/
noncomputable def SSATFormula.equalityClauses (φ : SSATFormula)
    (G : (v : ℕ) → SimpleGraph (Fin (φ.occ v))) : List (List (ℕ × Bool)) :=
  (List.range φ.n).flatMap fun v =>
    if IsRandomVar v then [] else
      (List.finRange (φ.occ v)).flatMap fun j =>
        (List.finRange (φ.occ v)).flatMap fun j' =>
          if j < j' ∧ (G v).Adj j j' then
            [[(φ.copyVar v j, true), (φ.copyVar v j', false)],
             [(φ.copyVar v j, false), (φ.copyVar v j', true)]]
          else []

/-- The formula `φ′` of §3.1 built from `φ` and the graphs `G v` on the copies of each
deterministic variable: the variables are the blocks of `x_1, x_2, …, x_n` in order, and the
clauses are the split original clauses followed by the consistency clauses (2). -/
noncomputable def SSATFormula.split (φ : SSATFormula)
    (G : (v : ℕ) → SimpleGraph (Fin (φ.occ v))) : SSATFormula where
  n := φ.blockStart φ.n
  clauses := φ.splitClauses ++ φ.equalityClauses G

/-- `E_n = ∑_{deterministic v} 2 |E(G_v)|`, the number of consistency clauses. -/
noncomputable def SSATFormula.En (φ : SSATFormula)
    (G : (v : ℕ) → SimpleGraph (Fin (φ.occ v))) : ℕ :=
  ∑ v ∈ (Finset.range φ.n).filter (fun v => ¬ IsRandomVar v), 2 * numEdges (G v)

end OnlineMaxWeightMatch.Approx.Supplement


