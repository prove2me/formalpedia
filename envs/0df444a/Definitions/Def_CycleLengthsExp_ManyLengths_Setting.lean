-- Prove2me | Definitions.Def_CycleLengthsExp_ManyLengths_Setting
-- name    : CycleLengthsExp_ManyLengths_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:48.3415+00:00
-- url     : https://prove2.me/theorems/a22098e2-577d-4170-ad43-b110a341ebe7
-- title:
--   External neighborhood, vertex expansion, cycle lengths, and the proof parameters
-- statement:
--   Let $G=(V,E)$ be a finite simple graph. For $U\subseteq V$, its **external neighborhood** is
--   $$N_G(U)=\{v\in V\setminus U:uv\in E\text{ for some }u\in U\}.$$
--   The graph is a **$(k,\alpha)$-expander** when $|N_G(U)|\ge\alpha|U|$ for every $U$ with $|U|\le k$. It is an **$\alpha$-expander** when the same inequality holds for every $U$ with $|U|\le\lceil |V|/2\rceil$. The set $L(G)$ consists of the lengths of simple cycles of $G$; a cycle length counts edges.
--
--   The proof of Theorem 2 also defines $k(\alpha)=2\lceil\log_2(3/\alpha)/\log_2(1+\alpha/2)\rceil+1$. Given a vertex set $S$ and a path $P$ disjoint from it, $X_0$ consists of vertices $x$ on $P$ reachable from some $s\in S$ by a simple path of at most $k(\alpha)$ edges whose internal vertices avoid $S\cup V(P)$.
--
--   These definitions provide the graph model shared by the goal and the intermediate claims. The paper's parameters $k$ and $\alpha$ are positive in the statements that use expansion; positivity is not built into the expansion predicates.
--
--   **Formalization Note** Graphs are finite simple graphs, vertex sets use `Set.ncard`, and cycles are Mathlib `Walk.IsCycle`, excluding a two-edge closed walk. All logarithms are base 2. The ceiling in the $\alpha$-expander definition is represented by $(|V|+1)/2$ in natural-number arithmetic.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, pp. 1–2, external neighborhood, α-expander, L(G); p. 4, (k,α)-expander and log convention; pp. 13–14, k and X₀

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.ManyLengths

/-- The `(k, α)` vertex-expansion condition of p. 4. Positivity belongs to the theorems. -/
def IsKAlphaExpander {V : Type*} [Fintype V] (k α : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ U : Set V, (U.ncard : ℝ) ≤ k → α * U.ncard ≤ (CycleLengthsExp.WellSpread.extNbhd G U).ncard

/-- The explicit integer `k` chosen at the foot of p. 13. -/
noncomputable def kNum (α : ℝ) : ℕ :=
  2 * Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 1

/-- The vertices `X₀` of pp. 13–14. Only internal vertices of the connecting path
are required to avoid `S` and the long path `p`. -/
def X0 {V : Type*} (α : ℝ) (G : SimpleGraph V) (S : Set V)
    {u v : V} (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧
    ∃ s ∈ S, ∃ q : G.Walk s x,
      q.IsPath ∧ q.length ≤ kNum α ∧
      ∀ y ∈ q.support.tail.dropLast, y ∉ S ∧ y ∉ p.support}

end CycleLengthsExp.ManyLengths


