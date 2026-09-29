-- Prove2me | Definitions.Def_ApproxCliqueWidth_Certificate_KExpr
-- name    : ApproxCliqueWidth_Certificate_KExpr
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:30:29.251381+00:00
-- url     : https://prove2.me/theorems/2cf5e6b8-8fe4-4039-94f6-025651999f47
-- title:
--   $k$-expressions built from $\cdot_i$, $\eta_{i,j}$, $\rho_{i\to j}$, $\oplus$; their value; clique-width at most $k$
-- statement:
--   Let $k$ be a positive integer. A **$k$-graph** is a graph with a labelling of its vertices by $\{1, \dots, k\}$. A **$k$-expression** is a well-formed term built from:
--
--   1. the constants $\cdot_i$ ($1 \le i \le k$): a single vertex labelled $i$;
--   2. for $i \ne j$, the unary operator $\eta_{i,j}$, which adds all edges $vw$ between vertices $v$ labelled $i$ and $w$ labelled $j$;
--   3. the unary operator $\rho_{i \to j}$, which relabels every vertex labelled $i$ into $j$;
--   4. the binary operator $\oplus$, disjoint union.
--
--   The **value** $\mathrm{val}(t)$ of $t$ is the $k$-graph obtained by performing these operations; its vertex set is the set of occurrences of constant symbols in $t$. $t$ is a $k$-expression **of** $G$ if its value is, up to isomorphism, $G$ with some labelling. The **clique-width** $\mathrm{cwd}(G)$ is the least $k$ such that $G$ has a $k$-expression; thus
--   $$\mathrm{cwd}(G) \le k \iff G \text{ has a } k\text{-expression}.$$
--   For example, $\rho_{2\to1}(\eta_{1,2}(\rho_{2\to1}(\eta_{1,2}(\rho_{2\to1}(\eta_{1,2}(\cdot_1\oplus\cdot_2))\oplus\cdot_2))\oplus\cdot_2))$ is a $2$-expression of $K_4$.
--
--   Clique-width is the graph parameter whose approximation is the goal of the mission; many graph problems are solvable in polynomial time on graphs of bounded clique-width when a $k$-expression is given.
--
--   **Formalization Note** Labels $\{1,\dots,k\}$ are `Fin k` (paper label $i$ is `i - 1`). The vertex type of $\mathrm{val}(t)$ is `Unit` for a constant, the same type for unary operators, and the sum type for $\oplus$, which is exactly the set of occurrences of constants. $\eta_{i,j}$ carries a proof of $i \ne j$, as on the page, and adds edges through `SimpleGraph.fromRel`, which keeps the graph loopless; $\rho_{i\to i}$ is allowed and is the identity. `HasKExpr G k` asserts a graph isomorphism from $\mathrm{val}(t)$ to $G$; the labelling is not constrained. There are no $0$-expressions, and a graph with no vertex has no $k$-expression.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 517, Section 3 (k-graphs, operations (1)–(4), k-expression, value, cwd(G)); p. 518 (K4 example)

import Mathlib

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Section 3 (p. 517): `k`-expressions. Labels `{1, …, k}` of the paper are
`Fin k` here (label `i` of the paper is `i - 1`).
* `const i` is `·i`, an isolated vertex labelled `i`;
* `eta i j h t` is `η_{i,j}(t)` for `i ≠ j`, adding all edges between label `i` and label `j`;
* `rho i j t` is `ρ_{i→j}(t)`, relabelling every vertex labelled `i` into `j`;
* `union t₁ t₂` is the disjoint union `t₁ ⊕ t₂`. -/
inductive KExpr (k : ℕ) : Type
  | const (i : Fin k) : KExpr k
  | eta (i j : Fin k) (h : i ≠ j) (t : KExpr k) : KExpr k
  | rho (i j : Fin k) (t : KExpr k) : KExpr k
  | union (t₁ t₂ : KExpr k) : KExpr k

namespace KExpr

variable {k : ℕ}

/-- The vertex set of the value of `t`: the set of occurrences of constant symbols in `t`. -/
def Vtx : KExpr k → Type
  | const _ => Unit
  | eta _ _ _ t => Vtx t
  | rho _ _ t => Vtx t
  | union t₁ t₂ => Vtx t₁ ⊕ Vtx t₂

/-- The labelling of the value of `t`. -/
def lab : (t : KExpr k) → Vtx t → Fin k
  | const i, _ => i
  | eta _ _ _ t, v => lab t v
  | rho i j t, v => if lab t v = i then j else lab t v
  | union t₁ t₂, v => Sum.elim (lab t₁) (lab t₂) v

/-- The graph of the value of `t`: `·i` has no edge; `η_{i,j}` adds the edges `vw` with
`lab(v) = i`, `lab(w) = j`; `ρ_{i→j}` keeps the graph; `⊕` is the disjoint union. -/
def graph : (t : KExpr k) → SimpleGraph (Vtx t)
  | const _ => ⊥
  | eta i j _ t => graph t ⊔ SimpleGraph.fromRel (fun v w => lab t v = i ∧ lab t w = j)
  | rho _ _ t => graph t
  | union t₁ t₂ => graph t₁ ⊕g graph t₂

end KExpr

/-- `G` has a `k`-expression (Oum–Seymour p. 517): some `k`-expression `t` whose value is
isomorphic to `G` (the labelling of the value is irrelevant). `cwd(G) ≤ k` iff `HasKExpr G k`;
`cwd(G) ≥ k + 1` iff `¬ HasKExpr G k`. -/
def HasKExpr {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ t : KExpr k, Nonempty (t.graph ≃g G)

end ApproxCliqueWidth.Certificate


