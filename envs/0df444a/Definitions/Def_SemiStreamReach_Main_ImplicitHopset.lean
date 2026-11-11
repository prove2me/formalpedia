-- Prove2me | Definitions.Def_SemiStreamReach_Main_ImplicitHopset
-- name    : SemiStreamReach_Main_ImplicitHopset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:51:37.126635+00:00
-- url     : https://prove2.me/theorems/d7cfa9b8-56b6-4a22-9ace-24a21a7db6eb
-- title:
--   $(h,\varepsilon,x)$-implicit hopsets (Definition 7) and the hopbound $h_x$ of (4)
-- statement:
--   Let $G=(V,E,w)$ be an $n$-vertex weighted directed graph and let $h\ge1$, $\varepsilon\in(0,1)$ and $x\in[n]$. An **$(h,\varepsilon,x)$-implicit hopset** of $G$ is a pair $(H_0,\mathcal B)$ of a set $H_0$ of weighted edges between pairs $(u,v)$ with $v$ reachable from $u$ in $G$, and a collection $\mathcal B$ of vertex sets $B\subseteq V$ (the **blocks**), such that
--
--   1. $|H_0|+\sum_{B\in\mathcal B}|B| = \tilde O(n)$,
--   2. $|B|\le x$ for every $B\in\mathcal B$, and
--   3. $$H\ :=\ H_0\ \cup\ \bigcup_{B\in\mathcal B} TC_w\big((G\cup H_0)[B]\big)$$ is an $(h,\varepsilon)$-hopset of $G$.
--
--   The pair can be stored in $\tilde O(n)$ space even when $H$ itself has many more edges; it is the central object of the paper. The hopbound used for it is (4): $h_x=\big\lceil\sqrt{n/x}\;n^{C_h/\log\log n}\big\rceil$ for a sufficiently large constant $C_h>0$.
--
--   **Formalization Note.** Clause 1 is read with an explicit constant $A$: $|H_0|+\sum_B|B|\le A\,n\,(\log_2(n+2))^A$; every theorem that produces an implicit hopset fixes $A$ before the instance. $H_0$ is a `WGraph`, $|H_0|$ its number of edges, the blocks a list of finite sets. In `hopboundX`, $\log\log n$ is $\log_2\log_2(n+4)$ (positive for all $n$, and asymptotically equal to $\log\log n$).
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 3 (PDF 5), Definition 7; p. 15 (PDF 17), eq. (4)

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances

open scoped ENNReal
open Classical

namespace SemiStreamReach.Main

/-! # Implicit hopsets (Definition 7)

Hoppenworth, Li, Mahabadi, Tarnawski, arXiv:2611.05061 (PDF sha256 c1b64474…), §1.2 p. 3 (PDF 5):
"For a weighted graph G′, the weighted transitive closure TC_w(G′) contains an edge (u, v) of weight
dist_{G′}(u, v) for every pair (u, v) ∈ TC(G′). Definition 7 (Implicit hopset). Let G = (V, E, w)
be an n-vertex weighted directed graph, and let h ≥ 1, ε ∈ (0, 1), and x ∈ [n]. An
(h, ε, x)-implicit hopset of G consists of a set H0 of weighted edges between pairs in TC(G) and a
collection B of vertex sets B ⊆ V, called blocks, such that: (1) |H0| + Σ_{B∈B} |B| = Õ(n),
(2) |B| ≤ x for every B ∈ B, and (3) H := H0 ∪ ⋃_{B∈B} TC_w((G ∪ H0)[B]) is an (h, ε)-hopset
of G."

**Formalization Note.** Clause (1) has content only with an explicit constant: the definition takes
a constant `A` and reads (1) as `|H0| + Σ_B |B| ≤ A · n · (log₂(n + 2))^A`, with `n = |V|`; the
theorems that produce implicit hopsets fix `A` before the instance. `H0` is a weighted graph
(`⊤` = no edge), `|H0|` is its number of edges, the blocks are a list of finite vertex sets (a block
listed twice counts twice in the sum). The block closures use `closureOn`, i.e. `TC_w` of the
induced subgraph, and all unions keep the lightest edge of each pair. The parameter ranges
`h ≥ 1`, `ε ∈ (0, 1)`, `x ∈ [n]` are hypotheses of the statements that use the definition.

The hopbound (4), p. 15 (PDF 17): "h_x = ⌈√(n/x) · n^{C_h/log log n}⌉, where C_h > 0 is a
sufficiently large constant and x ∈ [n]." Here `log log n` is read as `log₂ log₂ (n + 4)`, which
is positive for every `n ≥ 0` and differs from `log log n` by a factor tending to `1`. -/

variable {V : Type*} [Fintype V]

/-- The number `|H0|` of edges of a weighted graph. -/
noncomputable def edgeCount (H0 : WGraph V) : ℕ :=
  (Finset.univ.filter (fun p : V × V => H0 p.1 p.2 ≠ ⊤)).card

/-- The hopset `H = H0 ∪ ⋃_{B ∈ B} TC_w((G ∪ H0)[B])` represented by `(H0, B)`. -/
noncomputable def implicitEdges (G H0 : WGraph V) (Bs : List (Finset V)) : WGraph V :=
  fun u v => H0 u v ⊓ ⨅ B ∈ Bs, closureOn (G ⊓ H0) (↑B : Set V) u v

/-- Definition 7, with the constant `A` of clause (1) explicit: `(H0, Bs)` is an
`(h, ε, x)`-implicit hopset of `G`. -/
def IsImplicitHopset (G : WGraph V) (h : ℕ) (ε : ℝ) (x : ℕ) (A : ℝ) (H0 : WGraph V)
    (Bs : List (Finset V)) : Prop :=
  (∀ u v, H0 u v ≠ ⊤ → Reaches G u v) ∧
  (((edgeCount H0 + (Bs.map Finset.card).sum : ℕ) : ℝ) ≤
      A * (Fintype.card V : ℝ) * Real.logb 2 ((Fintype.card V : ℝ) + 2) ^ A) ∧
  (∀ B ∈ Bs, B.card ≤ x) ∧
  IsHopset G (implicitEdges G H0 Bs) h ε

/-- The hopbound `h_x = ⌈√(n/x) · n^{C_h / log₂ log₂ (n + 4)}⌉` of (4). -/
noncomputable def hopboundX (Ch : ℝ) (n x : ℕ) : ℕ :=
  ⌈Real.sqrt ((n : ℝ) / (x : ℝ)) *
      (n : ℝ) ^ (Ch / Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)))⌉₊

end SemiStreamReach.Main


