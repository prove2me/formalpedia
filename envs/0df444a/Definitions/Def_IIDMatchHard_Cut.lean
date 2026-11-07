-- Prove2me | Definitions.Def_IIDMatchHard_Cut
-- name    : IIDMatchHard_Cut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:17.890752+00:00
-- url     : https://prove2.me/theorems/4afab5eb-5ef3-422b-b6b2-d297ee38d110
-- title:
--   Cuts, the maximum cut $C(G)$, edge count, largest degree, blow-ups, and random vertex subsets
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with $n=|V|$ and $m=|E|$, and let $\Delta_G$ be its largest degree.
--
--   1. A **cut** is a map $\sigma:V\to\{+,-\}$. Its size is $|\delta_G(\sigma)|$, where $\delta_G(\sigma)=\{(u,v)\in E:\sigma(u)\ne\sigma(v)\}$ is the set of cut edges. $C(G)$ is the maximum size of a cut of $G$.
--   2. For an integer $B$, the **blow-up** $\tilde G$ of $G$ (Definition 3.7) has vertex set $V\times\{1,\dots,B\}$, and $(u,i)$ is adjacent to $(v,j)$ iff $(u,v)\in E$.
--   3. For a finite set $W$ and $p\in[0,1]$, let $A\subseteq W$ be a random set containing every element independently with probability $p$. The expectation of a function $f(A)$ is
--   $$\mathbb E[f(A)]=\sum_{A\subseteq W}p^{|A|}(1-p)^{|W|-|A|}f(A).$$
--
--   The reduction starts from Max Cut on cubic graphs. Blow-ups and random induced subgraphs are used to bound the advantage of adaptive policies (Lemmas 3.8 and 3.9).
--
--   **Formalization Note** A cut is a map `V → Bool`, with `true` for $+$. Copies are indexed by `Fin B` (0-based). The largest degree of a graph without vertices is $0$.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), §3, p.5 (PDF p.6); Definition 3.7, p.9 (PDF p.10); Lemma 3.8, p.10

import Mathlib

set_option autoImplicit false

namespace IIDMatchHard

variable {V : Type*}

/-- The edge `e` is cut by `σ : V → Bool` (`true` is the side `+`, `false` the side `−`): its two
endpoints receive different signs. -/
def IsCutEdge (σ : V → Bool) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => σ u ≠ σ v, fun _ _ => propext ne_comm⟩ e

/-- The size `|δ_G(σ)|` of the cut `σ : V → {+, −}` of `G`, where
`δ_G(σ) = {(u, v) ∈ E : σ(u) ≠ σ(v)}` is the set of edges that `σ` cuts. Teng, Yang,
*Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026, sha256
f0193d92…), §3, p.5 (PDF p.6).

**Formalization Note.** A cut is a map `V → Bool`, `true` standing for `+`. -/
noncomputable def cutSize (G : SimpleGraph V) (σ : V → Bool) : ℕ :=
  {e | e ∈ G.edgeSet ∧ IsCutEdge σ e}.ncard

open Classical in
/-- `C(G)`, the maximum size of a cut of the finite graph `G` (§3, p.5 (PDF p.6)). -/
noncomputable def maxCut [Fintype V] (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup fun σ : V → Bool => cutSize G σ

/-- `m = |E|`, the number of edges of `G`. -/
noncomputable def numEdges (G : SimpleGraph V) : ℕ :=
  G.edgeSet.ncard

/-- `∆_G`, the largest degree of the finite graph `G` (`0` for the empty graph on no vertices). -/
noncomputable def maxDeg [Fintype V] (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup fun v => (G.neighborSet v).ncard

/-- The **blow-up** `G̃` of `G` with `B` copies (Definition 3.7, p.9 (PDF p.10)): the graph on
`V × {1, …, B}` in which `(u, i)` and `(v, j)` are adjacent iff `(u, v) ∈ E`.

**Formalization Note.** The copy index is `Fin B = {0, …, B − 1}` (0-based). The definition is
total; the paper's `B ≥ 1` is a hypothesis of the statements that use it. -/
def blowUp (G : SimpleGraph V) (B : ℕ) : SimpleGraph (V × Fin B) where
  Adj x y := G.Adj x.1 y.1
  symm := ⟨fun _ _ h => G.adj_symm h⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h⟩

/-- The expectation `E[f(A)]` of a function of a random set `A ⊆ W` that contains every element
independently with probability `p`:
`E[f(A)] = ∑_A p^{|A|} (1 − p)^{|W| − |A|} f(A)`. Used in Lemma 3.8 (p.10 (PDF p.11)).

**Formalization Note.** The exponent `|W| − |A|` is natural-number subtraction with `|A| ≤ |W|`,
so it is exact. -/
noncomputable def randSubsetExp {W : Type*} [Fintype W] (p : ℝ) (f : Finset W → ℝ) : ℝ :=
  ∑ A : Finset W, p ^ A.card * (1 - p) ^ (Fintype.card W - A.card) * f A

end IIDMatchHard


