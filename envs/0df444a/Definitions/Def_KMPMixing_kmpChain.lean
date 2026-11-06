-- Prove2me | Definitions.Def_KMPMixing_kmpChain
-- name    : KMPMixing_kmpChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:36.928308+00:00
-- url     : https://prove2.me/theorems/fc377569-ba01-45ef-9284-2879353e9e2d
-- title:
--   The KMP chain $M^{(t,G)}_{\mathrm{KMP}}$ on $\Delta_G$
-- statement:
--   Let $G=(V=[d],E)$ be a simple graph and $t\in\mathbb N$. The state space of the KMP chain with $t$ particles is the set of multiplicity vectors
--   $$
--   \Delta_G=\Big\{r\in\mathbb N^d:\ \sum_{v\in V}r_v=t\Big\}.
--   $$
--   From $r\in\Delta_G$, the chain picks a uniformly random edge $e=\{i,j\}\in E$, sets $m=r_i+r_j$, and resamples $(r_i,r_j)$ uniformly from $\{(x,y)\in\mathbb N^2:x+y=m\}$, keeping all other coordinates. Its transition matrix is
--   $$
--   M^{(t,G)}_{\mathrm{KMP}}(r,r')=\frac1{|E|}\sum_{\{i,j\}\in E}\frac{\mathbb 1[r'_v=r_v\ \forall v\notin\{i,j\}]\ \mathbb 1[r'_i+r'_j=r_i+r_j]}{r_i+r_j+1}.
--   $$
--   The single summand is the redistribution rule $K_{ij}$ on the fixed edge $\{i,j\}$. The single-particle walk $M^{(1,G)}_{\mathrm{KMP}}$ is the instance $t=1$.
--
--   This is the chain whose mixing time the mission bounds; the fixed-edge kernel $K_{ij}$ is the update used in the coupling of Lemma 4.10.
--
--   **Formalization Note** Vertices are `Fin d` (vertex $i$ of the paper is index $i-1$), and $\Delta_G$ is the finset `Finset.Nat.antidiagonalTuple d t` viewed as a type. Each edge is written once as an ordered pair $(i,j)$ with $i<j$ (`edgePairs G`, footnote 2 of the paper), so `(edgePairs G).card` $=|E|$. On a graph without edges Lean's $1/0=0$ makes the matrix zero; every statement assumes $G$ connected with $d\ge2$.
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Definition 3.1, pp.14–15 (PDF pp.16–17); footnote 2, p.15

import Mathlib
import Definitions.Def_mm_spectral

namespace KMPMixing

open MarkovMixing

/-- The edges `{i, j}` of a simple graph `G` on `[d]`, each written once as the ordered pair
`(i, j)` with `i < j` (Chen, Liu, Qin, Schulman, Song, Yao, Zhao, *A Tale of Two Walks: From Kac
to KMP and Back*, arXiv:2609.38044, Definition 3.1 and footnote 2, p.15 (PDF p.17)).

**Formalization Note** Vertices are `Fin d`: the paper's vertex `i` is the index `i − 1`. The
map `(i, j) ↦ {i, j}` is a bijection from `edgePairs G` onto the edge set `E` of `G`, so
`(edgePairs G).card = |E|` and the uniform law on `edgePairs G` is the uniform law on `E`. -/
def edgePairs {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] : Finset (Fin d × Fin d) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ G.Adj p.1 p.2

/-- The state space `Δ_G = {r ∈ ℕ^d : Σ_v r_v = t}` of the KMP chain with `t` particles on `d`
vertices (arXiv:2609.38044, Definition 3.1, p.14 (PDF p.16)): the multiplicity vectors summing
to `t`. -/
abbrev State (d t : ℕ) := ↥(Finset.Nat.antidiagonalTuple d t)

/-- The KMP redistribution rule on a fixed edge `{i, j}` (arXiv:2609.38044, Definition 3.1,
step 2, p.15 (PDF p.17)): with `m = r_i + r_j`, the pair `(r_i, r_j)` is resampled uniformly
from `{(x, y) ∈ ℕ² : x + y = m}` and all other coordinates are kept, so
`K_{ij}(r, r') = 𝟙[r'_v = r_v ∀ v ∉ {i, j}] · 𝟙[r'_i + r'_j = r_i + r_j] / (r_i + r_j + 1)`.

**Formalization Note** The kernel is used only for `i ≠ j`; it is symmetric in `i` and `j`. -/
noncomputable def edgeKernel {d t : ℕ} (i j : Fin d) : Matrix (State d t) (State d t) ℝ :=
  fun r r' =>
    if (∀ v, v ≠ i → v ≠ j → r'.1 v = r.1 v) ∧ r'.1 i + r'.1 j = r.1 i + r.1 j then
      1 / ((r.1 i + r.1 j : ℕ) + 1 : ℝ)
    else 0

/-- The transition matrix `M^{(t,G)}_KMP` of the KMP chain (arXiv:2609.38044, Definition 3.1,
pp.14–15 (PDF pp.16–17)): pick a uniformly random edge `e = {i, j} ∈ E` and apply the
redistribution rule `edgeKernel i j` on it,
`M(r, r') = (1/|E|) Σ_{{i,j} ∈ E} K_{ij}(r, r')`.

The single-particle chain `M^{(1,G)}_KMP` is the instance `t = 1`.

**Formalization Note** The average runs over `edgePairs G`, the edges written with `i < j`.
For a graph with no edge (`d ≤ 1`, or a disconnected empty graph) Lean's `1/0 = 0` makes the
matrix zero; every statement of the mission assumes `G` connected on `d ≥ 2` vertices. -/
noncomputable def kmpChain {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] (t : ℕ) :
    Matrix (State d t) (State d t) ℝ :=
  ((edgePairs G).card : ℝ)⁻¹ • ∑ p ∈ edgePairs G, edgeKernel p.1 p.2

end KMPMixing


