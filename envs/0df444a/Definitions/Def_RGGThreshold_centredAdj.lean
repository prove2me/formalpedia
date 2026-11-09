-- Prove2me | Definitions.Def_RGGThreshold_centredAdj
-- name    : RGGThreshold_centredAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:13.740085+00:00
-- url     : https://prove2.me/theorems/2df23e31-a05d-4f9a-9eed-d33ffda8836e
-- title:
--   Centred adjacency $A-pJ$, the vertex sets $\{s+1,\dots,n\}$, and the weights $\lambda_{ij}$
-- statement:
--   Let $H$ be a graph on the vertex set $[n]$ with adjacency matrix $A$ ($A_{ij}=1$ if $ij\in E(H)$, else $0$). The **centred adjacency matrix** is $A-pJ$, with entries $A_{ij}-p$; on the diagonal $A_{ii}=0$, so the entry is $-p$. For $0\le s\le n$, the **tail set** is $\{s+1,\dots,n\}$; $H_s$ denotes the subgraph of $H$ it induces. The **weights** are
--
--   $$
--   \lambda_{ij}=\begin{cases} a/p, & ij\in E(H),\\ -a/(1-p), & i\ne j,\ ij\notin E(H),\\ 0, & i=j,\end{cases}
--   $$
--
--   with $a=\phi(z_p)$; for $i\ne j$, $\lambda_{ij}=\frac{a}{p(1-p)}(A_{ij}-p)$.
--
--   **Formalization Note** Vertices are `Fin n`, numbered from $0$, so the paper's $\{s+1,\dots,n\}$ is $\{i: s\le i\}$ in Lean labels.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), (1), p.2 (PDF p.4); §2.6, p.8 (PDF p.10); §5, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_RGGThreshold_gaussCDF

namespace RGGThreshold

open Classical in
/-- The centred adjacency matrix `A - pJ` of a graph `H` on `[n]`: its `(i, j)` entry is
`A_{ij} - p`, where `A_{ij} = 1` if `ij ∈ E(H)` and `0` otherwise (Hunter–Milojević–Sudakov,
arXiv:2607.22480, held version, sha256 1a398ef9…, (1), p.2 (PDF p.4); §2.6, p.8 (PDF p.10)).

**Formalization Note** Vertices are `Fin n` (the paper's `[n]` shifted to start at `0`). A simple
graph has no loops, so the diagonal entry is `A_{ii} - p = -p`, as in the matrix `A - pJ`. -/
noncomputable def centredAdj {n : ℕ} (p : ℝ) (H : SimpleGraph (Fin n)) (i j : Fin n) : ℝ :=
  (if H.Adj i j then 1 else 0) - p

/-- The vertex set `{s+1, …, n}` of the paper (1-based), which is `{i : Fin n | s ≤ i}` in 0-based
vertex labels (arXiv:2607.22480, held version, §5, p.14 (PDF p.16): `H_s` is the subgraph of `H`
induced by `{s+1, …, n}`; Definition 2.2 (ii), p.9: the intervals `I = [s+1, …, n]`). -/
def tailSet (n s : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => s ≤ i.val

open Classical in
/-- The weights `λ_{ij}` of a graph `H` (arXiv:2607.22480, held version, §2.6, p.8 (PDF p.10)):
`λ_{ij} = a/p` if `ij ∈ E(H)`, `λ_{ij} = -a/(1-p)` if `i ≠ j` and `ij ∉ E(H)`, and `λ_{ii} = 0`,
where `a = ϕ(z_p)`. -/
noncomputable def lam {n : ℕ} (p : ℝ) (H : SimpleGraph (Fin n)) (i j : Fin n) : ℝ :=
  if i = j then 0 else if H.Adj i j then aCoef p / p else -(aCoef p / (1 - p))

end RGGThreshold


