-- Prove2me | Definitions.Def_GeomDL_Filters_Defs
-- name    : GeomDL_Filters_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T18:13:31.237386+00:00
-- url     : https://prove2.me/theorems/faa1484f-5f33-42d5-ad61-befc1b212245
-- title:
--   §4.6, pp. 62–67 — the Laplacian Δ = D − W of (24), neighbourhoods 𝒩ᵤ, polynomial filters Σ αₖΔᵏ, r-hop neighbourhoods, remeshing invariance
-- statement:
--   Fix $n$ nodes $\{1,\dots,n\}$ and a real **weight matrix** $W=(w_{uv})\in\mathbb R^{n\times n}$. Node features are arranged as the rows $x_u$ of a matrix $X\in\mathbb R^{n\times d}$.
--
--   1. The **Laplacian** of $W$ is the $n\times n$ matrix
--   $$\Delta = D - W,\qquad D=\operatorname{diag}(d_1,\dots,d_n),\quad d_u=\sum_v w_{uv},$$
--   where $D$ is the degree matrix and $d_u$ the degree of node $u$ (equation (24)). It is the published definition `SpectralSparsify.Sampling.lapMat`, read on $W$.
--   2. The **neighbourhood** of $u$ is $\mathcal N_u=\{v : w_{uv}\neq 0\}$.
--   3. Given a degree $r$ and coefficients $\alpha_0,\dots,\alpha_r\in\mathbb R$, the **polynomial filter** is the matrix
--   $$\hat p(\Delta)=\sum_{k=0}^{r}\alpha_k\Delta^k ,$$
--   acting on features by $X\mapsto \hat p(\Delta)X$; its transfer function is the scalar polynomial $\hat p(\lambda)=\sum_{k=0}^r\alpha_k\lambda^k$.
--   4. For a simple graph $G$ on the nodes, $v$ is **within $r$ hops** of $u$ if some walk in $G$ from $u$ to $v$ has length at most $r$, i.e. the shortest-path distance from $u$ to $v$ is at most $r$.
--   5. A permutation $\sigma$ of the nodes acts by its permutation matrix $P$: $(PX)_u = x_{\sigma^{-1}(u)}$ and $(PWP^\top)_{uv}=w_{\sigma^{-1}(u)\sigma^{-1}(v)}$.
--   6. A function $f$ of $n\times n$ matrices is **remeshing invariant** if $f(CQC^\top)=f(Q)$ for every orthogonal $C\in O(n)$; a function $F$ with values in $\mathbb R^{n\times d}$ is **remeshing equivariant** if $CF(Q)=F(CQC^\top)$ for every $C\in O(n)$.
--
--   These are the objects of the book's Section 4.6 on Laplacian-based filters on graphs and meshes.
--
--   **Formalization Note** No symmetry, sign or loop condition is built into the Laplacian; theorems that need $W=W^\top$ assume it. A diagonal weight $w_{uu}$ cancels in $D-W$. "Within $r$ hops" is the existence of a walk of length $\le r$, so an unreachable node is within no number of hops (Mathlib's `SimpleGraph.dist` would be $0$ there). The permutation convention moves row $\sigma^{-1}(u)$ to row $u$.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning (arXiv:2104.13478v2), §4.6, (24), p. 62; p. 64 (polynomial filter); p. 65 (r-hop neighbourhood); p. 67 (remeshing invariance); §4.1, p. 32 (permutation matrices)

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph
import Definitions.Def_GeomDL_Sets_Defs

namespace GeomDL.Filters

open Matrix

noncomputable section

/-- §4.6, p. 62, (24): the Laplacian `Δ = D − W` of an `n × n` weight matrix `W`, where
`D = diag(d₁, …, dₙ)` and `d_u = ∑_v w_uv`. This is the published `SpectralSparsify.Sampling.lapMat`
(degree matrix minus weight matrix) read on `W : ℝ^{n×n}`; no symmetry, sign or loop condition on `W`
is imposed here (a diagonal weight `w_uu` cancels in `D − W`). -/
abbrev lap {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  SpectralSparsify.Sampling.lapMat W

/-- §4.6, p. 62: the neighbourhood `𝒩_u = {v : w_uv ≠ 0}` of node `u` in the weighted graph `W`. -/
def nbhd {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => W u v ≠ 0

/-- §4.6, p. 64: the polynomial filter of degree `r` with coefficients `α₀, …, α_r`,
`p̂(Δ) = ∑_{k=0}^r α_k Δ^k`, as an `n × n` matrix; it acts on a feature matrix `X ∈ ℝ^{n×d}` by
left multiplication, `p̂(Δ)X`. -/
def polyFilter {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (α : Fin (r + 1) → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ k : Fin (r + 1), α k • lap W ^ (k : ℕ)

/-- The scalar polynomial `p̂(λ) = ∑_{k=0}^r α_k λ^k` (the transfer function of `polyFilter`). -/
def polyEval {r : ℕ} (α : Fin (r + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ k : Fin (r + 1), α k * t ^ (k : ℕ)

/-- "`v` lies in the `r`-hop neighbourhood of `u`" in the graph `G`: some walk from `u` to `v` has
length at most `r` (the shortest-path distance is at most `r`, p. 34). `v = u` is within `0` hops;
an unreachable `v` is within no number of hops. -/
def WithinHops {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (u v : Fin n) : Prop :=
  ∃ p : G.Walk u v, p.length ≤ r

/-- §4.6, p. 67: `f` is remeshing invariant if `f(Q) = f(CQCᵀ)` for every `C ∈ O(n)`. -/
def IsRemeshingInvariant {n : ℕ} {Y : Type*} (f : Matrix (Fin n) (Fin n) ℝ → Y) : Prop :=
  ∀ C ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ Q : Matrix (Fin n) (Fin n) ℝ, f (C * Q * Cᵀ) = f Q

/-- §4.6, p. 67: `F`, with values signals `F(Q) ∈ ℝ^{n×d}` on the nodes, is remeshing equivariant if
`CF(Q) = F(CQCᵀ)` for every `C ∈ O(n)`. -/
def IsRemeshingEquivariant {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin d) ℝ) :
    Prop :=
  ∀ C ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ Q : Matrix (Fin n) (Fin n) ℝ, C * F Q = F (C * Q * Cᵀ)

end

end GeomDL.Filters


