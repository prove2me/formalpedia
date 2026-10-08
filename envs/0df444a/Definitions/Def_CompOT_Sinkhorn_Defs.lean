-- Prove2me | Definitions.Def_CompOT_Sinkhorn_Defs
-- name    : CompOT_Sinkhorn_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:21.461989+00:00
-- url     : https://prove2.me/theorems/1ef0f5d8-690d-4d0a-a923-1f7141c70cc3
-- title:
--   Remark 4.12, (4.14), (4.15), Theorem 4.1, pp. 432–441 — Hilbert's projective metric d_H, ‖·‖_var, η(K), λ(K), Sinkhorn runs and scaling solutions
-- statement:
--   Fix integers $n, m \ge 1$, a matrix $K \in \mathbb{R}^{n\times m}$ and vectors $a \in \mathbb{R}^n$, $b \in \mathbb{R}^m$. All products and quotients of vectors below are taken entrywise ($\odot$ and $/$).
--
--   1. **Hilbert's projective metric** (Remark 4.12). For vectors $u, u' \in \mathbb{R}^n$ with positive entries,
--   $$d_{\mathcal H}(u,u') = \log \max_{i,j} \frac{u_i\, u'_j}{u_j\, u'_i}.$$
--   2. **Variation seminorm** (4.21). For $f \in \mathbb{R}^n$, $\|f\|_{\mathrm{var}} = (\max_i f_i) - (\min_i f_i)$.
--   3. **Birkhoff's constants** (Theorem 4.1). For $K$ with positive entries,
--   $$\eta(K) = \max_{i,j,k,\ell} \frac{K_{i,k}K_{j,\ell}}{K_{j,k}K_{i,\ell}}, \qquad \lambda(K) = \frac{\sqrt{\eta(K)}-1}{\sqrt{\eta(K)}+1},$$
--   where $i, j$ range over rows and $k, \ell$ over columns.
--   4. **Sinkhorn runs** (4.15). Sequences $(u^{(\ell)})_{\ell}$ in $\mathbb{R}^n$ and $(v^{(\ell)})_{\ell}$ in $\mathbb{R}^m$ form a run of Sinkhorn's algorithm when
--   $$v^{(0)} = \mathbb{1}_m, \qquad u^{(\ell+1)} = \frac{a}{K v^{(\ell)}}, \qquad v^{(\ell+1)} = \frac{b}{K^\top u^{(\ell+1)}} \quad (\ell \ge 0).$$
--   5. **Scaling solutions** (4.14). A pair $(u, v)$ solves the scaling equations when $u \odot (Kv) = a$ and $v \odot (K^\top u) = b$.
--   6. **Scaled coupling.** $\mathrm{diag}(u)\,K\,\mathrm{diag}(v)$, the matrix with entries $u_i K_{i,j} v_j$; the book's $P^{(\ell)}$ is this matrix for $(u^{(\ell)}, v^{(\ell)})$.
--
--   These are the objects of the convergence analysis of Sinkhorn's algorithm in §4.2: $d_{\mathcal H}$ measures the distance between rays of the positive cone, and $\lambda(K) < 1$ is the factor by which a positive matrix contracts it.
--
--   **Formalization Note** Indices are $0$-based (`Fin n`). Maxima and minima are real `iSup`/`iInf` over the finite index set; they are the book's values when $n, m \ge 1$, and every theorem assumes $0 < n$, $0 < m$ and positive entries for all vectors and matrices passed to $d_{\mathcal H}$, $\eta$ and $\lambda$ (outside that domain Lean's junk values $x/0 = 0$, $\log x = 0$ for $x \le 0$ apply). The run predicate leaves $u^{(0)}$ unconstrained, since (4.15) does not define it; it is never used.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (4.14), p. 432; (4.15), p. 433; Remark 4.12 and (4.21), p. 439; Theorem 4.1, p. 440; Theorem 4.2 (P^(ℓ)), p. 441

import Mathlib

namespace CompOT.Sinkhorn

open Matrix

/-- Hilbert's projective metric of Remark 4.12 (p. 439):
`d_H(u, u') = log max_{i,j} (u_i u'_j) / (u_j u'_i)`.
Meaningful for entrywise positive `u, u'` on a nonempty index set `Fin n`; every theorem
using it assumes `0 < n` and positive entries (on `Fin 0` the maximum is the junk value `0`). -/
noncomputable def hilbertMetric {n : ℕ} (u u' : Fin n → ℝ) : ℝ :=
  Real.log (⨆ i, ⨆ j, u i * u' j / (u j * u' i))

/-- The variation seminorm `‖f‖_var = (max_i f_i) − (min_i f_i)` of (4.21), p. 439. -/
noncomputable def varNorm {n : ℕ} (f : Fin n → ℝ) : ℝ :=
  (⨆ i, f i) - (⨅ i, f i)

/-- The quantity `η(K) = max_{i,j,k,ℓ} (K_{i,k} K_{j,ℓ}) / (K_{j,k} K_{i,ℓ})` of Theorem 4.1
(p. 440); `i, j` are row indices and `k, ℓ` column indices. -/
noncomputable def eta {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ⨆ i, ⨆ j, ⨆ k, ⨆ l, K i k * K j l / (K j k * K i l)

/-- The contraction ratio `λ(K) = (√η(K) − 1) / (√η(K) + 1)` of Theorem 4.1 (p. 440). -/
noncomputable def lam {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  (Real.sqrt (eta K) - 1) / (Real.sqrt (eta K) + 1)

/-- A run of Sinkhorn's algorithm (4.15), p. 433:
`v^{(0)} = 𝟙_m`, `u^{(ℓ+1)} = a / (K v^{(ℓ)})`, `v^{(ℓ+1)} = b / (Kᵀ u^{(ℓ+1)})`,
with entrywise division. The value `u 0` is not constrained (it is not an iterate of
(4.15)) and is never used. -/
def IsSinkhornRun {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (u : ℕ → Fin n → ℝ) (v : ℕ → Fin m → ℝ) : Prop :=
  v 0 = 1 ∧
  (∀ ℓ, u (ℓ + 1) = a / (K *ᵥ v ℓ)) ∧
  (∀ ℓ, v (ℓ + 1) = b / (Kᵀ *ᵥ u (ℓ + 1)))

/-- `(u, v)` solves the scaling equations (4.14), p. 432:
`u ⊙ (K v) = a` and `v ⊙ (Kᵀ u) = b` (entrywise products). -/
def IsScalingSolution {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (u : Fin n → ℝ) (v : Fin m → ℝ) : Prop :=
  u * (K *ᵥ v) = a ∧ v * (Kᵀ *ᵥ u) = b

/-- The scaled coupling `P = diag(u) K diag(v)`, i.e. `P_{i,j} = u_i K_{i,j} v_j`
(the matrix `P^{(ℓ)}` of Theorem 4.2, p. 441). -/
def scaledCoupling {n m : ℕ} (u : Fin n → ℝ) (K : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ) :
    Matrix (Fin n) (Fin m) ℝ :=
  diagonal u * K * diagonal v

end CompOT.Sinkhorn


