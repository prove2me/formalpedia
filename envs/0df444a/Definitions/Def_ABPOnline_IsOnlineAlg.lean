-- Prove2me | Definitions.Def_ABPOnline_IsOnlineAlg
-- name    : ABPOnline_IsOnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:41.194301+00:00
-- url     : https://prove2.me/theorems/121765ec-a1b5-4ba5-96e7-f779eacae9d4
-- title:
--   Deterministic online algorithm, Gaussian matrix law and the success event
-- statement:
--   Let $G\in\mathbb R^{M\times N}$ have i.i.d. standard Gaussian entries, with columns $g_1,\dots,g_N\in\mathbb R^M$ revealed one at a time. A **deterministic online algorithm** is a sequence of signs $\sigma_1,\dots,\sigma_N\in\{-1,+1\}$ such that $\sigma_k$ is measurable with respect to $\mathcal F^G_k=\sigma(g_1,\dots,g_k)$. Its normalized partial sums are
--   $$
--   X_k:=\frac{1}{\sqrt N}\sum_{j=1}^k\sigma_j g_j,\qquad 0\le k\le N,
--   $$
--   and the algorithm **succeeds at margin** $\kappa$ if $X_N\ge\kappa\mathbf 1_M$ coordinatewise, i.e. $\min_{1\le i\le M}X_{N,i}\ge\kappa$. Note $X_{N,i}=(G\sigma)_i/\sqrt N$.
--
--   This is the information pattern of the online problem: each sign is chosen irrevocably before the next column arrives.
--
--   **Formalization Note** The matrix is a function on $\{0,\dots,M-1\}\times\{0,\dots,N-1\}$ with the product of standard Gaussians as its law; columns are indexed from $0$, so column $k$ is the paper's $g_{k+1}$. Measurability with respect to the first columns is written as: $\sigma_k$ is a Borel function of the matrix taking equal values on matrices that agree in columns $0,\dots,k$, which on this canonical space is the same condition. The minimum over rows is a universal quantifier.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), §2.1, Definition 2.1 and (6), p.5 (PDF p.6)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ABPOnline

/-- The law of an `M × N` matrix `G` with i.i.d. standard Gaussian entries (arXiv:2609.02124,
§2.1, printed p.5, PDF p.6): the product of `gaussianReal 0 1` over the `M·N` entries.

**Formalization Note** The matrix is a function `Fin M × Fin N → ℝ`; its `k`-th column is
`fun i => G (i, k)`. Columns are indexed from `0`, so column `k` here is the paper's `g_{k+1}`. -/
noncomputable def gaussMat (M N : ℕ) : Measure (Fin M × Fin N → ℝ) :=
  Measure.pi fun _ : Fin M × Fin N => gaussianReal 0 1

/-- A deterministic online algorithm for `M × N` instances (arXiv:2609.02124, Definition 2.1,
p.5): signs `σ_k ∈ {−1,+1}` such that `σ_k` is measurable with respect to the first `k` columns.

**Formalization Note** `σ k G` is the sign chosen for column `k` (0-based, the paper's `σ_{k+1}`).
"`σ_k` is `F^G_k`-measurable" is written as: `σ k` is Borel measurable on the matrix space and
takes equal values on matrices that agree in columns `0, …, k`. On the canonical space of the
matrix this is equivalent to measurability with respect to `σ(g₁, …, g_{k+1})` in the paper's
indexing. -/
def IsOnlineAlg (M N : ℕ) (σ : Fin N → (Fin M × Fin N → ℝ) → ℝ) : Prop :=
  ∀ k : Fin N,
    (∀ G, σ k G = 1 ∨ σ k G = -1) ∧ Measurable (σ k) ∧
      ∀ G G' : Fin M × Fin N → ℝ, (∀ i : Fin M, ∀ j : Fin N, j ≤ k → G (i, j) = G' (i, j)) →
        σ k G = σ k G'

/-- The normalized terminal sum `X_N = N^{-1/2} ∑_{k} σ_k g_k ∈ ℝ^M` of (6) (arXiv:2609.02124,
p.5), coordinate `i`. It equals `(Gσ)_i/√N`. -/
noncomputable def termX {M N : ℕ} (σ : Fin N → (Fin M × Fin N → ℝ) → ℝ)
    (G : Fin M × Fin N → ℝ) (i : Fin M) : ℝ :=
  (1 / Real.sqrt N) * ∑ k : Fin N, σ k G * G (i, k)

/-- The success event `{min_{1 ≤ i ≤ M} X_{N,i} ≥ κ}` of an online algorithm at margin `κ`
(arXiv:2609.02124, Definitions 2.1–2.2, p.5).

**Formalization Note** The minimum over rows is written as `∀ i`; for `M = 0` both readings are
vacuous. -/
def successSet {M N : ℕ} (σ : Fin N → (Fin M × Fin N → ℝ) → ℝ) (κ : ℝ) :
    Set (Fin M × Fin N → ℝ) :=
  {G | ∀ i : Fin M, κ ≤ termX σ G i}

end ABPOnline


