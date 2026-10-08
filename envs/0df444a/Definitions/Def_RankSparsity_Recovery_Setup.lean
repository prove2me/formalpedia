-- Prove2me | Definitions.Def_RankSparsity_Recovery_Setup
-- name    : RankSparsity_Recovery_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:06.190976+00:00
-- url     : https://prove2.me/theorems/174f30ab-cabd-4df1-b7d9-a36a8617a6fa
-- title:
--   ℓ₁ norm, support, sign, Ω(M), T(M), μ (1.2), ξ (1.1), program (1.3) and subgradients
-- statement:
--   This file fixes the objects of the rank-sparsity decomposition problem for real $n\times n$ matrices.
--
--   1. The **support** of $M$ is $\operatorname{support}(M)=\{(i,j) : M_{ij}\neq 0\}$, the **$\ell_1$ norm** is $\|M\|_1=\sum_{i,j}|M_{ij}|$, and $\operatorname{sign}(M)$ is the matrix with entries $+1$, $-1$ or $0$ according as $M_{ij}>0$, $M_{ij}<0$ or $M_{ij}=0$.
--   2. The **sparse tangent space** at $M$ is
--   $$\Omega(M)=\{N\in\mathbb R^{n\times n} : \operatorname{support}(N)\subseteq\operatorname{support}(M)\},$$
--   with orthogonal projection $P_{\Omega(M)}$ (keep the entries in $\operatorname{support}(M)$, zero the others) and $P_{\Omega(M)^c}=I-P_{\Omega(M)}$.
--   3. If $M=U\Sigma V^{T}$ is a compact SVD with $U,V\in\mathbb R^{n\times k}$, $k=\operatorname{rank}(M)$, the **low-rank tangent space** is
--   $$T(M)=\{UX^{T}+YV^{T} : X,Y\in\mathbb R^{n\times k}\}.$$
--   4. With $\|\cdot\|$ the spectral norm (largest singular value) and $\|\cdot\|_\infty$ the largest entry in magnitude, the two incoherence quantities are
--   $$\xi(M)=\max_{N\in T(M),\ \|N\|\le 1}\|N\|_\infty,\qquad \mu(M)=\max_{N\in\Omega(M),\ \|N\|_\infty\le 1}\|N\|.$$
--   5. For a trade-off parameter $\gamma$ and $C\in\mathbb R^{n\times n}$, program (1.3) minimizes $\gamma\|A\|_1+\|B\|_*$ subject to $A+B=C$, where $\|B\|_*$ is the nuclear norm (sum of singular values). A pair $(\hat A,\hat B)$ is an **optimum** if it is feasible and no feasible pair has a smaller objective; it is the **unique optimum** if it is feasible and every other feasible pair has a strictly larger objective.
--   6. $Z$ is a **subgradient** of $f$ at $\hat x$ if $f(x)\ge f(\hat x)+\langle Z,x-\hat x\rangle$ for all $x$, with the trace inner product $\langle A,B\rangle=\sum_{i,j}A_{ij}B_{ij}$.
--
--   These are the objects in terms of which every statement of the mission (Propositions 1–2 and Theorem 2) is written.
--
--   **Formalization Note** The SVD is carried as data `S : SVD M r` from the published `matrix_completion_svd` module (positive singular values, orthonormal singular vectors, $M=\sum_k\sigma_k u_kv_k^{T}$, which forces $r=\operatorname{rank}M$); $T(M)$ and $\xi$ are attached to that datum, and $UV^{T}$ is the imported `signMatrix S` (not the entrywise sign, which is `entrySign`). $\Omega(M)$ is stated literally as support inclusion. $\mu$ and $\xi$ are real suprema (`sSup`) of sets that contain $0$ and are bounded, so they equal the maxima of (1.1)–(1.2); the spectral norm, $\|\cdot\|_\infty$, nuclear norm, $P_T$, $P_{T^\perp}$ and $P_\Omega$ are the published `matrix_completion_basic`/`matrix_completion_tangent` objects.
-- source:
--   Chandrasekaran, Sanghavi, Parrilo, Willsky, Rank-Sparsity Incoherence for Matrix Decomposition, arXiv:0906.2220v1, (1.1)–(1.3), pp. 2–3; (3.2), (3.4), p. 7; §4.1 (projections and subgradient), pp. 8–9

import Definitions.Def_matrix_completion_tangent
import Mathlib.Data.Real.Sign

namespace RankSparsity.Recovery

open MatrixCompletion
open scoped BigOperators

/-- The support of a square real matrix: the set of positions `(i, j)` with
`M i j ≠ 0` (p. 7, used in (3.4)). -/
noncomputable def supp {n : ℕ} (M : RealMatrix n n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => M p.1 p.2 ≠ 0)

/-- The entrywise ℓ₁ norm `‖M‖₁ = ∑_{i,j} |M i j|` (p. 3). -/
noncomputable def l1Norm {n : ℕ} (M : RealMatrix n n) : ℝ :=
  ∑ i, ∑ j, |M i j|

/-- The entrywise sign matrix `sign(M)`: `+1` where `M i j > 0`, `-1` where
`M i j < 0`, `0` where `M i j = 0` (p. 9). Not to be confused with
`MatrixCompletion.signMatrix`, which is `UVᵀ`. -/
noncomputable def entrySign {n : ℕ} (M : RealMatrix n n) : RealMatrix n n :=
  fun i j => Real.sign (M i j)

/-- Membership in the tangent space `Ω(M) = {N | support(N) ⊆ support(M)}` (3.4). -/
def InOmega {n : ℕ} (M N : RealMatrix n n) : Prop :=
  supp N ⊆ supp M

/-- The orthogonal projection `P_{Ω(M)}`: keep the entries in `support(M)`, set the
others to zero (p. 8). -/
noncomputable def projOmega {n : ℕ} (M X : RealMatrix n n) : RealMatrix n n :=
  samplingProjection (supp M) X

/-- The orthogonal projection `P_{Ω(M)ᶜ} = I - P_{Ω(M)}`: keep the entries outside
`support(M)`, set the others to zero. -/
noncomputable def projOmegaC {n : ℕ} (M X : RealMatrix n n) : RealMatrix n n :=
  X - samplingProjection (supp M) X

/-- Membership in the tangent space `T(M) = {U Xᵀ + Y Vᵀ | X, Y ∈ ℝ^{n×k}}` (3.2),
where `M = U Σ Vᵀ` is the compact SVD `S` (columns `u k`, `v k`). -/
def InT {n r : ℕ} {M : RealMatrix n n} (S : SVD M r) (N : RealMatrix n n) : Prop :=
  ∃ X Y : Fin r → Fin n → ℝ,
    N = ∑ k, Matrix.vecMulVec (S.u k) (X k) + ∑ k, Matrix.vecMulVec (Y k) (S.v k)

/-- `μ(M) = max { ‖N‖ : N ∈ Ω(M), ‖N‖_∞ ≤ 1 }` (1.2), with `‖·‖` the spectral norm
and `‖·‖_∞` the largest entry in magnitude. -/
noncomputable def mu {n : ℕ} (M : RealMatrix n n) : ℝ :=
  sSup (spectralNorm '' {N : RealMatrix n n | InOmega M N ∧ entrySupNorm N ≤ 1})

/-- `ξ(M) = max { ‖N‖_∞ : N ∈ T(M), ‖N‖ ≤ 1 }` (1.1), with `T(M)` built from the
SVD `S` of `M` as in (3.2). -/
noncomputable def xi {n r : ℕ} {M : RealMatrix n n} (S : SVD M r) : ℝ :=
  sSup (entrySupNorm '' {N : RealMatrix n n | InT S N ∧ spectralNorm N ≤ 1})

/-- The objective `γ‖A‖₁ + ‖B‖_*` of program (1.3). -/
noncomputable def objective {n : ℕ} (γ : ℝ) (A B : RealMatrix n n) : ℝ :=
  γ * l1Norm A + nuclearNorm B

/-- `(Â, B̂)` is an optimum of (1.3): it is feasible (`Â + B̂ = C`) and its objective
is at most that of every feasible pair. -/
def IsOptimum {n : ℕ} (γ : ℝ) (C Ahat Bhat : RealMatrix n n) : Prop :=
  Ahat + Bhat = C ∧
    ∀ A B : RealMatrix n n, A + B = C → objective γ Ahat Bhat ≤ objective γ A B

/-- `(Â, B̂)` is the unique optimum of (1.3): it is feasible and every other
feasible pair has strictly larger objective. -/
def IsUniqueOptimum {n : ℕ} (γ : ℝ) (C Ahat Bhat : RealMatrix n n) : Prop :=
  Ahat + Bhat = C ∧
    ∀ A B : RealMatrix n n, A + B = C → (A, B) ≠ (Ahat, Bhat) →
      objective γ Ahat Bhat < objective γ A B

/-- `Z` is a subgradient of `f` at `X₀`: `f X ≥ f X₀ + ⟨Z, X - X₀⟩` for all `X`
(p. 9), with the trace inner product `⟨A, B⟩ = ∑ A i j * B i j`. -/
def IsSubgrad {n : ℕ} (f : RealMatrix n n → ℝ) (X₀ Z : RealMatrix n n) : Prop :=
  ∀ X : RealMatrix n n, f X₀ + matrixInner Z (X - X₀) ≤ f X

end RankSparsity.Recovery


