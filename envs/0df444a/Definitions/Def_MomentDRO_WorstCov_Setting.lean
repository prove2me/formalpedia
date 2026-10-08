-- Prove2me | Definitions.Def_MomentDRO_WorstCov_Setting
-- name    : MomentDRO_WorstCov_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:23:48.633039+00:00
-- url     : https://prove2.me/theorems/f64b5771-0225-4ba2-9b60-8658b0ff820e
-- title:
--   Assumption 3 (p. 2), (1a)–(1b) (p. 4), §5.1 (p. 17), (19) (pp. 19–20) — the set D₁, the piecewise-linear cost, the SDP (19) and the mixture
-- statement:
--   This file fixes the objects of §5.2 of Delage and Ye. Throughout, $\xi\in\mathbb R^n$ is a random vector of asset returns and a **distribution** of $\xi$ is a Borel probability measure $P$ on $\mathbb R^n$ whose coordinates have finite second moments.
--
--   1. **Moments.** The mean is $\mathbb E_P[\xi]$ and, for a point $c\in\mathbb R^n$, the second-moment matrix about $c$ is $\mathbb E_P[(\xi-c)(\xi-c)^{\mathsf T}]$. For $c=0$ this is the uncentred second moment $\mathbb E_P[\xi\xi^{\mathsf T}]$.
--   2. **Loewner order.** For symmetric matrices, $A\preceq B$ means that $B-A$ is positive semidefinite.
--   3. **The distributional set of Assumption 3.** For $S\subseteq\mathbb R^n$, $\mu_0\in\mathbb R^n$, a matrix $\Sigma_0$ and $\gamma_1,\gamma_2\in\mathbb R$,
--   $$\mathcal D_1(S,\mu_0,\Sigma_0,\gamma_1,\gamma_2)=\Big\{P \;\Big|\; P(\xi\in S)=1,\ (\mathbb E[\xi]-\mu_0)^{\mathsf T}\Sigma_0^{-1}(\mathbb E[\xi]-\mu_0)\le\gamma_1,\ \mathbb E[(\xi-\mu_0)(\xi-\mu_0)^{\mathsf T}]\preceq\gamma_2\Sigma_0\Big\}.$$
--   4. **Piecewise-linear cost.** For $K\ge1$ pieces with slopes $a_k$ and intercepts $b_k$, the concave utility is $u(y)=\min_k a_ky+b_k$, and the cost of the inner problem (18) at a portfolio $x$ is
--   $$h(x,\xi)=\max_{k\in\{1,\dots,K\}}\big(-a_k\,\xi^{\mathsf T}x-b_k\big)=-u(\xi^{\mathsf T}x).$$
--   5. **The SDP (19).** Its variables are $\Lambda_k\in\mathbb R^{n\times n}$, $\lambda_k\in\mathbb R^n$, $\nu_k\in\mathbb R$ for $k=1,\dots,K$. They are feasible when
--   $$\sum_k\Lambda_k\preceq\gamma_2\hat\Sigma+\hat\mu\hat\mu^{\mathsf T},\qquad \sum_k\lambda_k=\hat\mu,\qquad \sum_k\nu_k=1,\qquad \begin{bmatrix}\Lambda_k&\lambda_k\\ \lambda_k^{\mathsf T}&\nu_k\end{bmatrix}\succeq0\ \ \forall k,$$
--   and their objective value is $\sum_k\big(-a_k\,x^{\mathsf T}\lambda_k-b_k\nu_k\big)$.
--   6. **Mixture.** For weights $\nu_k$ and distributions $P_k$, the mixture $\sum_k\nu_kP_k$ is the law of $\xi=\zeta_{\tilde k}$, where $\zeta_k\sim P_k$ and $\tilde k$ is an independent index with $\mathbb P(\tilde k=k)=\nu_k$.
--
--   These objects are shared by Proposition 3 and every step of its proof.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; the Euclidean inner product is the dot product (no norm is used). $A\preceq B$ is `LoewnerLE A B := (B - A).PosSemidef`. A member of $\mathcal D_1$ is a probability measure with `MemLp 2` coordinates (the paper's "mean and covariance" are finite; without this a non-integrable expectation would read as $0$). $P(\xi\in S)=1$ is `∀ᵐ ξ ∂P, ξ ∈ S`. $\Sigma_0^{-1}$ is Mathlib's matrix inverse; every theorem assumes $\Sigma_0\succ0$. The convexity of $S$, $\mu_0\in\operatorname{int}S$ and the separation oracle of Assumption 3 are hypotheses of the paper's algorithms and are not part of the set. The objective of (19) carries the sign of the last display of the proof of Proposition 3 (p. 21); display (19a) on p. 19 prints $\sum_k a_k x^{\mathsf T}\lambda_k+\nu_kb_k$, a misprint. The block matrix is indexed by `Fin n ⊕ Fin 1`. The cost uses `Finset.sup'` over `Fin K` with `[NeZero K]`, so the maximum is never taken over an empty set. The mixture weights are `ENNReal.ofReal ν_k`.
-- source:
--   Delage & Ye, Distributionally robust optimization under moment uncertainty with application to data-driven problems, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 2 Assumption 3; p. 4 (1a)–(1b); p. 17 §5.1 (u, (16)); pp. 19–20 (18), (19a)–(19d); p. 20 construction of ξ* = ζ_k̃

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

namespace MomentDRO.WorstCov

open MeasureTheory
open Matrix
open scoped BigOperators

/-- The distributional set `D₁(S, µ₀, Σ₀, γ₁, γ₂)` of Assumption 3 (p. 2) and (1a)–(1b) (p. 4):
probability distributions with finite second moments such that `P(ξ ∈ S) = 1`,
`(E[ξ] - µ₀)ᵀ Σ₀⁻¹ (E[ξ] - µ₀) ≤ γ₁` and `E[(ξ - µ₀)(ξ - µ₀)ᵀ] ⪯ γ₂ Σ₀`. -/
def D1 {n : ℕ} (S : Set (Fin n → ℝ)) (μ0 : Fin n → ℝ) (Sig0 : Matrix (Fin n) (Fin n) ℝ)
    (γ1 γ2 : ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | MomentDRO.Conf.HasSecondMoments P ∧ (∀ᵐ ξ ∂P, ξ ∈ S) ∧
    MomentDRO.Conf.quadForm Sig0⁻¹ (MomentDRO.Conf.meanVec P - μ0) ≤ γ1 ∧
    MomentDRO.Conf.LoewnerLE (MomentDRO.Conf.secondMomentAbout P μ0) (γ2 • Sig0)}

/-- The piecewise-linear cost `max_k (-a_k ξᵀx - b_k)` of problem (18), i.e. `-u(ξᵀx)` for the
concave utility `u(y) = min_k a_k y + b_k` with `K ≥ 1` pieces. -/
noncomputable def pwCost {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x ξ : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k : Fin K => -(a k) * (ξ ⬝ᵥ x) - b k)

/-- The bordered matrix `[A v; vᵀ c]` of size `(n+1) × (n+1)`, indexed by `Fin n ⊕ Fin 1`. -/
def bordered {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (c : ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks A (Matrix.of fun i (_ : Fin 1) => v i) (Matrix.of fun (_ : Fin 1) j => v j)
    (Matrix.of fun _ _ => c)

/-- Feasibility in the SDP (19): constraints (19b), (19c) and (19d). -/
def Feasible19 {n K : ℕ} (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (γ2 : ℝ)
    (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ) (nu : Fin K → ℝ) : Prop :=
  MomentDRO.Conf.LoewnerLE (∑ k, Lam k) (γ2 • Sighat + Matrix.vecMulVec μhat μhat) ∧
  (∑ k, lam k = μhat ∧ ∑ k, nu k = 1) ∧
  ∀ k, (bordered (Lam k) (lam k) (nu k)).PosSemidef

/-- The objective of the SDP (19), with the sign of the last display of the proof of
Proposition 3 (p. 21): `∑_k (-a_k xᵀλ_k - b_k ν_k)`. -/
def obj19 {n K : ℕ} (a b : Fin K → ℝ) (x : Fin n → ℝ) (lam : Fin K → Fin n → ℝ)
    (nu : Fin K → ℝ) : ℝ :=
  ∑ k, (-(a k) * (x ⬝ᵥ lam k) - b k * nu k)

/-- The mixture `∑_k ν_k P_k`: the law of `ξ = ζ_k̃` for an independent index `k̃` with
`P(k̃ = k) = ν_k` and `ζ_k ∼ P_k`. -/
noncomputable def mixture {n K : ℕ} (nu : Fin K → ℝ) (Pk : Fin K → Measure (Fin n → ℝ)) :
    Measure (Fin n → ℝ) :=
  ∑ k, ENNReal.ofReal (nu k) • Pk k

end MomentDRO.WorstCov


