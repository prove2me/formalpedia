-- Prove2me | Definitions.Def_PropVolSampling_Reduction_Model
-- name    : PropVolSampling_Reduction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:45.439627+00:00
-- url     : https://prove2.me/theorems/56cad582-3f22-462c-b234-a332688163c8
-- title:
--   Definitions 1.1–1.2, (1)–(3), §2.1 — A-objective, relaxation, E_k, proportional volume sampling, approximate (d−1, d)-wise independence
-- statement:
--   Fix integers $d,n\ge 0$ and a real $d\times n$ matrix $V=[v_1,\dots,v_n]$ with columns $v_i\in\mathbb R^d$; write $[n]=\{1,\dots,n\}$. This file sets up the objects of the A-optimal design problem and of proportional volume sampling.
--
--   1. **Submatrices.** For $S\subseteq[n]$, $V_S$ is the $d\times|S|$ submatrix of the columns indexed by $S$, and for a weight vector $x\in\mathbb R^n$, $V_S(x)$ is the $d\times|S|$ matrix with columns $\sqrt{x_i}\,v_i$, $i\in S$.
--   2. **Gram matrices.** $V_SV_S^\top=\sum_{i\in S}v_iv_i^\top$ and $V(x)V(x)^\top=\sum_{i=1}^n x_i v_iv_i^\top$, both $d\times d$.
--   3. **Monomials.** $x^L=\prod_{i\in L}x_i$ for $L\subseteq[n]$, with $x^\emptyset=1$.
--   4. **Elementary symmetric functions of the spectrum.** For a square real matrix $M$, $E_k(M)=e_k(\lambda_1,\dots,\lambda_m)$, the degree-$k$ elementary symmetric polynomial of the eigenvalues of $M$ counted with multiplicity; in particular $E_0(M)=1$.
--   5. **The A-objective.** $\operatorname{tr}(M^{-1})$ for a $d\times d$ matrix $M$.
--   6. **The relaxation (1)–(3).** $x$ is *feasible* if $\sum_i x_i=k$ and $0\le x_i\le 1$ for all $i$. It is *optimal* (with finite value $\mathrm{CP}$) if it is feasible, $\sum_i x_iv_iv_i^\top$ is positive definite, and
--   $$\operatorname{tr}\Big(\sum_{i=1}^n x_iv_iv_i^\top\Big)^{-1}\le\operatorname{tr}\Big(\sum_{i=1}^n y_iv_iv_i^\top\Big)^{-1}$$
--   for every feasible $y$ whose matrix $\sum_i y_iv_iv_i^\top$ is positive definite.
--   7. **Measures on sets.** A probability measure $\mu$ on $\mathcal U_{\le k}$ (subsets of $[n]$ of size at most $k$) is a function $\mu\ge 0$ on subsets of $[n]$ with total mass $1$ vanishing on sets of size $>k$; measures on $\mathcal U_k$ are those supported on sets of size exactly $k$. $\Pr_{\mathcal S\sim\mu}[T\subseteq\mathcal S]=\sum_{S\supseteq T}\mu(S)$.
--   8. **Approximate independence (Definition 1.2).** $\mu$ is *$\alpha$-approximate $(d-1,d)$-wise independent with respect to $x$* if for all $T,R\subseteq[n]$ with $|T|=d-1$, $|R|=d$,
--   $$\Pr_{\mathcal S\sim\mu}[T\subseteq\mathcal S]\cdot x^R\le\alpha\,x^T\cdot\Pr_{\mathcal S\sim\mu}[R\subseteq\mathcal S].$$
--   9. **Proportional volume sampling (Definition 1.1).** The distribution $\mu'$ picks $S$ with probability $\mu(S)\det(V_SV_S^\top)/Z$, where $Z=\sum_{S'}\mu(S')\det(V_{S'}V_{S'}^\top)$; $\mathbb E_{\mathcal S\sim\mu'}[f(\mathcal S)]=\sum_S\frac{\mu(S)\det(V_SV_S^\top)}{Z}f(S)$.
--
--   These are the objects in which Theorem 1.3 and every step of its proof in §2 are stated.
--
--   **Formalization Note** Index sets are `Finset (Fin n)`. $E_k(M)$ is `Multiset.esymm k` of the roots of the characteristic polynomial over $\mathbb R$; for the real symmetric matrices to which it is applied the characteristic polynomial splits, so these are all eigenvalues with multiplicity (the page defines $E_k$ for positive semidefinite $M$). Lean's matrix inverse is $0$ on singular matrices, so the A-objective is a junk $0$ there; every theorem comparing A-objectives assumes positive definiteness of the inverted matrix. Definition 1.2 is stated cross-multiplied, which agrees with the page's ratio form whenever the ratio is defined. The relaxation's value is $+\infty$ at feasible points with a singular matrix, which is why optimality only compares against positive-definite feasible points.
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 2 (problem), p. 3 Definitions 1.1–1.2, p. 7 relaxation (1)–(3) and §2.1 notation, p. 8 Algorithm 1

import Mathlib

namespace PropVolSampling.Reduction
open Matrix Finset

variable {d n : ℕ}

/-- `V_S`: the `d × |S|` submatrix of `V` whose columns are the `v_i`, `i ∈ S`. -/
def colSub (V : Matrix (Fin d) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix (Fin d) S ℝ :=
  V.submatrix id (Subtype.val)

/-- `V_S(x)`: the `d × |S|` matrix whose columns are `√x_i v_i`, `i ∈ S`. -/
noncomputable def colSubW (V : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) (S : Finset (Fin n)) :
    Matrix (Fin d) S ℝ :=
  fun a i => Real.sqrt (x i) * V a i

/-- `V_S V_Sᵀ = ∑_{i ∈ S} v_i v_iᵀ`, a `d × d` matrix. -/
def gram (V : Matrix (Fin d) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix (Fin d) (Fin d) ℝ :=
  colSub V S * (colSub V S)ᵀ

/-- `V(x) V(x)ᵀ = ∑_{i=1}^n x_i v_i v_iᵀ`, a `d × d` matrix. -/
def weightedGram (V : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, x i • vecMulVec (fun a => V a i) (fun a => V a i)

/-- `x^L = ∏_{i ∈ L} x_i` (so `x^∅ = 1`). -/
def xPow (x : Fin n → ℝ) (L : Finset (Fin n)) : ℝ :=
  ∏ i ∈ L, x i

/-- `E_k(M) = e_k(λ_1, …, λ_m)`: the degree-`k` elementary symmetric polynomial of the eigenvalues
of `M`, taken (with multiplicity) as the real roots of the characteristic polynomial. For the real
symmetric matrices to which it is applied the characteristic polynomial splits over `ℝ`. -/
noncomputable def Ek {m : Type*} [Fintype m] [DecidableEq m] (k : ℕ) (M : Matrix m m ℝ) : ℝ :=
  (M.charpoly.roots).esymm k

/-- The A-optimality objective `tr(M⁻¹)`. Mathlib's `M⁻¹` is `0` when `M` is singular, so this
value is a junk `0` on singular `M`; statements comparing it carry a `PosDef` hypothesis. -/
noncomputable def aObj (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (M⁻¹).trace

/-- Constraints (2)–(3) of the relaxation: `∑ x_i = k` and `0 ≤ x_i ≤ 1`. -/
def IsRelaxFeasible (k : ℕ) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = k

/-- `x` is an optimal solution of the relaxation (1)–(3) with finite value `CP`: it is feasible,
`∑ x_i v_i v_iᵀ` is positive definite, and its objective is at most that of every feasible `y`
whose matrix `∑ y_i v_i v_iᵀ` is positive definite (the objective is `+∞` at the others). -/
def IsRelaxOptimal (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ) (x : Fin n → ℝ) : Prop :=
  IsRelaxFeasible k x ∧ (weightedGram V x).PosDef ∧
    ∀ y, IsRelaxFeasible k y → (weightedGram V y).PosDef →
      aObj (weightedGram V x) ≤ aObj (weightedGram V y)

/-- `μ` is a probability measure on `U_{≤k}`, the subsets of `[n]` of size at most `k`
(measures on `U_k` are the special case supported on sets of size exactly `k`). -/
def IsSetDist (k : ℕ) (μ : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ μ S) ∧ ∑ S, μ S = 1 ∧ ∀ S, μ S ≠ 0 → S.card ≤ k

/-- `Pr_{S∼μ}[T ⊆ S]`. -/
def prSup (μ : Finset (Fin n) → ℝ) (T : Finset (Fin n)) : ℝ :=
  ∑ S ∈ univ.filter (fun S => T ⊆ S), μ S

/-- Definition 1.2 (cross-multiplied): `μ` is `α`-approximate `(d − 1, d)`-wise independent with
respect to `x`: for all `T, R ⊆ [n]` with `|T| = d − 1`, `|R| = d`,
`Pr_μ[T ⊆ S] · x^R ≤ α · x^T · Pr_μ[R ⊆ S]`. -/
def IsApproxIndep (d : ℕ) (α : ℝ) (x : Fin n → ℝ) (μ : Finset (Fin n) → ℝ) : Prop :=
  ∀ T R : Finset (Fin n), T.card = d - 1 → R.card = d →
    prSup μ T * xPow x R ≤ α * xPow x T * prSup μ R

/-- Definition 1.1: the unnormalised weight `μ(S) det(V_S V_Sᵀ)` of proportional volume sampling. -/
noncomputable def pvsWeight (V : Matrix (Fin d) (Fin n) ℝ) (μ : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  μ S * (gram V S).det

/-- The normaliser `∑_{S'} μ(S') det(V_{S'} V_{S'}ᵀ)` of proportional volume sampling. -/
noncomputable def pvsNormalizer (V : Matrix (Fin d) (Fin n) ℝ) (μ : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S, pvsWeight V μ S

/-- `E_{S∼μ'}[f(S)]`, where `μ'` is proportional volume sampling with measure `μ`:
`Pr_{μ'}[S] = μ(S) det(V_S V_Sᵀ) / ∑_{S'} μ(S') det(V_{S'} V_{S'}ᵀ)`. -/
noncomputable def pvsExpect (V : Matrix (Fin d) (Fin n) ℝ) (μ : Finset (Fin n) → ℝ)
    (f : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S, pvsWeight V μ S / pvsNormalizer V μ * f S

end PropVolSampling.Reduction


