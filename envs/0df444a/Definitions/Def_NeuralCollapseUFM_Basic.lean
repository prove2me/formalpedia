-- Prove2me | Definitions.Def_NeuralCollapseUFM_Basic
-- name    : NeuralCollapseUFM_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T02:15:00.961606+00:00
-- url     : https://prove2.me/theorems/4376b38f-c3bb-437f-9852-5bd16caa6ac2
-- title:
--   Unconstrained feature model with regularized cross-entropy: objective, nuclear norm, Simplex ETF Gram matrix, landscape notions
-- statement:
--   Objects of Sections 2.2 and 3 and Appendices A-C of Zhu, Ding, Zhou, Li, You, Sulam and Qu (2021).
--
--   1. **Cross-entropy (eq. 3).** For logits $z\in\mathbb{R}^K$ and the one-hot label $y_k$, $\mathcal L_{CE}(z,y_k)=-\log\big(e^{z_k}/\sum_{i=1}^K e^{z_i}\big)$.
--   2. **Norms.** $\|v\|_2^2=\sum_i v_i^2$, $\|A\|_F^2=\sum_{i,j}A_{ij}^2$, $\|A\|$ is the spectral (operator $\ell^2\to\ell^2$) norm, and $\|Z\|_*=\sum_k\sigma_k(Z)$ is the nuclear norm.
--   3. **Simplex ETF (Definition A.1).** $1_K1_K^\top$ is the all-ones matrix, and $\frac{K}{K-1}\big(I_K-\frac1K1_K1_K^\top\big)$ is the Gram matrix $M^\top M$ of the standard $K$-Simplex ETF $M=\sqrt{\frac{K}{K-1}}\big(I_K-\frac1K1_K1_K^\top\big)$.
--   4. **Unconstrained feature model (eqs. 4, 14, 15).** There are $K$ classes with $n$ samples each, $N=nK$. The parameters are a classifier $W\in\mathbb{R}^{K\times d}$ with rows $(w^k)^\top$, features $H=[h_{1,1}\cdots h_{K,n}]\in\mathbb{R}^{d\times N}$ and a bias $b\in\mathbb{R}^K$. The averaged cross-entropy of a logit matrix $Z\in\mathbb{R}^{K\times N}$ with columns $z_{k,i}$ is $g(Z)=\frac1N\sum_{k=1}^K\sum_{i=1}^n\mathcal L_{CE}(z_{k,i},y_k)$, and the objective is
--   $$f(W,H,b)=g(WH+b1^\top)+\frac{\lambda_W}2\|W\|_F^2+\frac{\lambda_H}2\|H\|_F^2+\frac{\lambda_b}2\|b\|_2^2.$$
--   5. **Gradient of $g$.** $[\nabla g(Z)]_{j,(k,i)}=\frac1N\big(\operatorname{softmax}(z_{k,i})_j-\mathbb 1[j=k]\big)$.
--   6. **Constant of Lemma B.5.** $c_2(c_1)=\frac1{1+c_1}\log\big((1+c_1)(K-1)\big)+\frac{c_1}{1+c_1}\log\frac{1+c_1}{c_1}$.
--   7. **Convex counterpart (eq. 37).** $\tilde f(Z,b)=g(Z+b1^\top)+\sqrt{\lambda_W\lambda_H}\|Z\|_*+\frac{\lambda_b}2\|b\|_2^2$.
--   8. **Landscape notions.** A critical point is a point where every directional derivative of $f$ vanishes. A global minimizer minimizes $f$ over all parameters. A strict saddle (footnote 3) is a critical point at which the Hessian has a negative eigenvalue, that is, $\frac{d^2}{dt^2}f(x+t\Delta)\big|_{t=0}<0$ for some direction $\Delta$.
--   9. **Collapsed solution (Theorem 3.1).** $(W,H,b)$ is collapsed if there are $w,b_0\in\mathbb{R}$ with $\|w^k\|_2=w$ for all $k$, $b=b_01$ with $b_0=0$ or $\lambda_b=0$, $h_{k,i}=\sqrt{\lambda_W/(\lambda_Hn)}\,w^k$ for all $k,i$, $\bar h_i=\frac1K\sum_jh_{j,i}=0$ for all $i$, and
--   $$WW^\top=w^2\,\frac{K}{K-1}\Big(I_K-\frac1K1_K1_K^\top\Big).$$
--
--   **Formalization Note** The parameters are the triple $(W,H,b)$ with the product topology. Column $(k,i)$ of $H$ is the feature $h_{k,i}$. The nuclear norm is the sum of the square roots of the eigenvalues of $ZZ^\top$ (the roots of its characteristic polynomial, with multiplicity). The gradient $\nabla g$ is written out explicitly. The collapsed form is stated with $WW^\top$ multiplied by $w^2$ instead of normalizing $W$ by $1/w$, so that it is defined when $w=0$ (see Theorem 3.1).
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Sections 2.2 and 3 (eqs. (3)-(6), footnote 3), Appendix A (Definition A.1, Lemma A.3), Appendix B (eqs. (14)-(15), Lemma B.5), Appendix C (eq. (37))

import Mathlib

/-!
Zhu, Ding, Zhou, Li, You, Sulam and Qu, *A Geometric Analysis of Neural Collapse with
Unconstrained Features*, arXiv:2105.02375v1 (2021): the cross-entropy loss (eq. (3)), the
unconstrained feature model with weight decay (eq. (4), restated as eqs. (14)-(15)), the Simplex
ETF (Definition A.1), the nuclear norm (Lemma A.3), the constant `c_2` of Lemma B.5, the
convex counterpart (37), and the notions of critical point, local and global minimizer and
strict saddle used in Section 3 (footnote 3, p. 4).
-/

open Matrix

noncomputable section

namespace NeuralCollapseUFM

variable {K d n : ℕ}

/-- Eq. (3), p. 7: the cross-entropy loss of a logit vector `z ∈ ℝ^K` for the one-hot label
`y_k`, `L_CE(z, y_k) = -log(exp(z_k) / ∑_i exp(z_i))`. -/
def ceLoss (z : Fin K → ℝ) (k : Fin K) : ℝ :=
  -Real.log (Real.exp (z k) / ∑ i, Real.exp (z i))

/-- Squared Euclidean norm `‖v‖₂²` of a vector (Notations, p. 6). -/
def sqNorm {m : Type*} [Fintype m] (v : m → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Squared Frobenius norm `‖A‖_F²` of a real matrix (Notations, p. 6). -/
def frobSq {m p : Type*} [Fintype m] [Fintype p] (A : Matrix m p ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- The all-ones matrix `1_K 1_K^T` (Notations, p. 6). -/
def onesMat (K : ℕ) : Matrix (Fin K) (Fin K) ℝ := Matrix.of fun _ _ => 1

/-- Definition A.1, p. 28: the Gram matrix `M^T M = K/(K-1) (I_K - (1/K) 1_K 1_K^T)` of the
standard `K`-Simplex ETF `M = sqrt(K/(K-1)) (I_K - (1/K) 1_K 1_K^T)`. -/
def etfGram (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  ((K : ℝ) / ((K : ℝ) - 1)) • ((1 : Matrix (Fin K) (Fin K) ℝ) - (1 / (K : ℝ)) • onesMat K)

/-- Section 2.2, p. 8: the parameters `(W, H, b)` of the unconstrained feature model, with
classifier `W ∈ ℝ^{K×d}` (rows `w^k`), features `H = [h_{1,1} ⋯ h_{K,n}] ∈ ℝ^{d×N}`, `N = nK`,
whose column `(k, i)` is the feature `h_{k,i}` of the `i`-th sample of class `k`, and bias
`b ∈ ℝ^K`. -/
abbrev Params (K d n : ℕ) : Type :=
  Matrix (Fin K) (Fin d) ℝ × Matrix (Fin d) (Fin K × Fin n) ℝ × (Fin K → ℝ)

/-- Eq. (14), p. 30: the logit matrix `W H + b 1^T ∈ ℝ^{K×N}`; its column `(k, i)` is
`W h_{k,i} + b`. -/
def logits (W : Matrix (Fin K) (Fin d) ℝ) (H : Matrix (Fin d) (Fin K × Fin n) ℝ)
    (b : Fin K → ℝ) : Matrix (Fin K) (Fin K × Fin n) ℝ :=
  W * H + Matrix.of fun j _ => b j

/-- Eq. (15), p. 30: the averaged cross-entropy
`g(Z) = (1/N) ∑_{k=1}^K ∑_{i=1}^n L_CE(z_{k,i}, y_k)` of a logit matrix `Z ∈ ℝ^{K×N}`, `N = Kn`,
whose column `(k, i)` is `z_{k,i}`. -/
def ceRisk (Z : Matrix (Fin K) (Fin K × Fin n) ℝ) : ℝ :=
  (1 / ((K : ℝ) * n)) * ∑ k, ∑ i, ceLoss (fun j => Z j (k, i)) k

/-- Eq. (4), p. 8 (restated as eq. (14), p. 30): the regularized cross-entropy objective
`f(W, H, b) = g(W H + b 1^T) + (λ_W/2) ‖W‖_F² + (λ_H/2) ‖H‖_F² + (λ_b/2) ‖b‖₂²`. -/
def objective (lamW lamH lamb : ℝ) (x : Params K d n) : ℝ :=
  ceRisk (logits x.1 x.2.1 x.2.2) + lamW / 2 * frobSq x.1 + lamH / 2 * frobSq x.2.1 +
    lamb / 2 * sqNorm x.2.2

/-- Eqs. (17)-(18), p. 32: the gradient `∇g(Z) ∈ ℝ^{K×N}` of the averaged cross-entropy (15),
written out: its entry `(j, (k, i))` is `(1/N) (softmax(z_{k,i})_j - [j = k])`. -/
def ceRiskGrad (Z : Matrix (Fin K) (Fin K × Fin n) ℝ) : Matrix (Fin K) (Fin K × Fin n) ℝ :=
  Matrix.of fun j c =>
    (1 / ((K : ℝ) * n)) *
      (Real.exp (Z j c) / ∑ l, Real.exp (Z l c) - if j = c.1 then 1 else 0)

/-- The spectral (operator) norm `‖A‖` of a real matrix, as the operator norm of
`A : ℓ²(p) → ℓ²(m)` (used in eq. (43), p. 41 and in Lemma C.3). -/
def opNorm {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p] (A : Matrix m p ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-- Lemma A.3, p. 28: the nuclear norm `‖Z‖_* = ∑_k σ_k(Z)`, computed as the sum of the square
roots of the eigenvalues of `Z Z^T` (the roots of its characteristic polynomial, with
multiplicity). -/
def nuclearNorm {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] (Z : Matrix m p ℝ) : ℝ :=
  (((Z * Zᵀ).charpoly.roots).map Real.sqrt).sum

/-- Lemma B.5, p. 36: the constant
`c_2 = (1/(1+c_1)) log((1+c_1)(K-1)) + (c_1/(1+c_1)) log((1+c_1)/c_1)`. -/
def cTwo (K : ℕ) (c1 : ℝ) : ℝ :=
  1 / (1 + c1) * Real.log ((1 + c1) * ((K : ℝ) - 1)) + c1 / (1 + c1) * Real.log ((1 + c1) / c1)

/-- Eq. (37), p. 38: the convex counterpart
`f̃(Z, b) = g(Z + b 1^T) + sqrt(λ_W λ_H) ‖Z‖_* + (λ_b/2) ‖b‖₂²`. -/
def convexObjective (lamW lamH lamb : ℝ) (Z : Matrix (Fin K) (Fin K × Fin n) ℝ)
    (b : Fin K → ℝ) : ℝ :=
  ceRisk (Z + Matrix.of fun j _ => b j) + Real.sqrt (lamW * lamH) * nuclearNorm Z +
    lamb / 2 * sqNorm b

/-- A critical point `∇F(x) = 0` (Section 3.2 and Appendix C, p. 38), written as the vanishing of
every directional derivative `d/dt F(x + t Δ)|_{t=0}`. -/
def IsCriticalPoint {E : Type*} [AddCommGroup E] [Module ℝ E] (F : E → ℝ) (x : E) : Prop :=
  ∀ Δ : E, HasDerivAt (fun t : ℝ => F (x + t • Δ)) 0 0

/-- A global minimizer of `F` (Theorem 3.1, p. 9). -/
def IsGlobalMinimizer {E : Type*} (F : E → ℝ) (x : E) : Prop :=
  ∀ y : E, F x ≤ F y

/-- Footnote 3, p. 4: the Hessian of `F` at `x` has a negative eigenvalue, i.e. there is a
direction `Δ` with negative curvature `∇²F(x)[Δ, Δ] = d²/dt² F(x + t Δ)|_{t=0} < 0`. -/
def HasNegativeCurvature {E : Type*} [AddCommGroup E] [Module ℝ E] (F : E → ℝ) (x : E) :
    Prop :=
  ∃ Δ : E, deriv (deriv fun t : ℝ => F (x + t • Δ)) 0 < 0

/-- Footnote 3, p. 4: a strict saddle is a critical point at which the Hessian has at least one
negative eigenvalue. -/
def IsStrictSaddle {E : Type*} [AddCommGroup E] [Module ℝ E] (F : E → ℝ) (x : E) : Prop :=
  IsCriticalPoint F x ∧ HasNegativeCurvature F x

/-- Theorem 3.1, eqs. (5)-(6), p. 9, in the form established by its proof (Appendix B,
conditions (a)-(d), p. 31): all rows of `W` have the same norm `w`, `b = b 1` with `b = 0` or
`λ_b = 0`, `h_{k,i} = sqrt(λ_W/(λ_H n)) w^k`, the class-wise means `h̄_i = (1/K) ∑_j h_{j,i}`
vanish, and `W W^T = w² · K/(K-1) (I_K - (1/K) 1_K 1_K^T)`. -/
def IsCollapsedSolution (lamW lamH lamb : ℝ) (x : Params K d n) : Prop :=
  ∃ w b0 : ℝ,
    (∀ k, Real.sqrt (sqNorm (x.1 k)) = w) ∧
    (x.2.2 = fun _ => b0) ∧ (b0 = 0 ∨ lamb = 0) ∧
    (∀ k i, (fun r => x.2.1 r (k, i)) = Real.sqrt (lamW / (lamH * n)) • x.1 k) ∧
    (∀ i, (1 / (K : ℝ)) • (∑ j, fun r => x.2.1 r (j, i)) = 0) ∧
    x.1 * x.1ᵀ = w ^ 2 • etfGram K

end NeuralCollapseUFM


