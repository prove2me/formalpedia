-- Prove2me | Definitions.Def_DimensionalCollapse_Basic
-- name    : DimensionalCollapse_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T06:49:59.210864+00:00
-- url     : https://prove2.me/theorems/a4838283-42ca-45a9-a4ec-6ff393f7ccde
-- title:
--   InfoNCE linear models, gradients, the matrix $X$ and differentiable SVDs
-- statement:
--   Objects of Sections 3–5 and Appendices A–B of Jing, Vincent, LeCun and Tian (ICLR 2022).
--
--   1. **Data and embeddings.** There are $N$ pairs of inputs $(x_i,x_i')$, $x_i,x_i'\in\mathbb{R}^n$, where $x_i'$ is an augmented view of $x_i$. A linear model $W\in\mathbb{R}^{d\times n}$ gives embeddings $z_i=Wx_i$, $z_i'=Wx_i'$. The two-layer model has $W_1,W_2\in\mathbb{R}^{d\times d}$ (inputs in $\mathbb{R}^d$) and $z=W_2W_1x$. We write $|v|^2=\sum_c v_c^2$.
--   2. **InfoNCE (eq. 2).** With $Z_i=\sum_{j\neq i}e^{-|z_i-z_j|^2/2}+e^{-|z_i-z_i'|^2/2}$,
--   $$L=-\sum_{i=1}^N\log\frac{e^{-|z_i-z_i'|^2/2}}{Z_i}.$$
--   The softmax weights are $\alpha_{ij}=e^{-|z_i-z_j|^2/2}/Z_i$ for $j\neq i$ and $\alpha_{ii}=e^{-|z_i-z_i'|^2/2}/Z_i$, so $\sum_j\alpha_{ij}=1$.
--   3. **Gradients (Lemma 1, eq. 3).** $g_{z_i}$ and $g_{z_i'}$ are the gradients of $L$ with respect to $z_i$ and $z_i'$, and $G=\sum_i(g_{z_i}x_i^\top+g_{z_i'}x_i'^\top)\in\mathbb{R}^{d\times n}$, evaluated at $z=Wx$. The gradient $\partial F/\partial W$ of a function of a matrix is the matrix of its partial derivatives $\partial F/\partial W_{ab}$.
--   4. **The matrix $X$ (eq. 6, in the form of Appendix B.2).**
--   $$X=\sum_i\Big(\sum_{j\neq i}\alpha_{ij}(x_i'-x_j)+\sum_{j\neq i}\alpha_{ji}(x_i-x_j)\Big)x_i^\top-\sum_i(1-\alpha_{ii})(x_i'-x_i)x_i'^\top,$$
--   with $\alpha$ computed from $z=Wx$, $z'=Wx'$. The weighted covariances of Lemma 2 are $\hat\Sigma_0=\sum_{i,j}\alpha_{ij}(x_i-x_j)(x_i-x_j)^\top$ and $\hat\Sigma_1=\sum_i(1-\alpha_{ii})(x_i'-x_i)(x_i'-x_i)^\top$.
--   5. **Gradient flows.** The linear loss is $L(W)$ with $z=Wx$; the two-layer loss is $L(W_1,W_2)$ with $z=W_2W_1x$. The two-layer weights follow the gradient flow at time $t$ if $\dot W_1(t)=-\partial L/\partial W_1$ and $\dot W_2(t)=-\partial L/\partial W_2$ at $(W_1(t),W_2(t))$.
--   6. **Differentiable SVD (Section 5.3, Appendix A).** $W(s)=U(s)\,\mathrm{diag}(\sigma(s))\,V(s)^\top$ with $U(s),V(s)$ orthogonal and $\sigma(s)\ge0$ for all $s$ near $t$, and $U,V,\sigma$ differentiable at $t$. The columns $u^k,v^k$ of $U,V$ are the singular vectors of $\sigma^k$.
--   7. **Spectra.** $\sigma_{\min}(A)$ is the smallest of the $n$ singular values of $A\in\mathbb{R}^{m\times n}$ (zero when $m<n$). The embedding covariance (eq. 1) is $C=\frac1N\sum_i(z_i-\bar z)(z_i-\bar z)^\top$ with $\bar z=\frac1N\sum_i z_i$, $z_i=Wx_i$.
--
--   **Formalization Note** The gradients are defined as vectors and matrices of partial derivatives (`deriv` along coordinate directions), which are the true gradients because the loss is smooth. The matrix $X$ uses the sign convention of Appendix B.2: eq. (6) as printed on p. 4 has an extra minus sign on its first sum, and with that sign neither eq. (5) nor Lemma 2 holds. Singular values are Mathlib's `LinearMap.singularValues`, sorted in decreasing order.
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Sections 3, 4.1–4.2, 5.1–5.3, Appendix A and Appendix B.2, eqs. (1)–(9), pp. 3–6, 11–14

import Mathlib

/-!
Jing, Vincent, LeCun and Tian, *Understanding Dimensional Collapse in Contrastive Self-supervised
Learning*, ICLR 2022, arXiv:2110.09348v3: the InfoNCE loss of eq. (2), the linear and two-layer
linear models of Sections 4.1 and 5.1, the gradients and the matrix `X` of eqs. (3)–(9)
(Sections 4.2 and 5.2, Appendix B.2), the embedding covariance of eq. (1), and the differentiable
singular value decompositions of Section 5.3 and Appendix A.
-/

open Matrix Filter Topology

noncomputable section

namespace DimensionalCollapse

/-- Squared Euclidean norm `|v|² = ∑_c v_c²` of a vector `v ∈ ℝ^d`. -/
def sqNorm {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ c, v c ^ 2

/-- Section 4.2, below eq. (4): `Z_i = ∑_{j ≠ i} exp(-|z_i - z_j|²/2) + exp(-|z_i - z_i'|²/2)`,
for embeddings `z_i, z_i'` (`i = 1, …, N`) of the two branches. -/
def partitionZ {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i : Fin N) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, Real.exp (-sqNorm (z i - z j) / 2)) +
    Real.exp (-sqNorm (z i - z' i) / 2)

/-- Eq. (2), Section 4.1: the InfoNCE loss
`L = -∑_i log (exp(-|z_i - z_i'|²/2) / Z_i)`, whose negatives for `z_i` are the `z_j`, `j ≠ i`. -/
def infoNCE {N d : ℕ} (z z' : Fin N → Fin d → ℝ) : ℝ :=
  -∑ i, Real.log (Real.exp (-sqNorm (z i - z' i) / 2) / partitionZ z z' i)

/-- Section 4.2, below eq. (4): the softmax weights `α_ij = exp(-|z_i - z_j|²/2) / Z_i` for
`j ≠ i` and `α_ii = exp(-|z_i - z_i'|²/2) / Z_i`, so that `∑_j α_ij = 1`. -/
def alpha {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i j : Fin N) : ℝ :=
  (if j = i then Real.exp (-sqNorm (z i - z' i) / 2) else Real.exp (-sqNorm (z i - z j) / 2)) /
    partitionZ z z' i

/-- Sections 4.1 and 5.1: the embeddings `z_i = W x_i` of inputs `x_i ∈ ℝ^n` under a linear
map `W ∈ ℝ^{d×n}` (for the two-layer model, `W = W₂ W₁`). -/
def embed {N n d : ℕ} (W : Matrix (Fin d) (Fin n) ℝ) (x : Fin N → Fin n → ℝ) :
    Fin N → Fin d → ℝ :=
  fun i => W *ᵥ x i

/-- Lemma 1, Section 4.2: `g_{z_i}`, the gradient of the InfoNCE loss with respect to the
embedding vector `z_i` (its vector of partial derivatives; the loss is smooth). -/
def gradZ {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i : Fin N) : Fin d → ℝ :=
  fun c => deriv (fun s : ℝ => infoNCE (Function.update z i (z i + s • Pi.single c 1)) z') 0

/-- Lemma 1, Section 4.2: `g_{z_i'}`, the gradient of the InfoNCE loss with respect to the
embedding vector `z_i'` (its vector of partial derivatives). -/
def gradZ' {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i : Fin N) : Fin d → ℝ :=
  fun c => deriv (fun s : ℝ => infoNCE z (Function.update z' i (z' i + s • Pi.single c 1))) 0

/-- Lemma 1, eq. (3): `G = ∑_i (g_{z_i} x_iᵀ + g_{z_i'} x_i'ᵀ)`, with the gradients evaluated at
the embeddings `z_i = W x_i`, `z_i' = W x_i'`. -/
def Gmat {N n d : ℕ} (x x' : Fin N → Fin n → ℝ) (W : Matrix (Fin d) (Fin n) ℝ) :
    Matrix (Fin d) (Fin n) ℝ :=
  Matrix.of fun a b => ∑ i, (gradZ (embed W x) (embed W x') i a * x i b +
    gradZ' (embed W x) (embed W x') i a * x' i b)

/-- Eq. (6) in the form used in Appendix B.2 (the form for which eq. (5), `G = -W X`, holds):
`X = ∑_i (∑_{j≠i} α_ij (x_i' - x_j) + ∑_{j≠i} α_ji (x_i - x_j)) x_iᵀ
  - ∑_i (1 - α_ii)(x_i' - x_i) x_i'ᵀ`, with `α` computed from the embeddings `W x_i`, `W x_i'`. -/
def Xmat {N n d : ℕ} (x x' : Fin N → Fin n → ℝ) (W : Matrix (Fin d) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b =>
    (∑ i, ((∑ j ∈ Finset.univ.erase i, alpha (embed W x) (embed W x') i j * (x' i a - x j a)) +
        (∑ j ∈ Finset.univ.erase i, alpha (embed W x) (embed W x') j i * (x i a - x j a))) * x i b) -
      ∑ i, (1 - alpha (embed W x) (embed W x') i i) * (x' i a - x i a) * x' i b

/-- Lemma 2, eq. (7): the weighted data covariance `Σ̂₀ = ∑_{i,j} α_ij (x_i - x_j)(x_i - x_j)ᵀ`. -/
def Sigma0 {N n d : ℕ} (x x' : Fin N → Fin n → ℝ) (W : Matrix (Fin d) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b =>
    ∑ i, ∑ j, alpha (embed W x) (embed W x') i j * (x i a - x j a) * (x i b - x j b)

/-- Lemma 2, eq. (7): the weighted augmentation covariance
`Σ̂₁ = ∑_i (1 - α_ii)(x_i' - x_i)(x_i' - x_i)ᵀ`. -/
def Sigma1 {N n d : ℕ} (x x' : Fin N → Fin n → ℝ) (W : Matrix (Fin d) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b =>
    ∑ i, (1 - alpha (embed W x) (embed W x') i i) * (x' i a - x i a) * (x' i b - x i b)

/-- The gradient `∂F/∂W` of a function of a matrix, as the matrix of its partial derivatives
`∂F/∂W_ab` (used for the gradient flows of Lemmas 1 and 3). -/
def matGrad {m n : ℕ} (F : Matrix (Fin m) (Fin n) ℝ → ℝ) (W : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun a b => deriv (fun s : ℝ => F (W + s • Matrix.single a b 1)) 0

/-- Section 4.1: the InfoNCE loss of the linear model `z = W x` on the pairs `(x_i, x_i')`. -/
def linLoss {N n d : ℕ} (x x' : Fin N → Fin n → ℝ) (W : Matrix (Fin d) (Fin n) ℝ) : ℝ :=
  infoNCE (embed W x) (embed W x')

/-- Section 5.1: the InfoNCE loss of the two-layer linear model `z = W₂ W₁ x`,
`W₁, W₂ ∈ ℝ^{d×d}`. -/
def twoLayerLoss {N d : ℕ} (x x' : Fin N → Fin d → ℝ) (W1 W2 : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  infoNCE (embed (W2 * W1) x) (embed (W2 * W1) x')

/-- Sections 5.1–5.2: at time `t`, the weights `W₁(·), W₂(·)` follow the gradient flow of the
two-layer InfoNCE loss, `Ẇ₁ = -∂L/∂W₁`, `Ẇ₂ = -∂L/∂W₂` (entrywise derivatives). -/
def IsTwoLayerFlowAt {N d : ℕ} (x x' : Fin N → Fin d → ℝ)
    (W1 W2 : ℝ → Matrix (Fin d) (Fin d) ℝ) (t : ℝ) : Prop :=
  (∀ a b, HasDerivAt (fun s => W1 s a b)
      (-(matGrad (fun M => twoLayerLoss x x' M (W2 t)) (W1 t)) a b) t) ∧
    (∀ a b, HasDerivAt (fun s => W2 s a b)
      (-(matGrad (fun M => twoLayerLoss x x' (W1 t) M) (W2 t)) a b) t)

/-- Section 5.3 and Appendix A (Lemma 4): `W(s) = U(s) diag(σ(s)) V(s)ᵀ` is a singular value
decomposition (`U, V` orthogonal, `σ ≥ 0`) for all `s` near `t`, and `U`, `V`, `σ` are
differentiable at `t`. -/
def IsDiffSVDAt {d : ℕ} (W U V : ℝ → Matrix (Fin d) (Fin d) ℝ) (sig : ℝ → Fin d → ℝ)
    (t : ℝ) : Prop :=
  (∀ᶠ s in 𝓝 t, U s ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      V s ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧ (∀ k, 0 ≤ sig s k) ∧
      W s = U s * Matrix.diagonal (sig s) * (V s)ᵀ) ∧
    (∀ a b, DifferentiableAt ℝ (fun s => U s a b) t) ∧
    (∀ a b, DifferentiableAt ℝ (fun s => V s a b) t) ∧
    (∀ k, DifferentiableAt ℝ (fun s => sig s k) t)

/-- Theorem 1 ("vanishing singular values"): the smallest of the `n` singular values of
`W ∈ ℝ^{d×n}` (Mathlib's singular values, in decreasing order and indexed from `0`; it is `0`
when `d < n`). -/
def minSingVal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues (n - 1)

/-- Eq. (1) and Corollary 1: the covariance matrix of the embeddings `z_i = W x_i`,
`C = (1/N) ∑_i (z_i - z̄)(z_i - z̄)ᵀ` with `z̄ = (1/N) ∑_i z_i`. -/
def embCov {N n d : ℕ} (x : Fin N → Fin n → ℝ) (W : Matrix (Fin d) (Fin n) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b =>
    (N : ℝ)⁻¹ * ∑ i, (embed W x i a - (N : ℝ)⁻¹ * ∑ j, embed W x j a) *
      (embed W x i b - (N : ℝ)⁻¹ * ∑ j, embed W x j b)

end DimensionalCollapse


