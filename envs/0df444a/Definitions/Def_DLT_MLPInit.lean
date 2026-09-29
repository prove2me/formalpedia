-- Prove2me | Definitions.Def_DLT_MLPInit
-- name    : DLT_MLPInit
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T21:16:25.438986+00:00
-- url     : https://prove2.me/theorems/50210c89-b8fb-4cea-b22c-a1fa5f00b245
-- title:
--   MLPs at initialization, the first-layer metric, and Gaussian averages
-- statement:
--   Definitions for Chapter 4 of *The Principles of Deep Learning Theory*, building on the deep-linear-network definitions (`DLT_DeepLinearNetwork`).
--
--   1. **MLP preactivations** (eqs. 4.2, 4.30): with widths $n_0,n_1,\dots$, activation $\sigma$, biases $b^{(\ell)}_i$ and weights $W^{(\ell)}_{ij}$,
--   $$z^{(1)}_i=b^{(1)}_i+\sum_{j=1}^{n_0}W^{(1)}_{ij}x_j,\qquad z^{(\ell+1)}_i=b^{(\ell+1)}_i+\sum_{j=1}^{n_\ell}W^{(\ell+1)}_{ij}\sigma\big(z^{(\ell)}_j\big)\ (\ell\ge1).$$
--   2. The **initialization distribution** (eqs. 4.3–4.4): all biases $b^{(\ell)}_i$ and weights $W^{(\ell)}_{ij}$ ($\ell\ge1$) are mutually independent, $b^{(\ell)}_i\sim\mathcal{N}(0,C_b^{(\ell)})$ and $W^{(\ell)}_{ij}\sim\mathcal{N}(0,C_W^{(\ell)}/n_{\ell-1})$.
--   3. The **first-layer metric** on inputs $x_{\alpha}$ (eq. 4.8): $G^{(1)}_{\alpha_1\alpha_2}=C_b^{(1)}+C_W^{(1)}\frac1{n_0}\sum_jx_{j;\alpha_1}x_{j;\alpha_2}$.
--   4. The **Gaussian average** over sample indices (eq. 4.25): $\langle F\rangle_g=\mathbb{E}[F(z)]$ for $z=(z_\alpha)$ a centered Gaussian vector with covariance $g$.
--   5. **Polynomial growth** of $\sigma$: $|\sigma(u)|\le C(1+|u|)^k$ for some constants.
--
--   **Formalization Note** Indices start at $0$; the sample set of a Gaussian average is $\{0,\dots,D-1\}$. The Gaussian average uses Mathlib's `multivariateGaussian 0 g` on Euclidean space, which for a positive-semidefinite (possibly singular) $g$ is the centered Gaussian with covariance $g$.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.1–4.2, pp. 73–80, eqs. (4.2)–(4.4), (4.8), (4.25), (4.30) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

/-!
# The Principles of Deep Learning Theory — MLPs at initialization (§2.1, §4.1–4.2)

Multilayer-perceptron preactivations with biases and a general activation function
(eqs. 4.2, 4.30), their Gaussian initialization distribution (eqs. 4.3–4.4), the first-layer
metric (eq. 4.8), and Gaussian expectations `⟨F⟩_g` over sample indices (eq. 4.25).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

/-- Preactivations of an MLP with activation `σ` (eqs. 4.2, 4.30).
`n ℓ` is the width of layer `ℓ` (`n 0` is the input dimension), `b ℓ i = b^{(ℓ)}_i` and
`W ℓ i j = W^{(ℓ)}_{ij}` (used for `ℓ ≥ 1`), and `x` is the input. Then
`mlpPreact n σ b W x ℓ i = z^{(ℓ)}_i(x)`, where `z^{(0)} = x`,
`z^{(1)}_i = b^{(1)}_i + ∑_{j < n_0} W^{(1)}_{ij} x_j`, and for `ℓ ≥ 1`
`z^{(ℓ+1)}_i = b^{(ℓ+1)}_i + ∑_{j < n_ℓ} W^{(ℓ+1)}_{ij} σ(z^{(ℓ)}_j)`. -/
def mlpPreact (n : ℕ → ℕ) (σ : ℝ → ℝ) (b : ℕ → ℕ → ℝ) (W : ℕ → ℕ → ℕ → ℝ) (x : ℕ → ℝ) :
    ℕ → ℕ → ℝ
  | 0, i => x i
  | ℓ + 1, i => b (ℓ + 1) i + ∑ j ∈ Finset.range (n ℓ),
      W (ℓ + 1) i j * (if ℓ = 0 then x j else σ (mlpPreact n σ b W x ℓ j))

/-- Index set of the biases of a network with widths `n`: pairs `(ℓ, i)` with `ℓ ≥ 1`,
`i < n ℓ`. -/
def BiasIndex (n : ℕ → ℕ) : Type :=
  {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 < n p.1}

/-- Initialization distribution of an MLP (eqs. 4.3–4.4, for every layer): all biases
`b^{(ℓ)}_i` and weights `W^{(ℓ)}_{ij}` (`ℓ ≥ 1`, `i < n_ℓ`, `j < n_{ℓ-1}`) are mutually
independent random variables on `(Ω, P)`; each bias is a centered Gaussian with variance
`C_b^{(ℓ)}` and each weight is a centered Gaussian with variance `C_W^{(ℓ)} / n_{ℓ-1}`. -/
def IsMLPInit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) : Prop :=
  iIndepFun (fun (p : BiasIndex n ⊕ WeightIndex n) =>
      Sum.elim (fun q (ω : Ω) => b ω q.1.1 q.1.2) (fun q (ω : Ω) => W ω q.1.1 q.1.2.1 q.1.2.2) p) P ∧
  (∀ ℓ i, 1 ≤ ℓ → i < n ℓ → P.map (fun ω => b ω ℓ i) = gaussianReal 0 (Cb ℓ)) ∧
  (∀ ℓ i j, 1 ≤ ℓ → i < n ℓ → j < n (ℓ - 1) →
    P.map (fun ω => W ω ℓ i j) = gaussianReal 0 (CW ℓ / (n (ℓ - 1) : ℝ≥0)))

/-- First-layer metric on the inputs `x_0, …, x_{D-1}` (eq. 4.8):
`G^{(1)}_{α₁α₂} = C_b^{(1)} + C_W^{(1)} (1/n₀) ∑_{j} x_{j;α₁} x_{j;α₂}`. -/
noncomputable def firstLayerMetric (Cb₁ CW₁ : ℝ≥0) (n₀ : ℕ) {D : ℕ} (x : Fin D → ℕ → ℝ) :
    Matrix (Fin D) (Fin D) ℝ :=
  fun α₁ α₂ => (Cb₁ : ℝ) + (CW₁ : ℝ) * inputKernel n₀ (x α₁) (x α₂)

/-- Gaussian expectation over sample indices (eq. 4.25): `⟨F(z_{α})⟩_g` is the expectation of
`F(z)` for `z = (z_α)_{α < D}` a centered Gaussian vector with covariance matrix `g`
(for positive semidefinite `g`; possibly degenerate). -/
noncomputable def gaussAvg {D : ℕ} (g : Matrix (Fin D) (Fin D) ℝ) (F : (Fin D → ℝ) → ℝ) : ℝ :=
  ∫ u, F (fun α => u α) ∂(multivariateGaussian 0 g)

/-- Polynomial growth of the activation function: `|σ(u)| ≤ C (1 + |u|)^k` for all `u`. -/
def HasPolyGrowth (σ : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ u, |σ u| ≤ C * (1 + |u|) ^ k

end DeepLearningTheory


