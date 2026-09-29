-- Prove2me | Definitions.Def_DLT_DeepLinearNetwork
-- name    : DLT_DeepLinearNetwork
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T21:15:32.219988+00:00
-- url     : https://prove2.me/theorems/c02c06df-a25c-4e07-8ee2-87508df6f1a7
-- title:
--   Deep linear networks and their Gaussian initialization
-- statement:
--   Definitions for Chapter 3 of *The Principles of Deep Learning Theory* (also reused by later chapters).
--
--   1. The **Kronecker delta** $\delta_{ij}$ (as a real number) and the four-index **Wick tensor structure** $\Delta_{i_1i_2i_3i_4} = \delta_{i_1i_2}\delta_{i_3i_4}+\delta_{i_1i_3}\delta_{i_2i_4}+\delta_{i_1i_4}\delta_{i_2i_3}$.
--   2. The **normalized input inner product** (eq. 3.9)
--   $$G^{(0)}_{\alpha_1\alpha_2} = \frac{1}{n_0}\sum_{j=1}^{n_0} x_{j;\alpha_1}x_{j;\alpha_2}.$$
--   3. **Zero-bias deep linear network preactivations** (eqs. 3.1–3.2): with widths $n_0,n_1,\dots$ and weights $W^{(\ell)}_{ij}$,
--   $$z^{(0)}_i = x_i,\qquad z^{(\ell+1)}_i = \sum_{j=1}^{n_\ell} W^{(\ell+1)}_{ij} z^{(\ell)}_j .$$
--   4. The **initialization distribution** (eq. 3.4): on a probability space $(\Omega,P)$, the weights $W^{(\ell)}_{ij}$ with $\ell\ge1$, $1\le i\le n_\ell$, $1\le j\le n_{\ell-1}$ are mutually independent and each is a centered Gaussian of variance $C_W/n_{\ell-1}$, i.e. $\mathbb{E}[W^{(\ell)}_{i_1j_1}W^{(\ell)}_{i_2j_2}] = \delta_{i_1i_2}\delta_{j_1j_2}C_W/n_{\ell-1}$.
--
--   All statements of the mission are phrased in terms of these objects.
--
--   **Formalization Note** Neural and input indices start at $0$. Widths are a function `n : ℕ → ℕ` and the weights a random field `W : Ω → ℕ → ℕ → ℕ → ℝ`; entries outside the ranges above are unconstrained and never used. $C_W$ is a nonnegative real (`ℝ≥0`).
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §3.1–3.2, pp. 54–56, eqs. (3.1), (3.2), (3.4), (3.9), (3.21) (page numbers are the book's printed page numbers)

import Mathlib

/-!
# The Principles of Deep Learning Theory — deep linear networks (§3.1)

Kronecker delta, the Wick tensor structure of four neural indices, the normalized input
inner product (eq. 3.9), zero-bias deep linear networks (eqs. 3.1–3.2), and their Gaussian
initialization distribution (eq. 3.4).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

/-- Kronecker delta `δ_{ij}` as a real number. -/
def kron (i j : ℕ) : ℝ := if i = j then 1 else 0

/-- The tensor structure `δ_{i₁i₂}δ_{i₃i₄} + δ_{i₁i₃}δ_{i₂i₄} + δ_{i₁i₄}δ_{i₂i₃}`. -/
def wickDelta4 (i₁ i₂ i₃ i₄ : ℕ) : ℝ :=
  kron i₁ i₂ * kron i₃ i₄ + kron i₁ i₃ * kron i₂ i₄ + kron i₁ i₄ * kron i₂ i₃

/-- Normalized inner product of two inputs,
`G⁽⁰⁾_{α₁α₂} = (1/n₀) ∑_{j=1}^{n₀} x_{j;α₁} x_{j;α₂}` (eq. 3.9).
Input components are indexed `0, …, n₀ - 1`. -/
noncomputable def inputKernel (n₀ : ℕ) (x₁ x₂ : ℕ → ℝ) : ℝ :=
  (1 / (n₀ : ℝ)) * ∑ j ∈ Finset.range n₀, x₁ j * x₂ j

/-- Preactivations of a zero-bias deep linear network (eqs. 3.1–3.2).
`n ℓ` is the width of layer `ℓ` (`n 0` is the input dimension), `W ℓ i j` is the weight
`W^{(ℓ)}_{ij}` (used for `ℓ ≥ 1`), and `x` is the input. Then
`linearPreact n W x ℓ i = z^{(ℓ)}_i(x)` with `z^{(0)} = x` and
`z^{(ℓ+1)}_i = ∑_{j < n_ℓ} W^{(ℓ+1)}_{ij} z^{(ℓ)}_j`. Neural indices are `0, …, n_ℓ - 1`. -/
def linearPreact (n : ℕ → ℕ) (W : ℕ → ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, i => x i
  | ℓ + 1, i => ∑ j ∈ Finset.range (n ℓ), W (ℓ + 1) i j * linearPreact n W x ℓ j

/-- Index set of the weights of a network with widths `n`: triples `(ℓ, i, j)` with
`ℓ ≥ 1`, `i < n ℓ`, `j < n (ℓ - 1)`. -/
def WeightIndex (n : ℕ → ℕ) : Type :=
  {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)}

/-- Initialization distribution of a zero-bias deep linear network (eq. 3.4), with
`C_W^{(ℓ)} = C_W` in every layer: all weights `W^{(ℓ)}_{ij}` (`ℓ ≥ 1`, `i < n_ℓ`,
`j < n_{ℓ-1}`) are mutually independent random variables on `(Ω, P)`, and each is a centered
Gaussian with variance `C_W / n_{ℓ-1}`. -/
def IsLinearNetInit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ → ℕ) (CW : ℝ≥0)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) : Prop :=
  iIndepFun (fun (p : WeightIndex n) (ω : Ω) => W ω p.1.1 p.1.2.1 p.1.2.2) P ∧
  ∀ ℓ i j, 1 ≤ ℓ → i < n ℓ → j < n (ℓ - 1) →
    P.map (fun ω => W ω ℓ i j) = gaussianReal 0 (CW / (n (ℓ - 1) : ℝ≥0))

end DeepLearningTheory


