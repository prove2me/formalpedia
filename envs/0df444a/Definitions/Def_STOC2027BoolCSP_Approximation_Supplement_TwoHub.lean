-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_TwoHub
-- name    : STOC2027BoolCSP_Approximation_Supplement_TwoHub
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:24.7572+00:00
-- url     : https://prove2.me/theorems/6af9c7f4-f089-4420-ad6d-e168583437a7
-- title:
--   The two-hub matrix $A^*$, independent Gaussian columns and the two-hub acceptance $L_0$
-- statement:
--   Fix $k\ge 4$ and number the coordinates $1,\dots,k$: coordinates $1,2$ are the **hubs** and $3,\dots,k$ the $n=k-2$ **leaves**. The **two-hub matrix** $A^*$ of (47) is the symmetric $k\times k$ matrix with
--   $$A^*_{1\ell}=A^*_{\ell1}=+1,\qquad A^*_{2\ell}=A^*_{\ell2}=-1\qquad(\ell\ \text{a leaf}),$$
--   and $0$ on every other entry: the diagonal, the hub–hub entry and the leaf–leaf entries.
--
--   For a covariance matrix $\Sigma$ on $\mathbb R^k$, a $k\times N$ Gaussian array with covariance $\Sigma\otimes I_N$ has $N$ independent columns, each $N(0,\Sigma)$; its rows are $G_1,\dots,G_k\in\mathbb R^N$. For a scale $u$ and $f:\mathbb R^N\to\mathbb R$, the normalized two-hub conjunction acceptance of §12.2 is
--   $$L_0^u(f)=\mathbb E\prod_{i=1}^k\big(1+f(G_i)\big),\qquad \mathrm{Cov}(G_1,\dots,G_k)=(I+uA^*)\otimes I_N .$$
--
--   This is the quantity bounded in Theorem 12.2; the paper's $L_0(f)$ is $L_0^t(f)$.
--
--   **Formalization Note** Indices are $0$-based in Lean: hubs $0,1$, leaves $2,\dots,k-1$. Columns are independent `multivariateGaussian 0 (1 + u • A*)` vectors in `EuclideanSpace ℝ (Fin k)` (`Measure.pi`). For $0<u\le t$ the matrix $I+uA^*$ is positive definite (its nonzero eigenvalues of $A^*$ are $\pm\sqrt{2n}$).
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 24, 26 (PDF 27, 29), equation (47) and §12.2

import Mathlib

namespace STOC2027BoolCSP.Approximation.Supplement

open MeasureTheory ProbabilityTheory

/-- The two-hub matrix `A*` of (47), rows and columns `0, …, k−1` (0-based): index `0` is hub 1,
index `1` is hub 2, indices `2, …, k−1` are the `n = k − 2` leaves. `A*` has `+1` between hub 1
and each leaf, `−1` between hub 2 and each leaf, and `0` elsewhere (diagonal, hub–hub and
leaf–leaf entries). -/
def twoHubMat (k : ℕ) : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j =>
  if (i.val = 0 ∧ 2 ≤ j.val) ∨ (j.val = 0 ∧ 2 ≤ i.val) then 1
  else if (i.val = 1 ∧ 2 ≤ j.val) ∨ (j.val = 1 ∧ 2 ≤ i.val) then -1
  else 0

/-- The law of a `k × N` Gaussian array whose `N` columns are independent `N(0, S)` vectors in
`ℝ^k` (covariance `S ⊗ I_N`). -/
noncomputable def colGauss (k N : ℕ) (S : Matrix (Fin k) (Fin k) ℝ) :
    Measure (Fin N → EuclideanSpace ℝ (Fin k)) :=
  Measure.pi fun _ : Fin N => multivariateGaussian 0 S

/-- Row `i` of the array: the vector `G_i ∈ ℝ^N`. -/
def row {k N : ℕ} (ω : Fin N → EuclideanSpace ℝ (Fin k)) (i : Fin k) : Fin N → ℝ :=
  fun col => ω col i

/-- The normalized two-hub conjunction acceptance `L_0(f) = E Π_{i=1}^k (1 + f(G_i))` of
§12.2 at scale `u`, where `(G_1, …, G_k)` has covariance `(I + u A*) ⊗ I_N`. -/
noncomputable def twoHubAcc (k : ℕ) (u : ℝ) {N : ℕ} (f : (Fin N → ℝ) → ℝ) : ℝ :=
  ∫ ω, ∏ i, (1 + f (row ω i)) ∂colGauss k N (1 + u • twoHubMat k)

end STOC2027BoolCSP.Approximation.Supplement


