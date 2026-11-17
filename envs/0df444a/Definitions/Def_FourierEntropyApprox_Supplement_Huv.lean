-- Prove2me | Definitions.Def_FourierEntropyApprox_Supplement_Huv
-- name    : FourierEntropyApprox_Supplement_Huv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:05:32.211959+00:00
-- url     : https://prove2.me/theorems/6a98febb-1ce4-41b2-b583-ab6c8d77155d
-- title:
--   The singular-value entropy $H_{u,v}(M)$ of $D_{\sqrt u}MD_{\sqrt v}$
-- statement:
--   Let $X,Y$ be finite sets, $M\in\mathbb R^{X\times Y}$, and $u=(u_x)_{x\in X}$, $v=(v_y)_{y\in Y}$ weight vectors. Put
--
--   $$A_{u,v}=D_{\sqrt u}\,M\,D_{\sqrt v},\qquad (A_{u,v})_{xy}=\sqrt{u_x}\,M_{xy}\,\sqrt{v_y},$$
--
--   and let $\sigma_1(A_{u,v})\ge\sigma_2(A_{u,v})\ge\dots\ge0$ be its singular values. Then
--
--   $$H_{u,v}(M)=\sum_i\sigma_i(A_{u,v})^2\log_2\frac{1}{\sigma_i(A_{u,v})^2},$$
--
--   with $0\log(1/0)=0$. When $M$ is a sign matrix and $u,v$ are probability vectors, $\sum_i\sigma_i^2=\|A_{u,v}\|_F^2=1$, so $H_{u,v}(M)$ is the Shannon entropy of the squared singular values.
--
--   This is the quantity that Theorem 5.1 shows to lower-bound entanglement-assisted quantum communication complexity.
--
--   **Formalization Note** The squared singular values are taken as the eigenvalues of the real symmetric positive semidefinite matrix $A_{u,v}^{\mathsf T}A_{u,v}$, indexed by $Y$; eigenvalues beyond the rank are $0$ and contribute nothing. The term $p\log_2(1/p)$ is $\mathrm{negMulLog}(p)/\ln 2$.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), §5, (30) and (32), pp.20–21

import Mathlib

set_option autoImplicit false

namespace FourierEntropyApprox

/-!
# The entropy `H_{u,v}(M)` of the squared singular values of `D_{√u} M D_{√v}`

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), §5, pp.20–21: "For probability vectors u = (u_x)_{x∈X} and v = (v_y)_{y∈Y}, let
A_{u,v} = D_{√u} M D_{√v}, where D_{√u} = diag(√u_x)_{x∈X} and D_{√v} = diag(√v_y)_{y∈Y}. (30) Let
σ₁(A_{u,v}) ≥ σ₂(A_{u,v}) ≥ ⋯ ≥ 0 be the singular values of A_{u,v}. … Define
H_{u,v}(M) = ∑ᵢ σᵢ(A_{u,v})² log 1/σᵢ(A_{u,v})², (32) with 0 log(1/0) = 0."

**Formalization Note.**
* `Auv u v M` is the real matrix with entries `√u_x M_{xy} √v_y`.
* The squared singular values of `A` are the eigenvalues of the positive semidefinite matrix `AᵀA` (indexed by
  `Y`); the eigenvalues beyond the rank are zeros, which contribute `0 log(1/0) = 0`, so the sum over `Y`
  equals the paper's sum over `i`.
* `p log₂(1/p)` is `Real.negMulLog p / Real.log 2` (base-two logarithms, p.2; `negMulLog 0 = 0`).
* The definition is stated for an arbitrary real matrix and arbitrary weight vectors; the paper applies it to
  sign matrices `M ∈ {−1, 1}^{X×Y}` and probability vectors, which the theorem using it assumes.
-/

namespace Supplement

/-- `A_{u,v} = D_{√u} M D_{√v}` ((30), p.20). -/
noncomputable def Auv {X Y : Type} (u : X → ℝ) (v : Y → ℝ) (M : Matrix X Y ℝ) : Matrix X Y ℝ :=
  fun x y => Real.sqrt (u x) * M x y * Real.sqrt (v y)

/-- `H_{u,v}(M) = ∑ᵢ σᵢ(A_{u,v})² log₂(1/σᵢ(A_{u,v})²)` ((32), pp.20–21), with the squared singular values
taken as the eigenvalues of `A_{u,v}ᵀ A_{u,v}`. -/
noncomputable def Huv {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    (u : X → ℝ) (v : Y → ℝ) (M : Matrix X Y ℝ) : ℝ :=
  ∑ y, Real.negMulLog
      ((Matrix.isHermitian_conjTranspose_mul_self (Auv u v M)).eigenvalues y) / Real.log 2

end Supplement

end FourierEntropyApprox


