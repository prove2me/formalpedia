-- Prove2me | Definitions.Def_PFRelease_Supplement_sketchMech
-- name    : PFRelease_Supplement_sketchMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:43:25.628244+00:00
-- url     : https://prove2.me/theorems/57f9f191-19e3-4e93-961f-6803ca40df46
-- title:
--   Gaussian sketches $M_{\lambda,r}$, their second moment $R$, top-$k$ eigenprojectors and the geometric spectrum
-- statement:
--   For a dataset $s$ of vectors in $\mathbb R^d$, the **Gaussian-sketch mechanism** releases
--   $$
--   M_{\lambda,r}(s):=(Z_1,\dots,Z_r),\qquad Z_j\sim\mathcal N\big(0,\widehat\Sigma_\lambda(s)\big)\ \text{independent},
--   $$
--   where $\mathcal N(0,A)$ for a positive semidefinite (possibly singular) $A$ is the law of $A^{1/2}G$ with $G$ standard Gaussian. The empirical second moment of the sketches is $R:=r^{-1}\sum_{j\in[r]}Z_jZ_j^T$.
--
--   A matrix $P$ is a **top-$k$ eigenprojector** of a symmetric matrix $R$ if it is the orthogonal projector onto the span of $k$ orthonormal eigenvectors of $R$ for its $k$ largest eigenvalues (counted with multiplicity). Equivalently: $P^T=P$, $P^2=P$, $\operatorname{rank}P=k$, $RP=PR$, and every Rayleigh quotient of $R$ on the range of $P$ is at least every Rayleigh quotient of $R$ on the kernel of $P$.
--
--   The **geometric spectrum** with $\ell:=\lceil\log_2 d\rceil<k$ has, in decreasing order, $k-\ell$ eigenvalues equal to $1$ followed by $\lambda_{k-\ell+j}=2^{-j}$ for $j=1,\dots,d-k+\ell$; in particular $\lambda_k=2^{-\ell}=2\lambda_{k+1}$.
--
--   These are the objects of the private subspace-estimation guarantee of §5.2: the mechanism releases sketches and post-processes them into a top-$k$ eigenprojector of $R$.
--
--   **Formalization Note** $\mathcal N(0,A)$ is Mathlib's `multivariateGaussian 0 A` on `EuclideanSpace ℝ ι`, which is defined for singular positive semidefinite $A$ without a density. The eigenprojector condition is stated with cleared denominators and without choosing eigenvectors, so ties $\lambda_k(R)=\lambda_{k+1}(R)$ give several eigenprojectors. $\lceil\log_2 d\rceil$ is `Nat.clog 2 d`; the spectrum is indexed from $0$.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), eq. (2), p.17 (PDF p.19); §5.2 Utility and the geometric spectrum, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PFRelease_Supplement_phiLam

open MeasureTheory ProbabilityTheory Matrix

namespace PFRelease.Supplement

/-- The Gaussian-sketch release mechanism `M_{λ,r}(s) := (Z₁, …, Z_r)` with independent
`Z_j ∼ N(0, Σ̂_λ(s))` (Shenfeld, Tsfadia, Ligett, arXiv:2610.40654, held version sha256 e1d516b3…,
eq. (2), p.17 = PDF p.19).

**Formalization Note** `N(0, A)` is Mathlib's `multivariateGaussian 0 A` on `EuclideanSpace ℝ ι`, the
image of the standard Gaussian under `x ↦ A^{1/2} x`; it is well defined for a singular positive
semidefinite `A` (no density is used). The `r` sketches are independent: the law is the product
`Measure.pi`. -/
noncomputable def sketchMech {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ℝ) (r : ℕ) {n : ℕ}
    (s : Fin n → Option (EuclideanSpace ℝ ι)) : Measure (Fin r → EuclideanSpace ℝ ι) :=
  Measure.pi fun _ : Fin r => multivariateGaussian 0 (secondMoment lam (toList s))

/-- The empirical second moment `R := r⁻¹ Σ_{j∈[r]} Z_j Z_jᵀ` of the sketches (§5.2, p.18 = PDF p.20). -/
noncomputable def sketchCov {ι : Type*} [Fintype ι] {r : ℕ} (Z : Fin r → EuclideanSpace ℝ ι) :
    Matrix ι ι ℝ :=
  (r : ℝ)⁻¹ • ∑ j, vecMulVec (WithLp.ofLp (Z j)) (WithLp.ofLp (Z j))

/-- `P` is an orthogonal projector onto the span of `k` orthonormal eigenvectors of the symmetric
matrix `R` for its `k` largest eigenvalues, counted with multiplicity (§5.2, p.18 = PDF p.20: "the
projector onto the top k eigenvectors").

**Formalization Note** Characterized without choosing eigenvectors: `P` is symmetric, idempotent, of
rank `k`, commutes with `R` (so its range is `R`-invariant), and every Rayleigh quotient of `R` on
`range P` is at least every Rayleigh quotient on `ker P` (written with cleared denominators). For
symmetric `R` these are exactly the projectors onto top-`k` eigenspans; when `λ_k(R) = λ_{k+1}(R)`
there are several, and the theorems quantify over all of them. -/
def IsTopKProj {ι : Type*} [Fintype ι] (R : Matrix ι ι ℝ) (k : ℕ) (P : Matrix ι ι ℝ) : Prop :=
  Pᵀ = P ∧ P * P = P ∧ P.rank = k ∧ R * P = P * R ∧
    ∀ x y : ι → ℝ, P *ᵥ x = x → P *ᵥ y = 0 →
      (x ⬝ᵥ x) * (y ⬝ᵥ (R *ᵥ y)) ≤ (y ⬝ᵥ y) * (x ⬝ᵥ (R *ᵥ x))

/-- The geometric spectrum (§5.2, p.18 = PDF p.20), in decreasing order and 0-based: with
`ℓ := ⌈log₂ d⌉`, the first `k − ℓ` eigenvalues are `1`, followed by `λ_{k−ℓ+j} = 2^{−j}` for
`j = 1, …, d − k + ℓ`.

**Formalization Note** `⌈log₂ d⌉` is `Nat.clog 2 d` (the least `ℓ` with `d ≤ 2^ℓ`). Index `i`
(0-based) is the paper's eigenvalue `λ_{i+1}`; for `i ≥ k − ℓ` the exponent is `j = i − (k − ℓ) + 1`.
The theorems assume `ℓ < k`, so `k − ℓ ≥ 1`. -/
noncomputable def geomSpectrum (d k : ℕ) (i : Fin d) : ℝ :=
  if (i : ℕ) < k - Nat.clog 2 d then 1 else (2 : ℝ)⁻¹ ^ ((i : ℕ) - (k - Nat.clog 2 d) + 1)

end PFRelease.Supplement


