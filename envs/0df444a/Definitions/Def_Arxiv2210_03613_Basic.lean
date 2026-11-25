-- Prove2me | Definitions.Def_Arxiv2210_03613_Basic
-- name    : Arxiv2210_03613_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T16:30:33.240162+00:00
-- url     : https://prove2.me/theorems/8e9a0195-0436-5f59-bdb3-532a5b7b3f01
-- title:
--   Mean-field Gaussian family, KL-optimality, and the kernel, permutation and Cholesky matrices of stochastic SVGD
-- statement:
--   Objects of Sections 2.1, 2.2 and 2.4 of Zhang, Lomas, Zhou, Zheng and Curtis (2022).
--
--   1. **Mean-field Gaussian family (eq. 9).** On the unconstrained parameter space $\mathbb{R}^\iota$ (a finite index set $\iota$), $q(\theta;\mu,\omega)=\mathcal N\big(\theta\mid\mu,\operatorname{diag}(e^{2\omega_i})\big)$, the Gaussian with mean $\mu$ and independent coordinates of standard deviations $\sigma_i=e^{\omega_i}>0$.
--   2. **KL-optimal member (eq. 2).** For a target probability measure $p$, $q(\cdot;\mu,\omega)$ is KL-optimal if $\mathrm{KL}[q(\cdot;\mu,\omega)\,\|\,p]\le\mathrm{KL}[q(\cdot;\mu',\omega')\,\|\,p]$ for all $\mu'\in\mathbb{R}^\iota$, $\omega'\in\mathbb{R}^\iota$.
--   3. **Kernel matrices (eqs. 22, 25).** For a function $k:\mathbb{R}^d\times\mathbb{R}^d\to\mathbb{R}$ and particles $m_1,\dots,m_n\in\mathbb{R}^d$, $\overline K_{ij}=k(m_i,m_j)$ is $n\times n$. The $nd\times nd$ matrix $K=\frac1n\big[k(m_i,m_j)I_{d\times d}\big]_{i,j}$ acts on the augmented vector $z=(m_1,\dots,m_n)$, with entries indexed by (particle, coordinate). $D_K=\frac1n\operatorname{diag}(\overline K,\dots,\overline K)$ has $d$ blocks and is indexed by (coordinate, particle).
--   4. **Permutation (eq. 26).** $P$ maps $z$, listed particle by particle, to the vector listing the first coordinates of all particles, then the second, and so on: $(Pz)_{(a,i)}=z_{(i,a)}$.
--   5. **Cholesky factor.** $L$ is the lower triangular Cholesky factor of $A$ if $LL^\top=A$, $L$ is lower triangular for the order of the index set, and $L_{ii}>0$ for every $i$. The index set of $D_K$ is ordered lexicographically by (coordinate, particle).
--   6. **sSVGD noise (eq. 24).** At step size $\epsilon_t$, the noise term $\eta$ of stochastic SVGD has law $\mathcal N(0,2\epsilon_tK)$.
--
--   **Formalization Note** Gaussian laws are Mathlib's `multivariateGaussian` on `EuclideanSpace`, and the KL divergence is Mathlib's `klDiv`, which takes values in $[0,\infty]$. Vectors indexed by (coordinate, particle) carry Mathlib's lexicographic order (`Lex`), so that "lower triangular" refers to the coordinate-major ordering of the paper.
-- source:
--   Zhang, Lomas, Zhou, Zheng and Curtis, 3D Bayesian Variational Full Waveform Inversion, arXiv:2210.03613v2 (2022), Section 2.1 eq. (2), Section 2.2 eq. (9), Section 2.4 eqs. (22), (24)-(27), PDF pp. 7, 9, 14-15

import Mathlib

/-!
Zhang, Lomas, Zhou, Zheng and Curtis, *3D Bayesian Variational Full Waveform Inversion*,
arXiv:2210.03613v2 (2022): the mean-field Gaussian family of ADVI and its KL-optimal members
(Sections 2.1-2.2, eqs. (2), (9)), and the kernel matrices, permutation, Cholesky factors and
noise law of stochastic SVGD (Section 2.4, eqs. (22), (24)-(27)).
-/

open MeasureTheory ProbabilityTheory InformationTheory

noncomputable section

namespace Arxiv2210_03613

section ADVI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Eq. (9), Section 2.2, p. 9: the factorised (mean-field) Gaussian variational family
`q(θ; ζ) = N(θ | μ, diag(exp(ω)²))` on the unconstrained space, with mean `μ` and standard
deviations `σ = exp(ω)`. -/
def meanFieldGaussian (μ : EuclideanSpace ℝ ι) (ω : ι → ℝ) : Measure (EuclideanSpace ℝ ι) :=
  multivariateGaussian μ (Matrix.diagonal fun i => Real.exp (ω i) ^ 2)

/-- Eq. (2), Section 2.1, p. 7, with the family `Q` of eq. (9): the member `q(θ; μ, ω)` of the
mean-field Gaussian family minimises `KL[q || p]` over that family. -/
def IsMeanFieldKLMin (p : Measure (EuclideanSpace ℝ ι)) (μ : EuclideanSpace ℝ ι) (ω : ι → ℝ) :
    Prop :=
  ∀ (μ' : EuclideanSpace ℝ ι) (ω' : ι → ℝ),
    klDiv (meanFieldGaussian μ ω) p ≤ klDiv (meanFieldGaussian μ' ω') p

end ADVI

section SSVGD

variable {n d : ℕ}

/-- Section 2.4, p. 15 (below eq. (25)): the `n × n` kernel matrix of the particles,
`K̄_ij = k(m_i, m_j)`, for particles `m_1, …, m_n ∈ ℝ^d`. -/
def gramMat (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (m : Fin n → Fin d → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => k (m i) (m j)

/-- Eq. (22), Section 2.4, p. 14: the `nd × nd` matrix
`K = (1/n) [k(m_i, m_j) I_{d×d}]_{i,j}` on the augmented space `z = (m_1, …, m_n)`, whose
entries are indexed by (particle, coordinate). -/
def svgdK (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (m : Fin n → Fin d → ℝ) :
    Matrix (Fin n × Fin d) (Fin n × Fin d) ℝ :=
  fun x y => (1 / (n : ℝ)) * (if x.2 = y.2 then k (m x.1) (m y.1) else 0)

/-- Eq. (26), Section 2.4, p. 15: the permutation matrix `P` that reorders `z` from the basis in
which the particles are listed one after another, (particle, coordinate), to the basis in which
the first coordinates of all particles are listed, then the second, and so on,
(coordinate, particle) in lexicographic order: `(P z)_(a, i) = z_(i, a)`. -/
def permP (n d : ℕ) : Matrix (Lex (Fin d × Fin n)) (Fin n × Fin d) ℝ :=
  fun x y => if (ofLex x).1 = y.2 ∧ (ofLex x).2 = y.1 then 1 else 0

/-- Eq. (25), Section 2.4, p. 15: the block-diagonal matrix
`D_K = (1/n) diag(K̄, …, K̄)` with `d` diagonal blocks, indexed by (coordinate, particle) in
lexicographic order. -/
def blockDK (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (m : Fin n → Fin d → ℝ) :
    Matrix (Lex (Fin d × Fin n)) (Lex (Fin d × Fin n)) ℝ :=
  fun x y => (1 / (n : ℝ)) *
    (if (ofLex x).1 = (ofLex y).1 then gramMat k m (ofLex x).2 (ofLex y).2 else 0)

/-- Section 2.4, p. 15 (below eq. (27)): `L` is the lower triangular Cholesky factor of `A`:
`L Lᵀ = A`, `L` is lower triangular for the order of the index set, and its diagonal is
positive. -/
def IsLowerCholesky {κ : Type*} [Fintype κ] [LinearOrder κ] (L A : Matrix κ κ ℝ) : Prop :=
  L * L.transpose = A ∧ (∀ i j, i < j → L i j = 0) ∧ ∀ i, 0 < L i i

/-- Eq. (24), Section 2.4, p. 14: the law `N(0, 2 ε_t K)` of the noise term of stochastic SVGD
at step size `ε_t`. -/
def ssvgdNoise (ε : ℝ) (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (m : Fin n → Fin d → ℝ) :
    Measure (EuclideanSpace ℝ (Fin n × Fin d)) :=
  multivariateGaussian 0 ((2 * ε) • svgdK k m)

end SSVGD

end Arxiv2210_03613


