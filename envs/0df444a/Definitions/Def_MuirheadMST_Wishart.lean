-- Prove2me | Definitions.Def_MuirheadMST_Wishart
-- name    : MuirheadMST_Wishart
-- status  : Definition
-- author  : @domodus
-- created : 2026-11-26T17:36:58.541135+00:00
-- url     : https://prove2.me/theorems/de8e6e51-1f24-5c47-8df4-d346f3dfef44
-- title:
--   The Wishart distribution $W_m(n,\Sigma)$, Lebesgue measure on symmetric matrices, latent roots and $\Gamma_m$
-- statement:
--   Definitions for the Wishart chapter of Muirhead's *Aspects of Multivariate Statistical Theory*. Real $m\times m$ matrices are represented as arrays $\{0,\dots,m-1\}^2\to\mathbb R$ with the product σ-algebra.
--
--   1. **Normal data matrix.** For an $m\times m$ matrix $\Sigma$, the law of an $n\times m$ matrix $Z$ whose rows are independent $N_m(0,\Sigma)$ vectors (Mathlib's `multivariateGaussian 0 Σ`).
--   2. **Wishart distribution.** $W_m(n,\Sigma)$ is the law of $A = Z^{\mathsf T}Z$, $A_{jk}=\sum_{i=1}^n Z_{ij}Z_{ik}$ (Muirhead, Definition 3.1.3).
--   3. **Multivariate gamma function**, in product form,
--   $$\Gamma_m(a)=\pi^{m(m-1)/4}\prod_{i=1}^m\Gamma\Big(a-\frac{i-1}{2}\Big).$$
--   Muirhead defines $\Gamma_m(a)$ as the integral $\int_{A>0}\operatorname{etr}(-A)(\det A)^{a-(m+1)/2}(dA)$ (§2.1.2, p. 61) and evaluates it as this product in Theorem 2.1.12; that theorem is a milestone of this mission.
--   4. **Lebesgue measure on symmetric matrices**, $(dA)=\prod_{i\le j}dA_{ij}$: the image of Lebesgue measure on the upper-triangular entries under symmetric completion.
--   5. **Latent roots** of a symmetric matrix: its eigenvalues $l_1\ge\dots\ge l_m$ in decreasing order.
--   6. **The diagonal matrix** $\operatorname{diag}(l_1,\dots,l_m)$ and the **Vandermonde product** $\prod_{i<j}(l_i-l_j)$.
--   7. **Bartlett's construction.** Independent standard Gaussian vectors $g_i\in\mathbb R^{n-i+1}$ ($i=1,\dots,m$) and independent $N(0,1)$ entries, assembled into the upper-triangular matrix $T$ with $t_{ii}=\|g_i\|$ (so $t_{ii}^2\sim\chi^2_{n-i+1}$) and $t_{ij}$ the $N(0,1)$ entries for $i<j$.
--
--   **Formalization Note** Indices start at $0$ in Lean, so row $i$ there is row $i+1$ here, and $g_i\in\mathbb R^{n-i}$. `multivariateGaussian 0 Σ` is the Gaussian with covariance $\Sigma$ only for positive semidefinite $\Sigma$; every theorem using these definitions assumes $\Sigma$ positive definite or $\Sigma=I_m$. `latentRoots` returns $0$ on non-symmetric arrays, a null set for every law in this mission. Degrees of freedom $n$ are natural numbers because the Wishart law is defined through the data matrix.
-- source:
--   R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley, 1982 (reprinted 2005, same pagination), https://doi.org/10.1002/9780470316559: Definition 3.1.3, §3.1 (Wishart distribution); §2.1, pp. 61-62 (Lebesgue measure (dA) on symmetric matrices); §2.1.2, p. 61 (multivariate gamma function defined as an integral) and Theorem 2.1.12, pp. 62-63 (its product form); §3.2.4 'Bartlett's Decomposition and the Generalized Variance', Theorem 3.2.14, p. 99 (Bartlett's construction); §3.2.5 'The Latent Roots of a Wishart Matrix', p. 103 (latent roots)

import Mathlib

/-!
R. J. Muirhead, *Aspects of Multivariate Statistical Theory* (Wiley, 1982), Chapter 3: the Wishart
distribution and the latent roots of a Wishart matrix. Real `m × m` matrices are represented as arrays
`Fin m → Fin m → ℝ` (with the product σ-algebra and Lebesgue measure); matrix algebra goes through
`Matrix.of`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MuirheadMST

/-- The `n × m` normal data matrix `Z` with independent rows, each `N_m(0, Σ)` (the law `N(0, I_n ⊗ Σ)`
of Muirhead §3.1). Row `i` is `Z i`. -/
def normalDataMatrix (n m : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) :
    Measure (Fin n → EuclideanSpace ℝ (Fin m)) :=
  Measure.pi fun _ => multivariateGaussian 0 S

/-- `Z'Z` for a data matrix `Z` with rows `Z i`: the entry `(j, k)` is `∑_i Z_{ij} Z_{ik}`. -/
def gram {n m : ℕ} (Z : Fin n → EuclideanSpace ℝ (Fin m)) : Fin m → Fin m → ℝ :=
  fun j k => ∑ i, (Z i).ofLp j * (Z i).ofLp k

/-- The Wishart distribution `W_m(n, Σ)`: the law of `A = Z'Z` when `Z` is `n × m` with independent
`N_m(0, Σ)` rows (Muirhead, Definition 3.1.3). Meaningful for positive semidefinite `S`; for other `S`,
Mathlib's `multivariateGaussian` is a point mass, so this is the point mass at the zero array. -/
def wishart (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) : Measure (Fin m → Fin m → ℝ) :=
  (normalDataMatrix n m S).map gram

/-- The multivariate gamma function in product form, `Γ_m(a) = π^{m(m-1)/4} ∏_{i=1}^m Γ(a - (i-1)/2)`.
Muirhead (§2.1.2, p. 61) defines `Γ_m(a)` as `∫_{A>0} etr(-A) (det A)^{a-(m+1)/2} (dA)`; Theorem 2.1.12
(pp. 62-63) evaluates that integral as this product for `a > (m - 1)/2`. Below that the integral diverges; the product
is then the meromorphic continuation, and at its poles `Real.Gamma` (hence this definition) returns `0`. -/
def multivariateGamma (m : ℕ) (a : ℝ) : ℝ :=
  Real.pi ^ ((m : ℝ) * ((m : ℝ) - 1) / 4) * ∏ i : Fin m, Real.Gamma (a - (i : ℝ) / 2)

/-- Lebesgue measure on real symmetric `m × m` matrices, `(dA) = ∏_{i ≤ j} da_{ij}`: the image of
Lebesgue measure on the upper-triangular entries under symmetric completion. -/
def symVolume (m : ℕ) : Measure (Fin m → Fin m → ℝ) :=
  (volume : Measure ({p : Fin m × Fin m // p.1 ≤ p.2} → ℝ)).map
    fun a i j => if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), le_of_not_ge h⟩

/-- The latent roots (eigenvalues) of a symmetric matrix, in decreasing order `l₁ ≥ ⋯ ≥ l_m`;
`0` for a non-symmetric array. -/
def latentRoots {m : ℕ} (A : Fin m → Fin m → ℝ) : Fin m → ℝ :=
  if h : (Matrix.of A).IsHermitian then
    fun i => h.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm i)
  else 0

/-- The diagonal matrix `diag(l₁, …, l_m)` as an array. -/
def diagArray {m : ℕ} (l : Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => if i = j then l i else 0

/-- The sample space of Bartlett's construction: for each row index `i`, a vector in `ℝ^{n-i}` (whose norm
gives the diagonal entry `t_ii`), and an array of reals (whose entries above the diagonal give `t_ij`, `i < j`).
Indices start at `0`, so row `i` here is row `i + 1` in Muirhead's numbering. -/
abbrev BartlettSample (m n : ℕ) : Type :=
  (∀ i : Fin m, EuclideanSpace ℝ (Fin (n - i))) × (Fin m → Fin m → ℝ)

/-- The law of Bartlett's sample: independent standard Gaussian vectors `g_i ∈ ℝ^{n-i}`, independent of an
array of independent `N(0, 1)` entries. -/
def bartlettLaw (m n : ℕ) : Measure (BartlettSample m n) :=
  (Measure.pi fun i : Fin m => stdGaussian (EuclideanSpace ℝ (Fin (n - i)))).prod
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin m => gaussianReal 0 1)

/-- The upper-triangular matrix `T` of Bartlett's decomposition: `t_ii = ‖g_i‖` (so `t_ii² ~ χ²_{n-i}`,
i.e. `χ²_{n-i+1}` in 1-based numbering), `t_ij` the given `N(0, 1)` entry for `i < j`, and `0` below the
diagonal. The entries of the array on and below the diagonal are sampled but never used. -/
def bartlettFactor {m n : ℕ} (ω : BartlettSample m n) : Fin m → Fin m → ℝ :=
  fun i j => if i = j then ‖ω.1 i‖ else if i < j then ω.2 i j else 0

/-- The Vandermonde factor `∏_{i<j} (l_i - l_j)`. -/
def vandermondeProd {m : ℕ} (l : Fin m → ℝ) : ℝ :=
  ∏ i : Fin m, ∏ j : Fin m, if i < j then l i - l j else 1

end MuirheadMST


