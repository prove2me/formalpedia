-- Prove2me | Definitions.Def_NonlinearICAAux_Basic
-- name    : NonlinearICAAux_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T06:43:55.607056+00:00
-- url     : https://prove2.me/theorems/792f4566-1a78-4d3c-b872-91f0ebcfefff
-- title:
--   Nonlinear ICA with auxiliary variables: model, contrastive logistic loss, Assumption of Variability, conditional exponentiality
-- statement:
--   Objects of Sections 3 and 4 and Supplementary A-D of Hyvärinen, Sasaki and Turner (2019).
--
--   1. **Model (eqs. 1, 4).** An auxiliary variable $\mathbf u\in\mathbb R^m$ has a probability law $\mu$. Given $\mathbf u$, the sources $\mathbf s\in\mathbb R^n$ have the density $p(\mathbf s\mid\mathbf u)=\exp\sum_{i=1}^n q_i(s_i,\mathbf u)$, so they are conditionally independent; the $q_i$ are jointly measurable and $\int p(\mathbf s\mid\mathbf u)\,d\mathbf s=1$ for every $\mathbf u$. The observation is $\mathbf x=\mathbf f(\mathbf s)$, where $\mathbf f:\mathbb R^n\to\mathbb R^n$ is invertible and both $\mathbf f$ and $\mathbf g=\mathbf f^{-1}$ have continuous second derivatives (a $C^2$ diffeomorphism). The marginal source density $p_{\mathbf s}(\mathbf s)=\int p(\mathbf s\mid\mathbf u)\,d\mu(\mathbf u)$ is required to be a finite integral at every $\mathbf s$.
--   2. **Densities of the two classes (eq. 5).** $p(\mathbf x\mid\mathbf u)=p(\mathbf g(\mathbf x)\mid\mathbf u)\,|\det J\mathbf g(\mathbf x)|$ is the density of $\tilde{\mathbf x}=(\mathbf x,\mathbf u)$, and $p(\mathbf x)=p_{\mathbf s}(\mathbf g(\mathbf x))\,|\det J\mathbf g(\mathbf x)|$ is the density of $\tilde{\mathbf x}^*=(\mathbf x,\mathbf u^*)$ with $\mathbf u^*$ independent of $\mathbf x$, both with respect to Lebesgue measure times $\mu$. The log-density ratio is $\log p(\mathbf x\mid\mathbf u)-\log p(\mathbf x)$.
--   3. **Logistic regression (eqs. 5, 6).** The population logistic loss of a regression function $r(\mathbf x,\mathbf u)$ is $\mathbb E_{\tilde{\mathbf x}}\log(1+e^{-r})+\mathbb E_{\tilde{\mathbf x}^*}\log(1+e^{r})\in[0,\infty]$. The constrained regression function of eq. (6) is $r(\mathbf x,\mathbf u)=\sum_i\psi_i(h_i(\mathbf x),\mathbf u)$.
--   4. **Assumption of Variability (eqs. 8, 9).** $\mathbf w(\mathbf y,\mathbf u)=\big(\partial_{y_1}q_1(y_1,\mathbf u),\dots,\partial_{y_n}q_n(y_n,\mathbf u),\partial^2_{y_1}q_1(y_1,\mathbf u),\dots,\partial^2_{y_n}q_n(y_n,\mathbf u)\big)\in\mathbb R^{2n}$. The assumption holds if for every $\mathbf y\in\mathbb R^n$ there are $\mathbf u_0,\dots,\mathbf u_{2n}$ with $\mathbf w(\mathbf y,\mathbf u_j)-\mathbf w(\mathbf y,\mathbf u_0)$, $j=1,\dots,2n$, linearly independent.
--   5. **Alternative Assumption of Variability (eqs. 41, 42).** $\tilde{\mathbf w}(\mathbf y,\mathbf u)$ collects $\partial^2q_i(y_i,\mathbf u)/\partial y_i\partial u_j$ and $\partial^3q_i(y_i,\mathbf u)/\partial y_i^2\partial u_j$. The assumption holds if for every $\mathbf y$ there are an index $j$ and $\mathbf u_1,\dots,\mathbf u_{2n}$ with $\tilde{\mathbf w}(\mathbf y,\mathbf u_l)$ linearly independent.
--   6. **Conditional exponentiality (Definition 1, eq. 7).** $s_i$ is conditionally exponential of order $k$ given $\mathbf u$ if its conditional density $p(s_i\mid\mathbf u)=e^{q_i(s_i,\mathbf u)}/\int e^{q_i(t,\mathbf u)}dt$ equals $\frac{Q_i(s_i)}{Z_i(\mathbf u)}\exp\sum_{j=1}^k\tilde q_{ij}(s_i)\lambda_{ij}(\mathbf u)$ for all $s_i$ and $\mathbf u$, with $Q_i,Z_i>0$ and $\tilde q_{i1},\dots,\tilde q_{ik}$ linearly independent functions.
--   7. **Objects of Theorem 3 (eqs. 10-12).** $\boldsymbol\lambda(\mathbf u)=(\lambda_{ij}(\mathbf u))_{(i,j)}\in\mathbb R^{nk}$; $\tilde{\mathbf q}(\mathbf s)=(\tilde q_{11}(s_1),\dots,\tilde q_{nk}(s_n))$; $\bar{\mathbf L}$ is the $nk\times nk$ matrix with entry $\lambda_{ij}(\mathbf u_l)-\lambda_{ij}(\mathbf u_0)$ in row $(i,j)$ and column $l$; the regression function of eq. (11) is $\tilde{\mathbf h}(\mathbf x)^T\mathbf v(\mathbf u)+a(\mathbf x)+b(\mathbf u)$.
--   8. **Partial derivatives.** $\partial_jF(\mathbf y)$ is the derivative of $F:\mathbb R^n\to\mathbb R$ in the direction of the $j$-th basis vector.
--
--   **Formalization Note** The auxiliary variable is taken in $\mathbb R^m$ as in Section 3.1, and the conditional densities $q_i(\cdot,\mathbf u)$ are given for every $\mathbf u\in\mathbb R^m$; statements quantify over all $\mathbf u$ rather than over the support of $\mu$. The finiteness of $p_{\mathbf s}$ and the joint measurability of the $q_i$ are implicit in the paper, which takes $\log p_{\mathbf s}$ and expectations freely. The logistic loss is valued in $[0,\infty]$ so that no non-integrable case is silently set to $0$.
-- source:
--   Hyvärinen, Sasaki and Turner, Nonlinear ICA Using Auxiliary Variables and Generalized Contrastive Learning, arXiv:1805.08651v3 (AISTATS 2019), Sections 3.1-3.2 (eqs. (1), (4)-(6)), Section 4.1 Definition 1 (eq. (7)), Section 4.2 Theorem 1 (eqs. (8)-(9)), Section 4.3 (eqs. (10)-(12)), Supplementary A and D (eqs. (41)-(42)), pp. 3-6, 11-13

import Mathlib

/-!
Hyvärinen, Sasaki and Turner, *Nonlinear ICA Using Auxiliary Variables and Generalized
Contrastive Learning*, arXiv:1805.08651v3 (AISTATS 2019): the nonlinear ICA model with auxiliary
variables (Section 3.1, eqs. (1), (4)), the contrastive logistic-regression problem (Section 3.2,
eqs. (5), (6)), the Assumption of Variability (Section 4.2, Theorem 1, eqs. (8), (9)) and its
alternative form (Supplementary D, eqs. (41), (42)), conditional exponentiality (Section 4.1,
Definition 1, eq. (7)) and the objects of Theorem 3 (Section 4.3, eqs. (10)-(12)).

Sources live in `ℝ^n = Fin n → ℝ`, the auxiliary variable in `ℝ^m = Fin m → ℝ`, and the
mixing `x = f(s)` is an equivalence of `ℝ^n` with `g = f⁻¹ = f.symm`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace NonlinearICAAux

variable {n m k : ℕ}

/-- Section 3.1 (p. 3): a map `ℝ^n → ℝ^n` that is invertible, has continuous second derivatives,
and whose inverse has continuous second derivatives. -/
def IsC2Diffeo (e : (Fin n → ℝ) ≃ (Fin n → ℝ)) : Prop :=
  ContDiff ℝ 2 e ∧ ContDiff ℝ 2 e.symm

/-- Eq. (4) (Section 3.1, p. 3): the conditional log-density of the sources,
`log p(s | u) = ∑ᵢ qᵢ(sᵢ, u)`. -/
def condLogDensityS (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (s : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  ∑ i, q i (s i) u

/-- Section 3.1, eqs. (1) and (4) (p. 3): the nonlinear ICA model with auxiliary variables. The
auxiliary variable `u ∈ ℝ^m` has law `μ`; given `u`, the sources `s ∈ ℝ^n` have the density
`exp (∑ᵢ qᵢ(sᵢ, u))` (integrable with integral `1` for every `u`); the observation is
`x = f(s)` with `f` a `C²` diffeomorphism. The `qᵢ` are jointly measurable, and the marginal
density of the sources, `p_s(s) = ∫ exp (∑ᵢ qᵢ(sᵢ, u)) dμ(u)`, is a finite integral at every `s`
(its logarithm is used in the proofs of Theorems 1 and 3, Supplementary A and C). -/
def IsAuxICAModel (μ : Measure (Fin m → ℝ)) (q : Fin n → ℝ → (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) ≃ (Fin n → ℝ)) : Prop :=
  IsC2Diffeo f ∧ (∀ i, Measurable (fun p : ℝ × (Fin m → ℝ) => q i p.1 p.2)) ∧
    (∀ u, Integrable (fun s => Real.exp (condLogDensityS q s u)) ∧
      ∫ s, Real.exp (condLogDensityS q s u) = 1) ∧
    (∀ s, Integrable (fun u => Real.exp (condLogDensityS q s u)) μ)

/-- Supplementary A (p. 11): the marginal density of the sources, `p_s(s) = ∫ p(s | u) dμ(u)`. -/
def margDensityS (μ : Measure (Fin m → ℝ)) (q : Fin n → ℝ → (Fin m → ℝ) → ℝ)
    (s : Fin n → ℝ) : ℝ :=
  ∫ u, Real.exp (condLogDensityS q s u) ∂μ

/-- Supplementary A (p. 11): the absolute Jacobian determinant `|det J g(x)|` of a map
`g : ℝ^n → ℝ^n`. -/
def absJacDet (g : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  |LinearMap.det ((fderiv ℝ g x : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))|

/-- Supplementary A (p. 11): the conditional density of the observation given the auxiliary
variable, `p(x | u) = p(g(x) | u) |det J g(x)|` with `g = f⁻¹`; it is the density of the pair
`x̃ = (x, u)` of eq. (5) with respect to Lebesgue measure times the law of `u`. -/
def condDensityX (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (f : (Fin n → ℝ) ≃ (Fin n → ℝ))
    (x : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  Real.exp (condLogDensityS q (f.symm x) u) * absJacDet f.symm x

/-- Supplementary A (p. 11): the marginal density of the observation,
`p(x) = p_s(g(x)) |det J g(x)|`; it is the density of the pair `x̃* = (x, u*)` of eq. (5), with
`u*` independent of `x`, with respect to Lebesgue measure times the law of `u`. -/
def margDensityX (μ : Measure (Fin m → ℝ)) (q : Fin n → ℝ → (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) ≃ (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  margDensityS μ q (f.symm x) * absJacDet f.symm x

/-- Supplementary A (p. 11): the difference of the log-densities of the two classes `x̃` and `x̃*`
of eq. (5), `log p(x, u) - log p(x) - log p(u) = log p(x | u) - log p(x)`. -/
def logRatio (μ : Measure (Fin m → ℝ)) (q : Fin n → ℝ → (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) ≃ (Fin n → ℝ)) (x : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  Real.log (condDensityX q f x u) - Real.log (margDensityX μ q f x)

/-- Section 3.2 (p. 3): the population logistic loss of a regression function `r(x, u)` that
discriminates `x̃ = (x, u)` (class 1, posterior `1 / (1 + exp (-r))`) from `x̃* = (x, u*)`
(class 0), the two classes having equal weight:
`E_{x̃} log (1 + e^{-r}) + E_{x̃*} log (1 + e^{r})`, valued in `[0, ∞]`. -/
def logisticLoss (μ : Measure (Fin m → ℝ)) (q : Fin n → ℝ → (Fin m → ℝ) → ℝ)
    (f : (Fin n → ℝ) ≃ (Fin n → ℝ)) (r : (Fin n → ℝ) × (Fin m → ℝ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ p, (ENNReal.ofReal (Real.log (1 + Real.exp (-r p)) * condDensityX q f p.1 p.2) +
      ENNReal.ofReal (Real.log (1 + Real.exp (r p)) * margDensityX μ q f p.1))
    ∂((volume : Measure (Fin n → ℝ)).prod μ)

/-- Eq. (6) (Section 3.2, p. 3): the regression function `r(x, u) = ∑ᵢ ψᵢ(hᵢ(x), u)`. -/
def regFun (ψ : Fin n → ℝ → (Fin m → ℝ) → ℝ) (h : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  ∑ i, ψ i (h x i) u

/-- Eq. (9) (Theorem 1, p. 5): `w(y, u) ∈ ℝ^{2n}`, the first derivatives `∂qᵢ(yᵢ, u)/∂yᵢ`
(left block) followed by the second derivatives `∂²qᵢ(yᵢ, u)/∂yᵢ²` (right block). -/
def wVec (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (y : Fin n → ℝ) (u : Fin m → ℝ) :
    Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun i => deriv (fun s => q i s u) (y i))
    (fun i => iteratedDeriv 2 (fun s => q i s u) (y i))

/-- Theorem 1, Assumption 3, eq. (8) (p. 5), the Assumption of Variability: for every
`y ∈ ℝ^n` there are `2n + 1` values `u₀, …, u_{2n}` such that the `2n` vectors
`w(y, u_j) - w(y, u₀)`, `j = 1, …, 2n`, are linearly independent. -/
def Variability (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, ∃ u₀ : Fin m → ℝ, ∃ us : Fin (2 * n) → (Fin m → ℝ),
    LinearIndependent ℝ (fun j => wVec q y (us j) - wVec q y u₀)

/-- Eq. (42) (Supplementary D, p. 13): `w̃(y, u)`, the derivatives with respect to the
coordinate `u_j` of the entries of `w(y, u)`: `∂²qᵢ(yᵢ, u)/∂yᵢ∂u_j` (left block) and
`∂³qᵢ(yᵢ, u)/∂yᵢ²∂u_j` (right block). -/
def wAltVec (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (y : Fin n → ℝ) (u : Fin m → ℝ) (j : Fin m) :
    Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun i => fderiv ℝ (fun u' => deriv (fun s => q i s u') (y i)) u (Pi.single j 1))
    (fun i => fderiv ℝ (fun u' => iteratedDeriv 2 (fun s => q i s u') (y i)) u (Pi.single j 1))

/-- Supplementary D, eq. (41) (p. 13), the Alternative Assumption of Variability: for every
`y ∈ ℝ^n` there are an index `j` of the auxiliary variable and `2n` values `u₁, …, u_{2n}`
such that the vectors `w̃(y, u_l)` (derivatives in `u_j`) are linearly independent. -/
def AltVariability (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, ∃ j : Fin m, ∃ us : Fin (2 * n) → (Fin m → ℝ),
    LinearIndependent ℝ (fun l => wAltVec q y (us l) j)

/-- Definition 1 (p. 4): the conditional density `p(sᵢ | u)` of the single source `sᵢ` in the
model of eq. (4), `exp qᵢ(sᵢ, u) / ∫ exp qᵢ(t, u) dt`. -/
def condMarginal (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (i : Fin n) (u : Fin m → ℝ) (s : ℝ) : ℝ :=
  Real.exp (q i s u) / ∫ t, Real.exp (q i t u)

/-- Definition 1, eq. (7) (p. 4), with its data named: `sᵢ` is conditionally exponential of
order `k` given `u` with base `Qᵢ > 0`, normaliser `Zᵢ > 0`, linearly independent sufficient
statistics `q̃ᵢ₁, …, q̃ᵢₖ` and natural parameters `λᵢ₁(u), …, λᵢₖ(u)`:
`p(sᵢ | u) = Qᵢ(sᵢ) / Zᵢ(u) · exp (∑ⱼ q̃ᵢⱼ(sᵢ) λᵢⱼ(u))`. -/
def IsCondExpWith (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (i : Fin n) (Q : ℝ → ℝ)
    (Z : (Fin m → ℝ) → ℝ) (qt : Fin k → ℝ → ℝ) (lam : Fin k → (Fin m → ℝ) → ℝ) : Prop :=
  (∀ s, 0 < Q s) ∧ (∀ u, 0 < Z u) ∧ LinearIndependent ℝ qt ∧
    ∀ u s, condMarginal q i u s = Q s / Z u * Real.exp (∑ j, qt j s * lam j u)

/-- Definition 1 (p. 4): `sᵢ` is conditionally exponential of order `k` given `u`. -/
def IsCondExp (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (i : Fin n) (k : ℕ) : Prop :=
  ∃ (Q : ℝ → ℝ) (Z : (Fin m → ℝ) → ℝ) (qt : Fin k → ℝ → ℝ) (lam : Fin k → (Fin m → ℝ) → ℝ),
    IsCondExpWith q i Q Z qt lam

/-- Theorem 2 (ii) (p. 5): the vector `(λᵢⱼ(u))_{(i,j)} ∈ ℝ^{nk}` of all natural parameters. -/
def lamVec (lam : Fin n → Fin k → (Fin m → ℝ) → ℝ) (u : Fin m → ℝ) : Fin n × Fin k → ℝ :=
  fun p => lam p.1 p.2 u

/-- Eq. (12) (Theorem 3, p. 6): the vector of all sufficient statistics
`(q̃₁₁(s₁), q̃₁₂(s₁), …, q̃ₙₖ(sₙ))`. -/
def sstatVec (qt : Fin n → Fin k → ℝ → ℝ) (s : Fin n → ℝ) : Fin n × Fin k → ℝ :=
  fun p => qt p.1 p.2 (s p.1)

/-- Eq. (10) (Theorem 3, Assumption 3, p. 5): the `nk × nk` matrix `L̄` with row `(i, j)` and
column `l` equal to `λᵢⱼ(u_l) - λᵢⱼ(u₀)`. -/
def lamBar (lam : Fin n → Fin k → (Fin m → ℝ) → ℝ) (u₀ : Fin m → ℝ)
    (us : Fin n × Fin k → (Fin m → ℝ)) : Matrix (Fin n × Fin k) (Fin n × Fin k) ℝ :=
  fun p l => lam p.1 p.2 (us l) - lam p.1 p.2 u₀

/-- Eq. (11) (Theorem 3, p. 5): the regression function `h̃(x)ᵀ v(u) + a(x) + b(u)` with
`h̃ : ℝ^n → ℝ^{nk}` and `v : ℝ^m → ℝ^{nk}`. -/
def regExp (ht : (Fin n → ℝ) → (Fin n × Fin k → ℝ)) (v : (Fin m → ℝ) → (Fin n × Fin k → ℝ))
    (a : (Fin n → ℝ) → ℝ) (b : (Fin m → ℝ) → ℝ) (x : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  ∑ p, ht x p * v u p + a x + b u

/-- Supplementary A (p. 11): the partial derivative `∂F(y)/∂y_j` of `F : ℝ^n → ℝ`. -/
def partialDeriv (F : (Fin n → ℝ) → ℝ) (j : Fin n) (y : Fin n → ℝ) : ℝ :=
  fderiv ℝ F y (Pi.single j 1)

end NonlinearICAAux


