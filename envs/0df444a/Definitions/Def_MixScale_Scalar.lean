-- Prove2me | Definitions.Def_MixScale_Scalar
-- name    : MixScale_Scalar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:54.360209+00:00
-- url     : https://prove2.me/theorems/766929dc-cf30-427b-8369-63d39ea62122
-- title:
--   Scalar projections: bounds (17), coefficients (18), the kernel $K$ and the midpoint-grid Fourier features
-- statement:
--   For a scalar projection with centers $b_j$, scales $v_j$ and weights $w_j$, the bounds (17) are $|b_j|\le M$, $|b_j-b_\ell|\ge\Delta$, $K^{-1}\le v_j\le K$, $w_j\ge w_\star$, $\sum_jw_j=1$, with $M,K\ge1$ and $0<\Delta\le1$.
--
--   The spectral coefficients (18) are $a_j=c_0w_jv_j^{-q/2}$ and $c_j=\lambda a_jv_j^{-\alpha/2}$, with $a_*=c_0w_\star K^{-q/2}$, $A=c_0K^{q/2}$, $c_*=\lambda a_*K^{-\alpha/2}$ and $c^*=\lambda AK^{\alpha/2}$. The inverse maps are $v=(\lambda a/c)^{2/\alpha}$ and $w=av^{q/2}/c_0$.
--
--   The kernel is $K(z)=\int_1^2e^{izx}\,dx$. The midpoint grid is $x_\ell=1+(\ell+1/2)/n$. The Fourier features are $U(X)=n^{-1/2}(e^{iRx_\ell X})_\ell$ and $Y(X)=n^{-1/2}((Rx_\ell)^qe^{iRx_\ell X})_\ell$, with $E\,UU^*$, $\mathrm{Cov}(Y)$ and the covariance of the realified vector (real parts stacked on imaginary parts).
--
--   These are the objects of the scalar analysis that the algorithm applies to each projection.
--
--   **Formalization Note** The operator norm is the norm on the Euclidean space. Grid points are `Fin n` ($\ell=0,\dots,n-1$), components `Fin k`. Real powers are `Real.rpow`.
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), (16)–(18), p.14 (PDF p.16); (21)–(22), p.15; §B.1, p.18; Lemma C.1, p.21

import Mathlib
import Definitions.Def_MixScale_Profile

open MeasureTheory

namespace MixScale

/-!
# The scalar projection: coefficients (18), the scalar bounds (17), the kernel `K` and the
# midpoint-grid Fourier features

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*,
STOC 2027 submission manuscript (sha256 5277f95e…7c6c). (16)–(18), p.14 (PDF p.16); (21), p.15
(PDF p.17); Lemma A.4, p.15; the kernel `K` of §B.1, p.18 (PDF p.20); Lemma C.1, p.21 (PDF p.23).

"assume known scalar bounds `|b_j| ≤ M`, `|b_j − b_ℓ| ≥ Δ`, `K⁻¹ ≤ v_j ≤ K`, `w_j ≥ w★`,
`Σ_j w_j = 1`, (17) with `M, K ≥ 1` and `0 < Δ ≤ 1`. […] Let `a_j = c₀w_jv_j^{−q/2}`,
`c_j = λa_jv_j^{−α/2}`, `a∗ = c₀w★K^{−q/2}`, `A = c₀K^{q/2}`. (18) Then `a_j ≥ a∗`, `Σ_j a_j ≤ A`,
and `c∗ := λa∗K^{−α/2} ≤ c_j ≤ c^∗ := λAK^{α/2}`." "`θ = (a_j, ζ_j, β_j)_{j=1}^k`, `ζ_j = c_j/R^α`,
`β_j = Rb_j`. (21)" "`K(z) = ∫_1^2 e^{izx} dx`". "the midpoint grid `x_ℓ = 1 + (ℓ + 1/2)/n` […]
`U(X) = n^{−1/2}(e^{iRx_ℓX})_ℓ`, `Y(X) = n^{−1/2}((Rx_ℓ)^q e^{iRx_ℓX})_ℓ`."

**Formalization Note.** Components are `Fin k` (0-based), grid points `Fin n` (`ℓ = 0, …, n − 1`).
Real powers are `Real.rpow`. The bounds (17) are a predicate on scalar lists `b, v, w`. `E UU∗`,
`Cov(Y)` are entrywise integrals against the scalar law; `‖·‖_op` is the operator norm on the
Euclidean space (`Matrix.toEuclideanCLM`). Realification (p.15, (22)) stacks real and imaginary
parts, indexed by `Fin n ⊕ Fin n`.
-/

/-- The scalar bounds (17) on centers `b`, scales `v` and weights `w` of a `k`-component scalar
mixture, with `M, K ≥ 1` and `0 < Δ ≤ 1`. -/
def Scalar17 {k : ℕ} (M K Δ wstar : ℝ) (b v w : Fin k → ℝ) : Prop :=
  1 ≤ M ∧ 1 ≤ K ∧ 0 < Δ ∧ Δ ≤ 1 ∧
  (∀ j, |b j| ≤ M) ∧ (∀ j l, j ≠ l → Δ ≤ |b j - b l|) ∧ (∀ j, K⁻¹ ≤ v j ∧ v j ≤ K) ∧
  (∀ j, wstar ≤ w j) ∧ ∑ j, w j = 1

/-- The leading amplitude `a = c₀ w v^{−q/2}` (18). -/
noncomputable def ampl (S : ProfileSpec) (w v : ℝ) : ℝ := S.c0 * w * v ^ (-S.q / 2)

/-- The correction coefficient `c = λ a v^{−α/2}` (18). -/
noncomputable def corr (S : ProfileSpec) (w v : ℝ) : ℝ := S.lam * ampl S w v * v ^ (-S.α / 2)

/-- `a∗ = c₀ w★ K^{−q/2}` (18). -/
noncomputable def aLow (S : ProfileSpec) (wstar K : ℝ) : ℝ := S.c0 * wstar * K ^ (-S.q / 2)

/-- `A = c₀ K^{q/2}` (18). -/
noncomputable def aHigh (S : ProfileSpec) (K : ℝ) : ℝ := S.c0 * K ^ (S.q / 2)

/-- `c∗ = λ a∗ K^{−α/2}` (p.14). -/
noncomputable def cLow (S : ProfileSpec) (wstar K : ℝ) : ℝ := S.lam * aLow S wstar K * K ^ (-S.α / 2)

/-- `c^∗ = λ A K^{α/2}` (p.14). -/
noncomputable def cHigh (S : ProfileSpec) (K : ℝ) : ℝ := S.lam * aHigh S K * K ^ (S.α / 2)

/-- The inverse scale map `v = (λ a / c)^{2/α}` (Lemma A.3). -/
noncomputable def invScale (S : ProfileSpec) (a c : ℝ) : ℝ := (S.lam * a / c) ^ (2 / S.α)

/-- The inverse weight map `w = a v^{q/2} / c₀` with `v = (λ a/c)^{2/α}` (Lemma A.3). -/
noncomputable def invWeight (S : ProfileSpec) (a c : ℝ) : ℝ :=
  a * invScale S a c ^ (S.q / 2) / S.c0

/-- The kernel `K(z) = ∫_1^2 e^{izx} dx` of §B.1. -/
noncomputable def kernelK (z : ℝ) : ℂ :=
  ∫ x in (1 : ℝ)..2, Complex.exp ((z * x : ℝ) * Complex.I)

/-- The midpoint grid point `x_ℓ = 1 + (ℓ + 1/2)/n`. -/
noncomputable def gridPt (n : ℕ) (l : ℕ) : ℝ := 1 + ((l : ℝ) + 1 / 2) / n

/-- The feature `U_ℓ(X) = n^{−1/2} e^{iRx_ℓX}` (Lemma C.1). -/
noncomputable def featU (R : ℝ) (n : ℕ) (X : ℝ) (l : Fin n) : ℂ :=
  ((Real.sqrt n)⁻¹ : ℝ) * Complex.exp ((R * gridPt n l * X : ℝ) * Complex.I)

/-- The feature `Y_ℓ(X) = n^{−1/2}(Rx_ℓ)^q e^{iRx_ℓX}` (Lemma C.1). -/
noncomputable def featY (q R : ℝ) (n : ℕ) (X : ℝ) (l : Fin n) : ℂ :=
  ((Real.sqrt n)⁻¹ * (R * gridPt n l) ^ q : ℝ) *
    Complex.exp ((R * gridPt n l * X : ℝ) * Complex.I)

/-- The operator norm `‖A‖_op` of a square matrix over `ℝ` or `ℂ` on the Euclidean space. -/
noncomputable def opNorm {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) A‖

/-- The matrix `E UU∗` under the scalar law `μ` (Lemma C.1). -/
noncomputable def momentU (μ : Measure ℝ) (R : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun l h => ∫ X, featU R n X l * (starRingEnd ℂ) (featU R n X h) ∂μ

/-- The complex covariance `Cov(Y) = E YY∗ − (E Y)(E Y)∗` under the scalar law `μ` (Lemma C.1). -/
noncomputable def covY (μ : Measure ℝ) (q R : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun l h => (∫ X, featY q R n X l * (starRingEnd ℂ) (featY q R n X h) ∂μ) -
    (∫ X, featY q R n X l ∂μ) * (starRingEnd ℂ) (∫ X, featY q R n X h ∂μ)

/-- The realification of `Y(X)`: real parts, then imaginary parts (p.15, (22)). -/
noncomputable def realifyY (q R : ℝ) (n : ℕ) (X : ℝ) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun l => (featY q R n X l).re) (fun l => (featY q R n X l).im)

/-- The covariance matrix of the realified vector under the scalar law `μ` (Lemma C.1). -/
noncomputable def covYReal (μ : Measure ℝ) (q R : ℝ) (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fun l h => (∫ X, realifyY q R n X l * realifyY q R n X h ∂μ) -
    (∫ X, realifyY q R n X l ∂μ) * (∫ X, realifyY q R n X h ∂μ)

end MixScale


