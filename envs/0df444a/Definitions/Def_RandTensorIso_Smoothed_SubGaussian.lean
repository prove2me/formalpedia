-- Prove2me | Definitions.Def_RandTensorIso_Smoothed_SubGaussian
-- name    : RandTensorIso_Smoothed_SubGaussian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:36:15.990889+00:00
-- url     : https://prove2.me/theorems/9d9ce8aa-2354-499b-be67-abf5a418988d
-- title:
--   Mean-zero, variance-one sub-Gaussian laws (Definition 3.1), $K_\xi$, $\chi_\xi$, i.i.d. random tensors and matrices, the Lévy concentration function and clustered vectors
-- statement:
--   **Definition 3.1.** A real or complex random variable $\xi$ is **sub-Gaussian** if $\mathbb P[|\xi|>t]\le2\exp(-t^2/K^2)$ for all $t>0$ and some $K>0$; the minimal such $K$ is the **sub-Gaussian constant** $K_\xi$. A **mean-zero, variance-one sub-Gaussian distribution** satisfies in addition $\mathbb E\xi=0$ and $\mathbb E|\xi|^2=1$ (on $\mathbb C$ the real and imaginary parts may be dependent; $\xi$ may be real-valued or atomic). For $\xi$ on $\mathbb C$, $\chi_\xi$ is the smallest eigenvalue of the covariance matrix of $(\operatorname{Re}\xi,\operatorname{Im}\xi)\in\mathbb R^2$: for that matrix $\begin{pmatrix}a&b\\b&c\end{pmatrix}$,
--   $$\chi_\xi=\frac{a+c}2-\sqrt{\Big(\frac{a-c}2\Big)^2+b^2}.$$
--   A random tensor $M\in\mathbb C^{n\times n\times n}$ (an $n\times p$ matrix, a vector of $\mathbb R^n$) **has i.i.d. entries $\sim\xi$** when its law is the product of copies of $\xi$.
--
--   **Definition 4.2.** The **Lévy concentration function** of a real random variable $Y$ is $\mathcal L(Y,r)=\sup_{x\in\mathbb R}\mathbb P(|Y-x|\le r)$, $r>0$.
--
--   **Definition 4.4.** For $q\ge1$ and $r>0$, $z\in\mathbb R^n$ is **$(q,r)$-clustered** if some union of $q$ closed intervals of length $2r$ contains at least $\lceil n/2\rceil$ of its coordinates.
--
--   **Formalization Note.** `SubGaussianTail ξ K` is the tail bound with $K>0$, `subGaussConst ξ` is the infimum of such $K$ (the minimum: the admissible set is closed and bounded away from $0$ under variance one), and `IsStdSubGaussian ξ` is $\int x\,d\xi=0$, $\int\|x\|^2d\xi=1$ plus the tail bound for some $K$; the tail bound makes both integrands integrable, so the Bochner integrals are genuine. Theorems quantify over `ξ : ProbabilityMeasure ℝ` or `ℂ`. `tensorLaw ξ n` and `matrixLaw ξ n p` are `Measure.pi` products; `levyConc` is valued in $[0,1]\subseteq\mathbb R_{\ge0}\cup\{\infty\}$; coordinates of $z$ are counted with their index, $\lceil n/2\rceil=\lfloor (n+1)/2\rfloor$.
--
--   Integrability of the identity and squared norm is explicit in `IsStdSubGaussian`. For the probability laws on $\mathbb R$ and $\mathbb C$ used in the mission, these conditions follow from the tail bound and add no restriction. The infimum defining $K_\xi$ is positive and attained for variance-one laws; for the zero law it is zero.
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), pp. 34–35, 51, 59 (PDF 36–37, 53, 61), Definition 3.1, Definitions 4.2, 4.4, §4.4 (χ_ξ)

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor

namespace RandTensorIso.Smoothed

open MeasureTheory
open scoped Classical

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- Definition 3.1 (tail bound): `P[|ξ| > t] ≤ 2 exp(−t²/K²)` for all `t > 0`, with `K > 0`. -/
def SubGaussianTail (ξ : Measure E) (K : ℝ) : Prop :=
  0 < K ∧ ∀ t : ℝ, 0 < t → ξ {x | t < ‖x‖} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / K ^ 2))

/-- Definition 3.1: the sub-Gaussian constant `K_ξ`, the minimal `K` for which the tail bound
holds (the infimum of the admissible `K`; positive and attained for the variance-one laws used here). -/
noncomputable def subGaussConst (ξ : Measure E) : ℝ :=
  sInf {K : ℝ | SubGaussianTail ξ K}

/-- A mean-zero, variance-one sub-Gaussian distribution (Definition 3.1), on `ℝ` or on `ℂ`:
`E ξ = 0`, `E |ξ|² = 1`, and the tail bound of Definition 3.1 holds for some `K > 0`.
(Integrability is explicit. For probability laws on ℝ or ℂ it follows from the tail bound.) -/
def IsStdSubGaussian [CompleteSpace E] (ξ : Measure E) : Prop :=
  Integrable (fun x : E => x) ξ ∧ Integrable (fun x : E => ‖x‖ ^ 2) ξ ∧
    ∫ x, x ∂ξ = 0 ∧ ∫ x, ‖x‖ ^ 2 ∂ξ = 1 ∧ ∃ K : ℝ, SubGaussianTail ξ K

end General

/-- `χ_ξ`: the smallest eigenvalue of the covariance matrix
`[[Var Re ξ, Cov(Re ξ, Im ξ)], [Cov(Re ξ, Im ξ), Var Im ξ]]` of `(Re ξ, Im ξ) ∈ ℝ²`, i.e.
`(a + c)/2 − √(((a − c)/2)² + b²)` for that matrix `[[a, b], [b, c]]`. -/
noncomputable def chiConst (ξ : Measure ℂ) : ℝ :=
  let mr := ∫ z, z.re ∂ξ
  let mi := ∫ z, z.im ∂ξ
  let a := ∫ z, (z.re - mr) ^ 2 ∂ξ
  let c := ∫ z, (z.im - mi) ^ 2 ∂ξ
  let b := ∫ z, (z.re - mr) * (z.im - mi) ∂ξ
  (a + c) / 2 - Real.sqrt (((a - c) / 2) ^ 2 + b ^ 2)

/-- The law of a random tensor `M ∈ ℂ^{n×n×n}` with i.i.d. entries `m_{ijk} ∼ ξ`. -/
noncomputable def tensorLaw (ξ : ProbabilityMeasure ℂ) (n : ℕ) : Measure (Tensor3 n) :=
  Measure.pi (fun _ : Fin n × Fin n × Fin n => (ξ : Measure ℂ))

/-- The law of a random `n × p` matrix with i.i.d. entries `m_{ij} ∼ ξ`, as a function
`Fin n → Fin p → ℂ` (read as a matrix with `Matrix.of`). -/
noncomputable def matrixLaw (ξ : ProbabilityMeasure ℂ) (n p : ℕ) : Measure (Fin n → Fin p → ℂ) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin p => (ξ : Measure ℂ)))

/-- The law of a random vector `X ∈ ℝ^n` with i.i.d. entries `X_i ∼ ξ`. -/
noncomputable def vectorLawR (ξ : ProbabilityMeasure ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => (ξ : Measure ℝ))

/-- Definition 4.2: the Lévy concentration function `L(Y, r) = sup_{x ∈ ℝ} P(|Y − x| ≤ r)` of a
real random variable `Y` on `(Ω, μ)`, valued in `[0, 1] ⊆ ℝ≥0∞`. -/
noncomputable def levyConc {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ)
    (r : ℝ) : ENNReal :=
  ⨆ x : ℝ, μ {ω | |Y ω - x| ≤ r}

/-- Definition 4.4: `z ∈ ℝ^n` is `(q, r)`-clustered if some union of `q` closed intervals of
length `2r` (centres `c_1, …, c_q`, intervals `[c_k − r, c_k + r]`) contains at least `⌈n/2⌉`
of its coordinates (counted with their index). -/
def IsClustered {n : ℕ} (q : ℕ) (r : ℝ) (z : Fin n → ℝ) : Prop :=
  ∃ c : Fin q → ℝ, (n + 1) / 2 ≤
    (Finset.univ.filter (fun i : Fin n => ∃ k : Fin q, |z i - c k| ≤ r)).card

end RandTensorIso.Smoothed


