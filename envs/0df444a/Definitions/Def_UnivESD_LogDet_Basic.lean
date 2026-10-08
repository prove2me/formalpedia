-- Prove2me | Definitions.Def_UnivESD_LogDet_Basic
-- name    : UnivESD_LogDet_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:33.781843+00:00
-- url     : https://prove2.me/theorems/b2beb37a-767c-4642-b861-eda095823fdc
-- title:
--   The ESD $\mu_A$, one-based singular values $\sigma_i(A)$, the log-potential, and convergence in probability / almost surely
-- statement:
--   For an $n\times n$ complex matrix $A$ with eigenvalues $\lambda_1,\dots,\lambda_n\in\mathbb C$ (the roots of its characteristic polynomial, counted with algebraic multiplicity), the **empirical spectral distribution** (ESD) of $A$ is the discrete probability measure
--   $$\mu_A = \frac1n\sum_{i=1}^n \delta_{\lambda_i}$$
--   on $\mathbb C$. The **singular values** of an $m\times n$ complex matrix $A$ are written $\sigma_1(A)\ge\sigma_2(A)\ge\dots\ge0$, indexed from $1$. The **logarithmic potential** of a measure $\mu$ on $\mathbb C$ at $z\in\mathbb C$ is
--   $$\int_{\mathbb C}\log|w-z|\,d\mu(w).$$
--
--   For real random variables $Y_n$ on a probability space $(\Omega,\mathbf P)$ and a constant $L$: $Y_n$ **converges in probability** to $L$ if $\mathbf P(|Y_n-L|\ge\varepsilon)\to0$ for every $\varepsilon>0$, and **converges almost surely** to $L$ if $\mathbf P(\lim_n Y_n=L)=1$.
--
--   For random $n\times n$ matrices $B_n$ and a deterministic measure $\mu$ on $\mathbb C$, the ESDs $\mu_{B_n}$ **converge in probability to $\mu$** (vague topology) if for every continuous compactly supported $f:\mathbb C\to\mathbb R$ the quantity $\int f\,d\mu_{B_n}-\int f\,d\mu$ converges to zero in probability; they **converge almost surely to $\mu$** if, with probability one, $\int f\,d\mu_{B_n}\to\int f\,d\mu$ for all such $f$ simultaneously.
--
--   These are the objects in which Theorem 1.15 and its proof are stated.
--
--   **Formalization Note** The ESD is $n^{-1}$ times the sum of Dirac masses over the multiset `A.charpoly.roots`, so multiplicities are kept; for $n=0$ it is the zero measure, which is harmless because every statement is asymptotic in $n$. `sv A i` is Mathlib's zero-based `LinearMap.singularValues` of the Euclidean linear map of $A$ at index $i-1$; only $1\le i\le n$ is ever used. The logarithmic potential is a Bochner integral and equals $0$ when $w\mapsto\log|w-z|$ is not $\mu$-integrable. The almost sure ESD convergence uses one null set for all test functions.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, pp. 2023–2024 (PDF 1–2), Definition 1.1 and §1.1 (ESD, vague topology); p. 2044 (singular values)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic

namespace UnivESD.LogDet

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The `i`-th singular value `σ_i(A)` of a complex matrix `A`, **one-based** as in the paper
(p. 2044): `σ_1(A) ≥ σ_2(A) ≥ ⋯ ≥ σ_n(A) ≥ 0`. It is Mathlib's zero-based, antitone
`LinearMap.singularValues` of the Euclidean linear map of `A`, shifted by one:
`sv A i = singularValues (i - 1)`. Only indices `1 ≤ i ≤ n` are used. -/
noncomputable def sv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues (i - 1)

/-- The logarithmic potential `∫_ℂ log|w − z| dμ(w)` of a measure `μ` on `ℂ` at `z`
(Bochner integral: it is `0` when `w ↦ log|w − z|` is not `μ`-integrable). -/
noncomputable def logPotential (μ : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ w, Real.log ‖w - z‖ ∂μ

/-- Convergence in probability of real random variables `Y n` to the constant `L`
(Definition 1.1, p. 2023): for every `ε > 0`, `P(|Y_n − L| ≥ ε) → 0`. -/
def ConvInProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ) (L : ℝ) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P {ω | ε ≤ |Y n ω - L|}) atTop (𝓝 0)

/-- Almost sure convergence of real random variables `Y n` to the constant `L`
(Definition 1.1, p. 2024): `P(lim_n Y_n = L) = 1`. -/
def ConvAS {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ) (L : ℝ) : Prop :=
  ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 L)

/-- The ESDs of the random matrices `B n` converge in probability to the deterministic measure
`μ` in the vague topology (p. 2024): for every continuous compactly supported `f : ℂ → ℝ`,
`∫ f dμ_{B_n} − ∫ f dμ` converges to zero in probability. -/
def ESDConvInProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℂ) (μ : Measure ℂ) : Prop :=
  ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    ConvInProb P (fun n ω => ∫ w, f w ∂(UnivESD.Universality.esd (B n ω))) (∫ w, f w ∂μ)

/-- The ESDs of the random matrices `B n` converge almost surely to `μ` (p. 2024): with
probability one, for **all** continuous compactly supported `f : ℂ → ℝ` simultaneously,
`∫ f dμ_{B_n} → ∫ f dμ`. -/
def ESDConvAS {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℂ) (μ : Measure ℂ) : Prop :=
  ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun n => ∫ w, f w ∂(UnivESD.Universality.esd (B n ω))) atTop (𝓝 (∫ w, f w ∂μ))

end UnivESD.LogDet


