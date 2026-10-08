-- Prove2me | Definitions.Def_UnivESD_Universality_Model
-- name    : UnivESD_Universality_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:47.007804+00:00
-- url     : https://prove2.me/theorems/f92b7be5-1173-4034-a566-9b24285fbd08
-- title:
--   The i.i.d. model $A_n=M_n+X_n$, hypotheses (1.3), (1.4), and convergence of ESDs in probability and almost surely
-- statement:
--   This file fixes the random model of Theorem 1.5 and the probabilistic vocabulary of Definition 1.1.
--
--   1. **Entries.** A complex random variable $x$ has *zero mean and unit variance* if $x\in L^2$, $\mathbf E x=0$ and $\mathbf E|x|^2=1$. An *i.i.d. array* is a family $(x_{ij})_{i,j\ge1}$ of jointly independent random variables, each distributed as one such $x$; the random matrix $X_n=(x_{ij})_{1\le i,j\le n}$ is its top-left $n\times n$ corner.
--   2. **Hypothesis (1.3)** on deterministic matrices $M_n\in M_n(\mathbb C)$:
--   $$\sup_n\frac1{n^2}\|M_n\|_2^2<\infty .$$
--   3. **Vague convergence of ESDs.** A sequence of $n\times n$ matrices $N_n$ has convergent ESDs if there is a probability measure $\nu$ on $\mathbb C$ with $\int f\,d\mu_{N_n}\to\int f\,d\nu$ for every continuous compactly supported $f:\mathbb C\to\mathbb R$. **Hypothesis (1.4)**: for Lebesgue-almost every $z\in\mathbb C$ the ESDs of $\bigl(\frac1{\sqrt n}M_n-zI\bigr)\bigl(\frac1{\sqrt n}M_n-zI\bigr)^*$ converge.
--   4. **Modes of convergence** for real random variables $Y_n$: $Y_n\to0$ *in probability* if $\mathbf P(|Y_n|\ge\varepsilon)\to0$ for every $\varepsilon>0$; $Y_n$ is *bounded in probability* if $\lim_{C\to\infty}\liminf_n\mathbf P(|Y_n|\le C)=1$; $Y_n$ is *almost surely bounded* if $\mathbf P(\limsup_n|Y_n|<\infty)=1$.
--   5. **Convergence of ESD differences.** For random matrices $A_n,B_n$, $\mu_{\frac1{\sqrt n}A_n}-\mu_{\frac1{\sqrt n}B_n}$ converges to zero *in probability* if for every test function $f$ the real random variable
--   $$\int_{\mathbb C}f\,d\mu_{\frac1{\sqrt n}A_n}-\int_{\mathbb C}f\,d\mu_{\frac1{\sqrt n}B_n}$$
--   tends to $0$ in probability; it converges to zero *almost surely* if, with probability one, this expression tends to $0$ for all test functions $f$ simultaneously.
--
--   These are the hypotheses and conclusions of the universality principle and of the replacement principle.
--
--   **Formalization Note.** The matrices $X_n$ for different $n$ are the corners of one infinite i.i.d. array on one probability space. The in-probability statements do not depend on this coupling; the almost-sure ones do, and the paper's proof of Lemma 1.7 (strong law of large numbers for $\frac1{n^2}\|X_n\|_2^2$) uses it. The limit in (1.4) is required to be a probability measure; under (1.3) the ESDs in (1.4) have uniformly bounded first moments, so any vague limit is a probability measure and nothing is lost. Bounded in probability is stated in the equivalent form "for every $\varepsilon>0$ there is $C$ with $\mathbf P(|Y_n|>C)\le\varepsilon$ for all large $n$". In the almost-sure ESD convergence a single null set serves all test functions.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, pp. 2023–2024 (PDF 1–2), Definition 1.1 and (1.1); p. 2027 (PDF 5), Theorem 1.5, (1.3), (1.4)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- A complex random variable with zero mean and unit variance: measurable, square integrable,
`E x = 0` and `E |x|² = 1` (Theorem 1.5, p. 2027). -/
structure IsStandardEntry {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x : Ω → ℂ) : Prop where
  measurable : Measurable x
  memLp : MemLp x 2 P
  mean_zero : ∫ ω, x ω ∂P = 0
  second_moment : ∫ ω, ‖x ω‖ ^ 2 ∂P = 1

/-- An infinite array `(x_ij)_{i,j ≥ 0}` of independent copies of a zero-mean, unit-variance
complex random variable (the law of `x_00`). The paper's `X_n = (x_ij)_{1≤i,j≤n}` is the top-left
`n × n` corner of this array (`cornerMatrix`). -/
structure IsIIDArray {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (xs : ℕ → ℕ → Ω → ℂ) :
    Prop where
  measurable : ∀ i j, Measurable (xs i j)
  indep : ProbabilityTheory.iIndepFun (fun p : ℕ × ℕ => xs p.1 p.2) P
  ident : ∀ i j, ProbabilityTheory.IdentDistrib (xs i j) (xs 0 0) P P
  standard : IsStandardEntry P (xs 0 0)

/-- The `n × n` random matrix `X_n = (x_ij)_{1 ≤ i, j ≤ n}` (zero-based indices `0 ≤ i, j < n`). -/
def cornerMatrix {Ω : Type*} (xs : ℕ → ℕ → Ω → ℂ) (n : ℕ) (ω : Ω) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => xs i j ω

/-- Hypothesis (1.3): `sup_n n⁻² ‖M_n‖₂² < ∞`, with the Hilbert–Schmidt norm. -/
def ShiftBound (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, hsNormSq (M n) ≤ C * (n : ℝ) ^ 2

/-- A sequence of `n × n` matrices whose ESDs converge vaguely to a probability measure on `ℂ`:
`∫ f dμ_{N_n} → ∫ f dν` for every continuous compactly supported `f : ℂ → ℝ`. -/
def ESDConverges (N : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ ν : Measure ℂ, IsProbabilityMeasure ν ∧
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ w, f w ∂esd (N n)) atTop (𝓝 (∫ w, f w ∂ν))

/-- The matrices `(M_n/√n - zI)(M_n/√n - zI)*` of hypothesis (1.4). -/
noncomputable def shiftedGram (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (invSqrt n • M n - z • (1 : Matrix (Fin n) (Fin n) ℂ)) *
    (invSqrt n • M n - z • (1 : Matrix (Fin n) (Fin n) ℂ)).conjTranspose

/-- Hypothesis (1.4): for Lebesgue-almost every `z ∈ ℂ` the ESDs of
`(M_n/√n - zI)(M_n/√n - zI)*` converge to a limit. -/
def Hyp14 (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ), ESDConverges (shiftedGram M z)

/-- `Y_n → 0` in probability: `P(|Y_n| ≥ ε) → 0` for every `ε > 0` (Definition 1.1). -/
def TendstoInProbZero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P {ω | ε ≤ |Y n ω|}) atTop (𝓝 0)

/-- `Y_n` is bounded in probability (p. 2024): `lim_{C→∞} liminf_n P(|Y_n| ≤ C) = 1`,
in the equivalent form `∀ ε > 0, ∃ C, P(|Y_n| > C) ≤ ε` for all large `n`. -/
def BoundedInProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n in atTop, P {ω | C < |Y n ω|} ≤ ENNReal.ofReal ε

/-- `Y_n` is almost surely bounded (p. 2024): `P(limsup_n |Y_n| < ∞) = 1`. -/
def ASBounded {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ᶠ n in atTop, |Y n ω| ≤ C

/-- `μ_{A_n/√n} - μ_{B_n/√n} → 0` in probability (p. 2024): for every test function `f`,
`∫ f dμ_{A_n/√n} - ∫ f dμ_{B_n/√n} → 0` in probability. -/
def ESDDiffTendstoInProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    TendstoInProbZero P fun n ω =>
      (∫ w, f w ∂esd (invSqrt n • A n ω)) - ∫ w, f w ∂esd (invSqrt n • B n ω)

/-- `μ_{A_n/√n} - μ_{B_n/√n} → 0` almost surely (p. 2024): with probability one, for every test
function `f`, `∫ f dμ_{A_n/√n} - ∫ f dμ_{B_n/√n} → 0` (one null set for all `f`). -/
def ESDDiffTendstoAS {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun n => (∫ w, f w ∂esd (invSqrt n • A n ω)) - ∫ w, f w ∂esd (invSqrt n • B n ω))
      atTop (𝓝 0)

end UnivESD.Universality


