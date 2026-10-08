-- Prove2me | Definitions.Def_UnivESD_LogDet_Model
-- name    : UnivESD_LogDet_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:13.246923+00:00
-- url     : https://prove2.me/theorems/076cb72f-02c6-46ec-a2c2-50ef995749cd
-- title:
--   The model of Theorem 1.5: $A_n = M_n + X_n$ with an i.i.d. zero-mean unit-variance array, (1.3), and hypothesis (1.4)
-- statement:
--   Let $x$ be a complex random variable with $\mathbf E x=0$ and $\mathbf E|x|^2=1$, and let $(x_{ij})_{i,j\ge1}$ be an infinite array of independent copies of $x$ on a probability space $(\Omega,\mathbf P)$. For each $n$, $X_n=(x_{ij})_{1\le i,j\le n}$ is the top-left $n\times n$ corner of the array. Let $M_n$ be deterministic $n\times n$ complex matrices satisfying
--   $$\text{(1.3)}\qquad \sup_n \frac1{n^2}\|M_n\|_2^2<\infty,\qquad \|M\|_2^2=\sum_{i,j}|m_{ij}|^2 .$$
--   Put $A_n:=M_n+X_n$, and consider the normalized matrices $\frac1{\sqrt n}A_n$ and their shifts $\frac1{\sqrt n}A_n-zI$, $z\in\mathbb C$.
--
--   The additional hypothesis (1.4) is: for Lebesgue-almost every $z\in\mathbb C$, the ESDs of the deterministic matrices
--   $$\Big(\tfrac1{\sqrt n}M_n-zI\Big)\Big(\tfrac1{\sqrt n}M_n-zI\Big)^*$$
--   converge (vaguely) to a limit.
--
--   This is the setting "Let $A_n$ be as in Theorem 1.5" of Theorem 1.15 and of every step of its proof.
--
--   **Formalization Note** The entries are `xs i j` for `i j : ℕ`; they are measurable, mutually independent (indexed by $\mathbb N\times\mathbb N$), identically distributed with `xs 0 0`, square integrable, with $\mathbf E x=0$ and $\mathbf E|x|^2=1$. Reading "$X_n$ has i.i.d. entries" as the corner of one infinite array is a disclosed choice: in-probability statements do not depend on the coupling across $n$, but almost-sure ones do, and the paper's proof uses the strong law of large numbers on the array. (1.3) is written as $\exists C\,\forall n,\ \sum_{i,j}|m_{ij}|^2\le Cn^2$. In (1.4) the limit is required to be a probability measure; under (1.3) the ESDs have bounded first moment, so a vague limit is automatically a probability measure, and the requirement is equivalent.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2027 (PDF 5), Theorem 1.5 (model, (1.3), (1.4)) and the Hilbert–Schmidt norm

import Mathlib
import Definitions.Def_UnivESD_LogDet_Basic

namespace UnivESD.LogDet

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

variable {Ω : Type*}

/-- The i.i.d. entry array of Theorem 1.5 (Tao–Vu, Ann. Probab. 38 (2010), p. 2027): the entries
`xs i j : Ω → ℂ` (`i, j ∈ ℕ`) form one infinite array of independent copies of a complex random
variable `x = xs 0 0` with zero mean and unit variance, `E x = 0`, `E|x|² = 1`, on a probability
space `(Ω, P)`. The matrix `X_n` is the top-left `n × n` corner of the array. -/
structure IIDArray [MeasurableSpace Ω] (P : Measure Ω) (xs : ℕ → ℕ → Ω → ℂ) :
    Prop where
  measurable : ∀ i j, Measurable (xs i j)
  indep : iIndepFun (fun p : ℕ × ℕ => xs p.1 p.2) P
  identDistrib : ∀ i j, IdentDistrib (xs i j) (xs 0 0) P P
  memLp_two : MemLp (xs 0 0) 2 P
  mean_zero : ∫ ω, xs 0 0 ω ∂P = 0
  second_moment_one : ∫ ω, ‖xs 0 0 ω‖ ^ 2 ∂P = 1

/-- Condition (1.3), p. 2027: `sup_n n^{-2} ‖M_n‖₂² < ∞` for the deterministic matrices `M_n`,
with the Hilbert–Schmidt norm `‖M‖₂² = Σ_{i,j} |m_ij|²` written out. -/
def HSBound (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∑ i, ∑ j, ‖M n i j‖ ^ 2 ≤ C * (n : ℝ) ^ 2

/-- The normalization factor `1/√n`, as a complex scalar. -/
noncomputable def invSqrtN (n : ℕ) : ℂ := ((Real.sqrt n : ℝ) : ℂ)⁻¹

/-- The random matrix `X_n = (x_ij)_{1 ≤ i,j ≤ n}`: the top-left `n × n` corner of the array. -/
def Xmat (xs : ℕ → ℕ → Ω → ℂ) (n : ℕ) (ω : Ω) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => xs i j ω

/-- `A_n := M_n + X_n` (Theorem 1.5, p. 2027). -/
def Amat (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (xs : ℕ → ℕ → Ω → ℂ) (n : ℕ) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℂ :=
  M n + Xmat xs n ω

/-- The normalized matrix `(1/√n) A_n`. -/
noncomputable def normA (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (xs : ℕ → ℕ → Ω → ℂ)
    (n : ℕ) (ω : Ω) : Matrix (Fin n) (Fin n) ℂ :=
  invSqrtN n • Amat M xs n ω

/-- The shifted normalized matrix `(1/√n) A_n − zI`. -/
noncomputable def shiftA (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (xs : ℕ → ℕ → Ω → ℂ)
    (z : ℂ) (n : ℕ) (ω : Ω) : Matrix (Fin n) (Fin n) ℂ :=
  normA M xs n ω - z • (1 : Matrix (Fin n) (Fin n) ℂ)

/-- Hypothesis (1.4), p. 2027: for Lebesgue-almost every `z ∈ ℂ`, the ESDs of the deterministic
matrices `(M_n/√n − zI)(M_n/√n − zI)*` converge (vaguely) to a limit, here a probability
measure `ν` on `ℂ`. -/
def Cond14 (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ), ∃ ν : Measure ℂ, IsProbabilityMeasure ν ∧
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ w, f w ∂(UnivESD.Universality.esd ((invSqrtN n • M n - z • (1 : Matrix (Fin n) (Fin n) ℂ)) *
        (invSqrtN n • M n - z • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ))) atTop (𝓝 (∫ w, f w ∂ν))

end UnivESD.LogDet


