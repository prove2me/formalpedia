-- Prove2me | Definitions.Def_HamburgerMoment_Defs
-- name    : HamburgerMoment_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T23:55:37.358304+00:00
-- url     : https://prove2.me/theorems/2f0edbfa-01f4-43b2-8780-4cec30aa8f9c
-- title:
--   Hamburger moment problem: moment measures, moment sequences, Hankel kernel and Hankel matrices
-- statement:
--   This file fixes the vocabulary of the Hamburger moment problem.
--
--   Let $m=(m_n)_{n\ge0}$ be a sequence of real numbers.
--
--   1. **Solution (`IsMomentMeasure m μ`).** A positive Borel measure $\mu$ on $\mathbb R$ solves the moment problem for $m$ if, for every $n\ge 0$, the function $x\mapsto x^n$ is $\mu$-integrable and
--   $$m_n=\int_{-\infty}^{\infty}x^n\,d\mu(x).$$
--   2. **Moment sequence (`IsMomentSequence m`).** $m$ is a moment sequence if it has at least one solution $\mu$.
--   3. **Hankel form (`hankelForm m c`).** For a finitary complex sequence $c=(c_j)_{j\ge0}$ (only finitely many $c_j\ne0$),
--   $$\sum_{j,k\ge0} m_{j+k}\,c_j\,\overline{c_k}\in\mathbb C.$$
--   4. **Positive definite Hankel kernel (`HankelPosDef m`).** The kernel $A=(m_{j+k})_{j,k\ge0}$ is positive definite if the Hankel form is $\ge 0$ for every finitary complex sequence $c$.
--   5. **Hankel matrices (`hankelMatrix m n`).** $\Delta_n=(m_{i+j})_{0\le i,j\le n}$, the real $(n+1)\times(n+1)$ matrix.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** Finitary sequences are finitely supported functions `ℕ →₀ ℂ` and the Hankel form sums over their support. "$\ge0$" for the complex-valued Hankel form is the standard partial order on $\mathbb C$, so it asserts that the value is a nonnegative real number. Integrability of $x^0=1$ forces a solution to be a finite measure.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, lead section and sections "Characterization" and "Uniqueness of solutions" (matrix $\Delta_n$)

import Mathlib

/-!
# Hamburger moment problem — definitions

Source: Wikipedia, "Hamburger moment problem" (revision oldid=1356180072),
sections "Hamburger moment problem" (lead), "Characterization" and
"Uniqueness of solutions".
-/

namespace HamburgerMoment

open MeasureTheory

/-- `μ` is a solution of the Hamburger moment problem for `m`: `μ` is a positive Borel
measure on `ℝ` all of whose power moments exist (are finite) and satisfy
`m n = ∫_{-∞}^{∞} x ^ n dμ(x)` for every `n ≥ 0`. -/
def IsMomentMeasure (m : ℕ → ℝ) (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ ∧ ∫ x, x ^ n ∂μ = m n

/-- The Hamburger moment problem for `m` is solvable: `m` is the moment sequence of some
positive Borel measure on the real line. -/
def IsMomentSequence (m : ℕ → ℝ) : Prop :=
  ∃ μ : Measure ℝ, IsMomentMeasure m μ

/-- The quadratic form `∑_{j,k ≥ 0} m_{j+k} c_j \overline{c_k}` of the Hankel kernel
`A = (m_{j+k})_{j,k ≥ 0}`, evaluated at a finitary complex sequence `c`
(a finitely supported function `ℕ →₀ ℂ`). -/
noncomputable def hankelForm (m : ℕ → ℝ) (c : ℕ →₀ ℂ) : ℂ :=
  ∑ j ∈ c.support, ∑ k ∈ c.support, (m (j + k) : ℂ) * c j * starRingEnd ℂ (c k)

open scoped ComplexOrder in
/-- The Hankel kernel `A = (m_{j+k})_{j,k ≥ 0}` is positive definite in the sense of the
source: `∑_{j,k ≥ 0} m_{j+k} c_j \overline{c_k} ≥ 0` for every finitary complex sequence
`(c_j)_{j ≥ 0}`. Here `≥ 0` is the order on `ℂ`, i.e. the sum is a nonnegative real. -/
def HankelPosDef (m : ℕ → ℝ) : Prop :=
  ∀ c : ℕ →₀ ℂ, 0 ≤ hankelForm m c

/-- The `(n + 1) × (n + 1)` Hankel matrix `Δ_n = (m_{i+j})_{0 ≤ i, j ≤ n}`. -/
def hankelMatrix (m : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => m (i.val + j.val)

end HamburgerMoment


