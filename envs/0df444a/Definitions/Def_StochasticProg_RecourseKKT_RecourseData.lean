-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_RecourseData
-- name    : StochasticProg_RecourseKKT_RecourseData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:43:05.487489+00:00
-- url     : https://prove2.me/theorems/22cda2f4-7485-40c4-9c30-a3f35fa94ec1
-- title:
--   Data of a two-stage stochastic linear program with fixed recourse
-- statement:
--   A **two-stage stochastic linear program with fixed recourse** (model (1.1)) is given by
--
--   1. a first-stage cost vector $c \in \mathbb R^{n_1}$, a first-stage constraint matrix $A \in \mathbb R^{m_1 \times n_1}$ and right-hand side $b \in \mathbb R^{m_1}$;
--   2. a **fixed recourse matrix** $W \in \mathbb R^{m_2 \times n_2}$, the same for every outcome;
--   3. a random vector $\xi(\omega) = (q(\omega), h(\omega), T(\omega))$ on a measurable space $(\Omega, \mathcal F)$, made of a second-stage cost $q(\omega) \in \mathbb R^{n_2}$, a right-hand side $h(\omega) \in \mathbb R^{m_2}$ and a technology matrix $T(\omega) \in \mathbb R^{m_2 \times n_1}$.
--
--   The decision maker chooses $x$ with $Ax = b$, $x \ge 0$, observes $\xi(\omega)$, and then chooses $y(\omega) \ge 0$ with $Wy(\omega) = h(\omega) - T(\omega)x$ at cost $q(\omega)^{\mathsf T} y(\omega)$.
--
--   This structure carries the data on which every other object of the mission (the value functions $Q$ and $\mathcal Q$, the sets $K_1$ and $K_2$) is built.
--
--   **Formalization Note** Indices are $0$-based (`Fin n`). "Random vector" means that every coordinate of $q$, $h$ and $T$ is a measurable function of $\omega$. No sign, rank or boundedness condition is imposed.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1a, model (1.1)–(1.4), printed pp. 103–104 (PDF pp. 128–129)

import Mathlib
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **Two-stage stochastic linear program with fixed recourse — the data of (1.1).**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1a, model (1.1)–(1.4), printed pp. 103–104 (PDF pp. 128–129):
"c is a known vector in ℜ^{n1}, b a known vector in ℜ^{m1}, A and W are known matrices of size
m1 × n1 and m2 × n2, respectively, and W is called the recourse matrix, which we assume here is
fixed. For each ω, T(ω) is m2 × n1, q(ω) ∈ ℜ^{n2} and h(ω) ∈ ℜ^{m2}."

The first-stage data `c, A, b` and the recourse matrix `W` are deterministic; the second-stage
data `ξ(ω) = (q(ω), h(ω), T(ω))` is a random vector on the measurable space `Ω`.

**Formalization Note.** Indices are `Fin n` (0-based). "Random vector" is encoded by the
measurability of every coordinate of `q`, `h` and `T`. No sign, rank or boundedness condition is
imposed on any of the data. -/
structure RecourseData (Ω : Type*) [MeasurableSpace Ω] (n1 m1 n2 m2 : ℕ) where
  /-- First-stage cost vector `c ∈ ℜ^{n1}`. -/
  c : Fin n1 → ℝ
  /-- First-stage constraint matrix `A` (size `m1 × n1`). -/
  A : Matrix (Fin m1) (Fin n1) ℝ
  /-- First-stage right-hand side `b ∈ ℜ^{m1}`. -/
  b : Fin m1 → ℝ
  /-- The fixed recourse matrix `W` (size `m2 × n2`). -/
  W : Matrix (Fin m2) (Fin n2) ℝ
  /-- Random second-stage cost `q(ω) ∈ ℜ^{n2}`. -/
  q : Ω → Fin n2 → ℝ
  /-- Random second-stage right-hand side `h(ω) ∈ ℜ^{m2}`. -/
  h : Ω → Fin m2 → ℝ
  /-- Random technology matrix `T(ω)` (size `m2 × n1`). -/
  T : Ω → Matrix (Fin m2) (Fin n1) ℝ
  measurable_q : ∀ j, Measurable fun ω => q ω j
  measurable_h : ∀ i, Measurable fun ω => h ω i
  measurable_T : ∀ i j, Measurable fun ω => T ω i j

end StochasticProg.RecourseKKT


