-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_secondStageValue
-- name    : StochasticProg_RecourseKKT_secondStageValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:43:25.950064+00:00
-- url     : https://prove2.me/theorems/313462d9-905b-41ad-9122-f3bf00cd5bc8
-- title:
--   Second-stage value $Q(x,\xi)$ of a linear recourse program
-- statement:
--   For a recourse matrix $W \in \mathbb R^{m_2 \times n_2}$, a realization $(q, h, T)$ of the second-stage data and a first-stage decision $x \in \mathbb R^{n_1}$, the **second-stage value** is
--
--   $$
--   Q(x, \xi) = \min_y \{\, q^{\mathsf T} y \;\mid\; W y = h - T x,\ y \ge 0 \,\} \in [-\infty, +\infty],
--   $$
--
--   with the book's convention: $Q(x,\xi) = +\infty$ if the linear program is infeasible and $Q(x,\xi) = -\infty$ if it is unbounded below.
--
--   This is the recourse cost of (1.4)/(1.6), the integrand of the expected recourse function $\mathcal Q$.
--
--   **Formalization Note** The value is the infimum, in the extended reals `EReal`, of $\{q^{\mathsf T}y\}$ over the feasible $y$. The infimum of the empty set is $+\infty$ and an unbounded-below program gives $-\infty$, exactly the stated convention; a feasible bounded linear program attains its infimum.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, eq. (1.6), printed p. 106 (PDF p. 131), and §3.1c, printed p. 109 (PDF p. 134)

import Mathlib
open Matrix

namespace StochasticProg.RecourseKKT

/-- **The second-stage value `Q(x, ξ)` — (1.4)/(1.6), with the p. 109 convention.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, eq. (1.6), printed p. 106 (PDF p. 131), and §3.1c, printed p. 109 (PDF p. 134):
"Q(x, ξ) = min_y {q(ω)ᵀy | W(ω)y = h(ω) − T(ω)x, y ≥ 0}". "When the mathematical program (1.6) is
unbounded below or infeasible, the value of the second-stage program is defined to be −∞ or +∞,
respectively."

For a cost vector `q`, a recourse matrix `W`, a right-hand side `h`, a technology matrix `T` and
a first-stage decision `x`, this is the infimum of `qᵀy` over `{y ≥ 0 | W y = h − T x}`, taken
in the extended reals.

**Formalization Note.** The value lies in `EReal`. The infimum of the empty set is `⊤` (an
infeasible program has value `+∞`), and an unbounded-below program has value `⊥` (`−∞`), exactly the
book's convention; when the program is feasible and bounded the infimum is the (attained) LP
minimum. The arguments are deterministic, so the same function serves for every realization
`ξ(ω) = (q(ω), h(ω), T(ω))`. -/
noncomputable def secondStageValue {n1 m2 n2 : ℕ} (W : Matrix (Fin m2) (Fin n2) ℝ)
    (q : Fin n2 → ℝ) (h : Fin m2 → ℝ) (T : Matrix (Fin m2) (Fin n1) ℝ) (x : Fin n1 → ℝ) :
    EReal :=
  sInf ((fun y : Fin n2 → ℝ => ((q ⬝ᵥ y : ℝ) : EReal)) '' {y | 0 ≤ y ∧ W *ᵥ y = h - T *ᵥ x})

end StochasticProg.RecourseKKT


