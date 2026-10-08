-- Prove2me | Definitions.Def_StochasticProg_Recourse_SimpleRecourseExpected
-- name    : StochasticProg_Recourse_SimpleRecourseExpected
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:18:50.321677+00:00
-- url     : https://prove2.me/theorems/caf2c0bf-d134-4d68-b19e-8bd10b82048d
-- title:
--   The expected simple-recourse function $\mathcal Q(x)=\sum_i \mathcal Q_i(T_{i\cdot}x)$ of Eq. (1.9) and the one-sided distribution functions $F_i^\pm$ of the right-hand side
-- statement:
--   For a simple recourse instance ($W=[I,-I]$, deterministic $T$, $q^+$, $q^-$) and a law $P$ of the random right-hand side $h\in\mathbb R^{m_2}$, this module defines the objects Corollary 10 is about: the one-sided distribution functions $F_i^-(t)=P(h_i<t)$ and $F_i^+(t)=P(h_i\le t)$ of $h_i$ (p. 114), the expected recourse term $\mathcal Q_i(\chi)=\mathbb E\big[q_i^+(h_i-\chi)^++q_i^-(\chi-h_i)^+\big]$ (the expected optimal value of the second-stage problem $\min q_i^+y_i^++q_i^-y_i^-$ s.t. $y_i^+-y_i^-=h_i-\chi$, $y\ge0$), and the expected recourse function $\mathcal Q(x)=\sum_i\mathcal Q_i(T_{i\cdot}x)$ of Eq. (1.9).
--
--   **Formalization Note.** `cdfLeft`/`cdfRight` are `toReal` of the measure of the half-lines; for a probability law they lie in $[0,1]$ and `cdfLeft ≤ cdfRight`. `Qi` is a Bochner integral; it is the book's value under the standing assumptions of the simple recourse model, $q_i^++q_i^-\ge0$ and finite first moments of $h$, which every theorem using it states explicitly. The module imports and extends `Def_StochasticProg_Recourse_SimpleRecourse`; it replaces nothing.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, Chapter 3, Section 1 (simple recourse), pp. 113–114, Eqs. (1.9)–(1.10)

import Mathlib
import Definitions.Def_StochasticProg_Recourse_SimpleRecourse

open MeasureTheory

namespace StochasticProg.Recourse

variable {n1 m1 m2 : ℕ}

/-- `F⁻_i(t) = P(h_i < t)`, the left-hand limit at `t` of the distribution function of the
`i`-th right-hand side `h_i`, for the law `P` of the random vector `h` (Birge & Louveaux,
*Introduction to Stochastic Programming*, 2nd ed., p. 114). -/
noncomputable def cdfLeft (P : Measure (Fin m2 → ℝ)) (i : Fin m2) (t : ℝ) : ℝ :=
  (P {h | h i < t}).toReal

/-- `F⁺_i(t) = P(h_i ≤ t) = F_i(t)`, the (right-continuous) distribution function of `h_i`,
i.e. its right-hand limit at `t` (p. 114). -/
noncomputable def cdfRight (P : Measure (Fin m2 → ℝ)) (i : Fin m2) (t : ℝ) : ℝ :=
  (P {h | h i ≤ t}).toReal

/-- The `i`-th expected simple-recourse term as a function of the tender `χ_i = T_i x`:
`Q_i(χ_i) = E[q⁺_i (h_i − χ_i)⁺ + q⁻_i (χ_i − h_i)⁺]`, the expected optimal value of the
second-stage problem `min q⁺_i y⁺_i + q⁻_i y⁻_i  s.t.  y⁺_i − y⁻_i = h_i − χ_i, y ≥ 0` of the
simple recourse model `W = [I, −I]` (pp. 113–114, Eq. (1.9)). It is the Bochner integral with
respect to the law `P` of `h`; it is the book's value whenever `h_i` has a finite first moment
and `q⁺_i + q⁻_i ≥ 0` (the standing assumptions of the simple recourse model). -/
noncomputable def SimpleRecourseInstance.Qi (inst : SimpleRecourseInstance n1 m1 m2)
    (P : Measure (Fin m2 → ℝ)) (i : Fin m2) (χ : ℝ) : ℝ :=
  ∫ h, (inst.qplus i * max (h i - χ) 0 + inst.qminus i * max (χ - h i) 0) ∂P

/-- The expected simple-recourse function `Q(x) = ∑_i Q_i(T_i x)` (p. 114, Eq. (1.9)), with
deterministic technology matrix `T` and recourse costs `q⁺, q⁻`; only `h` is random. -/
noncomputable def SimpleRecourseInstance.Q (inst : SimpleRecourseInstance n1 m1 m2)
    (P : Measure (Fin m2 → ℝ)) (x : Fin n1 → ℝ) : ℝ :=
  ∑ i, inst.Qi P i (Matrix.mulVec inst.T x i)

end StochasticProg.Recourse


