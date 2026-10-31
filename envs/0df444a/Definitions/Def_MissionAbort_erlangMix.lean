-- Prove2me | Definitions.Def_MissionAbort_erlangMix
-- name    : MissionAbort_erlangMix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:55.799369+00:00
-- url     : https://prove2.me/theorems/3c4ffabb-9fdb-4470-ac89-eebf03e93661
-- title:
--   Erlang mixture of (2) and (3)
-- statement:
--   For a law $F$ on the line, a shape $m\in\mathbb N_+$ and a rate $r>0$, the measure with distribution function
--   $$
--   t\mapsto\sum_{i=1}^{m-1}\Big[F\big(\tfrac ir\big)-F\big(\tfrac{i-1}r\big)\Big]E_i^{(r)}(t)+\Big[1-F\big(\tfrac{m-1}r\big)\Big]E_m^{(r)}(t),
--   $$
--   where $E_i^{(r)}$ is the Erlang distribution function of rate $r$ and shape $i$. Display (2) of the paper is $F^{(\lambda)}$, the case $(F,m_2,\lambda)$. Display (3) is $G^{(\lambda)}$, the case $(G,m_1,\lambda-\zeta)$: both the grid and the Erlang rate of (3) are $\lambda-\zeta$.
--
--   **Formalization Note** The Erlang law is `gammaMeasure` with integer shape.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, (2), (3), p.12

import Mathlib

namespace MissionAbort

open MeasureTheory ProbabilityTheory

/-- The Erlang mixture of (2) and (3) (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.12): the law with
CDF `t ↦ ∑_{i=1}^{m-1} [F(i/r) − F((i−1)/r)] E_i^{(r)}(t) + [1 − F((m−1)/r)] E_m^{(r)}(t)`, where
`E_i^{(r)}` is the Erlang CDF with rate `r` and shape `i`. Display (2) is `erlangMix F m₂ λ`, and
display (3) is `erlangMix G m₁ (λ − ζ)`: both the grid and the Erlang rate of (3) are `λ − ζ`.

**Formalization Note.** `gammaMeasure i r` with integer shape `i ≥ 1` is the Erlang law of rate `r`.
`F (Iic t)` is the CDF. `m - 1` is natural subtraction; the page has `m ∈ ℕ₊`. -/
noncomputable def erlangMix (F : Measure ℝ) (m : ℕ) (r : ℝ) : Measure ℝ :=
  (∑ i ∈ Finset.Icc 1 (m - 1),
      ENNReal.ofReal (F.real (Set.Iic ((i : ℝ) / r)) - F.real (Set.Iic (((i : ℝ) - 1) / r))) •
        gammaMeasure (i : ℝ) r) +
    ENNReal.ofReal (1 - F.real (Set.Iic (((m : ℝ) - 1) / r))) • gammaMeasure (m : ℝ) r

end MissionAbort


