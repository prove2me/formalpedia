-- Prove2me | Definitions.Def_MultiServerAppt_IsDPHSModel
-- name    : MultiServerAppt_IsDPHSModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:33.966141+00:00
-- url     : https://prove2.me/theorems/843e9794-d0f9-43fb-b557-22b34dd9476d
-- title:
--   The D/PH/s appointment system
-- statement:
--   The hypotheses of the paper's model. There are $s\ge 1$ identical servers, $n=s+m>s$ clients, and inter-arrival times $x_{s+l}\ge 0$. The service times $B_1,\dots,B_n$ are independent and each has the law $\mathrm{PH}(\alpha,S)$, where $\alpha$ is a probability vector on the phases and $S$ is a nonsingular phase-type generator.
--
--   **Formalization Note** The published `IsPHRep` allows an atom at $0$ and does not force absorption, so $\sum_a\alpha_a=1$ and the invertibility of $S$ are separate fields; neither restricts the paper, whose $\alpha$ holds initial probabilities and whose means are finite. $\mathbb P(B_c\le y)=F(y)$ is required for $y\ge 0$; since $F(0)=0$, $B_c>0$ a.s. follows. The normalization $\mathbb E B_i=1$ of p.9 is deliberately absent. Zero inter-arrival times are allowed, as on p.25.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §1, p.2, §3, p.8, §3.3, p.9, Eq. (6), p.10

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open MeasureTheory

namespace MultiServerAppt

/-- The D/PH/s appointment system: `s ≥ 1` identical servers, `n = s + m > s` clients, inter-arrival
times `x_{s+l} ≥ 0`, and i.i.d. service times `B_c ∼ PH(α, S)`, `c = 1, …, n`, with `α` a probability
vector on the phases and `S` nonsingular. Kuiper–Lee, Appointment Scheduling for Multiple Servers,
SSRN 3975471, §1, p.2, §3, p.8, §3.3, p.9, Eq. (6), p.10.

**Formalization Note** `MatrixAnalytic.PH.IsPHRep` allows an atom at `0` and does not force
absorption. So `sum_alpha` ("α a row vector describing initial probabilities", p.10) and `det_unit`
(p.14 uses `S⁻¹`, and `E B_i` is finite, p.9) are separate fields; neither restricts the paper. `B c`
has `P(B c ≤ y) = F(y)` for `y ≥ 0`, and `F(0) = 0`, so `B c > 0` a.s. follows and is not a field. The
normalization `E B_i = 1` of p.9 is deliberately absent. Zero inter-arrival times are allowed: p.25
has them ("overbooking"). -/
structure IsDPHSModel {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s m : ℕ) (α : ι → ℝ) (S : Matrix ι ι ℝ) (x : ℕ → ℝ) (B : ℕ → Ω → ℝ) :
    Prop where
  s_pos : 1 ≤ s
  m_pos : 1 ≤ m
  isPHRep : MatrixAnalytic.PH.IsPHRep α S
  sum_alpha : ∑ a, α a = 1
  det_unit : IsUnit S.det
  x_nonneg : ∀ l ∈ Finset.Icc 1 m, 0 ≤ x (s + l)
  measurable : ∀ c ∈ Finset.Icc 1 (s + m), Measurable (B c)
  indep : ProbabilityTheory.iIndepFun (fun c : Finset.Icc 1 (s + m) => B c) P
  law : ∀ c ∈ Finset.Icc 1 (s + m), ∀ y : ℝ, 0 ≤ y →
    P.real {ω | B c ω ≤ y} = MatrixAnalytic.PH.cdf α S y

end MultiServerAppt


