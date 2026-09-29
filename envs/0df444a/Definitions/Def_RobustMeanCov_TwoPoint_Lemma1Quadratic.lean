-- Prove2me | Definitions.Def_RobustMeanCov_TwoPoint_Lemma1Quadratic
-- name    : RobustMeanCov_TwoPoint_Lemma1Quadratic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:48:31.709985+00:00
-- url     : https://prove2.me/theorems/18ed8e8d-63b3-481c-a42f-94327663dd8d
-- title:
--   The quadratic $q(y)=Ay^2+By+C$ of Lemma 1(c) (Popescu 2007)
-- statement:
--   Given $u:\mathbb R\to\mathbb R$, points $a,b$ and slopes $q_a,q_b$, Lemma 1(c) of Popescu (2007) builds the quadratic $q(y)=Ay^2+By+C$ with
--   $$
--   A=\frac{q_b-q_a}{2(b-a)},\qquad B=\frac{bq_a-aq_b}{b-a},\qquad C=\frac{bu(a)-au(b)}{b-a}-ab\,\frac{q_a-q_b}{2(b-a)} .
--   $$
--   It is the quadratic with slope $q_a$ at $a$ and slope $q_b$ at $b$ that, whenever the chord slope of $u$ over $[a,b]$ equals $(q_a+q_b)/2$, passes through $(a,u(a))$ and $(b,u(b))$.
--
--   This quadratic is the candidate supporting quadratic in the paper's characterization of two-point support.
--
--   **Formalization Note** The coefficients are separate definitions `lemma1A`, `lemma1B`, `lemma1C` and the quadratic is `lemma1Quad u a b q_a q_b`. Every statement using them assumes $a<b$, so the division by $b-a$ is never by zero.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 102, Lemma 1(c)

import Mathlib

namespace RobustMeanCov.TwoPoint

/-- The coefficient `A = (q_b - q_a) / (2 (b - a))` of Lemma 1(c) (Popescu 2007, p. 102). -/
noncomputable def lemma1A (a b qa qb : ℝ) : ℝ :=
  (qb - qa) / (2 * (b - a))

/-- The coefficient `B = (b q_a - a q_b) / (b - a)` of Lemma 1(c). -/
noncomputable def lemma1B (a b qa qb : ℝ) : ℝ :=
  (b * qa - a * qb) / (b - a)

/-- The coefficient `C = (b u(a) - a u(b)) / (b - a) - a b (q_a - q_b) / (2 (b - a))`
of Lemma 1(c). -/
noncomputable def lemma1C (u : ℝ → ℝ) (a b qa qb : ℝ) : ℝ :=
  (b * u a - a * u b) / (b - a) - a * b * ((qa - qb) / (2 * (b - a)))

/-- The quadratic `q(y) = A y² + B y + C` of Lemma 1(c). -/
noncomputable def lemma1Quad (u : ℝ → ℝ) (a b qa qb : ℝ) (y : ℝ) : ℝ :=
  lemma1A a b qa qb * y ^ 2 + lemma1B a b qa qb * y + lemma1C u a b qa qb

end RobustMeanCov.TwoPoint


