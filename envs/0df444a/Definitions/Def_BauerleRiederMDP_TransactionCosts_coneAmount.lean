-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_coneAmount
-- name    : BauerleRiederMDP_TransactionCosts_coneAmount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:01.518006+00:00
-- url     : https://prove2.me/theorems/402697e9-bc22-4daa-8259-21666117058b
-- title:
--   Three-region stock amount (4.32) for thresholds $q_\pm$
-- statement:
--   For thresholds $0\le q_-\le q_+\le\infty$ and a state $x\in E$,
--   $$f(x)=\begin{cases}\dfrac{x_0+(1-c)x_1}{1+(1-c)q_+}\,q_+, & \frac{x_1}{x_0}>q_+\quad\text{(sell)},\\[4pt] x_1, & q_-\le\frac{x_1}{x_0}\le q_+\quad\text{(no transaction)},\\[4pt] \dfrac{x_0+(1+c)x_1}{1+(1+c)q_-}\,q_-, & \frac{x_1}{x_0}<q_-\quad\text{(buy)}.\end{cases}$$
--
--   **Formalization Note** In the sell case $q_+$ is finite. In the buy case with $q_-=\infty$ the printed fraction is $\infty/\infty$; its value is read as its limit $\frac{x_0+(1+c)x_1}{1+c}$, which is the proof's $(x_0+(1+c)x_1)a_-$ with $a_-=\frac1{1+c}$ (all wealth into the stock). The cases are tested in the printed order.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.5.4 b), eq. (4.32), p.113 (PDF 127)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_ratio

open scoped ENNReal

namespace BauerleRiederMDP.TransactionCosts

/-- The three-region stock amount (4.32) of Bäuerle & Rieder (2011), Theorem 4.5.4 b), p.113
(PDF 127), for thresholds `q₊, q₋ ∈ [0, ∞]` and transaction cost rate `c`:
`(x₀ + (1 − c)x₁)/(1 + (1 − c)q₊) · q₊` if `x₁/x₀ > q₊` (sell),
`x₁` if `q₋ ≤ x₁/x₀ ≤ q₊` (no transaction),
`(x₀ + (1 + c)x₁)/(1 + (1 + c)q₋) · q₋` if `x₁/x₀ < q₋` (buy).

**Formalization Note.** `x₁/x₀` is `ratio x ∈ [0, ∞]`. In the sell case `q₊ < x₁/x₀ ≤ ∞`, so
`q₊` is finite and the printed formula is used with `q₊.toReal`. In the buy case `q₋` may be
`∞` (then every `x` with `x₀ > 0` is in the buy region); the printed fraction is then `∞/∞`,
and its value is read as its limit `(x₀ + (1 + c)x₁)/(1 + c)`, which is the proof's
`(x₀ + (1 + c)x₁) a₋` with `a₋ = 1/(1 + c)` (step (v), p.111). The cases are tested in the
printed order (sell, no transaction, buy); for `q₋ ≤ q₊` they are disjoint and cover `[0, ∞]`. -/
noncomputable def coneAmount (c : ℝ) (qp qm : ℝ≥0∞) (x : ℝ × ℝ) : ℝ :=
  if qp < ratio x then
    (x.1 + (1 - c) * x.2) / (1 + (1 - c) * qp.toReal) * qp.toReal
  else if qm ≤ ratio x then
    x.2
  else if qm = ⊤ then
    (x.1 + (1 + c) * x.2) / (1 + c)
  else
    (x.1 + (1 + c) * x.2) / (1 + (1 + c) * qm.toReal) * qm.toReal

end BauerleRiederMDP.TransactionCosts


