-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qPlus
-- name    : BauerleRiederMDP_TransactionCosts_Market_qPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:06.810542+00:00
-- url     : https://prove2.me/theorems/8c4279de-a2e6-4bda-9927-b1b5ef1a1555
-- title:
--   Upper threshold $q_+(v)\in[0,\infty]$, (4.30)
-- statement:
--   The book defines
--   $$q_+(v):=\operatorname{argmax}_{q\ge0}\ \mathbb E\,v\Big(\frac{1+i_{n+1}}{1+q(1-c)},\ \frac{q\tilde R_{n+1}}{1+q(1-c)}\Big)\tag{4.30}$$
--   and shows (proof of Theorem 4.5.4) that the substitution $q=\frac{a}{(1-c)(1-a)}$ turns this problem into the selling problem at $(0,1)$ on $0\le a\le1$. Following (4.28), the threshold is
--   $$q_+:=\begin{cases}\dfrac{a_+}{(1-c)(1-a_+)}, & a_+<1,\\ \infty, & a_+=1,\end{cases}$$
--   with $a_+$ the largest maximum point of that problem. It is the optimal stock-to-bond ratio after selling.
--
--   **Formalization Note** The literal $\operatorname{argmax}_{q\ge0}$ is not attained when $a_+=1$ and need not be a single point, so the book's own definition (4.28) is used. Values in $[0,\infty]$ (`ℝ≥0∞`).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.30), p.112 (PDF 126); eq. (4.28), p.110 (PDF 124); proof of Theorem 4.5.4, p.113 (PDF 127)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_aPlus

open scoped ENNReal

namespace BauerleRiederMDP.TransactionCosts

/-- The upper threshold `q₊(v) ∈ [0, ∞]` of (4.30) (Bäuerle & Rieder 2011, p.112, PDF 126),
`q₊(v) := argmax_{q ≥ 0} IE v((1 + i_{n+1})/(1 + q(1 − c)), q R̃_{n+1}/(1 + q(1 − c)))`,
read through the transformation `q = a/((1 − c)(1 − a))` of the proof of Theorem 4.5.4
(p.113, PDF 127) and the definition (4.28) (p.110, PDF 124):
`q₊ := a₊/((1 − c)(1 − a₊))` if `a₊ < 1` and `q₊ := ∞` if `a₊ = 1`, where `a₊` is the largest
maximum point of the equivalent problem on `0 ≤ a ≤ 1` (`Market.aPlus`).

**Formalization Note.** (4.30) writes `argmax_{q ≥ 0}`, which is not attained when `a₊ = 1`
and need not be a single point; the book's own definition (4.28) of the threshold is used. -/
noncomputable def Market.qPlus {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (v : ℝ × ℝ → EReal) : ℝ≥0∞ :=
  if M.aPlus n v < 1 then
    ENNReal.ofReal (M.aPlus n v / ((1 - M.c) * (1 - M.aPlus n v)))
  else ⊤

end BauerleRiederMDP.TransactionCosts


