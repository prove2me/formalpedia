-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qMinus
-- name    : BauerleRiederMDP_TransactionCosts_Market_qMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:54.674363+00:00
-- url     : https://prove2.me/theorems/bcb75f3d-cf6b-4f5c-98f6-32b86217e4ae
-- title:
--   Lower threshold $q_-(v)\in[0,\infty]$, (4.31)
-- statement:
--   The book defines
--   $$q_-(v):=\operatorname{argmax}_{q\ge0}\ \mathbb E\,v\Big(\frac{1+i_{n+1}}{1+q(1+c)},\ \frac{q\tilde R_{n+1}}{1+q(1+c)}\Big)\tag{4.31}$$
--   which the substitution $q=\frac{a}{1-(1+c)a}$ turns into the buying problem at $(1,0)$ on $0\le a\le\frac1{1+c}$. Following (4.29), the threshold is
--   $$q_-:=\begin{cases}\dfrac{a_-}{1-(1+c)a_-}, & a_-<\frac1{1+c},\\ \infty, & a_-=\frac1{1+c},\end{cases}$$
--   with $a_-$ the largest maximum point of that problem. It is the optimal stock-to-bond ratio after buying.
--
--   **Formalization Note** As for $q_+$, the book's definition (4.29) replaces the literal argmax, which need not be attained or unique. Values in $[0,\infty]$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.31), p.112 (PDF 126); eq. (4.29), p.111 (PDF 125); proof of Theorem 4.5.4, p.113 (PDF 127)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_aMinus

open scoped ENNReal

namespace BauerleRiederMDP.TransactionCosts

/-- The lower threshold `q₋(v) ∈ [0, ∞]` of (4.31) (Bäuerle & Rieder 2011, p.112, PDF 126),
`q₋(v) := argmax_{q ≥ 0} IE v((1 + i_{n+1})/(1 + q(1 + c)), q R̃_{n+1}/(1 + q(1 + c)))`,
read through the analogous transformation `q = a/(1 − (1 + c)a)` (proof of Theorem 4.5.4, p.113,
PDF 127: "An analogous statement holds for q₋") and the definition (4.29) (p.111, PDF 125):
`q₋ := a₋/(1 − (1 + c)a₋)` if `a₋ < 1/(1 + c)` and `q₋ := ∞` if `a₋ = 1/(1 + c)`, where `a₋`
is the largest maximum point of the equivalent problem on `0 ≤ a ≤ 1/(1 + c)` (`Market.aMinus`).

**Formalization Note.** As for `qPlus`, the book's definition (4.29) is used in place of the
literal `argmax_{q ≥ 0}`, which need not be attained or unique. -/
noncomputable def Market.qMinus {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (v : ℝ × ℝ → EReal) : ℝ≥0∞ :=
  if M.aMinus n v < 1 / (1 + M.c) then
    ENNReal.ofReal (M.aMinus n v / (1 - (1 + M.c) * M.aMinus n v))
  else ⊤

end BauerleRiederMDP.TransactionCosts


