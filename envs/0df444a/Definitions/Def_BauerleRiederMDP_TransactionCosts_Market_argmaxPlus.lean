-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_argmaxPlus
-- name    : BauerleRiederMDP_TransactionCosts_Market_argmaxPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:03.676669+00:00
-- url     : https://prove2.me/theorems/f54d4bcf-778b-44d7-a2b8-ba8c245a82dc
-- title:
--   Maximum points of the selling problem at $(0,1)$
-- statement:
--   For $v:E\to[-\infty,\infty)$ and time $n$, the set of maximum points on $[0,1]$ of
--   $$a\mapsto \mathbb E\,v\big((1-c)(1-a)(1+i_{n+1}),\ a\tilde R_{n+1}\big),$$
--   the one-stage problem in the state $x=(0,1)$ (one unit in the stock, nothing in the bond) of the proof of Proposition 4.5.2, step (ii), and of the proof of Theorem 4.5.4.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), proof of Proposition 4.5.2, step (ii), p.109 (PDF 123); proof of Theorem 4.5.4, p.113 (PDF 127)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Lop

namespace BauerleRiederMDP.TransactionCosts

/-- The set of maximum points of the selling problem at the state `x = (0, 1)` (one unit in the
stock, nothing in the bond) of Bäuerle & Rieder (2011), proof of Proposition 4.5.2, step (ii),
p.109 (PDF 123), and proof of Theorem 4.5.4, p.113 (PDF 127):
`a ↦ IE v((1 − c)(1 − a)(1 + i_{n+1}), a R̃_{n+1})` on `0 ≤ a ≤ 1`. -/
def Market.argmaxPlus {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (v : ℝ × ℝ → EReal) : Set ℝ :=
  {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ b ∈ Set.Icc (0 : ℝ) 1,
    M.Lop n v (0, 1) ((1 - M.c) * (1 - b), b) ≤ M.Lop n v (0, 1) ((1 - M.c) * (1 - a), a)}

end BauerleRiederMDP.TransactionCosts


