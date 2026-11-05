-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_argmaxMinus
-- name    : BauerleRiederMDP_TransactionCosts_Market_argmaxMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:52.974792+00:00
-- url     : https://prove2.me/theorems/5ab1fc2d-d87e-4cb3-9779-228fe2945182
-- title:
--   Maximum points of the buying problem at $(1,0)$
-- statement:
--   For $v:E\to[-\infty,\infty)$ and time $n$, the set of maximum points on $[0,\frac1{1+c}]$ of
--   $$a\mapsto \mathbb E\,v\big((1-(1+c)a)(1+i_{n+1}),\ a\tilde R_{n+1}\big),$$
--   the one-stage problem in the state $x=(1,0)$ (one unit in the bond, nothing in the stock) of the proof of Proposition 4.5.2, step (iv).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), proof of Proposition 4.5.2, step (iv), p.111 (PDF 125)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Lop

namespace BauerleRiederMDP.TransactionCosts

/-- The set of maximum points of the buying problem at the state `x = (1, 0)` (one unit in the
bond, nothing in the stock) of Bäuerle & Rieder (2011), proof of Proposition 4.5.2, step (iv),
p.111 (PDF 125): `a ↦ IE v((1 − (1 + c)a)(1 + i_{n+1}), a R̃_{n+1})` on `0 ≤ a ≤ 1/(1 + c)`. -/
def Market.argmaxMinus {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (v : ℝ × ℝ → EReal) : Set ℝ :=
  {a | a ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)) ∧ ∀ b ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)),
    M.Lop n v (1, 0) (1 - (1 + M.c) * b, b) ≤ M.Lop n v (1, 0) (1 - (1 + M.c) * a, a)}

end BauerleRiederMDP.TransactionCosts


