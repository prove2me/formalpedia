-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_TChain
-- name    : BauerleRiederMDP_FiniteHorizon_TChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:27.022357+00:00
-- url     : https://prove2.me/theorems/ef040040-3672-46ca-8f80-5dd389fb0345
-- title:
--   Iterated operator $T_nT_{n+1}\cdots T_{n+k-1}v$
-- statement:
--   For $k\ge 0$, the function $T_nT_{n+1}\cdots T_{n+k-1}v$, where the inner operator is applied first; for $k=0$ it is $v$.
--
--   With $k=N-n$ and $v=g_N$ this is the right-hand side of part b) of the Structure Theorem.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Notation, p.20, and Theorem 2.3.8 b), p.23

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel T)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- The composition `T_n T_{n+1} … T_{n+k-1} v`, inner operator applied first (Bäuerle & Rieder
(2011), Notation on p.20, PDF 35); `k = 0` gives `v`. With `k = N - n` and `v = g_N` it is the
right-hand side of Theorem 2.3.8 b). -/
noncomputable def TChain {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) : (k : ℕ) → (n : ℕ) → (E → EReal) → (E → EReal)
  | 0, _, v => v
  | k + 1, n, v => T M n (TChain M k (n + 1) v)

end BauerleRiederMDP.FiniteHorizon


